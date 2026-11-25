import CmlTS.FpSem
import CmlTS.Ast
import CmlTS.Namespace
import CmlTS.Ffi
import CmlTS.SemanticPrimitives

/-
HOL4 theory `evaluate` (evaluateScript.sml).
-/

namespace CmlTS

noncomputable section

open scoped Classical

variable {ffi : Type}

/- HOL4:
Definition fix_clock_def:
  fix_clock s (s',res) =
    (s' with clock := if s'.clock ≤ s.clock then s'.clock else s.clock, res)
End
(`s` and `s'` may have different 'ffi types, as in HOL4) -/
def fix_clock {ffi1 ffi2 α : Type} (s : state ffi1) : state ffi2 × α → state ffi2 × α
  | (s', res) => ({ s' with clock := if s'.clock ≤ s.clock then s'.clock else s.clock }, res)

/- HOL4:
Definition dec_clock_def:
  dec_clock s = (s with clock := s.clock − 1)
End -/
def dec_clock (s : state ffi) : state ffi := { s with clock := s.clock - 1 }

/- HOL4:
Definition do_eval_res_def:
  do_eval_res vs s =
    case do_eval vs s.eval_state of
    | NONE => (s,Rerr (Rabort Rtype_error))
    | SOME (env1,decs,es1) => (s with eval_state := es1,Rval (env1,decs))
End -/
def do_eval_res {β : Type} (vs : List value) (s : state ffi) :
    state ffi × result (sem_env value × List dec) β :=
  match do_eval vs s.eval_state with
  | none => (s, Rerr (Rabort Rtype_error))
  | some (env1, decs, es1) => ({ s with eval_state := es1 }, Rval (env1, decs))

/- HOL4:
Definition list_result_def[simp]:
  list_result (Rval v) = Rval [v] ∧
  list_result (Rerr e) = Rerr e
End -/
def list_result {α β : Type} : result α β → result (List α) β
  | Rval v => Rval [v]
  | Rerr e => Rerr e

/-! Helper lemmas (not HOL4 constants) for the termination of `evaluate`. -/

theorem fix_clock_le_aux {α : Type} {s s1 : state ffi} {x : state ffi × α} {res : α}
    (h : fix_clock s x = (s1, res)) : s1.clock ≤ s.clock := by
  obtain ⟨s', r⟩ := x
  simp only [fix_clock, Prod.mk.injEq] at h
  obtain ⟨h, _⟩ := h
  subst h
  dsimp only
  split <;> omega

theorem sizeOf_append_aux {α : Type} [SizeOf α] (l1 l2 : List α) :
    sizeOf (l1 ++ l2) + 1 = sizeOf l1 + sizeOf l2 := by
  induction l1 with
  | nil => simp; omega
  | cons h t ih => simp only [List.cons_append, List.cons.sizeOf_spec]; omega

theorem sizeOf_reverse_aux {α : Type} [SizeOf α] (l : List α) : sizeOf l.reverse = sizeOf l := by
  induction l with
  | nil => simp
  | cons h t ih =>
    have := sizeOf_append_aux t.reverse [h]
    simp only [List.reverse_cons, List.cons.sizeOf_spec, List.nil.sizeOf_spec] at this ⊢
    omega

theorem sizeOf_list_pos_aux {α : Type} [SizeOf α] (l : List α) : 1 ≤ sizeOf l := by
  cases l <;> simp <;> omega

theorem do_log_exp_aux {l : lop} {v : value} {e e' : exp} (h : do_log l v e = some (Exp e')) :
    e' = e := by
  unfold do_log at h
  split at h
  · simp at h; exact h.symm
  · split at h <;> simp at h

theorem do_if_size_aux {v : value} {e1 e2 e : exp} (h : do_if v e1 e2 = some e) :
    sizeOf e ≤ sizeOf e1 + sizeOf e2 := by
  unfold do_if at h
  split at h
  · simp at h; subst h; omega
  · split at h
    · simp at h; subst h; omega
    · simp at h

theorem lex_lt_aux {a b c d : Nat} (h : a < b) :
    Prod.Lex (fun x y => x < y) (fun x y => x < y) (a, c) (b, d) :=
  Prod.Lex.left _ _ h

theorem lex_le_aux {a b c d : Nat} (h : a ≤ b) (h2 : c < d) :
    Prod.Lex (fun x y => x < y) (fun x y => x < y) (a, c) (b, d) := by
  rcases Nat.lt_or_ge a b with h1 | h1
  · exact Prod.Lex.left _ _ h1
  · have : a = b := by omega
    subst this
    exact Prod.Lex.right _ h2

/- HOL4:
Definition evaluate_def[nocompute]:
  evaluate st env [] = ((st:'ffi state),Rval [])
  ∧
  evaluate st env (e1::e2::es) =
    (case fix_clock st (evaluate st env [e1]) of
       (st',Rval v1) =>
         (case evaluate st' env (e2::es) of
            (st'',Rval vs) => (st'',Rval (HD v1::vs))
          | (st'',Rerr v8) => (st'',Rerr v8))
     | (st',Rerr v10) => (st',Rerr v10))
  ∧
  evaluate st env [Lit l] = (st,Rval [Litv l])
  ∧
  evaluate st env [Raise e] =
    (case evaluate st env [e] of
       (st',Rval v) => (st',Rerr (Rraise (HD v)))
     | (st',Rerr v8) => (st',Rerr v8))
  ∧
  evaluate st env [Handle e pes] =
    (case fix_clock st (evaluate st env [e]) of
       (st',Rval v7) => (st',Rval v7)
     | (st',Rerr (Rraise v)) =>
       if can_pmatch_all env.c st'.refs (MAP FST pes) v then
         evaluate_match st' env v pes v
       else (st',Rerr (Rabort Rtype_error))
     | (st',Rerr (Rabort v12)) => (st',Rerr (Rabort v12)))
  ∧
  evaluate st env [Con cn es] =
    (if do_con_check env.c cn (LENGTH es) then
       case evaluate st env (REVERSE es) of
         (st',Rval vs) =>
           (case build_conv env.c cn (REVERSE vs) of
              NONE => (st',Rerr (Rabort Rtype_error))
            | SOME v => (st',Rval [v]))
       | (st',Rerr v8) => (st',Rerr v8)
     else (st,Rerr (Rabort Rtype_error)))
  ∧
  evaluate st env [Var n] =
    (case nsLookup env.v n of
       NONE => (st,Rerr (Rabort Rtype_error))
     | SOME v => (st,Rval [v]))
  ∧
  evaluate st env [Fun x e] = (st,Rval [Closure env x e])
  ∧
  evaluate st env [App op es] =
   (case fix_clock st (evaluate st env (REVERSE es)) of
    (st', Rval vs) =>
    (case (getOpClass op) of
      FunApp =>
        (case do_opapp (REVERSE vs) of
          SOME (env',e) =>
            if st'.clock = 0 then
              (st', Rerr (Rabort Rtimeout_error))
            else
              evaluate (dec_clock st') env'  [e]
        | NONE => (st', Rerr (Rabort Rtype_error))
        )
     | Force =>
        (case dest_thunk (REVERSE vs) st'.refs of
         | BadRef => (st', Rerr (Rabort Rtype_error))
         | NotThunk => (st', Rerr (Rabort Rtype_error))
         | IsThunk Evaluated v => (st', Rval [v])
         | IsThunk NotEvaluated f =>
            (case do_opapp [f; Conv NONE []] of
             | SOME (env',e) =>
                 if st'.clock = 0 then (st', Rerr (Rabort Rtimeout_error)) else
                   (case evaluate (dec_clock st') env' [e] of
                    | (st2, Rval vs2) =>
                        (case update_thunk (REVERSE vs) st2.refs vs2 of
                         | NONE => (st2, Rerr (Rabort Rtype_error))
                         | SOME refs => (st2 with refs := refs, Rval vs2))
                    | (st2, Rerr e) => (st2, Rerr e))
             | NONE => (st', Rerr (Rabort Rtype_error))))
     | EvalOp =>
        (case fix_clock st' (do_eval_res (REVERSE vs) st') of
          (st1, Rval (env1, decs)) =>
            if st1.clock = 0 then
              (st1, Rerr (Rabort Rtimeout_error))
            else
              (case fix_clock (dec_clock st1)
                      (evaluate_decs (dec_clock st1) env1 decs) of
                (st2, Rval env2) => (case declare_env st2.eval_state
                  (extend_dec_env env2 env1) of
                  SOME (x, es2) => (( st2 with<| eval_state :=
                    (reset_env_generation st'.eval_state es2) |>), Rval [x])
                | NONE => (st2, Rerr (Rabort Rtype_error)))
              | (st2, Rerr (Rabort a)) => (st2, Rerr (Rabort a))
              | (st2, Rerr e) => (( st2 with<| eval_state :=
                  (reset_env_generation st'.eval_state st2.eval_state) |>), Rerr e))
        | (st1, Rerr e) => (st1, Rerr e))
    | Simple =>
        (case do_app (st'.refs,st'.ffi) op (REVERSE vs) of
          NONE => (st', Rerr (Rabort Rtype_error))
        | SOME ((refs,ffi),r) =>
            (( st' with<| refs := refs; ffi := ffi |>), list_result r)))
    | res => res)
  ∧
  evaluate st env [Log lop e1 e2] =
    (case fix_clock st (evaluate st env [e1]) of
       (st',Rval v1) =>
         (case do_log lop (HD v1) e2 of
            NONE => (st',Rerr (Rabort Rtype_error))
          | SOME (Exp e) => evaluate st' env [e]
          | SOME (Val v) => (st',Rval [v]))
     | (st',Rerr v9) => (st',Rerr v9))
  ∧
  evaluate st env [If e1 e2 e3] =
    (case fix_clock st (evaluate st env [e1]) of
       (st',Rval v) =>
         (case do_if (HD v) e2 e3 of
            NONE => (st',Rerr (Rabort Rtype_error))
          | SOME e => evaluate st' env [e])
     | (st',Rerr v8) => (st',Rerr v8))
  ∧
  evaluate st env [Mat e pes] =
    (case fix_clock st (evaluate st env [e]) of
       (st',Rval v) =>
         if can_pmatch_all env.c st'.refs (MAP FST pes) (HD v) then
           evaluate_match st' env (HD v) pes bind_exn_v
         else (st',Rerr (Rabort Rtype_error))
     | (st',Rerr v8) => (st',Rerr v8))
  ∧
  evaluate st env [Let xo e1 e2] =
    (case fix_clock st (evaluate st env [e1]) of
       (st',Rval v) =>
         evaluate st' (env with v := nsOptBind xo (HD v) env.v) [e2]
     | (st',Rerr v8) => (st',Rerr v8))
  ∧
  evaluate st env [Letrec funs e] =
    (if ALL_DISTINCT (MAP (λ(x,y,z). x) funs) then
       evaluate st (env with v := build_rec_env funs env env.v) [e]
     else (st,Rerr (Rabort Rtype_error)))
  ∧
  evaluate st env [Tannot e t] = evaluate st env [e]
  ∧
  evaluate st env [Lannot e l] = evaluate st env [e]
  ∧
  evaluate_match st env v [] err_v = (st,Rerr (Rraise err_v))
  ∧
  evaluate_match st env v ((p,e)::pes) err_v =
    (if ALL_DISTINCT (pat_bindings p []) then
       case pmatch env.c st.refs p v [] of
         No_match => evaluate_match st env v pes err_v
       | Match_type_error => (st,Rerr (Rabort Rtype_error))
       | Match env_v' =>
         evaluate st (env with v := nsAppend (alist_to_ns env_v') env.v) [e]
     else (st,Rerr (Rabort Rtype_error)))
  ∧
  evaluate_decs st env [] = (st,Rval <|v := nsEmpty; c := nsEmpty|>)
  ∧
  evaluate_decs st env (d1::d2::ds) =
    (case fix_clock st (evaluate_decs st env [d1]) of
       (st1,Rval env1) =>
         (case evaluate_decs st1 (extend_dec_env env1 env) (d2::ds) of
            (st2,r) => (st2,combine_dec_result env1 r))
     | (st1,Rerr v7) => (st1,Rerr v7))
  ∧
  evaluate_decs st env [Dlet locs p e] =
    (if ALL_DISTINCT (pat_bindings p []) ∧
        every_exp (one_con_check env.c) e
     then
       case evaluate st env [e] of
         (st',Rval v) =>
           (st',
            case pmatch env.c st'.refs p (HD v) [] of
              No_match => Rerr (Rraise bind_exn_v)
            | Match_type_error => Rerr (Rabort Rtype_error)
            | Match new_vals =>
              Rval <|v := alist_to_ns new_vals; c := nsEmpty|>)
       | (st',Rerr err) => (st',Rerr err)
     else (st,Rerr (Rabort Rtype_error)))
  ∧
  evaluate_decs st env [Dletrec locs funs] =
    (st,
     if ALL_DISTINCT (MAP (λ(x,y,z). x) funs) ∧
        EVERY (λ(f,n,e). every_exp (one_con_check env.c) e) funs
     then
       Rval <|v := build_rec_env funs env nsEmpty; c := nsEmpty|>
     else Rerr (Rabort Rtype_error))
  ∧
  evaluate_decs st env [Dtype locs tds] =
    (if EVERY check_dup_ctors tds then
       (st with next_type_stamp := st.next_type_stamp + LENGTH tds,
        Rval <|v := nsEmpty; c := build_tdefs st.next_type_stamp tds|>)
     else (st,Rerr (Rabort Rtype_error)))
  ∧
  evaluate_decs st env [Dtabbrev locs tvs tn t] =
    (st,Rval <|v := nsEmpty; c := nsEmpty|>)
  ∧
  evaluate_decs st env [Denv n] =
    (case declare_env st.eval_state env of
       NONE => (st,Rerr (Rabort Rtype_error))
     | SOME (x,es') =>
       (st with eval_state := es',Rval <|v := nsSing n x; c := nsEmpty|>))
  ∧
  evaluate_decs st env [Dexn locs cn ts] =
    (st with next_exn_stamp := st.next_exn_stamp + 1,
     Rval
       <|v := nsEmpty;
         c := nsSing cn (LENGTH ts,ExnStamp st.next_exn_stamp)|>)
  ∧
  evaluate_decs st env [Dmod mn ds] =
    (case evaluate_decs st env ds of
       (st',r) =>
         (st',
          case r of
            Rval env' =>
              Rval <|v := nsLift mn env'.v; c := nsLift mn env'.c|>
          | Rerr err => Rerr err))
  ∧
  evaluate_decs st env [Dlocal lds ds] =
    case fix_clock st (evaluate_decs st env lds) of
      (st1,Rval env1) => evaluate_decs st1 (extend_dec_env env1 env) ds
    | (st1,Rerr v7) => (st1,Rerr v7)
  [HOL4 proof text removed]
End
(HOL4 later rewrites the equations with `fix_clock_evaluate` and
`fix_clock_do_eval_res`; the function is the same.) -/
mutual

def evaluate : state ffi → sem_env value → List exp → state ffi × result (List value) value
  | st, _, [] => (st, Rval [])
  | st, env, e1 :: e2 :: es =>
    match _h : fix_clock st (evaluate st env [e1]) with
    | (st', Rval v1) =>
      match evaluate st' env (e2 :: es) with
      | (st'', Rval vs) => (st'', Rval (HD v1 :: vs))
      | (st'', Rerr v8) => (st'', Rerr v8)
    | (st', Rerr v10) => (st', Rerr v10)
  | st, _, [exp.Lit l] => (st, Rval [Litv l])
  | st, env, [exp.Raise e] =>
    match evaluate st env [e] with
    | (st', Rval v) => (st', Rerr (Rraise (HD v)))
    | (st', Rerr v8) => (st', Rerr v8)
  | st, env, [exp.Handle e pes] =>
    match _h : fix_clock st (evaluate st env [e]) with
    | (st', Rval v7) => (st', Rval v7)
    | (st', Rerr (Rraise v)) =>
      if can_pmatch_all env.c st'.refs (pes.map Prod.fst) v then
        evaluate_match st' env v pes v
      else (st', Rerr (Rabort Rtype_error))
    | (st', Rerr (Rabort v12)) => (st', Rerr (Rabort v12))
  | st, env, [exp.Con cn es] =>
    if do_con_check env.c cn es.length then
      match evaluate st env es.reverse with
      | (st', Rval vs) =>
        match build_conv env.c cn vs.reverse with
        | none => (st', Rerr (Rabort Rtype_error))
        | some v => (st', Rval [v])
      | (st', Rerr v8) => (st', Rerr v8)
    else (st, Rerr (Rabort Rtype_error))
  | st, env, [exp.Var n] =>
    match nsLookup env.v n with
    | none => (st, Rerr (Rabort Rtype_error))
    | some v => (st, Rval [v])
  | st, env, [exp.Fun x e] => (st, Rval [Closure env x e])
  | st, env, [exp.App o es] =>
    match _h : fix_clock st (evaluate st env es.reverse) with
    | (st', Rval vs) =>
      match getOpClass o with
      | FunApp =>
        match do_opapp vs.reverse with
        | some (env', e) =>
          if st'.clock = 0 then (st', Rerr (Rabort Rtimeout_error))
          else evaluate (dec_clock st') env' [e]
        | none => (st', Rerr (Rabort Rtype_error))
      | Force =>
        match dest_thunk vs.reverse st'.refs with
        | BadRef => (st', Rerr (Rabort Rtype_error))
        | NotThunk => (st', Rerr (Rabort Rtype_error))
        | IsThunk Evaluated v => (st', Rval [v])
        | IsThunk NotEvaluated f =>
          match do_opapp [f, Conv none []] with
          | some (env', e) =>
            if st'.clock = 0 then (st', Rerr (Rabort Rtimeout_error))
            else
              match evaluate (dec_clock st') env' [e] with
              | (st2, Rval vs2) =>
                match update_thunk vs.reverse st2.refs vs2 with
                | none => (st2, Rerr (Rabort Rtype_error))
                | some refs => ({ st2 with refs := refs }, Rval vs2)
              | (st2, Rerr e) => (st2, Rerr e)
          | none => (st', Rerr (Rabort Rtype_error))
      | EvalOp =>
        match _h2 : fix_clock st' (do_eval_res vs.reverse st') with
        | (st1, Rval (env1, decs)) =>
          if st1.clock = 0 then (st1, Rerr (Rabort Rtimeout_error))
          else
            match fix_clock (dec_clock st1) (evaluate_decs (dec_clock st1) env1 decs) with
            | (st2, Rval env2) =>
              match declare_env st2.eval_state (extend_dec_env env2 env1) with
              | some (x, es2) =>
                ({ st2 with eval_state := reset_env_generation st'.eval_state es2 }, Rval [x])
              | none => (st2, Rerr (Rabort Rtype_error))
            | (st2, Rerr (Rabort a)) => (st2, Rerr (Rabort a))
            | (st2, Rerr e) =>
              ({ st2 with
                  eval_state := reset_env_generation st'.eval_state st2.eval_state }, Rerr e)
        | (st1, Rerr e) => (st1, Rerr e)
      | Simple =>
        match do_app (st'.refs, st'.ffi) o vs.reverse with
        | none => (st', Rerr (Rabort Rtype_error))
        | some ((refs, ffi), r) => ({ st' with refs := refs, ffi := ffi }, list_result r)
    | res => res
  | st, env, [exp.Log l e1 e2] =>
    match _h : fix_clock st (evaluate st env [e1]) with
    | (st', Rval v1) =>
      match _h2 : do_log l (HD v1) e2 with
      | none => (st', Rerr (Rabort Rtype_error))
      | some (Exp e) => evaluate st' env [e]
      | some (Val v) => (st', Rval [v])
    | (st', Rerr v9) => (st', Rerr v9)
  | st, env, [exp.If e1 e2 e3] =>
    match _h : fix_clock st (evaluate st env [e1]) with
    | (st', Rval v) =>
      match _h2 : do_if (HD v) e2 e3 with
      | none => (st', Rerr (Rabort Rtype_error))
      | some e => evaluate st' env [e]
    | (st', Rerr v8) => (st', Rerr v8)
  | st, env, [exp.Mat e pes] =>
    match _h : fix_clock st (evaluate st env [e]) with
    | (st', Rval v) =>
      if can_pmatch_all env.c st'.refs (pes.map Prod.fst) (HD v) then
        evaluate_match st' env (HD v) pes bind_exn_v
      else (st', Rerr (Rabort Rtype_error))
    | (st', Rerr v8) => (st', Rerr v8)
  | st, env, [exp.Let xo e1 e2] =>
    match _h : fix_clock st (evaluate st env [e1]) with
    | (st', Rval v) => evaluate st' { env with v := nsOptBind xo (HD v) env.v } [e2]
    | (st', Rerr v8) => (st', Rerr v8)
  | st, env, [exp.Letrec funs e] =>
    if ALL_DISTINCT (funs.map (fun (x, _, _) => x)) then
      evaluate st { env with v := build_rec_env funs env env.v } [e]
    else (st, Rerr (Rabort Rtype_error))
  | st, env, [exp.Tannot e _] => evaluate st env [e]
  | st, env, [exp.Lannot e _] => evaluate st env [e]
termination_by st _ es => (st.clock, sizeOf es)
decreasing_by
  all_goals
    first
    | (refine lex_le_aux (Nat.le_refl _) ?_
       simp only [sizeOf_reverse_aux, List.cons.sizeOf_spec, List.nil.sizeOf_spec,
         exp.Raise.sizeOf_spec, exp.Handle.sizeOf_spec, exp.Con.sizeOf_spec, exp.App.sizeOf_spec,
         exp.Log.sizeOf_spec, exp.If.sizeOf_spec, exp.Mat.sizeOf_spec, exp.Let.sizeOf_spec,
         exp.Letrec.sizeOf_spec, exp.Tannot.sizeOf_spec, exp.Lannot.sizeOf_spec]
       omega)
    | (have hp := sizeOf_list_pos_aux es
       refine lex_le_aux (Nat.le_refl _) ?_
       simp only [List.cons.sizeOf_spec, List.nil.sizeOf_spec]
       omega)
    | (have hc := fix_clock_le_aux _h
       have hl := do_log_exp_aux _h2
       subst hl
       refine lex_le_aux hc ?_
       simp only [List.cons.sizeOf_spec, List.nil.sizeOf_spec, exp.Log.sizeOf_spec]
       omega)
    | (have hc := fix_clock_le_aux _h
       have hl := do_if_size_aux _h2
       refine lex_le_aux hc ?_
       simp only [List.cons.sizeOf_spec, List.nil.sizeOf_spec, exp.If.sizeOf_spec]
       omega)
    | (have hc := fix_clock_le_aux _h
       refine lex_le_aux hc ?_
       simp only [List.cons.sizeOf_spec, List.nil.sizeOf_spec, exp.Handle.sizeOf_spec,
         exp.Mat.sizeOf_spec, exp.Let.sizeOf_spec]
       omega)
    | (have hc := fix_clock_le_aux _h
       refine lex_lt_aux ?_
       simp only [dec_clock]
       omega)
    | (have hc := fix_clock_le_aux _h
       have hd := fix_clock_le_aux _h2
       refine lex_lt_aux ?_
       simp only [dec_clock]
       omega)

def evaluate_match : state ffi → sem_env value → value → List (pat × exp) → value →
    state ffi × result (List value) value
  | st, _, _, [], err_v => (st, Rerr (Rraise err_v))
  | st, env, v, (p, e) :: pes, err_v =>
    if ALL_DISTINCT (pat_bindings p []) then
      match pmatch env.c st.refs p v [] with
      | No_match => evaluate_match st env v pes err_v
      | Match_type_error => (st, Rerr (Rabort Rtype_error))
      | Match env_v' =>
        evaluate st { env with v := nsAppend (alist_to_ns env_v') env.v } [e]
    else (st, Rerr (Rabort Rtype_error))
termination_by st _ _ pes _ => (st.clock, sizeOf pes)
decreasing_by
  all_goals
    refine lex_le_aux (Nat.le_refl _) ?_
    simp only [List.cons.sizeOf_spec, List.nil.sizeOf_spec, Prod.mk.sizeOf_spec]
    have hp := sizeOf_list_pos_aux pes
    omega

def evaluate_decs : state ffi → sem_env value → List dec →
    state ffi × result (sem_env value) value
  | st, _, [] => (st, Rval { v := nsEmpty, c := nsEmpty })
  | st, env, d1 :: d2 :: ds =>
    match _h : fix_clock st (evaluate_decs st env [d1]) with
    | (st1, Rval env1) =>
      match evaluate_decs st1 (extend_dec_env env1 env) (d2 :: ds) with
      | (st2, r) => (st2, combine_dec_result env1 r)
    | (st1, Rerr v7) => (st1, Rerr v7)
  | st, env, [Dlet _ p e] =>
    if ALL_DISTINCT (pat_bindings p []) ∧ every_exp (one_con_check env.c) e then
      match evaluate st env [e] with
      | (st', Rval v) =>
        (st',
          match pmatch env.c st'.refs p (HD v) [] with
          | No_match => Rerr (Rraise bind_exn_v)
          | Match_type_error => Rerr (Rabort Rtype_error)
          | Match new_vals => Rval { v := alist_to_ns new_vals, c := nsEmpty })
      | (st', Rerr err) => (st', Rerr err)
    else (st, Rerr (Rabort Rtype_error))
  | st, env, [Dletrec _ funs] =>
    (st,
      if ALL_DISTINCT (funs.map (fun (x, _, _) => x)) ∧
          EVERY (fun (_, _, e) => every_exp (one_con_check env.c) e) funs then
        Rval { v := build_rec_env funs env nsEmpty, c := nsEmpty }
      else Rerr (Rabort Rtype_error))
  | st, _, [Dtype _ tds] =>
    if EVERY check_dup_ctors tds then
      ({ st with next_type_stamp := st.next_type_stamp + tds.length },
        Rval { v := nsEmpty, c := build_tdefs st.next_type_stamp tds })
    else (st, Rerr (Rabort Rtype_error))
  | st, _, [Dtabbrev _ _ _ _] => (st, Rval { v := nsEmpty, c := nsEmpty })
  | st, env, [Denv n] =>
    match declare_env st.eval_state env with
    | none => (st, Rerr (Rabort Rtype_error))
    | some (x, es') => ({ st with eval_state := es' }, Rval { v := nsSing n x, c := nsEmpty })
  | st, _, [Dexn _ cn ts] =>
    ({ st with next_exn_stamp := st.next_exn_stamp + 1 },
      Rval { v := nsEmpty, c := nsSing cn (ts.length, ExnStamp st.next_exn_stamp) })
  | st, env, [Dmod mn ds] =>
    match evaluate_decs st env ds with
    | (st', r) =>
      (st',
        match r with
        | Rval env' => Rval { v := nsLift mn env'.v, c := nsLift mn env'.c }
        | Rerr err => Rerr err)
  | st, env, [Dlocal lds ds] =>
    match _h : fix_clock st (evaluate_decs st env lds) with
    | (st1, Rval env1) => evaluate_decs st1 (extend_dec_env env1 env) ds
    | (st1, Rerr v7) => (st1, Rerr v7)
termination_by st _ ds => (st.clock, sizeOf ds)
decreasing_by
  all_goals
    first
    | (refine lex_le_aux (Nat.le_refl _) ?_
       simp only [List.cons.sizeOf_spec, List.nil.sizeOf_spec, dec.Dlet.sizeOf_spec,
         dec.Dmod.sizeOf_spec, dec.Dlocal.sizeOf_spec]
       omega)
    | (have hp := sizeOf_list_pos_aux ds
       refine lex_le_aux (Nat.le_refl _) ?_
       simp only [List.cons.sizeOf_spec, List.nil.sizeOf_spec]
       omega)
    | (have hc := fix_clock_le_aux _h
       refine lex_le_aux hc ?_
       simp only [List.cons.sizeOf_spec, List.nil.sizeOf_spec, dec.Dlocal.sizeOf_spec]
       omega)

end

/-! ### Auxiliary: an induction principle following the recursion of `evaluate` -/

theorem Aux.eval_induct {P : state ffi → sem_env value → List exp → Prop}
    {Q : state ffi → sem_env value → value → List (pat × exp) → value → Prop}
    {D : state ffi → sem_env value → List dec → Prop}
    (nil : ∀ st env, P st env [])
    (cons : ∀ st env e1 e2 es, P st env [e1] →
      (∀ st', st'.clock ≤ st.clock → P st' env (e2 :: es)) → P st env (e1 :: e2 :: es))
    (Lit : ∀ st env l, P st env [exp.Lit l])
    (Raise : ∀ st env e, P st env [e] → P st env [exp.Raise e])
    (Handle : ∀ st env e pes, P st env [e] →
      (∀ st' v, st'.clock ≤ st.clock → Q st' env v pes v) → P st env [exp.Handle e pes])
    (Con : ∀ st env cn es, P st env es.reverse → P st env [exp.Con cn es])
    (Var : ∀ st env n, P st env [exp.Var n])
    (Fun : ∀ st env x e, P st env [exp.Fun x e])
    (App : ∀ st env o es, P st env es.reverse →
      (∀ st' env' e, st'.clock < st.clock → P st' env' [e]) →
      (∀ st' env' ds, st'.clock < st.clock → D st' env' ds) → P st env [exp.App o es])
    (Log : ∀ st env l e1 e2, P st env [e1] →
      (∀ st', st'.clock ≤ st.clock → P st' env [e2]) → P st env [exp.Log l e1 e2])
    (If : ∀ st env e1 e2 e3, P st env [e1] →
      (∀ st', st'.clock ≤ st.clock → P st' env [e2]) →
      (∀ st', st'.clock ≤ st.clock → P st' env [e3]) → P st env [exp.If e1 e2 e3])
    (Mat : ∀ st env e pes, P st env [e] →
      (∀ st' v, st'.clock ≤ st.clock → Q st' env v pes bind_exn_v) → P st env [exp.Mat e pes])
    (Let : ∀ st env xo e1 e2, P st env [e1] →
      (∀ st' env', st'.clock ≤ st.clock → P st' env' [e2]) → P st env [exp.Let xo e1 e2])
    (Letrec : ∀ st env funs e, (∀ env', P st env' [e]) → P st env [exp.Letrec funs e])
    (Tannot : ∀ st env e t, P st env [e] → P st env [exp.Tannot e t])
    (Lannot : ∀ st env e l, P st env [e] → P st env [exp.Lannot e l])
    (mnil : ∀ st env v err, Q st env v [] err)
    (mcons : ∀ st env v p e pes err, Q st env v pes err → (∀ env', P st env' [e]) →
      Q st env v ((p, e) :: pes) err)
    (dnil : ∀ st env, D st env [])
    (dcons : ∀ st env d1 d2 ds, D st env [d1] →
      (∀ st' env', st'.clock ≤ st.clock → D st' env' (d2 :: ds)) → D st env (d1 :: d2 :: ds))
    (dlet : ∀ st env l p e, P st env [e] → D st env [Dlet l p e])
    (dletrec : ∀ st env l funs, D st env [Dletrec l funs])
    (dtype : ∀ st env l tds, D st env [Dtype l tds])
    (dtabbrev : ∀ st env l tvs tn t, D st env [Dtabbrev l tvs tn t])
    (dexn : ∀ st env l cn ts, D st env [Dexn l cn ts])
    (dmod : ∀ st env mn ds, D st env ds → D st env [Dmod mn ds])
    (dlocal : ∀ st env lds ds, D st env lds →
      (∀ st' env', st'.clock ≤ st.clock → D st' env' ds) → D st env [Dlocal lds ds])
    (denv : ∀ st env n, D st env [Denv n]) :
    (∀ st env es, P st env es) ∧ (∀ st env v pes err, Q st env v pes err) ∧
    (∀ st env ds, D st env ds) := by
  have key : ∀ k n, (∀ st env es, st.clock ≤ k → sizeOf es ≤ n → P st env es) ∧
      (∀ st env v pes err, st.clock ≤ k → sizeOf pes ≤ n → Q st env v pes err) ∧
      (∀ st env ds, st.clock ≤ k → sizeOf ds ≤ n → D st env ds) := by
    intro k
    induction k using Nat.strongRecOn with
    | ind k ihk =>
    intro n
    induction n with
    | zero =>
      refine ⟨fun st env es _ h => ?_, fun st env v pes err _ h => ?_, fun st env ds _ h => ?_⟩
      · have := sizeOf_list_pos_aux es; omega
      · have := sizeOf_list_pos_aux pes; omega
      · have := sizeOf_list_pos_aux ds; omega
    | succ n ihn =>
      obtain ⟨ihP, ihQ, ihD⟩ := ihn
      have lowP : ∀ (st : state ffi), st.clock ≤ k → ∀ st' env' e, st'.clock < st.clock →
          P st' env' [e] := fun st hk st' env' e h =>
        (ihk st'.clock (by omega) (sizeOf [e])).1 st' env' [e] (Nat.le_refl _) (Nat.le_refl _)
      have lowD : ∀ (st : state ffi), st.clock ≤ k → ∀ st' env' ds, st'.clock < st.clock →
          D st' env' ds := fun st hk st' env' ds h =>
        (ihk st'.clock (by omega) (sizeOf ds)).2.2 st' env' ds (Nat.le_refl _) (Nat.le_refl _)
      refine ⟨fun st env es hk h => ?_, fun st env v pes err hk h => ?_,
        fun st env ds hk h => ?_⟩
      · cases es with
        | nil => exact nil st env
        | cons e1 es =>
          cases es with
          | cons e2 es =>
            simp only [List.cons.sizeOf_spec] at h
            have hp := sizeOf_list_pos_aux es
            refine cons st env e1 e2 es (ihP _ _ _ hk ?_)
              (fun st' h' => ihP _ _ _ (by omega) ?_)
            · simp only [List.cons.sizeOf_spec, List.nil.sizeOf_spec]; omega
            · simp only [List.cons.sizeOf_spec]; omega
          | nil =>
            simp only [List.cons.sizeOf_spec, List.nil.sizeOf_spec] at h
            have single : ∀ e : exp, sizeOf [e] = 1 + sizeOf e + 1 := fun e => by
              simp only [List.cons.sizeOf_spec, List.nil.sizeOf_spec]
            cases e1 with
            | Raise e =>
              simp only [exp.Raise.sizeOf_spec] at h
              exact Raise _ _ _ (ihP _ _ _ hk (by rw [single]; omega))
            | Handle e pes =>
              simp only [exp.Handle.sizeOf_spec] at h
              exact Handle _ _ _ _ (ihP _ _ _ hk (by rw [single]; omega))
                (fun st' v h' => ihQ _ _ _ _ _ (by omega) (by omega))
            | Lit l => exact Lit _ _ _
            | Con cn es =>
              simp only [exp.Con.sizeOf_spec] at h
              exact Con _ _ _ _ (ihP _ _ _ hk (by rw [sizeOf_reverse_aux]; omega))
            | Var x => exact Var _ _ _
            | Fun x e => exact Fun _ _ _ _
            | App o es =>
              simp only [exp.App.sizeOf_spec] at h
              exact App _ _ _ _ (ihP _ _ _ hk (by rw [sizeOf_reverse_aux]; omega))
                (lowP st hk) (lowD st hk)
            | Log l e1 e2 =>
              simp only [exp.Log.sizeOf_spec] at h
              exact Log _ _ _ _ _ (ihP _ _ _ hk (by rw [single]; omega))
                (fun st' h' => ihP _ _ _ (by omega) (by rw [single]; omega))
            | If e1 e2 e3 =>
              simp only [exp.If.sizeOf_spec] at h
              exact If _ _ _ _ _ (ihP _ _ _ hk (by rw [single]; omega))
                (fun st' h' => ihP _ _ _ (by omega) (by rw [single]; omega))
                (fun st' h' => ihP _ _ _ (by omega) (by rw [single]; omega))
            | Mat e pes =>
              simp only [exp.Mat.sizeOf_spec] at h
              exact Mat _ _ _ _ (ihP _ _ _ hk (by rw [single]; omega))
                (fun st' v h' => ihQ _ _ _ _ _ (by omega) (by omega))
            | Let xo e1 e2 =>
              simp only [exp.Let.sizeOf_spec] at h
              exact Let _ _ _ _ _ (ihP _ _ _ hk (by rw [single]; omega))
                (fun st' env' h' => ihP _ _ _ (by omega) (by rw [single]; omega))
            | Letrec funs e =>
              simp only [exp.Letrec.sizeOf_spec] at h
              exact Letrec _ _ _ _ (fun env' => ihP _ _ _ hk (by rw [single]; omega))
            | Tannot e t =>
              simp only [exp.Tannot.sizeOf_spec] at h
              exact Tannot _ _ _ _ (ihP _ _ _ hk (by rw [single]; omega))
            | Lannot e l =>
              simp only [exp.Lannot.sizeOf_spec] at h
              exact Lannot _ _ _ _ (ihP _ _ _ hk (by rw [single]; omega))
      · cases pes with
        | nil => exact mnil _ _ _ _
        | cons pe pes =>
          obtain ⟨p, e⟩ := pe
          have hp := sizeOf_list_pos_aux pes
          simp only [List.cons.sizeOf_spec, Prod.mk.sizeOf_spec] at h
          refine mcons _ _ _ _ _ _ _ (ihQ _ _ _ _ _ hk (by omega))
            (fun env' => ihP _ _ _ hk ?_)
          simp only [List.cons.sizeOf_spec, List.nil.sizeOf_spec]
          omega
      · cases ds with
        | nil => exact dnil _ _
        | cons d1 ds =>
          cases ds with
          | cons d2 ds =>
            simp only [List.cons.sizeOf_spec] at h
            have hp := sizeOf_list_pos_aux ds
            refine dcons st env d1 d2 ds (ihD _ _ _ hk ?_)
              (fun st' env' h' => ihD _ _ _ (by omega) ?_)
            · simp only [List.cons.sizeOf_spec, List.nil.sizeOf_spec]; omega
            · simp only [List.cons.sizeOf_spec]; omega
          | nil =>
            simp only [List.cons.sizeOf_spec, List.nil.sizeOf_spec] at h
            cases d1 with
            | Dlet l p e =>
              simp only [dec.Dlet.sizeOf_spec] at h
              refine dlet _ _ _ _ _ (ihP _ _ _ hk ?_)
              simp only [List.cons.sizeOf_spec, List.nil.sizeOf_spec]
              omega
            | Dletrec l funs => exact dletrec _ _ _ _
            | Dtype l tds => exact dtype _ _ _ _
            | Dtabbrev l tvs tn t => exact dtabbrev _ _ _ _ _ _
            | Dexn l cn ts => exact dexn _ _ _ _ _
            | Dmod mn ds =>
              simp only [dec.Dmod.sizeOf_spec] at h
              exact dmod _ _ _ _ (ihD _ _ _ hk (by omega))
            | Dlocal lds ds =>
              simp only [dec.Dlocal.sizeOf_spec] at h
              exact dlocal _ _ _ _ (ihD _ _ _ hk (by omega))
                (fun st' env' h' => ihD _ _ _ (by omega) (by omega))
            | Denv n => exact denv _ _ _
  refine ⟨fun st env es => ?_, fun st env v pes err => ?_, fun st env ds => ?_⟩
  · exact (key st.clock (sizeOf es)).1 _ _ _ (Nat.le_refl _) (Nat.le_refl _)
  · exact (key st.clock (sizeOf pes)).2.1 _ _ _ _ _ (Nat.le_refl _) (Nat.le_refl _)
  · exact (key st.clock (sizeOf ds)).2.2 _ _ _ (Nat.le_refl _) (Nat.le_refl _)

/-! ### Theorems -/

/- HOL4:
Theorem evaluate_clock:
  (∀(s1:'ffi state) env e r s2.
     evaluate s1 env e = (s2,r) ⇒ s2.clock ≤ s1.clock) ∧
  (∀(s1:'ffi state) env v p v' r s2.
     evaluate_match s1 env v p v' = (s2,r) ⇒ s2.clock ≤ s1.clock) ∧
  (∀(s1:'ffi state) env ds r s2.
     evaluate_decs s1 env ds = (s2,r) ⇒ s2.clock ≤ s1.clock) -/
theorem evaluate_clock :
    (∀ (s1 : state ffi) (env : sem_env value) (e : List exp) (r : result (List value) value)
        (s2 : state ffi),
      evaluate s1 env e = (s2, r) → s2.clock ≤ s1.clock) ∧
    (∀ (s1 : state ffi) (env : sem_env value) (v : value) (p : List (pat × exp)) (v' : value)
        (r : result (List value) value) (s2 : state ffi),
      evaluate_match s1 env v p v' = (s2, r) → s2.clock ≤ s1.clock) ∧
    (∀ (s1 : state ffi) (env : sem_env value) (ds : List dec)
        (r : result (sem_env value) value) (s2 : state ffi),
      evaluate_decs s1 env ds = (s2, r) → s2.clock ≤ s1.clock) := by
  have H := Aux.eval_induct (ffi := ffi)
    (P := fun st env es => ∀ r s2, evaluate st env es = (s2, r) → s2.clock ≤ st.clock)
    (Q := fun st env v pes err =>
      ∀ r s2, evaluate_match st env v pes err = (s2, r) → s2.clock ≤ st.clock)
    (D := fun st env ds => ∀ r s2, evaluate_decs st env ds = (s2, r) → s2.clock ≤ st.clock)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact ⟨fun s1 env e r s2 => H.1 s1 env e r s2,
      fun s1 env v p v' r s2 => H.2.1 s1 env v p v' r s2,
      fun s1 env ds r s2 => H.2.2 s1 env ds r s2⟩
  · intro st env r s2 h
    rw [evaluate] at h
    cases h
    exact Nat.le_refl _
  · intro st env e1 e2 es ih1 ih2 r s2 h
    rw [evaluate] at h
    split at h
    · rename_i hf
      have hc := fix_clock_le_aux hf
      split at h
      · rename_i he; cases h
        exact Nat.le_trans (ih2 _ hc _ _ he) hc
      · rename_i he; cases h
        exact Nat.le_trans (ih2 _ hc _ _ he) hc
    · rename_i hf; cases h
      exact fix_clock_le_aux hf
  · intro st env l r s2 h
    rw [evaluate] at h; cases h; exact Nat.le_refl _
  · intro st env e ih r s2 h
    rw [evaluate] at h
    split at h <;> (rename_i he; cases h; exact ih _ _ he)
  · intro st env e pes ih1 ih2 r s2 h
    rw [evaluate] at h
    split at h
    · rename_i hf; cases h; exact fix_clock_le_aux hf
    · rename_i hf
      have hc := fix_clock_le_aux hf
      split at h
      · exact Nat.le_trans (ih2 _ _ hc _ _ h) hc
      · cases h; exact hc
    · rename_i hf; cases h; exact fix_clock_le_aux hf
  · intro st env cn es ih r s2 h
    rw [evaluate] at h
    split at h
    · split at h
      · rename_i he
        split at h <;> (cases h; exact ih _ _ he)
      · rename_i he; cases h; exact ih _ _ he
    · cases h; exact Nat.le_refl _
  · intro st env n r s2 h
    rw [evaluate] at h
    split at h <;> (cases h; exact Nat.le_refl _)
  · intro st env x e r s2 h
    rw [evaluate] at h; cases h; exact Nat.le_refl _
  · intro st env o es ih1 ih2 ih3 r s2 h
    rw [evaluate] at h
    split at h
    · rename_i st' vs hf
      have hc := fix_clock_le_aux hf
      split at h
      · split at h
        · split at h
          · cases h; exact hc
          · have hd : (dec_clock st').clock < st.clock := by simp only [dec_clock]; omega
            exact Nat.le_trans (ih2 _ _ _ hd _ _ h) (Nat.le_of_lt hd)
        · cases h; exact hc
      · split at h
        · cases h; exact hc
        · cases h; exact hc
        · cases h; exact hc
        · split at h
          · split at h
            · cases h; exact hc
            · have hd : (dec_clock st').clock < st.clock := by simp only [dec_clock]; omega
              split at h
              · rename_i he
                have := Nat.le_trans (ih2 _ _ _ hd _ _ he) (Nat.le_of_lt hd)
                split at h <;> (cases h; exact this)
              · rename_i he
                cases h
                exact Nat.le_trans (ih2 _ _ _ hd _ _ he) (Nat.le_of_lt hd)
          · cases h; exact hc
      · split at h
        · rename_i st1 _ _ hf2
          have hc2 := Nat.le_trans (fix_clock_le_aux hf2) hc
          split at h
          · cases h; exact hc2
          · have hd : (dec_clock st1).clock ≤ st.clock := by simp only [dec_clock]; omega
            split at h
            · rename_i he
              have := Nat.le_trans (fix_clock_le_aux he) hd
              split at h <;> (cases h; exact this)
            · rename_i he; cases h; exact Nat.le_trans (fix_clock_le_aux he) hd
            · rename_i he; have := Nat.le_trans (fix_clock_le_aux he) hd; cases h; exact this
        · rename_i hf2
          cases h
          exact Nat.le_trans (fix_clock_le_aux hf2) hc
      · split at h <;> (cases h; exact hc)
    · exact fix_clock_le_aux h
  · intro st env l e1 e2 ih1 ih2 r s2 h
    rw [evaluate] at h
    split at h
    · rename_i hf
      have hc := fix_clock_le_aux hf
      split at h
      · cases h; exact hc
      · rename_i hl
        rw [do_log_exp_aux hl] at h
        exact Nat.le_trans (ih2 _ hc _ _ h) hc
      · cases h; exact hc
    · rename_i hf; cases h; exact fix_clock_le_aux hf
  · intro st env e1 e2 e3 ih1 ih2 ih3 r s2 h
    rw [evaluate] at h
    split at h
    · rename_i hf
      have hc := fix_clock_le_aux hf
      split at h
      · cases h; exact hc
      · rename_i hl
        unfold do_if at hl
        split at hl
        · cases hl; exact Nat.le_trans (ih2 _ hc _ _ h) hc
        · split at hl
          · cases hl; exact Nat.le_trans (ih3 _ hc _ _ h) hc
          · cases hl
    · rename_i hf; cases h; exact fix_clock_le_aux hf
  · intro st env e pes ih1 ih2 r s2 h
    rw [evaluate] at h
    split at h
    · rename_i hf
      have hc := fix_clock_le_aux hf
      split at h
      · exact Nat.le_trans (ih2 _ _ hc _ _ h) hc
      · cases h; exact hc
    · rename_i hf; cases h; exact fix_clock_le_aux hf
  · intro st env xo e1 e2 ih1 ih2 r s2 h
    rw [evaluate] at h
    split at h
    · rename_i hf
      have hc := fix_clock_le_aux hf
      exact Nat.le_trans (ih2 _ _ hc _ _ h) hc
    · rename_i hf; cases h; exact fix_clock_le_aux hf
  · intro st env funs e ih r s2 h
    rw [evaluate] at h
    split at h
    · exact ih _ _ _ h
    · cases h; exact Nat.le_refl _
  · intro st env e t ih r s2 h
    rw [evaluate] at h; exact ih _ _ h
  · intro st env e l ih r s2 h
    rw [evaluate] at h; exact ih _ _ h
  · intro st env v err r s2 h
    rw [evaluate_match] at h; cases h; exact Nat.le_refl _
  · intro st env v p e pes err ih1 ih2 r s2 h
    rw [evaluate_match] at h
    split at h
    · split at h
      · exact ih1 _ _ h
      · cases h; exact Nat.le_refl _
      · exact ih2 _ _ _ h
    · cases h; exact Nat.le_refl _
  · intro st env r s2 h
    rw [evaluate_decs] at h; cases h; exact Nat.le_refl _
  · intro st env d1 d2 ds ih1 ih2 r s2 h
    rw [evaluate_decs] at h
    split at h
    · rename_i hf
      have hc := fix_clock_le_aux hf
      split at h
      rename_i he
      cases h
      exact Nat.le_trans (ih2 _ _ hc _ _ he) hc
    · rename_i hf; cases h; exact fix_clock_le_aux hf
  · intro st env l p e ih r s2 h
    rw [evaluate_decs] at h
    split at h
    · split at h <;> (rename_i he; cases h; exact ih _ _ he)
    · cases h; exact Nat.le_refl _
  · intro st env l funs r s2 h
    rw [evaluate_decs] at h; cases h; exact Nat.le_refl _
  · intro st env l tds r s2 h
    rw [evaluate_decs] at h
    split at h <;> (cases h; exact Nat.le_refl _)
  · intro st env l tvs tn t r s2 h
    rw [evaluate_decs] at h; cases h; exact Nat.le_refl _
  · intro st env l cn ts r s2 h
    rw [evaluate_decs] at h; cases h; exact Nat.le_refl _
  · intro st env mn ds ih r s2 h
    rw [evaluate_decs] at h
    split at h
    rename_i he
    cases h
    exact ih _ _ he
  · intro st env lds ds ih1 ih2 r s2 h
    rw [evaluate_decs] at h
    split at h
    · rename_i hf
      have hc := fix_clock_le_aux hf
      exact Nat.le_trans (ih2 _ _ hc _ _ h) hc
    · rename_i hf; cases h; exact fix_clock_le_aux hf
  · intro st env n r s2 h
    rw [evaluate_decs] at h
    split at h <;> (cases h; exact Nat.le_refl _)

theorem Aux.fix_clock_id {α : Type} {s s' : state ffi} {r : α} (h : s'.clock ≤ s.clock) :
    fix_clock s (s', r) = (s', r) := by
  simp only [fix_clock, if_pos h]

/- HOL4:
Theorem fix_clock_do_eval_res:
   fix_clock s (do_eval_res vs s) = do_eval_res vs s -/
theorem fix_clock_do_eval_res {β : Type} {s : state ffi} {vs : List value} :
    fix_clock s (do_eval_res vs s) =
      (do_eval_res vs s : state ffi × result (sem_env value × List dec) β) := by
  unfold do_eval_res
  split <;> exact Aux.fix_clock_id (Nat.le_refl _)

/- HOL4:
Theorem fix_clock_evaluate:
   fix_clock s1 (evaluate s1 env e) = evaluate s1 env e /\
   fix_clock s1 (evaluate_decs s1 env ds) = evaluate_decs s1 env ds -/
theorem fix_clock_evaluate {s1 : state ffi} {env : sem_env value} {e : List exp}
    {ds : List dec} :
    fix_clock s1 (evaluate s1 env e) = evaluate s1 env e ∧
    fix_clock s1 (evaluate_decs s1 env ds) = evaluate_decs s1 env ds :=
  ⟨Aux.fix_clock_id (evaluate_clock.1 _ _ _ _ _ rfl),
    Aux.fix_clock_id (evaluate_clock.2.2 _ _ _ _ _ rfl)⟩

/-! ### Auxiliary: the equations of `evaluate` without `fix_clock` (as in HOL4) -/

theorem Aux.evaluate_cons (st : state ffi) (env : sem_env value) (e1 e2 : exp) (es : List exp) :
    evaluate st env (e1 :: e2 :: es) =
      match evaluate st env [e1] with
      | (st', Rval v1) =>
        match evaluate st' env (e2 :: es) with
        | (st'', Rval vs) => (st'', Rval (HD v1 :: vs))
        | (st'', Rerr v8) => (st'', Rerr v8)
      | (st', Rerr v10) => (st', Rerr v10) := by
  rw [evaluate]
  have hf := (fix_clock_evaluate (s1 := st) (env := env) (e := [e1]) (ds := [])).1
  generalize fix_clock st (evaluate st env [e1]) = x at hf ⊢
  subst hf
  rcases evaluate st env [e1] with ⟨st', vs | e⟩ <;> rfl

theorem Aux.evaluate_Handle (st : state ffi) (env : sem_env value) (e : exp)
    (pes : List (pat × exp)) :
    evaluate st env [exp.Handle e pes] =
      match evaluate st env [e] with
      | (st', Rval v7) => (st', Rval v7)
      | (st', Rerr (Rraise v)) =>
        if can_pmatch_all env.c st'.refs (pes.map Prod.fst) v then
          evaluate_match st' env v pes v
        else (st', Rerr (Rabort Rtype_error))
      | (st', Rerr (Rabort v12)) => (st', Rerr (Rabort v12)) := by
  rw [evaluate]
  have hf := (fix_clock_evaluate (s1 := st) (env := env) (e := [e]) (ds := [])).1
  generalize fix_clock st (evaluate st env [e]) = x at hf ⊢
  subst hf
  rcases evaluate st env [e] with ⟨st', vs | e | e⟩ <;> rfl

theorem Aux.evaluate_App (st : state ffi) (env : sem_env value) (o : op) (es : List exp) :
    evaluate st env [exp.App o es] =
      match evaluate st env es.reverse with
      | (st', Rval vs) =>
        match getOpClass o with
        | FunApp =>
          match do_opapp vs.reverse with
          | some (env', e) =>
            if st'.clock = 0 then (st', Rerr (Rabort Rtimeout_error))
            else evaluate (dec_clock st') env' [e]
          | none => (st', Rerr (Rabort Rtype_error))
        | Force =>
          match dest_thunk vs.reverse st'.refs with
          | BadRef => (st', Rerr (Rabort Rtype_error))
          | NotThunk => (st', Rerr (Rabort Rtype_error))
          | IsThunk Evaluated v => (st', Rval [v])
          | IsThunk NotEvaluated f =>
            match do_opapp [f, Conv none []] with
            | some (env', e) =>
              if st'.clock = 0 then (st', Rerr (Rabort Rtimeout_error))
              else
                match evaluate (dec_clock st') env' [e] with
                | (st2, Rval vs2) =>
                  match update_thunk vs.reverse st2.refs vs2 with
                  | none => (st2, Rerr (Rabort Rtype_error))
                  | some refs => ({ st2 with refs := refs }, Rval vs2)
                | (st2, Rerr e) => (st2, Rerr e)
            | none => (st', Rerr (Rabort Rtype_error))
        | EvalOp =>
          match do_eval_res vs.reverse st' with
          | (st1, Rval (env1, decs)) =>
            if st1.clock = 0 then (st1, Rerr (Rabort Rtimeout_error))
            else
              match evaluate_decs (dec_clock st1) env1 decs with
              | (st2, Rval env2) =>
                match declare_env st2.eval_state (extend_dec_env env2 env1) with
                | some (x, es2) =>
                  ({ st2 with eval_state := reset_env_generation st'.eval_state es2 }, Rval [x])
                | none => (st2, Rerr (Rabort Rtype_error))
              | (st2, Rerr (Rabort a)) => (st2, Rerr (Rabort a))
              | (st2, Rerr e) =>
                ({ st2 with
                    eval_state := reset_env_generation st'.eval_state st2.eval_state }, Rerr e)
          | (st1, Rerr e) => (st1, Rerr e)
        | Simple =>
          match do_app (st'.refs, st'.ffi) o vs.reverse with
          | none => (st', Rerr (Rabort Rtype_error))
          | some ((refs, ffi), r) => ({ st' with refs := refs, ffi := ffi }, list_result r)
      | (st', Rerr e) => (st', Rerr e) := by
  rw [evaluate]
  have hf := (fix_clock_evaluate (s1 := st) (env := env) (e := es.reverse) (ds := [])).1
  generalize fix_clock st (evaluate st env es.reverse) = x at hf ⊢
  subst hf
  rcases evaluate st env es.reverse with ⟨st', vs | e⟩
  · dsimp only
    cases getOpClass o with
    | EvalOp =>
      dsimp only
      have hg := fix_clock_do_eval_res (β := value) (s := st') (vs := vs.reverse)
      generalize fix_clock st' (do_eval_res vs.reverse st') = y at hg ⊢
      subst hg
      rcases do_eval_res vs.reverse st' with ⟨st1, ⟨env1, decs⟩ | e⟩
      · dsimp only
        rw [(fix_clock_evaluate (s1 := dec_clock st1) (env := env1) (e := []) (ds := decs)).2]
      · rfl
    | _ => rfl
  · rfl

theorem Aux.evaluate_Log (st : state ffi) (env : sem_env value) (l : lop) (e1 e2 : exp) :
    evaluate st env [exp.Log l e1 e2] =
      match evaluate st env [e1] with
      | (st', Rval v1) =>
        match do_log l (HD v1) e2 with
        | none => (st', Rerr (Rabort Rtype_error))
        | some (Exp e) => evaluate st' env [e]
        | some (Val v) => (st', Rval [v])
      | (st', Rerr v9) => (st', Rerr v9) := by
  rw [evaluate]
  have hf := (fix_clock_evaluate (s1 := st) (env := env) (e := [e1]) (ds := [])).1
  generalize fix_clock st (evaluate st env [e1]) = x at hf ⊢
  subst hf
  rcases evaluate st env [e1] with ⟨st', vs | e⟩
  · dsimp only
    cases do_log l (HD vs) e2 with
    | none => rfl
    | some z => cases z <;> rfl
  · rfl

theorem Aux.evaluate_If (st : state ffi) (env : sem_env value) (e1 e2 e3 : exp) :
    evaluate st env [exp.If e1 e2 e3] =
      match evaluate st env [e1] with
      | (st', Rval v) =>
        match do_if (HD v) e2 e3 with
        | none => (st', Rerr (Rabort Rtype_error))
        | some e => evaluate st' env [e]
      | (st', Rerr v8) => (st', Rerr v8) := by
  rw [evaluate]
  have hf := (fix_clock_evaluate (s1 := st) (env := env) (e := [e1]) (ds := [])).1
  generalize fix_clock st (evaluate st env [e1]) = x at hf ⊢
  subst hf
  rcases evaluate st env [e1] with ⟨st', vs | e⟩
  · dsimp only
    cases do_if (HD vs) e2 e3 <;> rfl
  · rfl

theorem Aux.evaluate_Mat (st : state ffi) (env : sem_env value) (e : exp)
    (pes : List (pat × exp)) :
    evaluate st env [exp.Mat e pes] =
      match evaluate st env [e] with
      | (st', Rval v) =>
        if can_pmatch_all env.c st'.refs (pes.map Prod.fst) (HD v) then
          evaluate_match st' env (HD v) pes bind_exn_v
        else (st', Rerr (Rabort Rtype_error))
      | (st', Rerr v8) => (st', Rerr v8) := by
  rw [evaluate]
  have hf := (fix_clock_evaluate (s1 := st) (env := env) (e := [e]) (ds := [])).1
  generalize fix_clock st (evaluate st env [e]) = x at hf ⊢
  subst hf
  rcases evaluate st env [e] with ⟨st', vs | e⟩ <;> rfl

theorem Aux.evaluate_Let (st : state ffi) (env : sem_env value) (xo : Option varN)
    (e1 e2 : exp) :
    evaluate st env [exp.Let xo e1 e2] =
      match evaluate st env [e1] with
      | (st', Rval v) => evaluate st' { env with v := nsOptBind xo (HD v) env.v } [e2]
      | (st', Rerr v8) => (st', Rerr v8) := by
  rw [evaluate]
  have hf := (fix_clock_evaluate (s1 := st) (env := env) (e := [e1]) (ds := [])).1
  generalize fix_clock st (evaluate st env [e1]) = x at hf ⊢
  subst hf
  rcases evaluate st env [e1] with ⟨st', vs | e⟩ <;> rfl

theorem Aux.evaluate_decs_cons (st : state ffi) (env : sem_env value) (d1 d2 : dec)
    (ds : List dec) :
    evaluate_decs st env (d1 :: d2 :: ds) =
      match evaluate_decs st env [d1] with
      | (st1, Rval env1) =>
        match evaluate_decs st1 (extend_dec_env env1 env) (d2 :: ds) with
        | (st2, r) => (st2, combine_dec_result env1 r)
      | (st1, Rerr v7) => (st1, Rerr v7) := by
  rw [evaluate_decs]
  have hf := (fix_clock_evaluate (s1 := st) (env := env) (e := []) (ds := [d1])).2
  generalize fix_clock st (evaluate_decs st env [d1]) = x at hf ⊢
  subst hf
  rcases evaluate_decs st env [d1] with ⟨st', vs | e⟩ <;> rfl

theorem Aux.evaluate_Dlocal (st : state ffi) (env : sem_env value) (lds ds : List dec) :
    evaluate_decs st env [Dlocal lds ds] =
      match evaluate_decs st env lds with
      | (st1, Rval env1) => evaluate_decs st1 (extend_dec_env env1 env) ds
      | (st1, Rerr v7) => (st1, Rerr v7) := by
  rw [evaluate_decs]
  have hf := (fix_clock_evaluate (s1 := st) (env := env) (e := []) (ds := lds)).2
  generalize fix_clock st (evaluate_decs st env lds) = x at hf ⊢
  subst hf
  rcases evaluate_decs st env lds with ⟨st', vs | e⟩ <;> rfl

end

end CmlTS
