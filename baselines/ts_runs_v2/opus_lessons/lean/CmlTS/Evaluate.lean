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
Termination
  WF_REL_TAC ‘inv_image ($< LEX $<)
    (λx. case x of
         | INL(s,_,es) => (s.clock,list_size exp_size es)
         | INR(INL (s,_,_,pes,_)) => (s.clock,list_size (pair_size pat_size exp_size) pes)
         | INR(INR (s,_,ds)) => (s.clock,list_size dec_size ds))’
  ...
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
      evaluate_decs s1 env ds = (s2, r) → s2.clock ≤ s1.clock) := by sorry

/- HOL4:
Theorem fix_clock_do_eval_res:
   fix_clock s (do_eval_res vs s) = do_eval_res vs s -/
theorem fix_clock_do_eval_res {β : Type} {s : state ffi} {vs : List value} :
    fix_clock s (do_eval_res vs s) =
      (do_eval_res vs s : state ffi × result (sem_env value × List dec) β) := by sorry

/- HOL4:
Theorem fix_clock_evaluate:
   fix_clock s1 (evaluate s1 env e) = evaluate s1 env e /\
   fix_clock s1 (evaluate_decs s1 env ds) = evaluate_decs s1 env ds -/
theorem fix_clock_evaluate {s1 : state ffi} {env : sem_env value} {e : List exp}
    {ds : List dec} :
    fix_clock s1 (evaluate s1 env e) = evaluate s1 env e ∧
    fix_clock s1 (evaluate_decs s1 env ds) = evaluate_decs s1 env ds := by sorry

end

end CmlTS
