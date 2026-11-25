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

/-! ### Auxiliary lemmas for the theorems -/

theorem Aux.ev_wf_induct {P : state ffi → sem_env value → List exp → Prop}
    {Q : state ffi → sem_env value → value → List (pat × exp) → value → Prop}
    {R : state ffi → sem_env value → List dec → Prop}
    (hP : ∀ st env es,
      (∀ st' env' es', st'.clock < st.clock ∨ (st'.clock ≤ st.clock ∧ sizeOf es' < sizeOf es) → P st' env' es') →
      (∀ st' env' v pes v', st'.clock < st.clock ∨ (st'.clock ≤ st.clock ∧ sizeOf pes < sizeOf es) → Q st' env' v pes v') →
      (∀ st' env' (ds : List dec), st'.clock < st.clock ∨ (st'.clock ≤ st.clock ∧ sizeOf ds < sizeOf es) → R st' env' ds) →
      P st env es)
    (hQ : ∀ st env v pes v',
      (∀ st' env' (es' : List exp), st'.clock < st.clock ∨ (st'.clock ≤ st.clock ∧ sizeOf es' < sizeOf pes) → P st' env' es') →
      (∀ st' env' v pes' v', st'.clock < st.clock ∨ (st'.clock ≤ st.clock ∧ sizeOf pes' < sizeOf pes) → Q st' env' v pes' v') →
      Q st env v pes v')
    (hR : ∀ st env (ds : List dec),
      (∀ st' env' (es' : List exp), st'.clock < st.clock ∨ (st'.clock ≤ st.clock ∧ sizeOf es' < sizeOf ds) → P st' env' es') →
      (∀ st' env' (ds' : List dec), st'.clock < st.clock ∨ (st'.clock ≤ st.clock ∧ sizeOf ds' < sizeOf ds) → R st' env' ds') →
      R st env ds) :
    (∀ st env es, P st env es) ∧ (∀ st env v pes v', Q st env v pes v') ∧ (∀ st env ds, R st env ds) := by
  have key : ∀ c : Nat, ∀ n : Nat,
      (∀ st env es, st.clock = c → sizeOf es = n → P st env es) ∧
      (∀ st env v pes v', st.clock = c → sizeOf pes = n → Q st env v pes v') ∧
      (∀ st env (ds : List dec), st.clock = c → sizeOf ds = n → R st env ds) := by
    intro c
    induction c using Nat.strongRecOn with
    | _ c ihc =>
      intro n
      induction n using Nat.strongRecOn with
      | _ n ihn =>
        have hall : ∀ c' n', c' < c ∨ (c' ≤ c ∧ n' < n) →
            (∀ st env es, st.clock = c' → sizeOf es = n' → P st env es) ∧
            (∀ st env v pes v', st.clock = c' → sizeOf pes = n' → Q st env v pes v') ∧
            (∀ st env (ds : List dec), st.clock = c' → sizeOf ds = n' → R st env ds) := by
          intro c' n' h
          rcases h with h | ⟨h1, h2⟩
          · exact ihc c' h n'
          · rcases Nat.lt_or_ge c' c with h | h
            · exact ihc c' h n'
            · have : c' = c := by omega
              subst this
              exact ihn n' h2
        refine ⟨?_, ?_, ?_⟩
        · intro st env es hc hn
          subst hc; subst hn
          exact hP st env es (fun st' env' es' h => (hall _ _ h).1 st' env' es' rfl rfl)
            (fun st' env' v pes v' h => (hall _ _ h).2.1 st' env' v pes v' rfl rfl)
            (fun st' env' ds h => (hall _ _ h).2.2 st' env' ds rfl rfl)
        · intro st env v pes v' hc hn
          subst hc; subst hn
          exact hQ st env v pes v' (fun st' env' es' h => (hall _ _ h).1 st' env' es' rfl rfl)
            (fun st' env' v pes v' h => (hall _ _ h).2.1 st' env' v pes v' rfl rfl)
        · intro st env ds hc hn
          subst hc; subst hn
          exact hR st env ds (fun st' env' es' h => (hall _ _ h).1 st' env' es' rfl rfl)
            (fun st' env' ds h => (hall _ _ h).2.2 st' env' ds rfl rfl)
  exact ⟨fun st env es => (key _ _).1 st env es rfl rfl,
    fun st env v pes v' => (key _ _).2.1 st env v pes v' rfl rfl,
    fun st env ds => (key _ _).2.2 st env ds rfl rfl⟩

theorem Aux.fst_le {α : Type} {s1 : state ffi} {x : state ffi × α} {r : α} {c : Nat}
    (h : x = (s1, r)) (hx : x.1.clock ≤ c) : s1.clock ≤ c := by subst h; exact hx

theorem Aux.evaluate_clock1 :
    (∀ (st : state ffi) env es, (evaluate st env es).1.clock ≤ st.clock) ∧
    (∀ (st : state ffi) env v pes v', (evaluate_match st env v pes v').1.clock ≤ st.clock) ∧
    (∀ (st : state ffi) env ds, (evaluate_decs st env ds).1.clock ≤ st.clock) := by
  apply Aux.ev_wf_induct
  · intro st env es ihP ihQ ihR
    rcases es with _ | ⟨e1, _ | ⟨e2, es⟩⟩
    · simp [evaluate]
    · cases e1 with
      | Raise e =>
        have := ihP st env [e] (by simp)
        rw [evaluate]
        split <;> (rename_i h; exact Aux.fst_le h this)
      | Handle e pes =>
        rw [evaluate]
        split
        · rename_i h; exact fix_clock_le_aux h
        · rename_i h
          have := fix_clock_le_aux h
          split
          · exact Nat.le_trans (ihQ _ _ _ _ _ (Or.inr ⟨this, by simp; omega⟩)) this
          · exact this
        · rename_i h; exact fix_clock_le_aux h
      | Lit l => simp [evaluate]
      | Con cn es =>
        have := ihP st env es.reverse (by simp [sizeOf_reverse_aux]; omega)
        rw [evaluate]
        split
        · split
          · rename_i h
            have := Aux.fst_le h this
            split <;> exact this
          · rename_i h; exact Aux.fst_le h this
        · exact Nat.le_refl _
      | Var n => rw [evaluate]; split <;> exact Nat.le_refl _
      | Fun x e => simp [evaluate]
      | App o es =>
        rw [evaluate]
        split
        · rename_i st' vs h
          have hc := fix_clock_le_aux h
          split
          · split
            · split
              · exact hc
              · have h1 : (dec_clock st').clock < st'.clock := by simp [dec_clock]; omega
                exact Nat.le_trans (ihP _ _ _ (by omega)) (by omega)
            · exact hc
          · split
            · exact hc
            · exact hc
            · exact hc
            · split
              · split
                · exact hc
                · rename_i env' e _ _
                  have h1 : (dec_clock st').clock < st'.clock := by simp [dec_clock]; omega
                  have h2 := ihP (dec_clock st') env' [e] (by omega)
                  split
                  · rename_i h3
                    have := Aux.fst_le h3 h2
                    split <;> (show _ ≤ _; dsimp only; omega)
                  · rename_i h3
                    have := Aux.fst_le h3 h2
                    show _ ≤ _; dsimp only; omega
              · exact hc
          · split
            · rename_i st1 env1 decs h2
              have hd := fix_clock_le_aux h2
              split
              · show _ ≤ _; dsimp only; omega
              · have h1 : (dec_clock st1).clock < st1.clock := by simp [dec_clock]; omega
                split
                · rename_i h3
                  have := fix_clock_le_aux h3
                  split <;> (show _ ≤ _; dsimp only; omega)
                · rename_i h3
                  have := fix_clock_le_aux h3
                  show _ ≤ _; dsimp only; omega
                · rename_i h3
                  have := fix_clock_le_aux h3
                  show _ ≤ _; dsimp only; omega
            · rename_i h2
              have hd := fix_clock_le_aux h2
              show _ ≤ _; dsimp only; omega
          · split <;> exact hc
        · have : (fix_clock st (evaluate st env es.reverse)).1.clock ≤ st.clock :=
            fix_clock_le_aux (res := (fix_clock st (evaluate st env es.reverse)).2) rfl
          exact this
      | Log l e1 e2 =>
        rw [evaluate]
        split
        · rename_i h
          have hc := fix_clock_le_aux h
          split
          · exact hc
          · rename_i h2
            have := do_log_exp_aux h2
            subst this
            exact Nat.le_trans (ihP _ _ _ (Or.inr ⟨hc, by simp; omega⟩)) hc
          · exact hc
        · rename_i h; exact fix_clock_le_aux h
      | If e1 e2 e3 =>
        rw [evaluate]
        split
        · rename_i h
          have hc := fix_clock_le_aux h
          split
          · exact hc
          · rename_i h2
            have := do_if_size_aux h2
            exact Nat.le_trans (ihP _ _ _ (Or.inr ⟨hc, by simp; omega⟩)) hc
        · rename_i h; exact fix_clock_le_aux h
      | Mat e pes =>
        rw [evaluate]
        split
        · rename_i h
          have := fix_clock_le_aux h
          split
          · exact Nat.le_trans (ihQ _ _ _ _ _ (Or.inr ⟨this, by simp; omega⟩)) this
          · exact this
        · rename_i h; exact fix_clock_le_aux h
      | Let xo e1 e2 =>
        rw [evaluate]
        split
        · rename_i h
          have := fix_clock_le_aux h
          exact Nat.le_trans (ihP _ _ _ (Or.inr ⟨this, by simp; omega⟩)) this
        · rename_i h; exact fix_clock_le_aux h
      | Letrec funs e =>
        rw [evaluate]
        split
        · exact ihP _ _ _ (by simp; omega)
        · exact Nat.le_refl _
      | Tannot e t => rw [evaluate]; exact ihP _ _ _ (by simp; omega)
      | Lannot e l => rw [evaluate]; exact ihP _ _ _ (by simp; omega)
    · rw [evaluate]
      split
      · rename_i st' v1 h
        have hc := fix_clock_le_aux h
        have := ihP st' env (e2 :: es) (Or.inr ⟨hc, by simp; omega⟩)
        split
        · rename_i h2; have := Aux.fst_le h2 this
          show _ ≤ _; dsimp only; omega
        · rename_i h2; have := Aux.fst_le h2 this
          show _ ≤ _; dsimp only; omega
      · rename_i h; exact fix_clock_le_aux h
  · intro st env v pes v' ihP ihQ
    rcases pes with _ | ⟨⟨p, e⟩, pes⟩
    · simp [evaluate_match]
    · rw [evaluate_match]
      split
      · split
        · exact ihQ _ _ _ _ _ (by simp; omega)
        · exact Nat.le_refl _
        · have := sizeOf_list_pos_aux pes
          exact ihP _ _ _ (by simp; omega)
      · exact Nat.le_refl _
  · intro st env ds ihP ihR
    rcases ds with _ | ⟨d1, _ | ⟨d2, ds⟩⟩
    · simp [evaluate_decs]
    · cases d1 with
      | Dlet l p e =>
        have := ihP st env [e] (by simp; omega)
        rw [evaluate_decs]
        split
        · split <;> (rename_i h; exact Aux.fst_le h this)
        · exact Nat.le_refl _
      | Dletrec l funs => simp [evaluate_decs]
      | Dtype l tds => rw [evaluate_decs]; split <;> exact Nat.le_refl _
      | Dtabbrev l tvs tn t => simp [evaluate_decs]
      | Dexn l cn ts => simp [evaluate_decs]
      | Dmod mn ds =>
        rw [evaluate_decs]
        exact ihR _ _ _ (by simp; omega)
      | Dlocal lds ds =>
        rw [evaluate_decs]
        split
        · rename_i h
          have := fix_clock_le_aux h
          exact Nat.le_trans (ihR _ _ _ (Or.inr ⟨this, by simp; omega⟩)) this
        · rename_i h; exact fix_clock_le_aux h
      | Denv n => rw [evaluate_decs]; split <;> exact Nat.le_refl _
    · rw [evaluate_decs]
      split
      · rename_i st' v1 h
        have hc := fix_clock_le_aux h
        have := ihR st' (extend_dec_env v1 env) (d2 :: ds) (Or.inr ⟨hc, by simp; omega⟩)
        exact Nat.le_trans this hc
      · rename_i h; exact fix_clock_le_aux h

theorem Aux.fix_clock_of_le {α : Type} {s : state ffi} {x : state ffi × α}
    (h : x.1.clock ≤ s.clock) : fix_clock s x = x := by
  obtain ⟨s', r⟩ := x
  simp only [fix_clock, if_pos h]

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
      evaluate_decs s1 env ds = (s2, r) → s2.clock ≤ s1.clock) :=
  ⟨fun s1 env e _ _ h => Aux.fst_le h (Aux.evaluate_clock1.1 s1 env e),
    fun s1 env v p v' _ _ h => Aux.fst_le h (Aux.evaluate_clock1.2.1 s1 env v p v'),
    fun s1 env ds _ _ h => Aux.fst_le h (Aux.evaluate_clock1.2.2 s1 env ds)⟩

/- HOL4:
Theorem fix_clock_do_eval_res:
   fix_clock s (do_eval_res vs s) = do_eval_res vs s -/
theorem fix_clock_do_eval_res {β : Type} {s : state ffi} {vs : List value} :
    fix_clock s (do_eval_res vs s) =
      (do_eval_res vs s : state ffi × result (sem_env value × List dec) β) := by
  apply Aux.fix_clock_of_le
  unfold do_eval_res
  split <;> exact Nat.le_refl _

/- HOL4:
Theorem fix_clock_evaluate:
   fix_clock s1 (evaluate s1 env e) = evaluate s1 env e /\
   fix_clock s1 (evaluate_decs s1 env ds) = evaluate_decs s1 env ds -/
theorem fix_clock_evaluate {s1 : state ffi} {env : sem_env value} {e : List exp}
    {ds : List dec} :
    fix_clock s1 (evaluate s1 env e) = evaluate s1 env e ∧
    fix_clock s1 (evaluate_decs s1 env ds) = evaluate_decs s1 env ds :=
  ⟨Aux.fix_clock_of_le (Aux.evaluate_clock1.1 _ _ _),
    Aux.fix_clock_of_le (Aux.evaluate_clock1.2.2 _ _ _)⟩

/-! ### The equations of `evaluate` without `fix_clock`, and the induction principle -/

theorem Aux.fix_ev (st : state ffi) (env : sem_env value) (es : List exp) :
    fix_clock st (evaluate st env es) = evaluate st env es :=
  (fix_clock_evaluate (ds := [])).1

theorem Aux.fix_evd (st : state ffi) (env : sem_env value) (ds : List dec) :
    fix_clock st (evaluate_decs st env ds) = evaluate_decs st env ds :=
  (fix_clock_evaluate (e := [])).2

theorem Aux.evaluate_cons2 (st : state ffi) (env : sem_env value) (e1 e2 : exp) (es : List exp) :
    evaluate st env (e1 :: e2 :: es) =
      match evaluate st env [e1] with
      | (st', Rval v1) =>
        match evaluate st' env (e2 :: es) with
        | (st'', Rval vs) => (st'', Rval (HD v1 :: vs))
        | (st'', Rerr v8) => (st'', Rerr v8)
      | (st', Rerr v10) => (st', Rerr v10) := by
  rw [evaluate, Aux.fix_ev]
  generalize evaluate st env [e1] = x
  rcases x with ⟨_, _ | _⟩ <;> rfl

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
  rw [evaluate, Aux.fix_ev]
  generalize evaluate st env [e] = x
  rcases x with ⟨_, _ | (_ | _)⟩ <;> rfl

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
          match do_eval_res (β := value) vs.reverse st' with
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
      | res => res := by
  rw [evaluate, Aux.fix_ev]
  generalize evaluate st env es.reverse = x
  rcases x with ⟨st', vs | _⟩
  · dsimp only
    cases getOpClass o with
    | EvalOp =>
      dsimp only
      rw [fix_clock_do_eval_res]
      generalize do_eval_res (β := value) vs.reverse st' = y
      rcases y with ⟨_, ⟨_, _⟩ | _⟩
      · dsimp only
        rw [Aux.fix_evd]
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
  rw [evaluate, Aux.fix_ev]
  generalize evaluate st env [e1] = x
  rcases x with ⟨st', vs | _⟩
  · dsimp only
    generalize do_log l (HD vs) e2 = y
    rcases y with _ | (_ | _) <;> rfl
  · rfl

theorem Aux.evaluate_If (st : state ffi) (env : sem_env value) (e1 e2 e3 : exp) :
    evaluate st env [exp.If e1 e2 e3] =
      match evaluate st env [e1] with
      | (st', Rval v) =>
        match do_if (HD v) e2 e3 with
        | none => (st', Rerr (Rabort Rtype_error))
        | some e => evaluate st' env [e]
      | (st', Rerr v8) => (st', Rerr v8) := by
  rw [evaluate, Aux.fix_ev]
  generalize evaluate st env [e1] = x
  rcases x with ⟨st', vs | _⟩
  · dsimp only
    generalize do_if (HD vs) e2 e3 = y
    rcases y with _ | _ <;> rfl
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
  rw [evaluate, Aux.fix_ev]
  generalize evaluate st env [e] = x
  rcases x with ⟨_, _ | _⟩ <;> rfl

theorem Aux.evaluate_Let (st : state ffi) (env : sem_env value) (xo : Option varN)
    (e1 e2 : exp) :
    evaluate st env [exp.Let xo e1 e2] =
      match evaluate st env [e1] with
      | (st', Rval v) => evaluate st' { env with v := nsOptBind xo (HD v) env.v } [e2]
      | (st', Rerr v8) => (st', Rerr v8) := by
  rw [evaluate, Aux.fix_ev]
  generalize evaluate st env [e1] = x
  rcases x with ⟨_, _ | _⟩ <;> rfl

theorem Aux.evaluate_decs_cons2 (st : state ffi) (env : sem_env value) (d1 d2 : dec)
    (ds : List dec) :
    evaluate_decs st env (d1 :: d2 :: ds) =
      match evaluate_decs st env [d1] with
      | (st1, Rval env1) =>
        match evaluate_decs st1 (extend_dec_env env1 env) (d2 :: ds) with
        | (st2, r) => (st2, combine_dec_result env1 r)
      | (st1, Rerr v7) => (st1, Rerr v7) := by
  rw [evaluate_decs, Aux.fix_evd]
  generalize evaluate_decs st env [d1] = x
  rcases x with ⟨_, _ | _⟩ <;> rfl

theorem Aux.evaluate_decs_Dlocal (st : state ffi) (env : sem_env value) (lds ds : List dec) :
    evaluate_decs st env [Dlocal lds ds] =
      match evaluate_decs st env lds with
      | (st1, Rval env1) => evaluate_decs st1 (extend_dec_env env1 env) ds
      | (st1, Rerr v7) => (st1, Rerr v7) := by
  rw [evaluate_decs, Aux.fix_evd]
  generalize evaluate_decs st env lds = x
  rcases x with ⟨_, _ | _⟩ <;> rfl

theorem Aux.do_eval_res_clock {β : Type} {vs : List value} {s s1 : state ffi}
    {r : result (sem_env value × List dec) β} (h : do_eval_res vs s = (s1, r)) :
    s1.clock = s.clock := by
  unfold do_eval_res at h
  split at h <;> (cases h; rfl)

theorem Aux.full_evaluate_ind {P : state ffi → sem_env value → List exp → Prop}
    {Q : state ffi → sem_env value → value → List (pat × exp) → value → Prop}
    {R : state ffi → sem_env value → List dec → Prop}
    (nil : ∀ st env, P st env [])
    (cons2 : ∀ st env e1 e2 es, P st env [e1] →
      (∀ st' v1, evaluate st env [e1] = (st', Rval v1) → P st' env (e2 :: es)) →
      P st env (e1 :: e2 :: es))
    (lit : ∀ st env l, P st env [exp.Lit l])
    (raise : ∀ st env e, P st env [e] → P st env [exp.Raise e])
    (handle : ∀ st env e pes, P st env [e] →
      (∀ st' v, evaluate st env [e] = (st', Rerr (Rraise v)) →
        can_pmatch_all env.c st'.refs (pes.map Prod.fst) v → Q st' env v pes v) →
      P st env [exp.Handle e pes])
    (con : ∀ st env cn es, (do_con_check env.c cn es.length → P st env es.reverse) →
      P st env [exp.Con cn es])
    (var : ∀ st env n, P st env [exp.Var n])
    (func : ∀ st env x e, P st env [exp.Fun x e])
    (app : ∀ st env o es, P st env es.reverse →
      (∀ st' vs env' e, evaluate st env es.reverse = (st', Rval vs) → getOpClass o = FunApp →
        do_opapp vs.reverse = some (env', e) → st'.clock ≠ 0 → P (dec_clock st') env' [e]) →
      (∀ st' vs f env' e, evaluate st env es.reverse = (st', Rval vs) → getOpClass o = Force →
        dest_thunk vs.reverse st'.refs = IsThunk NotEvaluated f →
        do_opapp [f, Conv none []] = some (env', e) → st'.clock ≠ 0 →
        P (dec_clock st') env' [e]) →
      (∀ st' vs st1 env1 decs, evaluate st env es.reverse = (st', Rval vs) →
        getOpClass o = EvalOp →
        do_eval_res (β := value) vs.reverse st' = (st1, Rval (env1, decs)) → st1.clock ≠ 0 →
        R (dec_clock st1) env1 decs) →
      P st env [exp.App o es])
    (log : ∀ st env l e1 e2, P st env [e1] →
      (∀ st' v1 e, evaluate st env [e1] = (st', Rval v1) →
        do_log l (HD v1) e2 = some (Exp e) → P st' env [e]) →
      P st env [exp.Log l e1 e2])
    (ite : ∀ st env e1 e2 e3, P st env [e1] →
      (∀ st' v e, evaluate st env [e1] = (st', Rval v) →
        do_if (HD v) e2 e3 = some e → P st' env [e]) →
      P st env [exp.If e1 e2 e3])
    (mat : ∀ st env e pes, P st env [e] →
      (∀ st' v, evaluate st env [e] = (st', Rval v) →
        can_pmatch_all env.c st'.refs (pes.map Prod.fst) (HD v) →
        Q st' env (HD v) pes bind_exn_v) →
      P st env [exp.Mat e pes])
    (letc : ∀ st env xo e1 e2, P st env [e1] →
      (∀ st' v, evaluate st env [e1] = (st', Rval v) →
        P st' { env with v := nsOptBind xo (HD v) env.v } [e2]) →
      P st env [exp.Let xo e1 e2])
    (letrec : ∀ st env funs e,
      (ALL_DISTINCT (funs.map (fun (x, _, _) => x)) →
        P st { env with v := build_rec_env funs env env.v } [e]) →
      P st env [exp.Letrec funs e])
    (tannot : ∀ st env e t, P st env [e] → P st env [exp.Tannot e t])
    (lannot : ∀ st env e l, P st env [e] → P st env [exp.Lannot e l])
    (mnil : ∀ st env v v', Q st env v [] v')
    (mcons : ∀ st env v p e pes v',
      (ALL_DISTINCT (pat_bindings p []) → pmatch env.c st.refs p v [] = No_match →
        Q st env v pes v') →
      (∀ env_v', ALL_DISTINCT (pat_bindings p []) →
        pmatch env.c st.refs p v [] = Match env_v' →
        P st { env with v := nsAppend (alist_to_ns env_v') env.v } [e]) →
      Q st env v ((p, e) :: pes) v')
    (dnil : ∀ st env, R st env [])
    (dcons2 : ∀ st env d1 d2 ds, R st env [d1] →
      (∀ st1 env1, evaluate_decs st env [d1] = (st1, Rval env1) →
        R st1 (extend_dec_env env1 env) (d2 :: ds)) →
      R st env (d1 :: d2 :: ds))
    (dlet : ∀ st env l p e,
      (ALL_DISTINCT (pat_bindings p []) ∧ every_exp (one_con_check env.c) e → P st env [e]) →
      R st env [Dlet l p e])
    (dletrec : ∀ st env l funs, R st env [Dletrec l funs])
    (dtype : ∀ st env l tds, R st env [Dtype l tds])
    (dtabbrev : ∀ st env l tvs tn t, R st env [Dtabbrev l tvs tn t])
    (denv : ∀ st env n, R st env [Denv n])
    (dexn : ∀ st env l cn ts, R st env [Dexn l cn ts])
    (dmod : ∀ st env mn ds, R st env ds → R st env [Dmod mn ds])
    (dlocal : ∀ st env lds ds, R st env lds →
      (∀ st1 env1, evaluate_decs st env lds = (st1, Rval env1) →
        R st1 (extend_dec_env env1 env) ds) →
      R st env [Dlocal lds ds]) :
    (∀ st env es, P st env es) ∧ (∀ st env v pes v', Q st env v pes v') ∧
      (∀ st env ds, R st env ds) := by
  have hP : ∀ {st : state ffi} {env es st' r}, evaluate st env es = (st', r) →
      st'.clock ≤ st.clock := fun h => evaluate_clock.1 _ _ _ _ _ h
  have hR : ∀ {st : state ffi} {env ds st' r}, evaluate_decs st env ds = (st', r) →
      st'.clock ≤ st.clock := fun h => evaluate_clock.2.2 _ _ _ _ _ h
  have hdec : ∀ {st : state ffi}, st.clock ≠ 0 → (dec_clock st).clock < st.clock := by
    intro st h; simp only [dec_clock]; omega
  apply Aux.ev_wf_induct
  · intro st env es ihP ihQ ihR
    rcases es with _ | ⟨e1, _ | ⟨e2, es⟩⟩
    · exact nil _ _
    · cases e1 with
      | Raise e => exact raise _ _ _ (ihP _ _ _ (by simp))
      | Handle e pes =>
        exact handle _ _ _ _ (ihP _ _ _ (by simp; omega))
          fun st' v h _ => ihQ _ _ _ _ _ (Or.inr ⟨hP h, by simp; omega⟩)
      | Lit l => exact lit _ _ _
      | Con cn es =>
        exact con _ _ _ _ fun _ => ihP _ _ _ (by simp [sizeOf_reverse_aux]; omega)
      | Var n => exact var _ _ _
      | Fun x e => exact func _ _ _ _
      | App o es =>
        refine app _ _ _ _ (ihP _ _ _ (by simp [sizeOf_reverse_aux]; omega)) ?_ ?_ ?_
        · intro st' vs env' e h _ _ hc
          have := hP h
          have := hdec hc
          exact ihP _ _ _ (by omega)
        · intro st' vs f env' e h _ _ _ hc
          have := hP h
          have := hdec hc
          exact ihP _ _ _ (by omega)
        · intro st' vs st1 env1 decs h _ h2 hc
          have := hP h
          have := hdec hc
          have := Aux.do_eval_res_clock h2
          exact ihR _ _ _ (by omega)
      | Log l e1 e2 =>
        refine log _ _ _ _ _ (ihP _ _ _ (by simp; omega)) fun st' v1 e h h2 => ?_
        have := do_log_exp_aux h2
        subst this
        exact ihP _ _ _ (Or.inr ⟨hP h, by simp; omega⟩)
      | If e1 e2 e3 =>
        refine ite _ _ _ _ _ (ihP _ _ _ (by simp; omega)) fun st' v e h h2 => ?_
        have := do_if_size_aux h2
        exact ihP _ _ _ (Or.inr ⟨hP h, by simp; omega⟩)
      | Mat e pes =>
        exact mat _ _ _ _ (ihP _ _ _ (by simp; omega))
          fun st' v h _ => ihQ _ _ _ _ _ (Or.inr ⟨hP h, by simp; omega⟩)
      | Let xo e1 e2 =>
        exact letc _ _ _ _ _ (ihP _ _ _ (by simp; omega))
          fun st' v h => ihP _ _ _ (Or.inr ⟨hP h, by simp; omega⟩)
      | Letrec funs e => exact letrec _ _ _ _ fun _ => ihP _ _ _ (by simp; omega)
      | Tannot e t => exact tannot _ _ _ _ (ihP _ _ _ (by simp; omega))
      | Lannot e l => exact lannot _ _ _ _ (ihP _ _ _ (by simp; omega))
    · have := sizeOf_list_pos_aux es
      exact cons2 _ _ _ _ _ (ihP _ _ _ (by simp; omega))
        fun st' v1 h => ihP _ _ _ (Or.inr ⟨hP h, by simp; omega⟩)
  · intro st env v pes v' ihP ihQ
    rcases pes with _ | ⟨⟨p, e⟩, pes⟩
    · exact mnil _ _ _ _
    · have := sizeOf_list_pos_aux pes
      exact mcons _ _ _ _ _ _ _ (fun _ _ => ihQ _ _ _ _ _ (by simp; omega))
        fun env_v' _ _ => ihP _ _ _ (by simp; omega)
  · intro st env ds ihP ihR
    rcases ds with _ | ⟨d1, _ | ⟨d2, ds⟩⟩
    · exact dnil _ _
    · cases d1 with
      | Dlet l p e => exact dlet _ _ _ _ _ fun _ => ihP _ _ _ (by simp; omega)
      | Dletrec l funs => exact dletrec _ _ _ _
      | Dtype l tds => exact dtype _ _ _ _
      | Dtabbrev l tvs tn t => exact dtabbrev _ _ _ _ _ _
      | Dexn l cn ts => exact dexn _ _ _ _ _
      | Dmod mn ds => exact dmod _ _ _ _ (ihR _ _ _ (by simp; omega))
      | Dlocal lds ds =>
        exact dlocal _ _ _ _ (ihR _ _ _ (by simp; omega))
          fun st1 env1 h => ihR _ _ _ (Or.inr ⟨hR h, by simp; omega⟩)
      | Denv n => exact denv _ _ _
    · have := sizeOf_list_pos_aux ds
      exact dcons2 _ _ _ _ _ (ihR _ _ _ (by simp; omega))
        fun st1 env1 h => ihR _ _ _ (Or.inr ⟨hR h, by simp; omega⟩)

end

end CmlTS
