import CmlTS.FpSem
import CmlTS.Ast
import CmlTS.Namespace
import CmlTS.Ffi
import CmlTS.SemanticPrimitives
/-
  Translation of HOL4 theory `evaluate` (evaluateScript.sml): definitions.
-/
set_option autoImplicit false

namespace CmlTS
open Classical

/- HOL4:
Definition fix_clock_def:
  fix_clock s (s',res) =
    (s' with clock := if s'.clock ≤ s.clock then s'.clock else s.clock, res)
End -/
def fix_clock {ffiT1 ffiT2 α : Type} (s : state ffiT1) : state ffiT2 × α → state ffiT2 × α
  | (s', res) => ({ s' with clock := if s'.clock ≤ s.clock then s'.clock else s.clock }, res)

/- HOL4:
Definition dec_clock_def:
  dec_clock s = (s with clock := s.clock − 1)
End -/
def dec_clock {ffiT : Type} (s : state ffiT) : state ffiT := { s with clock := s.clock - 1 }

/- HOL4:
Definition do_eval_res_def:
  do_eval_res vs s =
    case do_eval vs s.eval_state of
    | NONE => (s,Rerr (Rabort Rtype_error))
    | SOME (env1,decs,es1) => (s with eval_state := es1,Rval (env1,decs))
End -/
noncomputable def do_eval_res {ffiT β : Type} (vs : List val) (s : state ffiT) :
    state ffiT × result (sem_env val × List dec) β :=
  match do_eval vs s.eval_state with
  | none => (s, .Rerr (.Rabort .Rtype_error))
  | some (env1, decs, es1) => ({ s with eval_state := es1 }, .Rval (env1, decs))

/- HOL4:
Definition list_result_def[simp]:
  list_result (Rval v) = Rval [v] ∧
  list_result (Rerr e) = Rerr e
End -/
def list_result {α β : Type} : result α β → result (List α) β
  | .Rval v => .Rval [v]
  | .Rerr e => .Rerr e

/- HOL4: Theorem fix_clock_IMP[local]: fix_clock s x = (s1,res) ==> s1.clock <= s.clock
   (used in the termination proof of evaluate) -/
theorem fix_clock_IMP {ffiT1 ffiT2 α : Type} {s : state ffiT1} {x : state ffiT2 × α}
    {s1 : state ffiT2} {res : α} (h : fix_clock s x = (s1, res)) : s1.clock ≤ s.clock := by
  obtain ⟨s', r⟩ := x
  simp only [fix_clock, Prod.mk.injEq] at h
  obtain ⟨h1, _⟩ := h
  subst h1
  dsimp only
  split <;> omega

theorem do_if_mem {α : Type} {v : val} {e1 e2 e : α} (h : do_if v e1 e2 = some e) :
    e = e1 ∨ e = e2 := by
  unfold do_if at h
  split at h
  · simp_all
  · split at h <;> simp_all

theorem do_log_mem {l : lop} {v : val} {e e' : exp} (h : do_log l v e = some (.Exp e')) :
    e' = e := by
  unfold do_log at h
  split at h
  · simp_all
  · split at h <;> simp_all

theorem evaluate_lex_le {a b c d : Nat} (h1 : a ≤ c) (h2 : b < d) :
    Prod.Lex (fun x y : Nat => x < y) (fun x y : Nat => x < y) (a, b) (c, d) := by
  rcases Nat.lt_or_eq_of_le h1 with h | h
  · exact Prod.Lex.left _ _ h
  · subst h; exact Prod.Lex.right _ h2

theorem evaluate_lex_lt {a b c d : Nat} (h1 : a < c) :
    Prod.Lex (fun x y : Nat => x < y) (fun x y : Nat => x < y) (a, b) (c, d) :=
  Prod.Lex.left _ _ h1

theorem dec_clock_lt {ffiT1 ffiT2 ffiT3 α : Type} {s : state ffiT1} {x : state ffiT2 × α}
    {s1 : state ffiT2} {res : α} (h : fix_clock s x = (s1, res)) (hc : ¬ s1.clock = 0)
    {s0 : state ffiT3} (h0 : s.clock ≤ s0.clock) : (dec_clock s1).clock < s0.clock := by
  have := fix_clock_IMP h
  simp only [dec_clock]
  omega

theorem sizeOf_list_pos {α : Type} [SizeOf α] (l : List α) : 0 < sizeOf l := by
  cases l with
  | nil => simp
  | cons h t => simp; omega

theorem evaluate_size_cons {α : Type} [SizeOf α] (a b : α) (l : List α) :
    sizeOf [a] < sizeOf (a :: b :: l) := by
  have := sizeOf_list_pos l
  simp
  omega

theorem evaluate_size_match {α β : Type} [SizeOf α] [SizeOf β] (a : α) (b : β)
    (l : List (α × β)) : sizeOf [b] < sizeOf ((a, b) :: l) := by
  have := sizeOf_list_pos l
  simp
  omega

/-- Termination tactic for `evaluate`: the measure is `(clock, size)`, lexicographically. -/
macro "evaluate_decreasing" : tactic => `(tactic| (
  first
    | exact evaluate_lex_le (Nat.le_refl _) (evaluate_size_cons _ _ _)
    | exact evaluate_lex_le (Nat.le_refl _) (evaluate_size_match _ _ _)
    | (apply evaluate_lex_le (Nat.le_refl _)
       simp [sizeOf_list_reverse]
       try omega
       done)
    | (apply evaluate_lex_le (fix_clock_IMP (by assumption))
       simp [sizeOf_list_reverse]
       try omega
       done)
    | (apply evaluate_lex_le (fix_clock_IMP (by assumption))
       have := do_log_mem (by assumption)
       subst this
       simp
       try omega
       done)
    | (apply evaluate_lex_le (fix_clock_IMP (by assumption))
       rcases do_if_mem (by assumption) with h | h <;> subst h <;> simp <;> omega
       done)
    | (apply evaluate_lex_lt
       apply dec_clock_lt
       all_goals first
         | assumption
         | exact Nat.le_refl _
         | exact fix_clock_IMP (by assumption))))

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
   (HOL4 later removes `fix_clock` from the equations: fix_clock_evaluate, full_evaluate_def.) -/
set_option wf.preprocess false in
set_option maxHeartbeats 2000000 in
mutual
noncomputable def evaluate {ffiT : Type} (st : state ffiT) (env : sem_env val) :
    List exp → state ffiT × result (List val) val
  | [] => (st, .Rval [])
  | e1 :: e2 :: es =>
    match _h : fix_clock st (evaluate st env [e1]) with
    | (st', .Rval v1) =>
      match evaluate st' env (e2 :: es) with
      | (st'', .Rval vs) => (st'', .Rval (HD v1 :: vs))
      | (st'', .Rerr v8) => (st'', .Rerr v8)
    | (st', .Rerr v10) => (st', .Rerr v10)
  | [.Lit l] => (st, .Rval [.Litv l])
  | [.Raise e] =>
    match evaluate st env [e] with
    | (st', .Rval v) => (st', .Rerr (.Rraise (HD v)))
    | (st', .Rerr v8) => (st', .Rerr v8)
  | [.Handle e pes] =>
    match _h : fix_clock st (evaluate st env [e]) with
    | (st', .Rval v7) => (st', .Rval v7)
    | (st', .Rerr (.Rraise v)) =>
      if can_pmatch_all env.c st'.refs (pes.map Prod.fst) v then
        evaluate_match st' env v pes v
      else (st', .Rerr (.Rabort .Rtype_error))
    | (st', .Rerr (.Rabort v12)) => (st', .Rerr (.Rabort v12))
  | [.Con cn es] =>
    if do_con_check env.c cn es.length then
      match evaluate st env es.reverse with
      | (st', .Rval vs) =>
        match build_conv env.c cn vs.reverse with
        | none => (st', .Rerr (.Rabort .Rtype_error))
        | some v => (st', .Rval [v])
      | (st', .Rerr v8) => (st', .Rerr v8)
    else (st, .Rerr (.Rabort .Rtype_error))
  | [.Var n] =>
    match nsLookup env.v n with
    | none => (st, .Rerr (.Rabort .Rtype_error))
    | some v => (st, .Rval [v])
  | [.Fun x e] => (st, .Rval [.Closure env x e])
  | [.App op es] =>
    match _h : fix_clock st (evaluate st env es.reverse) with
    | (st', .Rval vs) =>
      match getOpClass op with
      | .FunApp =>
        match do_opapp vs.reverse with
        | some (env', e) =>
          if _hc : st'.clock = 0 then
            (st', .Rerr (.Rabort .Rtimeout_error))
          else
            evaluate (dec_clock st') env' [e]
        | none => (st', .Rerr (.Rabort .Rtype_error))
      | .Force =>
        match dest_thunk vs.reverse st'.refs with
        | .BadRef => (st', .Rerr (.Rabort .Rtype_error))
        | .NotThunk => (st', .Rerr (.Rabort .Rtype_error))
        | .IsThunk .Evaluated v => (st', .Rval [v])
        | .IsThunk .NotEvaluated f =>
          match do_opapp [f, .Conv none []] with
          | some (env', e) =>
            if _hc : st'.clock = 0 then (st', .Rerr (.Rabort .Rtimeout_error)) else
              match evaluate (dec_clock st') env' [e] with
              | (st2, .Rval vs2) =>
                match update_thunk vs.reverse st2.refs vs2 with
                | none => (st2, .Rerr (.Rabort .Rtype_error))
                | some refs => ({ st2 with refs := refs }, .Rval vs2)
              | (st2, .Rerr e) => (st2, .Rerr e)
          | none => (st', .Rerr (.Rabort .Rtype_error))
      | .EvalOp =>
        match _h1 : fix_clock st' (do_eval_res vs.reverse st') with
        | (st1, .Rval (env1, decs)) =>
          if _hc : st1.clock = 0 then
            (st1, .Rerr (.Rabort .Rtimeout_error))
          else
            match fix_clock (dec_clock st1) (evaluate_decs (dec_clock st1) env1 decs) with
            | (st2, .Rval env2) =>
              match declare_env st2.eval_state (extend_dec_env env2 env1) with
              | some (x, es2) =>
                ({ st2 with eval_state := reset_env_generation st'.eval_state es2 }, .Rval [x])
              | none => (st2, .Rerr (.Rabort .Rtype_error))
            | (st2, .Rerr (.Rabort a)) => (st2, .Rerr (.Rabort a))
            | (st2, .Rerr e) =>
              ({ st2 with
                  eval_state := reset_env_generation st'.eval_state st2.eval_state }, .Rerr e)
        | (st1, .Rerr e) => (st1, .Rerr e)
      | .Simple =>
        match do_app (st'.refs, st'.ffi) op vs.reverse with
        | none => (st', .Rerr (.Rabort .Rtype_error))
        | some ((refs, ffi), r) => ({ st' with refs := refs, ffi := ffi }, list_result r)
    | res => res
  | [.Log lop e1 e2] =>
    match _h : fix_clock st (evaluate st env [e1]) with
    | (st', .Rval v1) =>
      match _hl : do_log lop (HD v1) e2 with
      | none => (st', .Rerr (.Rabort .Rtype_error))
      | some (.Exp e) => evaluate st' env [e]
      | some (.Val v) => (st', .Rval [v])
    | (st', .Rerr v9) => (st', .Rerr v9)
  | [.If e1 e2 e3] =>
    match _h : fix_clock st (evaluate st env [e1]) with
    | (st', .Rval v) =>
      match _hi : do_if (HD v) e2 e3 with
      | none => (st', .Rerr (.Rabort .Rtype_error))
      | some e => evaluate st' env [e]
    | (st', .Rerr v8) => (st', .Rerr v8)
  | [.Mat e pes] =>
    match _h : fix_clock st (evaluate st env [e]) with
    | (st', .Rval v) =>
      if can_pmatch_all env.c st'.refs (pes.map Prod.fst) (HD v) then
        evaluate_match st' env (HD v) pes bind_exn_v
      else (st', .Rerr (.Rabort .Rtype_error))
    | (st', .Rerr v8) => (st', .Rerr v8)
  | [.Let xo e1 e2] =>
    match _h : fix_clock st (evaluate st env [e1]) with
    | (st', .Rval v) =>
      evaluate st' { env with v := nsOptBind xo (HD v) env.v } [e2]
    | (st', .Rerr v8) => (st', .Rerr v8)
  | [.Letrec funs e] =>
    if ALL_DISTINCT (funs.map fun (x, _, _) => x) then
      evaluate st { env with v := build_rec_env funs env env.v } [e]
    else (st, .Rerr (.Rabort .Rtype_error))
  | [.Tannot e _] => evaluate st env [e]
  | [.Lannot e _] => evaluate st env [e]
termination_by es => (st.clock, sizeOf es)
decreasing_by all_goals evaluate_decreasing
noncomputable def evaluate_match {ffiT : Type} (st : state ffiT) (env : sem_env val) (v : val) :
    List (pat × exp) → val → state ffiT × result (List val) val
  | [], err_v => (st, .Rerr (.Rraise err_v))
  | (p, e) :: pes, err_v =>
    if ALL_DISTINCT (pat_bindings p []) then
      match pmatch env.c st.refs p v [] with
      | .No_match => evaluate_match st env v pes err_v
      | .Match_type_error => (st, .Rerr (.Rabort .Rtype_error))
      | .Match env_v' =>
        evaluate st { env with v := nsAppend (alist_to_ns env_v') env.v } [e]
    else (st, .Rerr (.Rabort .Rtype_error))
termination_by pes _ => (st.clock, sizeOf pes)
decreasing_by all_goals evaluate_decreasing
noncomputable def evaluate_decs {ffiT : Type} (st : state ffiT) (env : sem_env val) :
    List dec → state ffiT × result (sem_env val) val
  | [] => (st, .Rval { v := nsEmpty, c := nsEmpty })
  | d1 :: d2 :: ds =>
    match _h : fix_clock st (evaluate_decs st env [d1]) with
    | (st1, .Rval env1) =>
      match evaluate_decs st1 (extend_dec_env env1 env) (d2 :: ds) with
      | (st2, r) => (st2, combine_dec_result env1 r)
    | (st1, .Rerr v7) => (st1, .Rerr v7)
  | [.Dlet _ p e] =>
    if ALL_DISTINCT (pat_bindings p []) ∧ every_exp (one_con_check env.c) e then
      match evaluate st env [e] with
      | (st', .Rval v) =>
        (st',
          match pmatch env.c st'.refs p (HD v) [] with
          | .No_match => .Rerr (.Rraise bind_exn_v)
          | .Match_type_error => .Rerr (.Rabort .Rtype_error)
          | .Match new_vals => .Rval { v := alist_to_ns new_vals, c := nsEmpty })
      | (st', .Rerr err) => (st', .Rerr err)
    else (st, .Rerr (.Rabort .Rtype_error))
  | [.Dletrec _ funs] =>
    (st,
      if ALL_DISTINCT (funs.map fun (x, _, _) => x) ∧
          EVERY (fun (_, _, e) => every_exp (one_con_check env.c) e) funs then
        .Rval { v := build_rec_env funs env nsEmpty, c := nsEmpty }
      else .Rerr (.Rabort .Rtype_error))
  | [.Dtype _ tds] =>
    if EVERY check_dup_ctors tds then
      ({ st with next_type_stamp := st.next_type_stamp + tds.length },
        .Rval { v := nsEmpty, c := build_tdefs st.next_type_stamp tds })
    else (st, .Rerr (.Rabort .Rtype_error))
  | [.Dtabbrev _ _ _ _] => (st, .Rval { v := nsEmpty, c := nsEmpty })
  | [.Denv n] =>
    match declare_env st.eval_state env with
    | none => (st, .Rerr (.Rabort .Rtype_error))
    | some (x, es') => ({ st with eval_state := es' }, .Rval { v := nsSing n x, c := nsEmpty })
  | [.Dexn _ cn ts] =>
    ({ st with next_exn_stamp := st.next_exn_stamp + 1 },
      .Rval { v := nsEmpty, c := nsSing cn (ts.length, .ExnStamp st.next_exn_stamp) })
  | [.Dmod mn ds] =>
    match evaluate_decs st env ds with
    | (st', r) =>
      (st',
        match r with
        | .Rval env' => .Rval { v := nsLift mn env'.v, c := nsLift mn env'.c }
        | .Rerr err => .Rerr err)
  | [.Dlocal lds ds] =>
    match _h : fix_clock st (evaluate_decs st env lds) with
    | (st1, .Rval env1) => evaluate_decs st1 (extend_dec_env env1 env) ds
    | (st1, .Rerr v7) => (st1, .Rerr v7)
termination_by ds => (st.clock, sizeOf ds)
decreasing_by all_goals evaluate_decreasing
end

/- HOL4:
  (∀(s1:'ffi state) env e r s2.
     evaluate s1 env e = (s2,r) ⇒ s2.clock ≤ s1.clock) ∧
  (∀(s1:'ffi state) env v p v' r s2.
     evaluate_match s1 env v p v' = (s2,r) ⇒ s2.clock ≤ s1.clock) ∧
  (∀(s1:'ffi state) env ds r s2.
     evaluate_decs s1 env ds = (s2,r) ⇒ s2.clock ≤ s1.clock) -/
theorem evaluate_clock {ffiT : Type} :
    (∀ (s1 : state ffiT) (env : sem_env val) (e : List exp) (r : result (List val) val)
        (s2 : state ffiT),
      evaluate s1 env e = (s2, r) → s2.clock ≤ s1.clock) ∧
    (∀ (s1 : state ffiT) (env : sem_env val) (v : val) (p : List (pat × exp)) (v' : val)
        (r : result (List val) val) (s2 : state ffiT),
      evaluate_match s1 env v p v' = (s2, r) → s2.clock ≤ s1.clock) ∧
    (∀ (s1 : state ffiT) (env : sem_env val) (ds : List dec) (r : result (sem_env val) val)
        (s2 : state ffiT),
      evaluate_decs s1 env ds = (s2, r) → s2.clock ≤ s1.clock) := by
  sorry

/- HOL4:
   fix_clock s (do_eval_res vs s) = do_eval_res vs s -/
theorem fix_clock_do_eval_res {ffiT β : Type} {s : state ffiT} {vs : List val} :
    fix_clock s (do_eval_res vs s : state ffiT × result (sem_env val × List dec) β) =
      do_eval_res vs s := by
  sorry

/- HOL4:
   fix_clock s1 (evaluate s1 env e) = evaluate s1 env e /\
   fix_clock s1 (evaluate_decs s1 env ds) = evaluate_decs s1 env ds -/
theorem fix_clock_evaluate {ffiT : Type} {s1 : state ffiT} {env : sem_env val} {e : List exp}
    {ds : List dec} :
    fix_clock s1 (evaluate s1 env e) = evaluate s1 env e ∧
    fix_clock s1 (evaluate_decs s1 env ds) = evaluate_decs s1 env ds := by
  sorry

end CmlTS
