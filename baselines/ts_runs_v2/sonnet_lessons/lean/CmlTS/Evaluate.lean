import CmlTS.Ast
import CmlTS.Namespace
import CmlTS.Ffi
import CmlTS.SemanticPrimitives
import CmlTS.FpSem

/-!
# evaluate (HOL4 theory `evaluate`): functional big-step semantics

The semantics is defined using `fix_clock` so that termination (lexicographic on the clock and
the size of the syntax) can be proved.  As in HOL4, the clean equations without `fix_clock` hold
as theorems (HOL4 `evaluate_def`, not part of this definitions stage).
-/

universe u v w

noncomputable section

open Classical

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/- HOL4:
   Definition fix_clock_def:
     fix_clock s (s',res) =
       (s' with clock := if s'.clock ≤ s.clock then s'.clock else s.clock, res)
   End -/
def fix_clock {α : Type u} {β : Type v} (s : state α) (p : state α × β) : state α × β :=
  ({ p.1 with clock := if p.1.clock ≤ s.clock then p.1.clock else s.clock }, p.2)

/-- Auxiliary (not in HOL4): `fix_clock` together with the proof that the resulting clock is at
most the original one; `(fix_clock' s p).1 = fix_clock s p`.  Used so that the termination
proof of `evaluate` can see the clock bound. -/
def fix_clock' {α : Type u} {β : Type v} (s : state α) (p : state α × β) :
    { y : state α × β // y.1.clock ≤ s.clock } :=
  ⟨fix_clock s p, by
    unfold fix_clock
    simp only
    split <;> omega⟩

/- HOL4:
   Definition dec_clock_def:
     dec_clock s = (s with clock := s.clock − 1)
   End -/
def dec_clock {α : Type u} (s : state α) : state α := { s with clock := s.clock - 1 }

/- HOL4:
   Definition do_eval_res_def:
     do_eval_res vs s =
       case do_eval vs s.eval_state of
       | NONE => (s,Rerr (Rabort Rtype_error))
       | SOME (env1,decs,es1) => (s with eval_state := es1,Rval (env1,decs))
   End -/
def do_eval_res {α : Type u} (vs : List Value) (s : state α) :
    state α × result (sem_env Value × List dec) Value :=
  match do_eval vs s.eval_state with
  | none => (s, .Rerr (.Rabort .Rtype_error))
  | some (env1, decs, es1) => ({ s with eval_state := es1 }, .Rval (env1, decs))

/- HOL4:
   (* list_result is equivalent to map_result (\v. [v]) I, where map_result is
    * defined in evalPropsTheory *)
   Definition list_result_def[simp]:
     list_result (Rval v) = Rval [v] ∧
     list_result (Rerr e) = Rerr e
   End -/
def list_result {α : Type u} {β : Type v} : result α β → result (List α) β
  | .Rval v => .Rval [v]
  | .Rerr e => .Rerr e

theorem sizeOf_append' {α : Type u} [SizeOf α] (l1 l2 : List α) :
    sizeOf (l1 ++ l2) + 1 = sizeOf l1 + sizeOf l2 := by
  induction l1 with
  | nil => simp; omega
  | cons a l ih => simp; omega

theorem sizeOf_reverse' {α : Type u} [SizeOf α] (l : List α) : sizeOf l.reverse = sizeOf l := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.reverse_cons]
    have := sizeOf_append' l.reverse [a]
    simp at this ⊢
    omega

theorem sizeOf_list_pos {α : Type u} [SizeOf α] (l : List α) : 0 < sizeOf l := by
  cases l <;> simp <;> omega

theorem do_log_exp {l : lop} {v : Value} {e e' : exp} (h : do_log l v e = some (.Exp e')) :
    e' = e := by
  unfold do_log at h
  split at h
  · cases h; rfl
  · split at h <;> cases h

theorem do_if_exp {v : Value} {e1 e2 e : exp} (h : do_if v e1 e2 = some e) :
    e = e1 ∨ e = e2 := by
  unfold do_if at h
  split at h
  · cases h; left; rfl
  · split at h
    · cases h; right; rfl
    · cases h

/-- helper for the lexicographic termination measure `(clock, size)` -/
theorem lex_helper {a b c d : Nat} (h : a < c ∨ (a = c ∧ b < d)) :
    Prod.Lex (fun x1 x2 => x1 < x2) (fun x1 x2 => x1 < x2) (a, b) (c, d) := by
  rcases h with h | ⟨h1, h2⟩
  · exact Prod.Lex.left _ _ h
  · subst h1; exact Prod.Lex.right _ h2

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
     \\ rw [do_if_def,do_log_def,do_eval_res_def,dec_clock_def]
     \\ imp_res_tac fix_clock_IMP \\ fs []
     \\ fs [listTheory.list_size_def,list_size_REVERSE]
   End
   (Lean: `evaluate`, `evaluate_match`, `evaluate_decs` are mutually recursive; every call of
   `fix_clock` is `(fix_clock' ..).1`, matched through the subtype so that the bound
   `clock ≤` is available to the termination proof; `(fix_clock' s p).1 = fix_clock s p`.) -/
mutual
def evaluate {α : Type u} : state α → sem_env Value → List exp →
    state α × result (List Value) Value
  | st, _, [] => (st, .Rval [])
  | st, env, e1 :: e2 :: es =>
    match fix_clock' st (evaluate st env [e1]) with
    | ⟨(st', .Rval v1), _⟩ =>
      match evaluate st' env (e2 :: es) with
      | (st'', .Rval vs) => (st'', .Rval (HD v1 :: vs))
      | (st'', .Rerr v8) => (st'', .Rerr v8)
    | ⟨(st', .Rerr v10), _⟩ => (st', .Rerr v10)
  | st, _, [.Lit l] => (st, .Rval [.Litv l])
  | st, env, [.Raise e] =>
    match evaluate st env [e] with
    | (st', .Rval v) => (st', .Rerr (.Rraise (HD v)))
    | (st', .Rerr v8) => (st', .Rerr v8)
  | st, env, [.Handle e pes] =>
    match fix_clock' st (evaluate st env [e]) with
    | ⟨(st', .Rval v7), _⟩ => (st', .Rval v7)
    | ⟨(st', .Rerr (.Rraise v)), _⟩ =>
      if can_pmatch_all env.c st'.refs (MAP FST pes) v then
        evaluate_match st' env v pes v
      else (st', .Rerr (.Rabort .Rtype_error))
    | ⟨(st', .Rerr (.Rabort v12)), _⟩ => (st', .Rerr (.Rabort v12))
  | st, env, [.Con cn es] =>
    if do_con_check env.c cn (LENGTH es) then
      match evaluate st env (REVERSE es) with
      | (st', .Rval vs) =>
        match build_conv env.c cn (REVERSE vs) with
        | none => (st', .Rerr (.Rabort .Rtype_error))
        | some v => (st', .Rval [v])
      | (st', .Rerr v8) => (st', .Rerr v8)
    else (st, .Rerr (.Rabort .Rtype_error))
  | st, env, [.Var n] =>
    match nsLookup env.v n with
    | none => (st, .Rerr (.Rabort .Rtype_error))
    | some v => (st, .Rval [v])
  | st, env, [.Fun x e] => (st, .Rval [.Closure env x e])
  | st, env, [.App o es] =>
    match fix_clock' st (evaluate st env (REVERSE es)) with
    | ⟨(st', .Rval vs), _⟩ =>
      match getOpClass o with
      | .FunApp =>
        match do_opapp (REVERSE vs) with
        | some (env', e) =>
          if st'.clock = 0 then (st', .Rerr (.Rabort .Rtimeout_error))
          else evaluate (dec_clock st') env' [e]
        | none => (st', .Rerr (.Rabort .Rtype_error))
      | .Force =>
        match dest_thunk (REVERSE vs) st'.refs with
        | .BadRef => (st', .Rerr (.Rabort .Rtype_error))
        | .NotThunk => (st', .Rerr (.Rabort .Rtype_error))
        | .IsThunk .Evaluated v => (st', .Rval [v])
        | .IsThunk .NotEvaluated f =>
          match do_opapp [f, .Conv none []] with
          | some (env', e) =>
            if st'.clock = 0 then (st', .Rerr (.Rabort .Rtimeout_error))
            else
              match evaluate (dec_clock st') env' [e] with
              | (st2, .Rval vs2) =>
                match update_thunk (REVERSE vs) st2.refs vs2 with
                | none => (st2, .Rerr (.Rabort .Rtype_error))
                | some refs => ({ st2 with refs := refs }, .Rval vs2)
              | (st2, .Rerr e) => (st2, .Rerr e)
          | none => (st', .Rerr (.Rabort .Rtype_error))
      | .EvalOp =>
        match fix_clock' st' (do_eval_res (REVERSE vs) st') with
        | ⟨(st1, .Rval (env1, decs)), _⟩ =>
          if st1.clock = 0 then (st1, .Rerr (.Rabort .Rtimeout_error))
          else
            match fix_clock' (dec_clock st1) (evaluate_decs (dec_clock st1) env1 decs) with
            | ⟨(st2, .Rval env2), _⟩ =>
              match declare_env st2.eval_state (extend_dec_env env2 env1) with
              | some (x, es2) =>
                ({ st2 with eval_state := reset_env_generation st'.eval_state es2 }, .Rval [x])
              | none => (st2, .Rerr (.Rabort .Rtype_error))
            | ⟨(st2, .Rerr (.Rabort a)), _⟩ => (st2, .Rerr (.Rabort a))
            | ⟨(st2, .Rerr (.Rraise e)), _⟩ =>
              ({ st2 with eval_state := reset_env_generation st'.eval_state st2.eval_state },
                .Rerr (.Rraise e))
        | ⟨(st1, .Rerr e), _⟩ => (st1, .Rerr e)
      | .Simple =>
        match do_app (st'.refs, st'.ffi) o (REVERSE vs) with
        | none => (st', .Rerr (.Rabort .Rtype_error))
        | some ((refs, ffi), r) => ({ st' with refs := refs, ffi := ffi }, list_result r)
    | ⟨(st', .Rerr e), _⟩ => (st', .Rerr e)
  | st, env, [.Log l e1 e2] =>
    match fix_clock' st (evaluate st env [e1]) with
    | ⟨(st', .Rval v1), _⟩ =>
      match h : do_log l (HD v1) e2 with
      | none => (st', .Rerr (.Rabort .Rtype_error))
      | some (.Exp e) => evaluate st' env [e]
      | some (.Val v) => (st', .Rval [v])
    | ⟨(st', .Rerr v9), _⟩ => (st', .Rerr v9)
  | st, env, [.If e1 e2 e3] =>
    match fix_clock' st (evaluate st env [e1]) with
    | ⟨(st', .Rval v), _⟩ =>
      match h : do_if (HD v) e2 e3 with
      | none => (st', .Rerr (.Rabort .Rtype_error))
      | some e => evaluate st' env [e]
    | ⟨(st', .Rerr v8), _⟩ => (st', .Rerr v8)
  | st, env, [.Mat e pes] =>
    match fix_clock' st (evaluate st env [e]) with
    | ⟨(st', .Rval v), _⟩ =>
      if can_pmatch_all env.c st'.refs (MAP FST pes) (HD v) then
        evaluate_match st' env (HD v) pes bind_exn_v
      else (st', .Rerr (.Rabort .Rtype_error))
    | ⟨(st', .Rerr v8), _⟩ => (st', .Rerr v8)
  | st, env, [.Let xo e1 e2] =>
    match fix_clock' st (evaluate st env [e1]) with
    | ⟨(st', .Rval v), _⟩ =>
      evaluate st' { env with v := nsOptBind xo (HD v) env.v } [e2]
    | ⟨(st', .Rerr v8), _⟩ => (st', .Rerr v8)
  | st, env, [.Letrec funs e] =>
    if ALL_DISTINCT (MAP (fun xyz => xyz.1) funs) then
      evaluate st { env with v := build_rec_env funs env env.v } [e]
    else (st, .Rerr (.Rabort .Rtype_error))
  | st, env, [.Tannot e _] => evaluate st env [e]
  | st, env, [.Lannot e _] => evaluate st env [e]
termination_by st _ es => (st.clock, sizeOf es)
decreasing_by
  all_goals
    try (have h1 := do_log_exp ‹do_log _ _ _ = some (exp_or_val.Exp _)›; subst h1)
    try (rcases do_if_exp ‹do_if _ _ _ = some _› with h1 | h1 <;> subst h1)
    all_goals
      simp_wf
      apply lex_helper
      try dsimp only at *
      try have := sizeOf_list_pos ‹List exp›
      try have := sizeOf_list_pos ‹List dec›
      try have := sizeOf_list_pos ‹List (pat × exp)›
      try simp [sizeOf_reverse', dec_clock]
      try omega

def evaluate_match {α : Type u} : state α → sem_env Value → Value → List (pat × exp) → Value →
    state α × result (List Value) Value
  | st, _, _, [], err_v => (st, .Rerr (.Rraise err_v))
  | st, env, v, (p, e) :: pes, err_v =>
    if ALL_DISTINCT (pat_bindings p []) then
      match pmatch env.c st.refs p v [] with
      | .No_match => evaluate_match st env v pes err_v
      | .Match_type_error => (st, .Rerr (.Rabort .Rtype_error))
      | .Match env_v' =>
        evaluate st { env with v := nsAppend (alist_to_ns env_v') env.v } [e]
    else (st, .Rerr (.Rabort .Rtype_error))
termination_by st _ _ pes _ => (st.clock, sizeOf pes)
decreasing_by
  all_goals
    try (have h1 := do_log_exp ‹do_log _ _ _ = some (exp_or_val.Exp _)›; subst h1)
    try (rcases do_if_exp ‹do_if _ _ _ = some _› with h1 | h1 <;> subst h1)
    all_goals
      simp_wf
      apply lex_helper
      try dsimp only at *
      try have := sizeOf_list_pos ‹List exp›
      try have := sizeOf_list_pos ‹List dec›
      try have := sizeOf_list_pos ‹List (pat × exp)›
      try simp [sizeOf_reverse', dec_clock]
      try omega

def evaluate_decs {α : Type u} : state α → sem_env Value → List dec →
    state α × result (sem_env Value) Value
  | st, _, [] => (st, .Rval ⟨nsEmpty, nsEmpty⟩)
  | st, env, d1 :: d2 :: ds =>
    match fix_clock' st (evaluate_decs st env [d1]) with
    | ⟨(st1, .Rval env1), _⟩ =>
      match evaluate_decs st1 (extend_dec_env env1 env) (d2 :: ds) with
      | (st2, r) => (st2, combine_dec_result env1 r)
    | ⟨(st1, .Rerr v7), _⟩ => (st1, .Rerr v7)
  | st, env, [.Dlet _ p e] =>
    if ALL_DISTINCT (pat_bindings p []) ∧ every_exp (one_con_check env.c) e then
      match evaluate st env [e] with
      | (st', .Rval v) =>
        (st',
          match pmatch env.c st'.refs p (HD v) [] with
          | .No_match => .Rerr (.Rraise bind_exn_v)
          | .Match_type_error => .Rerr (.Rabort .Rtype_error)
          | .Match new_vals => .Rval ⟨alist_to_ns new_vals, nsEmpty⟩)
      | (st', .Rerr err) => (st', .Rerr err)
    else (st, .Rerr (.Rabort .Rtype_error))
  | st, env, [.Dletrec _ funs] =>
    (st,
      if ALL_DISTINCT (MAP (fun xyz => xyz.1) funs) ∧
          EVERY (fun fne => every_exp (one_con_check env.c) fne.2.2) funs then
        .Rval ⟨build_rec_env funs env nsEmpty, nsEmpty⟩
      else .Rerr (.Rabort .Rtype_error))
  | st, _, [.Dtype _ tds] =>
    if EVERY check_dup_ctors tds then
      ({ st with next_type_stamp := st.next_type_stamp + LENGTH tds },
        .Rval ⟨nsEmpty, build_tdefs st.next_type_stamp tds⟩)
    else (st, .Rerr (.Rabort .Rtype_error))
  | st, _, [.Dtabbrev _ _ _ _] => (st, .Rval ⟨nsEmpty, nsEmpty⟩)
  | st, env, [.Denv n] =>
    match declare_env st.eval_state env with
    | none => (st, .Rerr (.Rabort .Rtype_error))
    | some (x, es') => ({ st with eval_state := es' }, .Rval ⟨nsSing n x, nsEmpty⟩)
  | st, _, [.Dexn _ cn ts] =>
    ({ st with next_exn_stamp := st.next_exn_stamp + 1 },
      .Rval ⟨nsEmpty, nsSing cn (LENGTH ts, .ExnStamp st.next_exn_stamp)⟩)
  | st, env, [.Dmod mn ds] =>
    match evaluate_decs st env ds with
    | (st', r) =>
      (st',
        match r with
        | .Rval env' => .Rval ⟨nsLift mn env'.v, nsLift mn env'.c⟩
        | .Rerr err => .Rerr err)
  | st, env, [.Dlocal lds ds] =>
    match fix_clock' st (evaluate_decs st env lds) with
    | ⟨(st1, .Rval env1), _⟩ => evaluate_decs st1 (extend_dec_env env1 env) ds
    | ⟨(st1, .Rerr v7), _⟩ => (st1, .Rerr v7)
termination_by st _ ds => (st.clock, sizeOf ds)
decreasing_by
  all_goals
    try (have h1 := do_log_exp ‹do_log _ _ _ = some (exp_or_val.Exp _)›; subst h1)
    try (rcases do_if_exp ‹do_if _ _ _ = some _› with h1 | h1 <;> subst h1)
    all_goals
      simp_wf
      apply lex_helper
      try dsimp only at *
      try have := sizeOf_list_pos ‹List exp›
      try have := sizeOf_list_pos ‹List dec›
      try have := sizeOf_list_pos ‹List (pat × exp)›
      try simp [sizeOf_reverse', dec_clock]
      try omega
end

/-! ## Theorems (stage 2) -/

/- HOL4: Theorem evaluate_clock:
     (∀(s1:'ffi state) env e r s2.
        evaluate s1 env e = (s2,r) ⇒ s2.clock ≤ s1.clock) ∧
     (∀(s1:'ffi state) env v p v' r s2.
        evaluate_match s1 env v p v' = (s2,r) ⇒ s2.clock ≤ s1.clock) ∧
     (∀(s1:'ffi state) env ds r s2.
        evaluate_decs s1 env ds = (s2,r) ⇒ s2.clock ≤ s1.clock) -/
theorem evaluate_clock {α : Type u} :
    (∀ (s1 : state α) (env : sem_env Value) (e : List exp)
       (r : result (List Value) Value) (s2 : state α),
       evaluate s1 env e = (s2, r) → s2.clock ≤ s1.clock) ∧
    (∀ (s1 : state α) (env : sem_env Value) (v : Value) (p : List (pat × exp)) (v' : Value)
       (r : result (List Value) Value) (s2 : state α),
       evaluate_match s1 env v p v' = (s2, r) → s2.clock ≤ s1.clock) ∧
    (∀ (s1 : state α) (env : sem_env Value) (ds : List dec)
       (r : result (sem_env Value) Value) (s2 : state α),
       evaluate_decs s1 env ds = (s2, r) → s2.clock ≤ s1.clock) := by
  sorry

/- HOL4: Theorem fix_clock_do_eval_res:
     fix_clock s (do_eval_res vs s) = do_eval_res vs s -/
theorem fix_clock_do_eval_res {α : Type u} (s : state α) (vs : List Value) :
    fix_clock s (do_eval_res vs s) = do_eval_res vs s := by
  sorry

/- HOL4: Theorem fix_clock_evaluate:
     fix_clock s1 (evaluate s1 env e) = evaluate s1 env e /\
     fix_clock s1 (evaluate_decs s1 env ds) = evaluate_decs s1 env ds -/
theorem fix_clock_evaluate {α : Type u} (s1 : state α) (env : sem_env Value) (e : List exp)
    (ds : List dec) :
    fix_clock s1 (evaluate s1 env e) = evaluate s1 env e ∧
    fix_clock s1 (evaluate_decs s1 env ds) = evaluate_decs s1 env ds := by
  sorry

end
