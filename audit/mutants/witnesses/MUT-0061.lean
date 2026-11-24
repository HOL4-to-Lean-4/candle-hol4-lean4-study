import CandleLean
open HOL Candle Classical
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
universe u
noncomputable section

namespace Mut
def orda (env : List (term × term)) (t1 t2 : term) : ordering :=
  if t1 = t2 ∧ env = [] then EQUAL else
    match t1, t2 with
    | Var _ _, Var _ _ => ordav env t1 t2
    | Const _ _, Const _ _ => term_cmp t1 t2
    | Comb s1 t1', Comb s2 t2' =>
      let c := orda env s1 s2
      if c ≠ EQUAL then c else orda env t1' t2'
    | Abs s1 t1', Abs s2 t2' =>
      let c := type_cmp (typeof s1) (typeof s2)
      if c ≠ EQUAL then c else orda ((s1, s2) :: env) t1' t2'
    | Var _ _, _ => LESS
    | _, Var _ _ => GREATER
    | Const _ _, _ => LESS
    | _, Const _ _ => GREATER
    | Comb _ _, _ => LESS
    | _, Comb _ _ => LESS
termination_by sizeOf t1
end Mut

theorem witness : ∃ (env : List (term × term)) (t1 t2 : term), Mut.orda env t1 t2 ≠ Candle.orda env t1 t2 := by
  have hne : ¬ (Abs (Var (mls "x") (Tyvar (mls "a"))) (Var (mls "x") (Tyvar (mls "a"))) =
      Comb (Var (mls "x") (Tyvar (mls "a"))) (Var (mls "x") (Tyvar (mls "a"))) ∧ ([] : List (term × term)) = []) := by
    intro h; cases h.1
  refine ⟨[], Abs (Var (mls "x") (Tyvar (mls "a"))) (Var (mls "x") (Tyvar (mls "a"))),
    Comb (Var (mls "x") (Tyvar (mls "a"))) (Var (mls "x") (Tyvar (mls "a"))), ?_⟩
  have hm : Mut.orda [] (Abs (Var (mls "x") (Tyvar (mls "a"))) (Var (mls "x") (Tyvar (mls "a"))))
      (Comb (Var (mls "x") (Tyvar (mls "a"))) (Var (mls "x") (Tyvar (mls "a")))) = LESS := by
    rw [Mut.orda, if_neg hne]
    all_goals (intro _ _ h; cases h)
  have hb : Candle.orda [] (Abs (Var (mls "x") (Tyvar (mls "a"))) (Var (mls "x") (Tyvar (mls "a"))))
      (Comb (Var (mls "x") (Tyvar (mls "a"))) (Var (mls "x") (Tyvar (mls "a")))) = GREATER := by
    rw [Candle.orda, if_neg hne]
    all_goals (intro _ _ h; cases h)
  rw [hm, hb]; intro h; cases h

#print axioms witness
