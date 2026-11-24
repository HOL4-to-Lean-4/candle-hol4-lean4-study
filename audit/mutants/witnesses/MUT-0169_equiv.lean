import CandleLean
open HOL Candle Classical
set_option linter.unusedVariables false

/-- statement of `Candle.VSUBST_WELLTYPED` in the base (as a Prop; the base theorem itself is unproved, so it is not used) -/
def base_stmt : Prop :=
    ∀ (tm : term) (ty : type) (ilist : List (term × term)),
      welltyped tm ∧
      (∀ s s', (s', s) ∈ ilist → ∃ x ty, s = Var x ty ∧ has_type s' ty) →
      welltyped (VSUBST ilist tm)

/-- statement of the mutant: the quantified `ty` has type `term` instead of `type` -/
def mut_stmt : Prop :=
    ∀ (tm : term) (ty : term) (ilist : List (term × term)),
      welltyped tm ∧
      (∀ s s', (s', s) ∈ ilist → ∃ x ty, s = Var x ty ∧ has_type s' ty) →
      welltyped (VSUBST ilist tm)

/-- the bound variable `ty` is never used (it is shadowed by the inner `∃ x ty`), and both types are inhabited,
so the two statements are logically equivalent -/
theorem equiv : mut_stmt ↔ base_stmt := by
  constructor
  · intro h tm _ ilist
    exact h tm (Var (mls "x") BoolTy) ilist
  · intro h tm _ ilist
    exact h tm BoolTy ilist

#print axioms equiv
