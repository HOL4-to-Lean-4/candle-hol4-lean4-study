import CandleLean
open HOL Candle Classical
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
noncomputable section

namespace Mut
def typeof : term → type
  | Var _ ty => ty
  | Const _ ty => ty
  | Comb s _ => codomain (typeof s)
  | Abs v t => Fun (typeof t) (typeof v)
end Mut

/-- `λ(x:bool). y:a` has type `bool → a` in the base and `a → bool` in the mutant. -/
theorem witness : ∃ t : term, Mut.typeof t ≠ Candle.typeof t := by
  refine ⟨Abs (Var (mls "x") BoolTy) (Var (mls "y") (Tyvar (mls "a"))), ?_⟩
  intro h
  simp only [Mut.typeof, Candle.typeof, Fun, BoolTy] at h
  injection h with _ h2
  injection h2 with h3
  cases h3

#print axioms witness
