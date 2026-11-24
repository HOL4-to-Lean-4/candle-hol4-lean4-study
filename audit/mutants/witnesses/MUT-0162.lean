import CandleLean
open Candle HOL Classical

namespace Mut
@[reducible] def Equal (ty : type) : term := Const (mls "=") (Fun ty (Fun BoolTy ty))
end Mut

/-- with `ty = Fun BoolTy BoolTy` the mutant's type is `ty -> (bool -> ty)`, which differs from `ty -> (ty -> bool)` -/
theorem witness : ∃ ty, Mut.Equal ty ≠ Candle.Equal ty := by
  refine ⟨Fun BoolTy BoolTy, ?_⟩
  intro h
  simp [Mut.Equal, Candle.Equal, Fun, BoolTy] at h

#print axioms witness
