import CandleLean
open Candle HOL Classical

namespace Mut
@[reducible] def Equal (ty : type) : term := Const (mls "=") (Fun (Fun ty BoolTy) ty)
end Mut

theorem witness : ∃ ty, Mut.Equal ty ≠ Candle.Equal ty := by
  refine ⟨BoolTy, ?_⟩
  intro h
  simp [Mut.Equal, Candle.Equal, Fun, BoolTy] at h

#print axioms witness
