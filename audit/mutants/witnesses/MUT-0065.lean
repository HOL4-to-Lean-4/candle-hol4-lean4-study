import CandleLean

universe u v

open HOL Candle Classical

noncomputable section

namespace Mut

def alpha_lt (t1 t2 : term) : Prop := t1 ≠ t2 → orda [] t1 t2 = LESS

theorem witness : ¬ ∀ t1 t2, (Mut.alpha_lt t1 t2 ↔ Candle.alpha_lt t1 t2) := by
  intro h
  have h1 := (h (Var (mls "x") BoolTy) (Var (mls "x") BoolTy)).1 (fun hne => absurd rfl hne)
  simp [Candle.alpha_lt, orda] at h1

end Mut

#print axioms Mut.witness
