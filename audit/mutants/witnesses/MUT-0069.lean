import CandleLean

open Candle HOL Classical

namespace Mut
noncomputable section

def CLOSED (tm : term) : Prop := ∀ x ty,  VFREE_IN (Var x ty) tm

end
end Mut

theorem witness : ∃ tm : Candle.term, Mut.CLOSED tm ≠ Candle.CLOSED tm := by
  refine ⟨Candle.Const (Candle.mls "c") (Candle.Tyvar (Candle.mls "a")), ?_⟩
  intro h
  have h1 : Candle.CLOSED (Candle.Const (Candle.mls "c") (Candle.Tyvar (Candle.mls "a"))) := by
    intro x ty hv
    simp [Candle.VFREE_IN] at hv
  have h2 : Mut.CLOSED (Candle.Const (Candle.mls "c") (Candle.Tyvar (Candle.mls "a"))) := h ▸ h1
  have := h2 (Candle.mls "x") (Candle.Tyvar (Candle.mls "a"))
  simp [Candle.VFREE_IN] at this

#print axioms witness
