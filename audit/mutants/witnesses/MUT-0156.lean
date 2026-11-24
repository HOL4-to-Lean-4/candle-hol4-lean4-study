import CandleLean
open Candle HOL Classical

namespace Mut
def welltyped (tm : term) : Prop := ∀ ty, has_type tm ty
end Mut

/-- `Var x bool` is well typed in the base, but is not of type `Tyvar a` (as the mutant demands for every type). -/
theorem witness : ∃ tm : term, ¬ (Mut.welltyped tm ↔ welltyped tm) := by
  refine ⟨Var (mls "x") BoolTy, ?_⟩
  intro h
  have hb : welltyped (Var (mls "x") BoolTy) := ⟨BoolTy, has_type.Var⟩
  have hm := h.2 hb (Tyvar (mls "a"))
  cases hm

#print axioms witness
