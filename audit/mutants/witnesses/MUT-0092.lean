import CandleLean
open HOL Classical
noncomputable section
namespace Mut
def EXISTS_UNIQUE {α : Sort u} (P : α → Prop) : Prop :=
  (∃ x, P x) ∧ ∀ x y, P x ∨ P y → x = y
end Mut

theorem witness : ∃ P : Bool → Prop, HOL.EXISTS_UNIQUE P ∧ ¬ Mut.EXISTS_UNIQUE P := by
  refine ⟨fun b => b = true, ⟨⟨true, rfl⟩, fun x y h => by simp_all⟩, ?_⟩
  intro h
  have := h.2 true false (Or.inl rfl)
  simp at this

#print axioms witness
