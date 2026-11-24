import CandleLean
open HOL Classical
noncomputable section
namespace Mut
def symmetric {α : Type u} (R : α → α → Prop) : Prop := ∃ x y, R x y = R y x
end Mut

theorem witness : ∃ R : Bool → Bool → Prop, Mut.symmetric R ∧ ¬ HOL.symmetric R := by
  refine ⟨fun x y => x = true ∧ y = false, ⟨true, true, rfl⟩, ?_⟩
  intro h
  have := h true false
  simp at this

#print axioms witness
