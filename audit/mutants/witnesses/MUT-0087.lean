import CandleLean

open HOL Classical

universe u

namespace Mut
noncomputable section

def irreflexive {α : Type u} (R : α → α → Prop) : Prop := ∃ x, ¬ R x x

end
end Mut

theorem witness : ∃ R : Nat → Nat → Prop, Mut.irreflexive R ∧ ¬ HOL.irreflexive R := by
  refine ⟨fun x y => x = 0 ∧ y = 0, ?_, ?_⟩
  · exact ⟨1, by simp⟩
  · intro h
    exact h 0 ⟨rfl, rfl⟩

#print axioms witness
