import CandleLean

open HOL Classical

universe u

namespace Mut
noncomputable section

def antisymmetric {α : Type u} (R : α → α → Prop) : Prop := ∀ x y, R x y ∨ R y x → x = y

end
end Mut

-- R = (≤) on Nat is antisymmetric in the base sense, but not in the mutated sense (0 ≤ 1, 0 ≠ 1).
theorem witness : ∃ R : Nat → Nat → Prop, HOL.antisymmetric R ∧ ¬ Mut.antisymmetric R := by
  refine ⟨fun x y => x ≤ y, ?_, ?_⟩
  · intro x y ⟨h1, h2⟩
    exact Nat.le_antisymm h1 h2
  · intro h
    have := h 0 1 (Or.inl (Nat.zero_le 1))
    exact absurd this (by decide)

#print axioms witness
