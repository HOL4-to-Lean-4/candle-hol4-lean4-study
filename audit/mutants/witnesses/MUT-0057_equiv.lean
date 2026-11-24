import CandleLean

open HOL Classical

universe u

namespace Mut
noncomputable section

def TotOrd {α : Type u} (c : comp α) : Prop :=
  (∀ x y, c x y = EQUAL → x = y) ∧
  (∀ x y, c x y = GREATER ↔ c y x = LESS) ∧
  (∀ x y z, c x y = LESS ∧ c y z = LESS → c x z = LESS)

end
end Mut

-- The mutant is equivalent to the base: the second clause at x = y forces c x x = EQUAL
-- (an `ordering` has only three values), which is the missing converse of the first clause.
theorem equiv {α : Type u} (c : comp α) : Mut.TotOrd c ↔ HOL.TotOrd c := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨fun x y => ⟨h1 x y, ?_⟩, h2, h3⟩
    rintro rfl
    have := h2 x x
    revert this
    cases hc : c x x <;> simp
  · rintro ⟨h1, h2, h3⟩
    exact ⟨fun x y h => (h1 x y).1 h, h2, h3⟩

#print axioms equiv
