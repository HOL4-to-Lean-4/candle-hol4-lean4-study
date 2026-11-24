import CandleLean

open HOL Classical

universe u

namespace Mut
noncomputable section

def TotOrd {α : Type u} (c : comp α) : Prop :=
  (∀ x y, c x y = EQUAL ↔ x = y) ∧
  (∀ x y, c x y = GREATER ↔ c y x = LESS) ∧
  (∀ x y z, c x y = LESS → c x z = LESS)

end
end Mut

-- The usual comparison on Nat is a TotOrd in the base sense, but the mutant demands
-- c 0 1 = LESS -> c 0 0 = LESS, which fails.
theorem witness : ∃ c : comp Nat, HOL.TotOrd c ∧ ¬ Mut.TotOrd c := by
  let c : comp Nat := fun x y => if x = y then EQUAL else if x < y then LESS else GREATER
  refine ⟨c, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro x y
    simp only [c]
    split <;> rename_i h
    · simp [h]
    · split <;> simp [h]
  · intro x y
    simp only [c]
    by_cases h : x = y
    · simp [h]
    · have h' : ¬ y = x := fun e => h e.symm
      simp only [h, h', if_false]
      by_cases hl : x < y <;> by_cases hl' : y < x <;> simp [hl, hl'] <;> omega
  · rintro x y z ⟨h1, h2⟩
    simp only [c] at *
    by_cases hxy : x = y <;> simp [hxy] at h1
    by_cases hyz : y = z <;> simp [hyz] at h2
    by_cases hxz : x = z
    · subst hxz; omega
    · simp [hxz]; omega
  · rintro ⟨_, _, h3⟩
    have := h3 0 1 0 (by simp [c])
    simp [c] at this

#print axioms witness
