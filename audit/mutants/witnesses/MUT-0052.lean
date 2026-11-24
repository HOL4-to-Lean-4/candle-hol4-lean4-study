import CandleLean
open HOL Candle Classical
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
noncomputable section

namespace Mut
def transitive {α : Type u} (R : α → α → Prop) : Prop := ∀ x y z, R y z → R x z
end Mut

/-- equality on `Nat` is transitive, but `R y z → R x z` fails for `x ≠ y = z`. -/
theorem witness : ¬ ∀ R : Nat → Nat → Prop, (Mut.transitive R ↔ HOL.transitive R) := by
  intro h
  have h1 : HOL.transitive (fun a b : Nat => a = b) := by
    intro x y z ⟨h1, h2⟩
    exact h1.trans h2
  have h2 := (h (fun a b : Nat => a = b)).mpr h1
  have := h2 0 1 1 rfl
  exact absurd this (by decide)

#print axioms witness
