import CandleLean
open HOL Candle Classical
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
noncomputable section

namespace Mut
def StrongOrder {α : Type u} (Z : α → α → Prop) : Prop := irreflexive Z
end Mut

/-- the successor relation on `Nat` is irreflexive but not transitive. -/
theorem witness : ∃ Z : Nat → Nat → Prop, Mut.StrongOrder Z ∧ ¬ HOL.StrongOrder Z := by
  refine ⟨fun a b => b = a + 1, ?_, ?_⟩
  · intro x h
    simp at h
  · intro h
    have := h.2 0 1 2 ⟨rfl, rfl⟩
    simp at this

#print axioms witness
