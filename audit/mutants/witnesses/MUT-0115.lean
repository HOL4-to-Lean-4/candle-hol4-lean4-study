import CandleLean
open HOL Candle Classical
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
universe u
noncomputable section

namespace Mut
def Order {α : Type u} (Z : α → α → Prop) : Prop := transitive Z
end Mut

theorem witness : ∃ Z : Nat → Nat → Prop, Mut.Order Z ∧ ¬ HOL.Order Z := by
  refine ⟨fun _ _ => True, fun x y z _ => trivial, ?_⟩
  intro h
  have := h.1 0 1 ⟨trivial, trivial⟩
  cases this

#print axioms witness
