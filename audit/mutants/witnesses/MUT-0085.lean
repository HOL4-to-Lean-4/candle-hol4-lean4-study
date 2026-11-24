import CandleLean
open HOL Candle Classical
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
universe u
noncomputable section

namespace Mut
def INJ {α : Type u} {β : Type v} (f : α → β) (s : Set α) (t : Set β) : Prop :=
  (∀ x, x ∈ s → f x ∈ t) ∧ (∃ x y, (x ∈ s ∧ y ∈ s) → f x = f y → x = y)
end Mut

theorem witness : ∃ (f : Nat → Nat) (s t : Set Nat), Mut.INJ f s t ∧ ¬ HOL.INJ f s t := by
  have h0 : (0:Nat) ≤ 1 := by omega
  have h1 : (1:Nat) ≤ 1 := by omega
  have h2 : ¬ ((2:Nat) ≤ 1) := by omega
  refine ⟨fun _ => 0, fun x => x ≤ 1, fun _ => True, ?_, ?_⟩
  · exact ⟨fun x _ => trivial, 2, 0, fun h => (h2 h.1).elim⟩
  · intro h
    have := h.2 0 1 ⟨h0, h1⟩ rfl
    cases this

#print axioms witness
