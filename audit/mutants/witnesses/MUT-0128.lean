import CandleLean
open HOL Classical
noncomputable section
namespace Mut
def PERM {α : Type u} (L1 L2 : List α) : Prop :=
  ∀ x, L1 ≠ [] → FILTER (fun y => x = y) L1 = FILTER (fun y => x = y) L2
end Mut

theorem witness : ∃ L1 L2 : List Nat, Mut.PERM L1 L2 ∧ ¬ HOL.PERM L1 L2 := by
  refine ⟨[], [1], fun x h => absurd rfl h, ?_⟩
  intro h
  have := h 1
  simp [FILTER] at this

#print axioms witness
