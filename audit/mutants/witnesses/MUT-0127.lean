import CandleLean
open HOL Candle Classical
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
universe u
noncomputable section

namespace Mut
def BIJ {α : Type u} {β : Type v} (f : α → β) (s : Set α) (t : Set β) : Prop :=
  INJ f s t
end Mut

theorem witness : ∃ (f : Nat → Nat) (s t : Set Nat), Mut.BIJ f s t ∧ ¬ HOL.BIJ f s t := by
  refine ⟨Nat.succ, fun _ => True, fun _ => True, ⟨fun x _ => trivial, fun x y h e => Nat.succ.inj e⟩, ?_⟩
  intro h
  obtain ⟨y, _, hy⟩ := h.2.2 0 trivial
  exact Nat.succ_ne_zero y hy

#print axioms witness
