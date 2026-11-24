import CandleLean

universe u v

open HOL Candle Classical

noncomputable section

namespace Mut

def UPDATE {α : Type u} {β : Sort v} (a : α) (b : β) (f : α → β) (c : α) : β :=
  if a ≠ c then b else f c

theorem witness : ∃ (a : Nat) (b : Nat) (f : Nat → Nat) (c : Nat),
    Mut.UPDATE a b f c ≠ HOL.UPDATE a b f c :=
  ⟨0, 1, fun _ => 0, 0, by simp [Mut.UPDATE, HOL.UPDATE]⟩

end Mut

#print axioms Mut.witness
