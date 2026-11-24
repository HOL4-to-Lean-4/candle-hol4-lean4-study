import CandleLean

open Candle HOL Classical

universe u

namespace Mut
noncomputable section

variable {U : Type u}

def is_separation (mem : U → U → Prop) (sub : U → (U → Prop) → U) : Prop :=
  ∀ x P, ∃ a, mem a (sub x P) ↔ mem a x ∧ P a

end
end Mut

-- U = Bool, mem a _ := (a = false), sub x P := x.
-- Mutant: a = true makes both sides false.  Base: fails at P = False, a = false.
theorem witness : ∃ (mem : Bool → Bool → Prop) (sub : Bool → (Bool → Prop) → Bool),
    Mut.is_separation mem sub ∧ ¬ Candle.is_separation mem sub := by
  refine ⟨fun a _ => a = false, fun x _ => x, ?_, ?_⟩
  · intro x P
    exact ⟨true, by simp⟩
  · intro h
    have := h true (fun _ => False) false
    simp at this

#print axioms witness
