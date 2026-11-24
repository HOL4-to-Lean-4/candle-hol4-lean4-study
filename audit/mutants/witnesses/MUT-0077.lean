import CandleLean

universe u v

open HOL Candle Classical

noncomputable section

namespace Mut

variable {U : Type u}

@[reducible] def inhabited (mem : U → U → Prop) (s : U) : Prop := ∀ x, mem x s

theorem witness : ¬ ∀ (mem : Bool → Bool → Prop) (s : Bool),
    (Mut.inhabited mem s ↔ Candle.inhabited mem s) := by
  intro h
  have := (h (fun x _ => x = true) true).2 ⟨true, rfl⟩ false
  simp at this

end Mut

#print axioms Mut.witness
