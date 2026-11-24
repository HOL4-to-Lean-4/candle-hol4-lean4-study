import CandleLean

universe u v

open HOL Candle Classical

noncomputable section

namespace Mut

variable {U : Type u}

def is_union (mem : U → U → Prop) (union : U → U) : Prop :=
  ∀ x, ∀ a, mem a (union x) ↔ ∃ b, mem a b

theorem witness : ¬ ∀ (mem : Bool → Bool → Prop) (union : Bool → Bool),
    (Mut.is_union mem union ↔ Candle.is_union mem union) := by
  intro h
  have := h (fun _ b => b = true) (fun _ => true)
  have hm : Mut.is_union (fun (_ b : Bool) => b = true) (fun _ => true) := by
    intro x a
    exact ⟨fun _ => ⟨true, rfl⟩, fun _ => rfl⟩
  have hb := this.1 hm false true
  obtain ⟨b, _, hb2⟩ := hb.1 rfl
  simp at hb2

end Mut

#print axioms Mut.witness
