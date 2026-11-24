import CandleLean

universe u v

open HOL Candle Classical

noncomputable section

namespace Mut

variable {U : Type u}

def is_power (mem : U → U → Prop) (power : U → U) : Prop :=
  ∀ x, ∀ a, mem a (power x) ↔ ∀ b, mem b x

theorem witness : ¬ ∀ (mem : Unit → Unit → Prop) (power : Unit → Unit),
    (Mut.is_power mem power ↔ Candle.is_power mem power) := by
  intro h
  have := h (fun _ _ => False) id
  have hm : Mut.is_power (fun (_ _ : Unit) => False) id := by
    intro x a
    exact ⟨fun h => h.elim, fun h => h ()⟩
  have hb := this.1 hm
  exact hb () () |>.2 (fun _ h => h.elim)

end Mut

#print axioms Mut.witness
