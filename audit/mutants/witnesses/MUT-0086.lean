import CandleLean
open Candle HOL Classical
noncomputable section
namespace Mut
def is_power {U : Type u} (mem : U → U → Prop) (power : U → U) : Prop :=
  ∀ x, ∀ a, x ≠ a → (mem a (power x) ↔ ∀ b, mem b a → mem b x)
end Mut

-- U = Bool, mem a b := (a = false ∧ b = true), power = id: holds for x ≠ a, fails at x = a = true... (checked by decide)
theorem witness : ¬ ∀ (mem : Bool → Bool → Prop) (power : Bool → Bool),
    (Mut.is_power mem power ↔ Candle.is_power mem power) := by
  intro h
  have hm : Mut.is_power (fun (a b : Bool) => a = false ∧ b = true) (fun x => x) := by
    unfold Mut.is_power; decide
  have hb := (h _ _).1 hm
  revert hb
  unfold Candle.is_power
  decide

#print axioms witness
