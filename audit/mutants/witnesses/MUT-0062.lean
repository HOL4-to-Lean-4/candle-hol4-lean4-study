import CandleLean
open Candle HOL Classical
noncomputable section
namespace Mut
def is_union {U : Type u} (mem : U → U → Prop) (union : U → U) : Prop :=
  ∀ x, ∀ a, mem a (union x) ↔ ∃ b, mem b x
end Mut

-- U = Bool, mem a _ := (a = true), union = id: base holds (∃ b, a=true ∧ b=true  iff a=true), mutant fails at a = false.
theorem witness : ¬ ∀ (mem : Bool → Bool → Prop) (union : Bool → Bool),
    (Mut.is_union mem union ↔ Candle.is_union mem union) := by
  intro h
  have h1 : Candle.is_union (fun (a _ : Bool) => a = true) (fun x => x) :=
    fun x a => by simp
  have := ((h (fun (a _ : Bool) => a = true) (fun x => x)).2 h1) true false
  simp at this

#print axioms witness
