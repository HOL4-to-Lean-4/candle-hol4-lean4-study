import CandleLean
open Candle HOL Classical

noncomputable section
namespace Mut
def TO_of_LinearOrder {α : Type u} (r : α → α → Prop) (x y : α) : ordering :=
  if x = y then EQUAL else if r x y then GREATER else GREATER
end Mut
end

/-- r = always true on Nat, x = 0, y = 1: base gives LESS, mutant GREATER -/
theorem witness : ∃ (r : Nat → Nat → Prop) (x y : Nat),
    Mut.TO_of_LinearOrder r x y ≠ TO_of_LinearOrder r x y := by
  refine ⟨fun _ _ => True, 0, 1, ?_⟩
  intro h
  simp [Mut.TO_of_LinearOrder, TO_of_LinearOrder] at h

#print axioms witness
