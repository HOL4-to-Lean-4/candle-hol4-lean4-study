import CandleLean
open Candle HOL Classical

noncomputable section
namespace Mut
def sort2_tail {α : Type u} (neg : Prop) (R : α → α → Prop) (x y : α) : List α :=
  if R x y ≠ neg then [y, x] else [x, y]
end Mut
end

/-- neg = False, R = True, x = 0, y = 1: base [0,1], mutant [1,0] -/
theorem witness : ∃ (neg : Prop) (R : Nat → Nat → Prop) (x y : Nat),
    Mut.sort2_tail neg R x y ≠ sort2_tail neg R x y := by
  refine ⟨False, fun _ _ => True, 0, 1, ?_⟩
  simp [Mut.sort2_tail, sort2_tail]

#print axioms witness
