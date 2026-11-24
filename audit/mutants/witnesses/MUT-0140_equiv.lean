import CandleLean
open Candle
noncomputable section
namespace Mut
def max3 (x y z : Nat) : Nat :=
  if x ≥ y then (if z > x then z else x) else (if z > y then z else y)
end Mut

/-- The mutant is equivalent: for x = y both branches compute max z x. -/
theorem equiv : ∀ x y z, Mut.max3 x y z = Candle.max3 x y z := by
  intro x y z
  unfold Mut.max3 Candle.max3
  by_cases h1 : x ≥ y <;> by_cases h2 : x > y <;> by_cases h3 : z > x <;> by_cases h4 : z > y <;>
    simp only [h1, h2, h3, h4, if_true, if_false] <;> omega

#print axioms equiv
