import CandleLean
open Candle HOL Classical

/-- the mutated statement `∀ x : Int, x < 1 ↔ x = 0` (the base statement is over Nat) is false at x = -1 -/
theorem witness : ¬ (∀ x : Int, x < 1 ↔ x = 0) := by
  intro h
  have := (h (-1)).1 (by decide)
  omega

#print axioms witness
