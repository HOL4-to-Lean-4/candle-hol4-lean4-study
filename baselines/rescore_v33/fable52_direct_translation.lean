import CandleLean
open Candle
-- tier 1 attempts: expected to FAIL (no proof by rfl or simp)
#check_failure (rfl : HD ([] : List Nat) = ARB)
#check_failure (rfl : HD ([] : List Nat) = LAST [])
-- tier 2
example : (HD : List Nat → Nat) = Classical.epsilon (fun f => ∀ h t, f (h :: t) = h) := rfl
example : (ARB : Nat) = Classical.epsilon (fun _ => True) := rfl
example : CHR = Classical.epsilon (fun f => ∀ a, f (ORD a) = a) := rfl
