import CandleLean
open HOL Candle
-- tier 1: equation between mapped constants (ARB included), no choice term
example : HD ([] : List Nat) = ARB := rfl
example : LAST ([] : List Nat) = ARB := rfl
example : HD ([] : List Nat) = LAST [] := rfl
example (a : mlstring) (t : type) : dest_var (Const a t) = ARB := rfl
example (s t : Nat) : RESULT (Clash s) = RESULT (Clash t) := rfl
example (s t : Nat) : CLASH (Result s) = RESULT (Clash t) := rfl
example : CHR 256 = (ARB : Nat → char) 256 := rfl
-- tier 2: equation with a choice term
example : (ARB : Nat) = Classical.epsilon (fun _ => False) := rfl
example : (SEG : Nat → Nat → List Nat → List Nat) = Classical.epsilon SEG_spec := rfl
