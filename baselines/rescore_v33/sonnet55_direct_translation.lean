import CandleLean
open HOL Candle
-- tier 1
example : (ARB : Nat) = 0 := rfl
example : HD ([] : List Nat) = 0 := rfl
example : LAST ([] : List Nat) = 0 := rfl
example : SEG 1 0 ([] : List Nat) = [] := rfl
example : CHR 256 = CHR 0 := by first | rfl | (apply Fin.ext; rfl) | (unfold CHR; rfl) | simp [CHR]
example (t : Nat) : Candle.HolSyntaxLib.RESULT (.Clash t) = t := by first | rfl | simp [Candle.HolSyntaxLib.RESULT]
example (t : Nat) : Candle.HolSyntaxLib.CLASH (.Result t) = t := by first | rfl | simp [Candle.HolSyntaxLib.CLASH]
example (f : Nat → Nat) (P : Set Nat) (h : ¬ FINITE P) : FUN_FMAP f P = FEMPTY := by simp [FUN_FMAP, h]
-- tier 2
example (s : Set string) : Candle.HolSyntaxExtra.fresh s = Classical.epsilon (fun x => x ∉ s) := rfl
