import CandleLean
open HOL Candle Classical
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
universe u
noncomputable section

namespace Mut
def n2l (b n : Nat) : List Nat :=
  if n < b ∨ b < 2 then [n % b] else n % b :: n2l (n / b) (n / b)
termination_by n
decreasing_by
  apply Nat.div_lt_self <;> omega
end Mut

theorem witness : ∃ b n : Nat, Mut.n2l b n ≠ HOL.n2l b n := by
  refine ⟨10, 123, ?_⟩
  have hb : HOL.n2l 10 123 = [3, 2, 1] := by
    rw [HOL.n2l, if_neg (by omega)]
    show 123 % 10 :: HOL.n2l 10 (123 / 10) = _
    rw [show 123 / 10 = 12 by omega, HOL.n2l, if_neg (by omega)]
    show 3 :: (12 % 10 :: HOL.n2l 10 (12 / 10)) = _
    rw [show 12 / 10 = 1 by omega, HOL.n2l, if_pos (by omega)]
  have hm : Mut.n2l 10 123 = [3, 0, 0] := by
    rw [Mut.n2l, if_neg (by omega)]
    show 123 % 10 :: Mut.n2l (123 / 10) (123 / 10) = _
    rw [show 123 / 10 = 12 by omega, Mut.n2l, if_neg (by omega)]
    show 3 :: (12 % 12 :: Mut.n2l (12 / 12) (12 / 12)) = _
    rw [show 12 / 12 = 1 by omega, Mut.n2l, if_pos (by omega)]
  rw [hb, hm]; intro h; cases h

#print axioms witness
