import CandleLean
open Candle HOL Classical
noncomputable section
namespace Mut
def compare_aux (s1 s2 : mlstring) (ord : ordering) (start len : Nat) : ordering :=
  if len = 0 then ord
  else if char_lt (strsub s2 start) (strsub s1 start) then GREATER
  else if char_le (strsub s1 start) (strsub s2 start) then LESS
  else compare_aux s1 s2 ord (start + 1) (len - 1)
termination_by len
decreasing_by omega
end Mut

-- equal one-character strings: base falls through to `ord` (EQUAL), mutant answers LESS.
theorem witness : ∃ s1 s2 ord start len,
    Mut.compare_aux s1 s2 ord start len ≠ Candle.compare_aux s1 s2 ord start len := by
  refine ⟨mls "a", mls "a", ordering.EQUAL, 0, 1, ?_⟩
  rw [Mut.compare_aux, Candle.compare_aux]
  simp [char_lt, char_le]
  rw [Candle.compare_aux]
  simp

#print axioms witness
