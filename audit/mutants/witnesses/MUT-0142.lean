import CandleLean
open HOL Candle Classical
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
noncomputable section

namespace Mut
def INORDER_INSERT (x : string) (xs : List string) : List string :=
  FILTER (fun y => string_le y x) xs ++ ([x] ++ FILTER (fun y => string_lt x y) xs)
end Mut

/-- inserting the empty string into `[""]`: the base keeps one copy, the mutant duplicates it. -/
theorem witness : ∃ (x : string) (xs : List string), Mut.INORDER_INSERT x xs ≠ Candle.INORDER_INSERT x xs := by
  refine ⟨[], [[]], ?_⟩
  intro h
  simp [Mut.INORDER_INSERT, Candle.INORDER_INSERT, FILTER, string_lt, string_le] at h

#print axioms witness
