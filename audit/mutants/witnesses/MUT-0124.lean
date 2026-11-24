import CandleLean
open HOL Candle Classical
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
noncomputable section

namespace Mut
def is_subseq {α : Type u} : List α → List α → Prop
  | _, [] => True
  | [], _ :: _ => False
  | y :: ys, x :: xs => (x = y ∧ is_subseq ys xs) ∨ is_subseq ys (xs ++ [x])
end Mut

/-- `[1,2]` is not a subsequence of `[0,2,1]`, but the mutant rotates the second list after skipping `0`. -/
theorem witness : ∃ l1 l2 : List Nat, Mut.is_subseq l1 l2 ∧ ¬ Candle.is_subseq l1 l2 := by
  refine ⟨[0, 2, 1], [1, 2], ?_, ?_⟩
  · simp [Mut.is_subseq]
  · simp [Candle.is_subseq]

#print axioms witness
