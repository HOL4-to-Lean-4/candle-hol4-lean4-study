import CandleLean
open HOL Candle Classical
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
noncomputable section

namespace Mut
abbrev word8 := BitVec 7
end Mut

/-- The mutant `word8` is a 7-bit type: `128 = 0` there, while `128 ≠ 0` in the base `word8` (and its word-to-number
conversion `toNat 255 = 255` fails in the mutant). -/
theorem witness : ((128 : Mut.word8) = 0) ∧ ¬ ((128 : HOL.word8) = 0) ∧
    ((255 : Mut.word8).toNat ≠ 255) ∧ ((255 : HOL.word8).toNat = 255) := by
  refine ⟨by decide, by decide, by decide, by decide⟩

#print axioms witness
