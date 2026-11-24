import CandleLean
open HOL
namespace Mut
abbrev word8 := BitVec 9
end Mut

/-- Every base `word8` has `toNat < 256`; the mutated type contains a value with `toNat = 256`. -/
theorem witness : (∀ w : HOL.word8, w.toNat < 256) ∧ ∃ w : Mut.word8, ¬ w.toNat < 256 := by
  constructor
  · intro w; exact w.isLt
  · exact ⟨BitVec.ofNat 9 256, by simp [BitVec.toNat_ofNat]⟩

#print axioms witness
