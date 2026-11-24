import CandleLean
open HOL
namespace Mut
abbrev word32 := BitVec 31
end Mut

/-- In the base every `word32` value is below 2^32 but the mutated `word32` is a 31-bit type;
    concretely the number 2^31 is the `toNat` of a base word32 and of no mutated word32. -/
theorem witness : (∃ w : HOL.word32, w.toNat = 2 ^ 31) ∧ ¬ (∃ w : Mut.word32, w.toNat = 2 ^ 31) := by
  constructor
  · exact ⟨BitVec.ofNat 32 (2 ^ 31), by simp [BitVec.toNat_ofNat]⟩
  · rintro ⟨w, hw⟩
    have := w.isLt
    omega

#print axioms witness
