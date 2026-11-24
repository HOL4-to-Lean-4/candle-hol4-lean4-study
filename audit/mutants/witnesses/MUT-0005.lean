import CandleLean

universe u v

open HOL Candle Classical

noncomputable section

namespace Mut

theorem witness : ¬ (∀ (tm : dbterm_t) (ls ls' : List (dbterm_t × dbterm_t)),
      (∃ (k : dbterm_t), dbVFREE_IN k tm → REV_ASSOCD k ls k = REV_ASSOCD k ls' k)
       →
        dbVSUBST ls tm = dbVSUBST ls' tm) := by
  intro h
  have hab : mls "a" ≠ mls "b" := by decide
  have := h (dbVar (mls "a") BoolTy) [] [(dbVar (mls "b") BoolTy, dbVar (mls "a") BoolTy)]
    ⟨dbBound 0, fun hk => by simp [dbVFREE_IN] at hk⟩
  simp [dbVSUBST, REV_ASSOCD, hab] at this

end Mut

#print axioms Mut.witness
