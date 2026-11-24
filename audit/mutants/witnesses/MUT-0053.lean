import CandleLean

universe u v

open HOL Candle Classical

noncomputable section

namespace Mut

theorem witness : ¬ (∀ (tm : dbterm_t) (z x : mlstring × type) (n : Nat) (ls : List (dbterm_t × dbterm_t)),
      ¬ dbVFREE_IN (UNCURRY dbVar z) (dbVSUBST ls (bind x n tm))
      →
      bind z n (dbVSUBST (ls ++ [(UNCURRY dbVar z, UNCURRY dbVar x)]) tm) = dbVSUBST ls (bind x n tm)) := by
  intro h
  have hzw : mls "z" ≠ mls "w" := by decide
  have := h (dbVar (mls "x") BoolTy) (mls "z", BoolTy) (mls "x", BoolTy) 0
    [(dbVar (mls "w") BoolTy, dbVar (mls "x") BoolTy)]
    (by simp [UNCURRY, Candle.bind, dbVSUBST, dbVFREE_IN])
  simp [UNCURRY, Candle.bind, dbVSUBST, REV_ASSOCD, hzw] at this

end Mut

#print axioms Mut.witness
