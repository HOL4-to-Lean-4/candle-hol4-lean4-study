import CandleLean
open HOL Candle Classical
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
noncomputable section

namespace Mut
def dbVSUBST (ilist : List (dbterm_t × dbterm_t)) : dbterm_t → dbterm_t
  | dbVar x ty => REV_ASSOCD (dbVar x ty) ilist (dbVar x ty)
  | dbBound m => dbBound m
  | dbConst x ty => dbConst x ty
  | dbComb t1 t2 => dbComb (dbVSUBST ilist t2) (dbVSUBST ilist t1)
  | dbAbs ty t => dbAbs ty (dbVSUBST ilist t)
end Mut

/-- The mutant swaps the two components of an application. -/
theorem witness : ∃ (ilist : List (dbterm_t × dbterm_t)) (t : dbterm_t),
    Mut.dbVSUBST ilist t ≠ Candle.dbVSUBST ilist t := by
  refine ⟨[], dbComb (dbBound 0) (dbBound 1), ?_⟩
  simp [Mut.dbVSUBST, Candle.dbVSUBST]

#print axioms witness
