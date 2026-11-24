import CandleLean
open Candle HOL Classical

namespace Mut
def dbVFREE_IN (v : dbterm_t) : dbterm_t → Prop
  | dbVar x ty => dbVar x ty = v
  | dbBound _ => False
  | dbConst x ty => dbConst x ty = v
  | dbComb t1 t2 => dbVFREE_IN v t1 ∨ dbVFREE_IN t2 t2
  | dbAbs _ t => dbVFREE_IN v t
end Mut

/-- v = dbVar x bool, tm = dbComb (dbBound 0) (dbVar x a): v does not occur in tm (types differ), but the mutant
    tests `dbVar x a` against itself. -/
theorem witness : ∃ (v tm : dbterm_t), Mut.dbVFREE_IN v tm ∧ ¬ dbVFREE_IN v tm := by
  refine ⟨dbVar (mls "x") BoolTy, dbComb (dbBound 0) (dbVar (mls "x") (Tyvar (mls "a"))), ?_, ?_⟩
  · simp [Mut.dbVFREE_IN]
  · simp [dbVFREE_IN, BoolTy]

#print axioms witness
