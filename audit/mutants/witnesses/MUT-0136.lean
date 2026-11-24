import CandleLean
open HOL Candle Classical
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
noncomputable section

namespace Mut
def dbterm (env : List (mlstring × type)) : term → dbterm_t
  | Var s ty =>
    dbConst s ty
  | Const s ty => match find_index (s, ty) env 0 with
    | some n => dbBound n
    | none => dbVar s ty
  | Comb t1 t2 => dbComb (dbterm env t1) (dbterm env t2)
  | Abs v t => dbAbs (typeof v) (dbterm (dest_var v :: env) t)
end Mut

/-- a variable becomes `dbConst` in the mutant and `dbVar` in the base -/
theorem witness : ∃ (env : List (mlstring × type)) (t : term), Mut.dbterm env t ≠ Candle.dbterm env t := by
  refine ⟨[], Var (mls "x") (Tyvar (mls "a")), ?_⟩
  intro h
  simp [Mut.dbterm, Candle.dbterm, find_index] at h

#print axioms witness
