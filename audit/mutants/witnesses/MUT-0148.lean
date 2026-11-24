import CandleLean
open HOL Candle Classical
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
noncomputable section

namespace Mut
def db : term → dbterm_t
  | Var x ty => dbVar x ty
  | Const x ty => dbConst x ty
  | Comb t1 t2 => dbComb (db t1) (db t2)
  | Abs v tm => dbAbs (typeof v) (bind (dest_var v) 1 (db tm))
end Mut

/-- `λx. x` is `dbAbs ty (dbBound 0)` in the base and `dbAbs ty (dbBound 1)` in the mutant. -/
theorem witness : ∃ t : term, Mut.db t ≠ Candle.db t := by
  refine ⟨Abs (Var (mls "x") (Tyvar (mls "a"))) (Var (mls "x") (Tyvar (mls "a"))), ?_⟩
  intro h
  simp [Mut.db, Candle.db, Candle.bind, dest_var_def, typeof] at h

#print axioms witness
