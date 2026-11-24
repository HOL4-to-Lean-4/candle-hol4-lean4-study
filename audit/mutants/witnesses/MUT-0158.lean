import CandleLean
open Candle HOL Classical
noncomputable section
namespace Mut
def dbterm (env : List (mlstring × type)) : term → dbterm_t
  | Var s ty =>
    match find_index (s, ty) env 1 with
    | some n => dbBound n
    | none => dbVar s ty
  | Const s ty => dbConst s ty
  | Comb t1 t2 => dbComb (dbterm env t1) (dbterm env t2)
  | Abs v t => dbAbs (typeof v) (dbterm (dest_var v :: env) t)
end Mut

-- the variable is the head of the environment: base gives dbBound 0, mutant dbBound 1.
theorem witness : ∃ env t, Mut.dbterm env t ≠ Candle.dbterm env t := by
  refine ⟨[(mls "x", Tyvar (mls "a"))], Var (mls "x") (Tyvar (mls "a")), ?_⟩
  simp [Mut.dbterm, Candle.dbterm, find_index]

#print axioms witness
