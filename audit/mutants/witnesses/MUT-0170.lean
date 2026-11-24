import CandleLean
open Candle HOL Classical
noncomputable section
namespace Mut
def db : term → dbterm_t
  | Var x ty => dbConst x ty
  | Const x ty => dbVar x ty
  | Comb t1 t2 => dbComb (db t1) (db t2)
  | Abs v tm => dbAbs (typeof v) (bind (dest_var v) 0 (db tm))
end Mut

theorem witness : ∃ t, Mut.db t ≠ Candle.db t := by
  refine ⟨Var (mls "x") (Tyvar (mls "a")), ?_⟩
  simp [Mut.db, Candle.db]

#print axioms witness
