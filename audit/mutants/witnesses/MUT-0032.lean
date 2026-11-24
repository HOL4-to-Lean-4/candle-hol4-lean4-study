import CandleLean
open Candle HOL Classical
noncomputable section
namespace Mut
def dbINST (tyin : List (type × type)) : dbterm_t → dbterm_t
  | dbVar x ty => dbVar x (TYPE_SUBST tyin ty)
  | dbBound n => dbBound n
  | dbConst x ty => dbConst x (TYPE_SUBST tyin ty)
  | dbComb t1 t2 => dbComb (dbINST tyin t2) (dbINST tyin t1)
  | dbAbs ty t => dbAbs (TYPE_SUBST tyin ty) (dbINST tyin t)
end Mut

-- bound variables are untouched by any substitution, so the swap of the two subterms is visible.
theorem witness : ∃ tyin t, Mut.dbINST tyin t ≠ Candle.dbINST tyin t := by
  refine ⟨[], dbComb (dbBound 0) (dbBound 1), ?_⟩
  simp [Mut.dbINST, Candle.dbINST]

#print axioms witness
