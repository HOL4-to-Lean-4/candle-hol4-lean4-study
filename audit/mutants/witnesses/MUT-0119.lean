import CandleLean

universe u v

open HOL Candle Classical

noncomputable section

namespace Mut

def bind (v : mlstring × type) (n : Nat) : dbterm_t → dbterm_t
  | dbVar x ty => if v = (x, ty) then dbVar x ty else dbBound n
  | dbBound m => dbBound m
  | dbConst x ty => dbConst x ty
  | dbComb t1 t2 => dbComb (bind v n t1) (bind v n t2)
  | dbAbs ty tm => dbAbs ty (bind v (n + 1) tm)

theorem witness : ∃ v n t, Mut.bind v n t ≠ Candle.bind v n t :=
  ⟨(mls "x", BoolTy), 0, dbVar (mls "x") BoolTy, by simp [Mut.bind, Candle.bind]⟩

end Mut

#print axioms Mut.witness
