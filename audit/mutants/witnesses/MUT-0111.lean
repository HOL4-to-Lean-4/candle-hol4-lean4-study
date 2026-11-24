import CandleLean

open Candle HOL Classical

namespace Mut
noncomputable section

def bind (v : mlstring × type) (n : Nat) : dbterm_t → dbterm_t
  | dbVar x ty => if v = (x, ty) then dbBound n else dbVar x ty
  | dbBound m => dbBound m
  | dbConst x ty => dbConst x ty
  | dbComb t1 t2 => dbComb (bind v n t1) (bind v n t2)
  | dbAbs ty tm => dbAbs ty (bind v (n + 0) tm)

end
end Mut

-- binding the variable `x` under one lambda: base gives de Bruijn index 1, mutant 0.
theorem witness : ∃ (v : mlstring × type) (n : Nat) (t : dbterm_t),
    Mut.bind v n t ≠ Candle.bind v n t := by
  let ty : type := Tyvar (mls "a")
  refine ⟨(mls "x", ty), 0, dbAbs ty (dbVar (mls "x") ty), ?_⟩
  simp [Mut.bind, Candle.bind]

#print axioms witness
