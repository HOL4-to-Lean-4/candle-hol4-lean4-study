import CandleLean

universe u v

open HOL Candle Classical

noncomputable section

namespace Mut

def bind_list_aux : Nat → List (mlstring × type) → dbterm_t → dbterm_t
  | _, [], tm => tm
  | n, v :: vs, tm => bind_list_aux (n + 0) vs (bind v n tm)

theorem witness : ∃ n vs tm, Mut.bind_list_aux n vs tm ≠ Candle.bind_list_aux n vs tm := by
  refine ⟨0, [(mls "a", BoolTy), (mls "b", BoolTy)],
    dbComb (dbVar (mls "a") BoolTy) (dbVar (mls "b") BoolTy), ?_⟩
  have hab : mls "a" ≠ mls "b" := by decide
  simp [Mut.bind_list_aux, Candle.bind_list_aux, Candle.bind, hab]

end Mut

#print axioms Mut.witness
