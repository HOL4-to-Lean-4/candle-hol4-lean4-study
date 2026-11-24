import CandleLean
open HOL Candle Classical
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
noncomputable section

namespace Mut
def conexts_of_upd : update → List term
  | ConstSpec eqs prop =>
    let ilist := eqs.map (fun st => let ty := typeof st.2; (Const st.1 ty, Var st.1 ty))
    [VSUBST [] prop]
  | TypeDefn name pred abs_name rep_name =>
    let abs_type := Tyapp name (((STRING_SORT ((tvars pred).map explode)).map implode).map Tyvar)
    let rep_type := domain (typeof pred)
    let abs := Const abs_name (Fun rep_type abs_type)
    let rep := Const rep_name (Fun abs_type rep_type)
    let a := Var (mls "a") abs_type
    let r := Var (mls "r") rep_type
    [equation (Comb abs (Comb rep a)) a,
     equation (Comb pred r) (equation (Comb rep (Comb abs r)) r)]
  | _ => []
end Mut

/-- `ConstSpec [(c, y)] c`: the base substitutes `c` by the constant, the mutant substitutes nothing -/
theorem witness : ∃ u : update, Mut.conexts_of_upd u ≠ Candle.conexts_of_upd u := by
  refine ⟨ConstSpec [(mls "c", Var (mls "y") (Tyvar (mls "a")))] (Var (mls "c") (Tyvar (mls "a"))), ?_⟩
  intro h
  simp [Mut.conexts_of_upd, Candle.conexts_of_upd, typeof, VSUBST, REV_ASSOCD] at h

#print axioms witness
