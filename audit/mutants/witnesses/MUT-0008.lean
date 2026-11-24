import CandleLean
open Candle HOL Classical
noncomputable section
namespace Mut
def conexts_of_upd : update → List term
  | ConstSpec eqs prop =>
    let ilist := eqs.map (fun st => let ty := typeof st.2; (Const st.1 ty, Var st.1 ty))
    [VSUBST ilist prop]
  | TypeDefn name pred abs_name rep_name =>
    let abs_type := Tyapp name (((STRING_SORT ((tvars pred).map explode)).map implode).map Tyvar)
    let rep_type := domain (typeof pred)
    let abs := Const abs_name (Fun rep_type abs_type)
    let rep := Const rep_name (Fun abs_type rep_type)
    let a := Var (mls "b") abs_type
    let r := Var (mls "r") rep_type
    [equation (Comb abs (Comb rep a)) a,
     equation (Comb pred r) (equation (Comb rep (Comb abs r)) r)]
  | _ => []
end Mut

theorem witness : ∃ u : update, Mut.conexts_of_upd u ≠ Candle.conexts_of_upd u := by
  refine ⟨TypeDefn (mls "n") (Var (mls "p") (Tyvar (mls "t"))) (mls "A") (mls "R"), ?_⟩
  intro h
  have := congrArg (fun l : List term => match l with
    | t :: _ => (match t with | term.Comb _ a => a | x => x)
    | _ => default) h
  simp [equation, mls, Mut.conexts_of_upd, Candle.conexts_of_upd] at this
  revert this
  simp [str]
  decide

#print axioms witness
