import CandleLean
open Candle HOL Classical

noncomputable section
namespace Mut
def consts_of_upd : update → List (mlstring × type)
  | ConstSpec eqs _ => eqs.map (fun st => (st.1, typeof st.2))
  | TypeDefn name pred abs rep =>
    let rep_type := domain (typeof pred)
    let abs_type := Tyapp name (((STRING_SORT ((tvars pred).map explode)).map implode).map Tyvar)
    [(abs, Fun rep_type abs_type), (rep, Fun rep_type abs_type)]
  | NewType _ _ => []
  | NewConst name type => [(name, type)]
  | NewAxiom _ => []
end Mut
end

/-- `TypeDefn n p a r` with `p = Var p (bool -> bool)`: rep_type = bool, abs_type = Tyapp n _ with n ≠ "bool";
    the second constant has type `abs -> rep` in the base and `rep -> abs` in the mutant. -/
theorem witness : ∃ u : update, Mut.consts_of_upd u ≠ consts_of_upd u := by
  refine ⟨TypeDefn (mls "n") (Var (mls "p") (Fun BoolTy BoolTy)) (mls "a") (mls "r"), ?_⟩
  intro h
  simp only [Mut.consts_of_upd, consts_of_upd, typeof, domain, Fun, BoolTy, List.cons.injEq, Prod.mk.injEq,
    and_true, true_and, and_true] at h
  have hs : str "bool" ≠ str "n" := by decide
  simp only [type.Tyapp.injEq, List.cons.injEq, mlstring.implode.injEq, mls, true_and] at h
  exact hs h.1.1

#print axioms witness
