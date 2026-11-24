import CandleLean
open HOL Candle Classical
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
universe u
noncomputable section

namespace Mut
def consts_of_upd : update → List (mlstring × type)
  | ConstSpec eqs _ => eqs.map (fun st => (st.1, typeof st.2))
  | TypeDefn name pred abs rep =>
    let rep_type := domain (typeof pred)
    let abs_type := Tyapp name (((STRING_SORT ((tvars pred).map explode)).map implode).map Tyvar)
    [(abs, Fun abs_type rep_type), (rep, Fun abs_type rep_type)]
  | NewType _ _ => []
  | NewConst name type => [(name, type)]
  | NewAxiom _ => []
end Mut

theorem witness : ∃ u : update, Mut.consts_of_upd u ≠ Candle.consts_of_upd u := by
  refine ⟨TypeDefn (mls "t") (Var (mls "p") (Fun BoolTy BoolTy)) (mls "abs") (mls "rep"), ?_⟩
  have hne : mls "t" ≠ mls "bool" := by
    intro h
    simp only [mls, str, mlstring.implode.injEq] at h
    have h' := congrArg List.length h
    simp only [List.length_map] at h'
    revert h'; decide
  intro h
  simp [Mut.consts_of_upd, Candle.consts_of_upd, typeof, domain, Fun, BoolTy] at h
  exact absurd h.1.1 hne

#print axioms witness
