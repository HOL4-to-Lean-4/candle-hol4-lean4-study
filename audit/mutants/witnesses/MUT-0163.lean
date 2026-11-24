import CandleLean
open HOL Candle Classical
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
universe u
noncomputable section

namespace Mut
def simple_subst (ilist : List (term × term)) : term → term
  | Var x ty => REV_ASSOCD (Var x ty) ilist (Var x ty)
  | Const x ty => Const x ty
  | Comb t1 t2 => Comb (simple_subst ilist t1) (simple_subst ilist t2)
  | Abs v tm => Abs v (simple_subst (FILTER (fun p => p.2 = v) ilist) tm)
end Mut

theorem witness : ∃ (ilist : List (term × term)) (t : term), Mut.simple_subst ilist t ≠ Candle.simple_subst ilist t := by
  have hne : mls "x" ≠ mls "yy" := by
    intro h
    simp only [mls, str, mlstring.implode.injEq] at h
    have h' := congrArg List.length h
    simp only [List.length_map] at h'
    revert h'; decide
  let ty : type := Tyvar (mls "a")
  have hv : (Var (mls "x") ty) ≠ (Var (mls "yy") ty) := fun h => hne (by injection h)
  refine ⟨[(Const (mls "c") ty, Var (mls "x") ty)], Abs (Var (mls "yy") ty) (Var (mls "x") ty), ?_⟩
  intro h
  simp [Mut.simple_subst, Candle.simple_subst, FILTER, hv, REV_ASSOCD] at h

#print axioms witness
