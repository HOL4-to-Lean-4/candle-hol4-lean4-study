import CandleLean

universe u v

open HOL Candle Classical

noncomputable section

namespace Mut

def simple_subst (ilist : List (term × term)) : term → term
  | Var x ty => REV_ASSOCD (Var x ty) ilist (Var x ty)
  | Const x ty => Const x ty
  | Comb t1 t2 => Comb (simple_subst ilist t2) (simple_subst ilist t1)
  | Abs v tm => Abs v (simple_subst (FILTER (fun p => p.2 ≠ v) ilist) tm)

theorem witness : ∃ il t, Mut.simple_subst il t ≠ Candle.simple_subst il t := by
  refine ⟨[], Comb (Var (mls "a") BoolTy) (Var (mls "b") BoolTy), ?_⟩
  have hab : mls "a" ≠ mls "b" := by decide
  simp [Mut.simple_subst, Candle.simple_subst, REV_ASSOCD, hab, hab.symm]

end Mut

#print axioms Mut.witness
