import CandleLean
open Candle HOL Classical

noncomputable section
namespace Mut
def VSUBST (ilist : List (term × term)) : term → term
  | Var x ty => REV_ASSOCD (Var x ty) ilist (Var x ty)
  | Const x ty => Const x ty
  | Comb s t => Comb (VSUBST ilist s) (VSUBST ilist t)
  | Abs v t =>
    let ilist' := FILTER (fun p => ¬ (p.2 = v)) ilist
    let t' := VSUBST ilist' t
    if EVERY (fun p => VFREE_IN v p.1 ∧ VFREE_IN p.2 t) ilist'
    then
      let xty := dest_var v
      let z := Var (VARIANT t' (explode xty.1) xty.2) xty.2
      let ilist'' := (z, v) :: ilist'
      Abs z (VSUBST ilist'' t)
    else Abs v t'
end Mut
end

/-- ilist = [], `Abs v v` with v = Var x bool: EVERY over the empty list is true, so the mutant renames the bound variable
    (to a fresh z ≠ v, giving `Abs z z`), while the base keeps `Abs v v`. -/
theorem witness : ∃ (ilist : List (term × term)) (tm : term), Mut.VSUBST ilist tm ≠ VSUBST ilist tm := by
  refine ⟨[], Abs (Var (mls "x") BoolTy) (Var (mls "x") BoolTy), ?_⟩
  intro h
  have hv := (VARIANT_PRIMES_def (Var (mls "x") BoolTy) (explode (mls "x")) BoolTy).1
  simp only [VARIANT_PRIMES_P, VFREE_IN] at hv
  simp [Mut.VSUBST, VSUBST, FILTER, EVERY, EXISTS, dest_var_def, REV_ASSOCD, VARIANT] at h
  exact hv (by rw [h])

#print axioms witness
