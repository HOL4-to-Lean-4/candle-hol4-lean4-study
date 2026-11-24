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
    if EXISTS (fun p => VFREE_IN v p.1 ∧ VFREE_IN t p.2) ilist'
    then
      let xty := dest_var v
      let z := Var (VARIANT t' (explode xty.1) xty.2) xty.2
      let ilist'' := (z, v) :: ilist'
      Abs z (VSUBST ilist'' t)
    else Abs v t'
end Mut

-- ilist = [(y, x)], term = λy. x x.  Base: y occurs in the substitute and x is free in the body, so the
-- bound variable is renamed (to a variant that is not y). Mutant tests `VFREE_IN t p.2` (the body as a variable) and does not rename.
theorem witness : ∃ ilist tm, Mut.VSUBST ilist tm ≠ Candle.VSUBST ilist tm := by
  have hxy : mls "x" ≠ mls "y" := by simp [mls, str]; decide
  let ty : type := Tyvar (mls "a")
  refine ⟨[(Var (mls "y") ty, Var (mls "x") ty)], Abs (Var (mls "y") ty) (Comb (Var (mls "x") ty) (Var (mls "x") ty)), ?_⟩
  intro h
  simp [Mut.VSUBST, Candle.VSUBST, REV_ASSOCD, FILTER, EXISTS, VFREE_IN, hxy, dest_var_def] at h
  have hs := (VARIANT_PRIMES_def ((Var (mls "y") ty).Comb (Var (mls "y") ty)) (explode (mls "y")) ty).1
  have hs' : ¬ VFREE_IN (Var (VARIANT ((Var (mls "y") ty).Comb (Var (mls "y") ty)) (explode (mls "y")) ty) ty)
      ((Var (mls "y") ty).Comb (Var (mls "y") ty)) := hs
  rw [← h.1] at hs'
  simp [VFREE_IN] at hs'

#print axioms witness
