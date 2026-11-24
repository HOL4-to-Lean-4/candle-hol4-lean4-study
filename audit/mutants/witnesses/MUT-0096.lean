import CandleLean
open Candle HOL Classical

noncomputable section
namespace Mut
def ordav : List (term × term) → term → term → ordering
  | [], x1, x2 => term_cmp x1 x2
  | (t1, t2) :: env, x1, x2 =>
    if x1 = t1 then (if x2 = t2 then EQUAL else LESS)
    else if x2 = t2 then GREATER
    else ordav env x1 x1
end Mut
end

/-- env = [(c, c)] with two distinct variables x1 x2 not equal to c: the mutant compares x1 with itself (EQUAL),
    the base compares x1 with x2 (not EQUAL since x1 ≠ x2). -/
theorem witness : ∃ (env : List (term × term)) (x1 x2 : term),
    Mut.ordav env x1 x2 ≠ ordav env x1 x2 := by
  let c : term := Const (mls "c") BoolTy
  let a : term := Var (mls "a") BoolTy
  let b : term := Var (mls "a") (Tyvar (mls "x"))
  refine ⟨[(c, c)], a, b, ?_⟩
  have hac : a ≠ c := by simp [a, c]
  have hbc : b ≠ c := by simp [b, c]
  have hab : a ≠ b := by simp [a, b, BoolTy]
  intro h
  simp only [Mut.ordav, ordav, if_neg hac, if_neg hbc] at h
  simp [term_cmp, TO_of_LinearOrder, hab] at h
  split at h <;> simp at h

#print axioms witness
