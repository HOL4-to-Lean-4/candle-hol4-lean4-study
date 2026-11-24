import CandleLean

open Candle HOL Classical

namespace Mut
noncomputable section

def orda (env : List (term × term)) (t1 t2 : term) : ordering :=
  if t1 = t2 ∧ env = [] then EQUAL else
    match t1, t2 with
    | Var _ _, Var _ _ => ordav env t1 t2
    | Const _ _, Const _ _ => term_cmp t1 t2
    | Comb s1 t1', Comb s2 t2' =>
      let c := orda env s1 s2
      if c ≠ EQUAL then c else orda env t1' t2'
    | Abs s1 t1', Abs s2 t2' =>
      let c := type_cmp (typeof s1) (typeof s2)
      if c ≠ EQUAL then c else orda ((s1, s2) :: env) t1' t2'
    | Var _ _, _ => LESS
    | _, Var _ _ => LESS
    | Const _ _, _ => LESS
    | _, Const _ _ => GREATER
    | Comb _ _, _ => LESS
    | _, Comb _ _ => GREATER
termination_by sizeOf t1

end
end Mut

-- orda [] (Const c ty) (Var x ty): base GREATER, mutant LESS.
theorem witness : ∃ (env : List (term × term)) (t1 t2 : term),
    Mut.orda env t1 t2 ≠ Candle.orda env t1 t2 := by
  let ty : type := Tyvar (mls "a")
  refine ⟨[], Const (mls "c") ty, Var (mls "x") ty, ?_⟩
  have h1 : Candle.orda [] (Const (mls "c") ty) (Var (mls "x") ty) = GREATER := by
    simp [Candle.orda]
  have h2 : Mut.orda [] (Const (mls "c") ty) (Var (mls "x") ty) = LESS := by
    simp [Mut.orda]
  rw [h1, h2]
  intro h
  cases h

#print axioms witness
