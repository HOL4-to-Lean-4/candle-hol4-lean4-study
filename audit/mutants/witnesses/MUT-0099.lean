import CandleLean

open Candle HOL Classical

namespace Mut
noncomputable section

inductive RACONV : List (term × term) → term × term → Prop where
  | Var {env : List (term × term)} {x1 : mlstring} {ty1 : type} {x2 : mlstring} {ty2 : type} :
      ALPHAVARS env (Var x1 ty1, Var x2 ty2) → RACONV env (Var x1 ty1, Var x2 ty2)
  | Const {env : List (term × term)} {x : mlstring} {ty : type} :
      RACONV env (Const x ty, Const x ty)
  | Comb {env : List (term × term)} {s1 s2 t1 t2 : term} :
      RACONV env (s1, s2) → RACONV env (t1, t2) → RACONV env (Comb s1 t1, Comb s2 t2)
  | Abs {env : List (term × term)} {v1 v2 t1 t2 : term} :
      RACONV ((v1, v2) :: env) (t1, t2) →
      RACONV env (Abs v1 t1, Abs v2 t2)

end
end Mut

-- λ(x:a).x  vs  λ(x:b).x : the mutant relates them (no check that the binder types agree),
-- the base does not (the Abs rule needs typeof v1 = typeof v2, but a ≠ b).
theorem witness : ∃ (env : List (term × term)) (p : term × term),
    Mut.RACONV env p ∧ ¬ Candle.RACONV env p := by
  let ta : type := Tyvar (mls "a")
  let tb : type := Tyvar (mls "b")
  have hne : ta ≠ tb := by
    intro h
    have h'' : Tyvar (mls "a") = Tyvar (mls "b") := h
    have h' : mls "a" = mls "b" := by injection h''
    exact absurd h' (by decide)
  refine ⟨[], (Abs (Var (mls "x") ta) (Var (mls "x") ta), Abs (Var (mls "x") tb) (Var (mls "x") tb)), ?_, ?_⟩
  · refine Mut.RACONV.Abs (Mut.RACONV.Var ?_)
    exact Or.inl rfl
  · intro h
    generalize hp : ((Abs (Var (mls "x") ta) (Var (mls "x") ta),
      Abs (Var (mls "x") tb) (Var (mls "x") tb)) : term × term) = p at h
    cases h with
    | Var _ => simp at hp
    | Const => simp at hp
    | Comb _ _ => simp at hp
    | Abs hty _ =>
      simp only [Prod.mk.injEq] at hp
      obtain ⟨h1, h2⟩ := hp
      injection h1 with e1 e2
      injection h2 with e3 e4
      subst e1 e3
      exact hne hty

#print axioms witness
