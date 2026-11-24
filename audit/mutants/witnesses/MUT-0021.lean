import CandleLean

open Candle HOL Classical

namespace Mut
noncomputable section

def term_lt (a b : term) : Prop :=
  ∀ term_lt' : term → term → Prop,
    ((∀ x1 ty1 x2 ty2, LEX mlstring_lt type_lt (x1, ty1) (x2, ty2) →
        term_lt' (Var x1 ty1) (Var x2 ty2)) ∧
     (∀ x1 ty1 x2 ty2, term_lt' (Var x1 ty1) (Const x2 ty2)) ∧
     (∀ x1 ty1 t1 t2, term_lt' (Var x1 ty1) (Comb t1 t2)) ∧
     (∀ x1 ty1 t1 t2, term_lt' (Var x1 ty1) (Abs t1 t2)) ∧
     (∀ x1 ty1 x2 ty2, LEX mlstring_lt type_lt (x1, ty1) (x2, ty2) →
        term_lt' (Const x1 ty1) (Const x2 ty2)) ∧
     (∀ x1 ty1 t1 t2, term_lt' (Const x1 ty1) (Comb t1 t2)) ∧
     (∀ x1 ty1 t1 t2, term_lt' (Const x1 ty1) (Abs t1 t2)) ∧
     (∀ s1 s2 t1 t2, LEX term_lt' term_lt' (s1, s2) (t1, t2) →
        term_lt' (Comb s1 s2) (Comb t1 t2)) ∨
     (∀ s1 s2 t1 t2, term_lt' (Comb s1 s2) (Abs t1 t2)) ∧
     (∀ s1 s2 t1 t2, LEX term_lt' term_lt' (s1, s2) (t1, t2) →
        term_lt' (Abs s1 s2) (Abs t1 t2))) →
    term_lt' a b

end
end Mut

-- Under the mutant the hypothesis of the closure is (r1 ∧ … ∧ r8) ∨ (r9 ∧ r10).  The relation
-- R _ b := b is an `Abs` satisfies r9 ∧ r10 but relates no (Var, Const) pair, so
-- term_lt (Var x ty) (Const y ty') fails in the mutant; the base proves it from rule 2.
theorem witness : ∃ a b : term, ¬ (Mut.term_lt a b ↔ Candle.term_lt a b) := by
  let ty : type := Tyvar (mls "a")
  refine ⟨Var (mls "x") ty, Const (mls "y") ty, ?_⟩
  intro h
  have hb : Candle.term_lt (Var (mls "x") ty) (Const (mls "y") ty) := by
    intro R hR
    exact hR.2.1 _ _ _ _
  have hm := h.2 hb
  have := hm (fun _ b => ∃ s t, b = Abs s t)
    (Or.inr ⟨fun s1 s2 t1 t2 => ⟨t1, t2, rfl⟩, fun s1 s2 t1 t2 _ => ⟨t1, t2, rfl⟩⟩)
  obtain ⟨s, t, e⟩ := this
  cases e

#print axioms witness
