import CandleLean

universe u v

open HOL Candle Classical

noncomputable section

namespace Mut

def term_lt (a b : term) : Prop :=
  ∀ term_lt' : term → term → Prop,
    ((∀ x1 ty1 x2 ty2, LEX mlstring_lt type_lt (x1, ty1) (x2, ty2) →
        term_lt' (Var x1 ty1) (Var x2 ty2)) ∧
     (∀ x1 ty1 x2 ty2, term_lt' (Var ty1 x1) (Const x2 ty2)) ∧
     (∀ x1 ty1 t1 t2, term_lt' (Var x1 ty1) (Comb t1 t2)) ∧
     (∀ x1 ty1 t1 t2, term_lt' (Var x1 ty1) (Abs t1 t2)) ∧
     (∀ x1 ty1 x2 ty2, LEX mlstring_lt type_lt (x1, ty1) (x2, ty2) →
        term_lt' (Const x1 ty1) (Const x2 ty2)) ∧
     (∀ x1 ty1 t1 t2, term_lt' (Const x1 ty1) (Comb t1 t2)) ∧
     (∀ x1 ty1 t1 t2, term_lt' (Const x1 ty1) (Abs t1 t2)) ∧
     (∀ s1 s2 t1 t2, LEX term_lt' term_lt' (s1, s2) (t1, t2) →
        term_lt' (Comb s1 s2) (Comb t1 t2)) ∧
     (∀ s1 s2 t1 t2, term_lt' (Comb s1 s2) (Abs t1 t2)) ∧
     (∀ s1 s2 t1 t2, LEX term_lt' term_lt' (s1, s2) (t1, t2) →
        term_lt' (Abs s1 s2) (Abs t1 t2))) →
    term_lt' a b

/-- The mutated declaration is the base one up to renaming of the bound variables of the second
clause (`x1 : type`, `ty1 : mlstring` instead of the other order): the two are equal. -/
theorem equiv : Mut.term_lt = Candle.term_lt := by
  funext a b
  apply propext
  constructor
  · intro h f hf
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hf
    exact h f ⟨h1, fun x1 ty1 x2 ty2 => h2 ty1 x1 x2 ty2, h3, h4, h5, h6, h7, h8, h9, h10⟩
  · intro h f hf
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hf
    exact h f ⟨h1, fun x1 ty1 x2 ty2 => h2 ty1 x1 x2 ty2, h3, h4, h5, h6, h7, h8, h9, h10⟩

theorem witness : Mut.term_lt = Candle.term_lt := equiv

end Mut

#print axioms Mut.witness
