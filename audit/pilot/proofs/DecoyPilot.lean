import CandleLean
open HOL Classical
namespace Candle
example : (∀ ls : List string, ALL_DISTINCT ls → ALL_DISTINCT (List.map implode ls)) =
    (∀ ls : List string, ALL_DISTINCT ls → ALL_DISTINCT (List.map (fun x_e => implode x_e) ls)) := rfl

def term_lt_decoy (a b : term) : Prop :=
  ∀ term_lt' : term → term → Prop,
    ((∀ x1 ty1 x2 ty2, LEX mlstring_lt type_lt (x1, ty1) (x2, ty2) →
        term_lt' (Var x1 ty1) (Var x2 ty2)) ∧
     (∀ x1 ty1 x2 ty2, term_lt' (Var x1 ty1) (Const x2 ty2)) ∧
     (∀ x1 ty1 t1 t2, term_lt' (Var x1 ty1) (Comb t1 t2)) ∧
     (∀ x1 ty1 t1 t2, term_lt' (Var x1 ty1) (Abs t1 t2)) ∧
     (∀ x1 ty1 x2 ty2, LEX mlstring_lt type_lt (x1, ty1) (x2, ty2) →
        term_lt' (Const x1 ty1) (Const x2 ty2)) ∧
     (∀ ty1 x1 t1 t2, term_lt' (Const x1 ty1) (Comb t1 t2)) ∧
     (∀ x1 ty1 t1 t2, term_lt' (Const x1 ty1) (Abs t1 t2)) ∧
     (∀ s1 s2 t1 t2, LEX term_lt' term_lt' (s1, s2) (t1, t2) →
        term_lt' (Comb s1 s2) (Comb t1 t2)) ∧
     (∀ s1 s2 t1 t2, term_lt' (Comb s1 s2) (Abs t1 t2)) ∧
     (∀ s1 s2 t1 t2, LEX term_lt' term_lt' (s1, s2) (t1, t2) →
        term_lt' (Abs s1 s2) (Abs t1 t2))) →
    term_lt' a b

theorem decoy_eq : @term_lt_decoy = @term_lt := by
  funext a b
  apply propext
  constructor
  · intro h R ⟨h1, h2, h3, h4, h5, h6, h7⟩
    exact h R ⟨h1, h2, h3, h4, h5, fun a b => h6 b a, h7⟩
  · intro h R ⟨h1, h2, h3, h4, h5, h6, h7⟩
    exact h R ⟨h1, h2, h3, h4, h5, fun a b => h6 b a, h7⟩
#print axioms decoy_eq
end Candle
