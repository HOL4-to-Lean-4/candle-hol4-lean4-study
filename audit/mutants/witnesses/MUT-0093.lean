import CandleLean

open Candle HOL Classical

namespace Mut
noncomputable section

def type_lt (a b : type) : Prop :=
  ∀ type_lt' : type → type → Prop,
    ((∀ x1 x2, mlstring_lt x1 x2 → type_lt' (Tyvar x1) (Tyvar x2)) ∧
     (∀ x1 x2 args2, type_lt' (Tyvar x1) (Tyapp x2 args2)) ∨
     (∀ x1 args1 x2 args2,
        LEX mlstring_lt (LLEX type_lt') (x1, args1) (x2, args2) →
        type_lt' (Tyapp x1 args1) (Tyapp x2 args2))) →
    type_lt' a b

end
end Mut

-- Under the mutant the hypothesis of the closure is (r1 ∧ r2) ∨ r3.  The relation
-- R a b := (a is Tyapp ∧ b is Tyapp) satisfies r3 but does not relate (Tyvar, Tyapp), so
-- type_lt (Tyvar x) (Tyapp y []) fails in the mutant; the base proves it from rule 2.
theorem witness : ∃ a b : type, ¬ (Mut.type_lt a b ↔ Candle.type_lt a b) := by
  refine ⟨Tyvar (mls "x"), Tyapp (mls "y") [], ?_⟩
  intro h
  have hb : Candle.type_lt (Tyvar (mls "x")) (Tyapp (mls "y") []) := by
    intro R hR
    exact hR.2.1 _ _ _
  have hm := h.2 hb
  have := hm (fun a b => (∃ x l, a = Tyapp x l) ∧ (∃ x l, b = Tyapp x l))
    (Or.inr (fun x1 args1 x2 args2 _ => ⟨⟨x1, args1, rfl⟩, ⟨x2, args2, rfl⟩⟩))
  obtain ⟨⟨x, l, e⟩, _⟩ := this
  cases e

#print axioms witness
