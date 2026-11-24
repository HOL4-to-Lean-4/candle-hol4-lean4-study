import CandleLean

open Candle HOL Classical

namespace Mut

-- The mutated statement (∀ tm ty replaced by ∃ tm ty), as a Prop.
def simple_subst_has_type_stmt : Prop :=
    ∃ (tm : term) (ty : type),
        has_type tm ty →
        ∀ (subst : List (term × term)),
          EVERY (fun (p : term × term) => has_type p.1 (typeof p.2)) subst →
          has_type (simple_subst subst tm) ty

-- The same statement with an arbitrary conclusion Q in place of `has_type (simple_subst subst tm) ty`.
def simple_subst_has_type_stmt_Q (Q : term → type → List (term × term) → Prop) : Prop :=
    ∃ (tm : term) (ty : type),
        has_type tm ty →
        ∀ (subst : List (term × term)),
          EVERY (fun (p : term × term) => has_type p.1 (typeof p.2)) subst →
          Q tm ty subst

end Mut

-- The mutated statement is provable outright, by taking an ill-typed pair (tm, ty) so that the
-- premise `has_type tm ty` is false.  The same proof works for every conclusion Q (even `False`),
-- so the mutated statement says nothing about `simple_subst`; the base `∀` form is the real claim.
theorem witness : Mut.simple_subst_has_type_stmt ∧
    ∀ Q : term → type → List (term × term) → Prop, Mut.simple_subst_has_type_stmt_Q Q := by
  have key : ∀ Q : term → type → List (term × term) → Prop,
      ∃ (tm : term) (ty : type),
        has_type tm ty → ∀ (subst : List (term × term)),
          EVERY (fun (p : term × term) => has_type p.1 (typeof p.2)) subst → Q tm ty subst := by
    intro Q
    refine ⟨Var (mls "x") (Tyvar (mls "a")), Tyvar (mls "b"), ?_⟩
    intro h
    exfalso
    cases h
  exact ⟨key (fun tm ty subst => has_type (simple_subst subst tm) ty), key⟩

#print axioms witness
