import CandleLean

open Candle HOL Classical

namespace Mut

-- The mutated statement (∀ tm replaced by ∃ tm), as a Prop.
def FINITE_VFREE_IN_2_stmt : Prop :=
    ∃ (tm : term), FINITE (GSPEC (fun (p : mlstring × type) => ((p.1, p.2), VFREE_IN (Var p.1 p.2) tm)))

-- The same with an arbitrary predicate in place of `VFREE_IN (Var x ty) tm` that is false for some tm.
def FINITE_VFREE_IN_2_stmt_Q (Q : term → mlstring × type → Prop) : Prop :=
    ∃ (tm : term), FINITE (GSPEC (fun (p : mlstring × type) => ((p.1, p.2), Q tm p)))

end Mut

-- The mutated statement is provable outright, with a constant `tm` (no free variables, so the set
-- is empty).  The same argument works whenever some `tm` has no free variable under Q, so the
-- mutated statement is a weak, essentially degenerate claim; the base `∀ tm` form is the real one.
theorem witness : Mut.FINITE_VFREE_IN_2_stmt ∧
    ∀ Q : term → mlstring × type → Prop, (∃ tm, ∀ p, ¬ Q tm p) → Mut.FINITE_VFREE_IN_2_stmt_Q Q := by
  have key : ∀ Q : term → mlstring × type → Prop, (∃ tm, ∀ p, ¬ Q tm p) →
      ∃ (tm : term), FINITE (GSPEC (fun (p : mlstring × type) => ((p.1, p.2), Q tm p))) := by
    rintro Q ⟨tm, h⟩
    refine ⟨tm, ?_⟩
    have e : GSPEC (fun (p : mlstring × type) => ((p.1, p.2), Q tm p)) = (EMPTY : HOL.Set (mlstring × type)) := by
      funext v
      apply propext
      constructor
      · rintro ⟨x, hx⟩
        have := congrArg Prod.snd hx
        simp at this
        exact absurd this (h x)
      · intro h; exact h.elim
    rw [e]
    exact fun P hP => hP.1
  refine ⟨?_, key⟩
  · exact key (fun tm p => VFREE_IN (Var p.1 p.2) tm)
      ⟨Const (mls "c") (Tyvar (mls "a")), fun p hp => by simp [VFREE_IN] at hp⟩

#print axioms witness
