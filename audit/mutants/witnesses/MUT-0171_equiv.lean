import CandleLean

open Candle HOL Classical

-- Statement bodies of the base and the mutant theorem, exactly as in the source
-- (the binder `t2 : mlstring` (base) / `t2 : string` (mutant) is shadowed by the second `t2`, so unused).
def BaseStmt (t1 : mlstring) (c2 : char) : Prop :=
  ∀ (c1 : char) (s1 s2 : string) (t2 : mlstring) (t2 : mlstring),
    strcat (implode (c1 :: s1)) t1 = strcat (implode (c2 :: s2)) t2 ↔
      c1 = c2 ∧ strcat (implode s1) t1 = strcat (implode s2) t2

def MutStmt (t1 : mlstring) (c2 : char) : Prop :=
  ∀ (c1 : char) (s1 s2 : string) (t2 : string) (t2 : mlstring),
    strcat (implode (c1 :: s1)) t1 = strcat (implode (c2 :: s2)) t2 ↔
      c1 = c2 ∧ strcat (implode s1) t1 = strcat (implode s2) t2

-- Equivalent: the changed binder is never used, and both `mlstring` and `string` are inhabited.
theorem equiv (t1 : mlstring) (c2 : char) : MutStmt t1 c2 ↔ BaseStmt t1 c2 := by
  constructor
  · intro h c1 s1 s2 _ t2
    exact h c1 s1 s2 [] t2
  · intro h c1 s1 s2 _ t2
    exact h c1 s1 s2 (implode []) t2

#print axioms equiv
