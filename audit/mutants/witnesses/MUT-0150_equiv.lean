import CandleLean
open Candle HOL Classical

/-- Both versions bind `t2` twice; the inner binder shadows the outer one, so the outer `t2` (of type `mlstring` in the base,
    `type` in the mutant) is unused. Since `type` is inhabited, the two statements are equivalent. -/
theorem equiv (t1 : mlstring) (c2 : char) :
    (∀ (c1 : char) (s1 s2 : string) (t2 : type) (t2 : mlstring),
      strcat (implode (c1 :: s1)) t1 = strcat (implode (c2 :: s2)) t2 ↔
        c1 = c2 ∧ strcat (implode s1) t1 = strcat (implode s2) t2) ↔
    (∀ (c1 : char) (s1 s2 : string) (t2 : mlstring) (t2 : mlstring),
      strcat (implode (c1 :: s1)) t1 = strcat (implode (c2 :: s2)) t2 ↔
        c1 = c2 ∧ strcat (implode s1) t1 = strcat (implode s2) t2) := by
  constructor
  · intro h c1 s1 s2 _ t2
    exact h c1 s1 s2 (Tyvar default) t2
  · intro h c1 s1 s2 _ t2
    exact h c1 s1 s2 default t2

#print axioms equiv
