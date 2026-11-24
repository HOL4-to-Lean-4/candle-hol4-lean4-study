import CandleLean
open HOL Candle
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Mut
/-- mutated statement of `Candle.fresh_union` (premise `FINITE s ∧ FINITE t` dropped) -/
def fresh_union_stmt : Prop :=
  ∀ (s t : Set string), fresh (UNION s t) ∉ s ∧ fresh (UNION s t) ∉ t
end Mut

/-- with `s` the universal set, `fresh _` is trivially a member of `s` -/
theorem witness : ¬ Mut.fresh_union_stmt := by
  intro h
  exact (h (fun _ => True) (fun _ => True)).1 trivial

#print axioms witness
