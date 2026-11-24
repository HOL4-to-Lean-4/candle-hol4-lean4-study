import CandleLean
open HOL Candle Classical
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Mut
universe u v
/-- mutated statement of `Candle.REV_ASSOCD_thm` (`(x, y) :: t` replaced by `t ++ [(x, y)]` in the second clause) -/
def REV_ASSOCD_thm_stmt : Prop :=
  ∀ {α : Type u} {β : Type v},
    (∀ (a : β) (d : α), REV_ASSOCD a [] d = d) ∧
    (∀ (a : β) (x : α) (y : β) (t : List (α × β)) (d : α),
      REV_ASSOCD a (t ++ [(x, y)]) d = if y = a then x else REV_ASSOCD a t d)
end Mut

/-- `t = [(0, 0)]`, `(x, y) = (1, 0)`, `a = 0`: the left side finds the first entry (value 0), the right side says 1 -/
theorem witness : ¬ Mut.REV_ASSOCD_thm_stmt.{0, 0} := by
  intro h
  have := (h (α := Nat) (β := Nat)).2 0 1 0 [(0, 0)] 5
  simp [REV_ASSOCD] at this

#print axioms witness
