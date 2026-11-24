import CandleLean
open HOL Candle Classical
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
noncomputable section

namespace Mut
/-- mutated statement of `fresh_names_exist` (`n : Int`) -/
def fresh_names_exist_stmt : Prop :=
    ∀ (s : Set string) (n : Int), FINITE s →
        ∃ (names : List string), names.length = n ∧ ALL_DISTINCT names ∧ DISJOINT (LIST_TO_SET names) s
end Mut

/-- For `n = -1` no list has length `n`. -/
theorem witness : ¬ Mut.fresh_names_exist_stmt := by
  intro h
  obtain ⟨names, hl, _⟩ := h (EMPTY : Set string) (-1) (fun P hP => hP.1)
  omega

#print axioms witness
