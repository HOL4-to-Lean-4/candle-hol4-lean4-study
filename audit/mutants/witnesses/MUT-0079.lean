import CandleLean
open HOL Candle Classical
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
universe u
noncomputable section

namespace Mut
def arities_match : List type → List type → Prop
  | [], [] => True
  | [], _ => False
  | _, [] => False
  | Tyapp c1 a1 :: xs, Tyapp c2 a2 :: ys => (c1 = c2 → arities_match a1 a2) ∧ arities_match xs xs
  | _ :: xs, _ :: ys => arities_match xs ys
termination_by l1 => sizeOf l1
decreasing_by
  all_goals simp_wf
  all_goals omega
end Mut

theorem witness : ∃ l1 l2 : List type, ¬ (Mut.arities_match l1 l2 ↔ Candle.arities_match l1 l2) := by
  refine ⟨[Tyapp (mls "c") []], [Tyapp (mls "c") [], Tyapp (mls "c") []], ?_⟩
  intro h
  have hm : Mut.arities_match [Tyapp (mls "c") []] [Tyapp (mls "c") [], Tyapp (mls "c") []] := by
    rw [Mut.arities_match]
    · refine ⟨fun _ => ?_, ?_⟩ <;> (rw [Mut.arities_match]; try trivial)
    all_goals (intros; simp_all)
  have hb : ¬ Candle.arities_match [Tyapp (mls "c") []] [Tyapp (mls "c") [], Tyapp (mls "c") []] := by
    rw [Candle.arities_match]
    · intro hh
      have := hh.2
      rw [Candle.arities_match] at this
      exact this
      all_goals (intros; simp_all)
    all_goals (intros; simp_all)
  exact hb (h.1 hm)

#print axioms witness
