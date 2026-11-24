import CandleLean

universe u v

open HOL Candle Classical

noncomputable section

namespace Mut

def arities_match : List type → List type → Prop
  | [], [] => True
  | [], _ => False
  | _, [] => False
  | Tyapp c1 a1 :: xs, Tyapp c2 a2 :: ys => (c1 = c2 → arities_match a1 a1) ∧ arities_match xs ys
  | _ :: xs, _ :: ys => arities_match xs ys
termination_by l1 => sizeOf l1
decreasing_by
  all_goals simp_wf
  all_goals omega

theorem witness : ¬ ∀ l1 l2, (Mut.arities_match l1 l2 ↔ Candle.arities_match l1 l2) := by
  intro h
  have h1 : Mut.arities_match [Tyapp (mls "c") [Tyvar (mls "x")]] [Tyapp (mls "c") []] := by
    simp [Mut.arities_match]
  have h2 := (h _ _).1 h1
  simp [Candle.arities_match] at h2

end Mut

#print axioms Mut.witness
