import CandleLean

universe u v

open HOL Candle Classical

noncomputable section

namespace Mut

def is_subseq {α : Type u} : List α → List α → Prop
  | _, [] => False
  | [], _ :: _ => True
  | y :: ys, x :: xs => (x = y ∧ is_subseq ys xs) ∨ is_subseq ys (x :: xs)

theorem witness : ¬ ∀ (l1 l2 : List Nat), (Mut.is_subseq l1 l2 ↔ Candle.is_subseq l1 l2) := by
  intro h
  have := (h [] []).2 (by simp [Candle.is_subseq])
  simp [Mut.is_subseq] at this

end Mut

#print axioms Mut.witness
