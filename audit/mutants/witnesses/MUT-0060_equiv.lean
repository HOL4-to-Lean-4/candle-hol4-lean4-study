import CandleLean
open Candle HOL Classical

theorem SEG_take_drop : ∀ (l : List α) (m k : Nat), m + k ≤ l.length →
    SEG m k l = List.take m (List.drop k l)
  | l, 0, k, _ => by rw [(SEG_def (α := α)).1]; simp
  | [], m + 1, k, h => by simp at h
  | x :: l, m + 1, 0, h => by
    rw [(SEG_def (α := α)).2.1]
    have := SEG_take_drop l m 0 (by simp at h; omega)
    simp [this]
  | x :: l, m + 1, k + 1, h => by
    rw [(SEG_def (α := α)).2.2]
    have := SEG_take_drop l (m + 1) k (by simp at h; omega)
    simp [this]

noncomputable section
namespace Mut
def substring : mlstring → Nat → Nat → mlstring
  | .implode s, off, len =>
    strlit (if off + len < s.length then SEG len off s
            else if off ≤ s.length then s.drop off
            else [])
end Mut
end

/-- At `off + len = s.length` the base takes `SEG len off s`, which is `s.drop off`, exactly the mutant's else-branch. -/
theorem equiv : ∀ (x : mlstring) (off len : Nat), Mut.substring x off len = substring x off len := by
  intro x off len
  cases x with
  | implode s =>
    simp only [Mut.substring, substring]
    by_cases h1 : off + len < s.length
    · rw [if_pos h1, if_pos (by omega)]
    · by_cases h2 : off + len = s.length
      · rw [if_neg h1, if_pos (by omega), if_pos (by omega), SEG_take_drop s len off (by omega)]
        congr 1
        exact (List.take_of_length_le (by simp; omega)).symm
      · have h4 : ¬ off + len ≤ s.length := by omega
        simp only [h1, h4, if_false]

#print axioms equiv
