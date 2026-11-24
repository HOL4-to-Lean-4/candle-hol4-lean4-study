import CandleLean

open HOL Classical

universe u

namespace Mut
noncomputable section

def merge_tail {α : Type u} (negate : Prop) (R : α → α → Prop) :
    List α → List α → List α → List α
  | [], [], acc => acc
  | l, [], acc => REV l acc
  | [], l, acc => REV l acc
  | x :: l1, y :: l2, acc =>
    if R x y ≠ negate then merge_tail negate R l1 (y :: l2) (x :: acc)
    else merge_tail negate R (l1 ++ [x]) l2 (y :: acc)
termination_by l1 l2 => l1.length + l2.length

end
end Mut

-- R always True, negate = True: R x y ≠ negate is false, so the else branch is taken.
-- merge_tail [0,1] [2] []: base [1,0,2], mutant [0,1,2].
theorem witness : ∃ (negate : Prop) (R : Nat → Nat → Prop) (l1 l2 acc : List Nat),
    Mut.merge_tail negate R l1 l2 acc ≠ HOL.merge_tail negate R l1 l2 acc := by
  refine ⟨True, fun _ _ => True, [0, 1], [2], [], ?_⟩
  have e1 : HOL.merge_tail True (fun _ _ => True) [0, 1] [2] [] = [1, 0, 2] := by
    rw [HOL.merge_tail]
    simp [HOL.merge_tail, REV]
  have e2 : Mut.merge_tail True (fun _ _ => True) [0, 1] [2] [] = [0, 1, 2] := by
    rw [Mut.merge_tail]
    simp [Mut.merge_tail, REV]
  rw [e1, e2]
  simp

#print axioms witness
