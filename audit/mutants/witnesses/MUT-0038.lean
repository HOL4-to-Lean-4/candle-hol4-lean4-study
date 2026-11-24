import CandleLean
open HOL Classical
noncomputable section
namespace Mut
def merge_tail {α : Type u} (negate : Prop) (R : α → α → Prop) :
    List α → List α → List α → List α
  | [], [], acc => acc
  | l, [], acc => REV l acc
  | [], l, acc => REV l acc
  | x :: l1, y :: l2, acc =>
    if R x y ≠ negate then merge_tail negate R l1 (l2 ++ [y]) (x :: acc)
    else merge_tail negate R (x :: l1) l2 (y :: acc)
termination_by l1 l2 => l1.length + l2.length
end Mut

-- l1 = [1], l2 = [2,3], R = (<=), negate = False:
-- base: x=1 taken, then REV [2,3] [1] = [3,2,1]; mutant requeues 2 behind 3: REV [3,2] [1] = [2,3,1].
theorem witness : ∃ (neg : Prop) (R : Nat → Nat → Prop) (l1 l2 acc : List Nat),
    Mut.merge_tail neg R l1 l2 acc ≠ HOL.merge_tail neg R l1 l2 acc := by
  refine ⟨False, fun a b => a ≤ b, [1], [2, 3], [], ?_⟩
  have h1 : ((1 : Nat) ≤ 2) ≠ False := by simp
  simp [Mut.merge_tail, HOL.merge_tail, REV]

#print axioms witness
