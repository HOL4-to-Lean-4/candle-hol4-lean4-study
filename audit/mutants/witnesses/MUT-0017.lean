import CandleLean

universe u v

open HOL Candle Classical

noncomputable section

namespace Mut

def mergesortN_tail {α : Type u} (negate : Prop) (R : α → α → Prop) : Nat → List α → List α
  | 0, _ => []
  | 1, x :: _ => [x]
  | 1, [] => []
  | 2, x :: y :: _ => sort2_tail negate R x y
  | 2, [x] => [x]
  | 2, [] => []
  | 3, x :: y :: z :: _ => sort3_tail negate R x y z
  | 3, [x, y] => sort2_tail negate R x y
  | 3, [x] => [x]
  | 3, [] => []
  | n + 4, l =>
    let len1 := DIV2 (n + 4)
    let neg := ¬ negate
    merge_tail neg R (mergesortN_tail neg R (DIV2 (n + 4)) l)
                     (mergesortN_tail neg R ((n + 3) - len1) (List.drop len1 l))
                     []
termination_by n _ => n
decreasing_by all_goals (simp only [DIV2]; omega)

theorem witness : ∃ (negate : Prop) (R : Nat → Nat → Prop) (n : Nat) (l : List Nat),
    Mut.mergesortN_tail negate R n l ≠ HOL.mergesortN_tail negate R n l := by
  refine ⟨False, fun _ _ => True, 4, [0, 1, 2, 3], ?_⟩
  intro h
  have := congrArg List.length h
  simp [Mut.mergesortN_tail, HOL.mergesortN_tail, DIV2, sort2_tail, merge_tail, REV] at this

end Mut

#print axioms Mut.witness
