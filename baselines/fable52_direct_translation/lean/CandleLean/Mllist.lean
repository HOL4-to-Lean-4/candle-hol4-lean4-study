/-
  HOL4 theory `mllist` (basis/pure/mllistScript.sml): the definitions the targets need.
  (`merge_tail`, `mergesortN_tail`, `mergesort_tail`, `sort2_tail`, `sort3_tail` are HOL4
  library constants of theory `mergesort`: see `CandleLean/Prelude/Mergesort.lean`.)
-/
import CandleLean.Misc

namespace Candle

noncomputable section
open Classical

/- HOL4:
Definition sort_def:
  sort = mergesort$mergesort_tail
End -/
def sort {α : Type} : (α → α → Prop) → List α → List α := mergesort_tail

end

end Candle

/-! ## Stage 2: theorem statements (HOL4 source order) -/

namespace Candle
noncomputable section
open Classical
set_option autoImplicit false

/- HOL4:
Theorem merge_tail_MEM:
  !negate R xs ys acc. MEM x (merge_tail negate R xs ys acc) = ((MEM x xs) \/ (MEM x ys) \/ (MEM x acc))
-/
theorem merge_tail_MEM {α : Type} [Nonempty α] (x : α) :
    ∀ (negate : Prop) (R : α → α → Prop) (xs ys acc : List α),
      MEM x (merge_tail negate R xs ys acc) ↔ ((MEM x xs) ∨ (MEM x ys) ∨ (MEM x acc)) := by
  sorry

/- HOL4:
Theorem mergesortN_tail_MEM:
  !negate R length lst. (MEM x (mergesortN_tail negate R length lst) <=> MEM x (TAKE length lst))
-/
theorem mergesortN_tail_MEM {α : Type} [Nonempty α] (x : α) :
    ∀ (negate : Prop) (R : α → α → Prop) (length : Nat) (lst : List α),
      (MEM x (mergesortN_tail negate R length lst) ↔ MEM x (TAKE length lst)) := by
  sorry

/- HOL4:
Theorem mergesort_tail_MEM:
  ∀R l. MEM x (mergesort$mergesort_tail R l) ⇔ MEM x l
-/
theorem mergesort_tail_MEM {α : Type} [Nonempty α] (x : α) :
    ∀ (R : α → α → Prop) (l : List α), MEM x (mergesort_tail R l) ↔ MEM x l := by
  sorry

/- HOL4:
Theorem merge_tail_PERM:
  !negate R xs ys acc. PERM (xs++ys++acc) (merge_tail negate R xs ys acc)
-/
theorem merge_tail_PERM {α : Type} [Nonempty α] :
    ∀ (negate : Prop) (R : α → α → Prop) (xs ys acc : List α),
      PERM (xs ++ ys ++ acc) (merge_tail negate R xs ys acc) := by
  sorry

/- HOL4:
Theorem sort2_tail_PERM:
  !neg R x y. PERM [x;y] (sort2_tail neg R x y)
-/
theorem sort2_tail_PERM {α : Type} [Nonempty α] :
    ∀ (neg : Prop) (R : α → α → Prop) (x y : α), PERM [x, y] (sort2_tail neg R x y) := by
  sorry

/- HOL4:
Theorem sort3_tail_PERM:
  !neg R x y z. PERM [x;y;z] (sort3_tail neg R x y z)
-/
theorem sort3_tail_PERM {α : Type} [Nonempty α] :
    ∀ (neg : Prop) (R : α → α → Prop) (x y z : α), PERM [x, y, z] (sort3_tail neg R x y z) := by
  sorry

/- HOL4:
Theorem mergesortN_tail_PERM:
  !neg R len l. PERM (TAKE len l) (mergesortN_tail neg R len l)
-/
theorem mergesortN_tail_PERM {α : Type} [Nonempty α] :
    ∀ (neg : Prop) (R : α → α → Prop) (len : Nat) (l : List α),
      PERM (TAKE len l) (mergesortN_tail neg R len l) := by
  sorry

/- HOL4:
Theorem sort_MEM[simp]:
  !R L. MEM x (sort R L) ⇔ MEM x L
-/
theorem sort_MEM {α : Type} [Nonempty α] (x : α) :
    ∀ (R : α → α → Prop) (L : List α), MEM x (sort R L) ↔ MEM x L := by
  sorry

/- HOL4:
Theorem sort_PERM:
  !R L. sorting$PERM L (sort R L)
-/
theorem sort_PERM {α : Type} [Nonempty α] :
    ∀ (R : α → α → Prop) (L : List α), PERM L (sort R L) := by
  sorry

/- HOL4:
Theorem sort_LENGTH[simp]:
  !R l. LENGTH (sort R l) = LENGTH l
-/
theorem sort_LENGTH {α : Type} [Nonempty α] :
    ∀ (R : α → α → Prop) (l : List α), LENGTH (sort R l) = LENGTH l := by
  sorry

/- HOL4:
Theorem sort_set[simp]:
  set (sort R ls) = set ls
-/
theorem sort_set {α : Type} [Nonempty α] (R : α → α → Prop) (ls : List α) :
    set (sort R ls) = set ls := by
  sorry

end
end Candle
