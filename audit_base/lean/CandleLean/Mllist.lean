import CandleLean.Misc

/-!
# mllist (CakeML `basis/pure/mllistScript.sml`), reduced to what the targets need

The mergesort functions the targets mention (`merge_tail`, `sort2_tail`, `sort3_tail`,
`mergesortN_tail`, `mergesort_tail`) are HOL4 library constants (theory `mergesort`),
translated in `CandleLean/Prelude/List.lean` (namespace `HOL`).
-/

universe u

namespace Candle

open HOL Classical

noncomputable section

/- HOL4:
Theorem merge_tail_MEM:
  !negate R xs ys acc. MEM x (merge_tail negate R xs ys acc) = ((MEM x xs) \/ (MEM x ys) \/ (MEM x acc)) -/
theorem merge_tail_MEM {α : Type u} (x : α) :
    ∀ (negate : Prop) (R : α → α → Prop) (xs ys acc : List α),
      (x ∈ merge_tail negate R xs ys acc) = (x ∈ xs ∨ x ∈ ys ∨ x ∈ acc) := by
  sorry

/- HOL4:
Theorem mergesortN_tail_MEM:
  !negate R length lst. (MEM x (mergesortN_tail negate R length lst) <=> MEM x (TAKE length lst)) -/
theorem mergesortN_tail_MEM {α : Type u} (x : α) :
    ∀ (negate : Prop) (R : α → α → Prop) (length : Nat) (lst : List α),
      (x ∈ mergesortN_tail negate R length lst ↔ x ∈ List.take length lst) := by
  sorry

/- HOL4:
Theorem mergesort_tail_MEM:
  ∀R l. MEM x (mergesort$mergesort_tail R l) ⇔ MEM x l -/
theorem mergesort_tail_MEM {α : Type u} (x : α) :
    ∀ (R : α → α → Prop) (l : List α), x ∈ mergesort_tail R l ↔ x ∈ l := by
  sorry

/- HOL4:
Theorem merge_tail_PERM:
  !negate R xs ys acc. PERM (xs++ys++acc) (merge_tail negate R xs ys acc) -/
theorem merge_tail_PERM {α : Type u} :
    ∀ (negate : Prop) (R : α → α → Prop) (xs ys acc : List α),
      PERM (xs ++ ys ++ acc) (merge_tail negate R xs ys acc) := by
  sorry

/- HOL4:
Theorem sort2_tail_PERM:
  !neg R x y. PERM [x;y] (sort2_tail neg R x y) -/
theorem sort2_tail_PERM {α : Type u} :
    ∀ (neg : Prop) (R : α → α → Prop) (x y : α), PERM [x, y] (sort2_tail neg R x y) := by
  sorry

/- HOL4:
Theorem sort3_tail_PERM:
  !neg R x y z. PERM [x;y;z] (sort3_tail neg R x y z) -/
theorem sort3_tail_PERM {α : Type u} :
    ∀ (neg : Prop) (R : α → α → Prop) (x y z : α),
      PERM [x, y, z] (sort3_tail neg R x y z) := by
  sorry

/- HOL4:
Theorem mergesortN_tail_PERM:
  !neg R len l. PERM (TAKE len l) (mergesortN_tail neg R len l) -/
theorem mergesortN_tail_PERM {α : Type u} :
    ∀ (neg : Prop) (R : α → α → Prop) (len : Nat) (l : List α),
      PERM (List.take len l) (mergesortN_tail neg R len l) := by
  sorry

/- HOL4:
Definition sort_def:
  sort = mergesort$mergesort_tail
End -/
def sort {α : Type u} : (α → α → Prop) → List α → List α := mergesort_tail

/- HOL4:
Theorem sort_MEM[simp]:
  !R L. MEM x (sort R L) ⇔ MEM x L -/
theorem sort_MEM {α : Type u} (x : α) :
    ∀ (R : α → α → Prop) (L : List α), x ∈ sort R L ↔ x ∈ L := by
  sorry

/- HOL4:
Theorem sort_PERM:
  !R L. sorting$PERM L (sort R L) -/
theorem sort_PERM {α : Type u} :
    ∀ (R : α → α → Prop) (L : List α), PERM L (sort R L) := by
  sorry

/- HOL4:
Theorem sort_LENGTH[simp]:
  !R l. LENGTH (sort R l) = LENGTH l -/
theorem sort_LENGTH {α : Type u} :
    ∀ (R : α → α → Prop) (l : List α), (sort R l).length = l.length := by
  sorry

/- HOL4:
Theorem sort_set[simp]:
  set (sort R ls) = set ls -/
theorem sort_set {α : Type u} (R : α → α → Prop) (ls : List α) :
    LIST_TO_SET (sort R ls) = LIST_TO_SET ls := by
  sorry

end

end Candle
