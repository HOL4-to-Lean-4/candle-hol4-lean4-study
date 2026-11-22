/-
  Translation of CakeML `basis/pure/mllistScript.sml` (theory `mllist`):
  the definitions needed by the Candle soundness development.
-/
import CandleLean.Misc
import CandleLean.Prelude.Mergesort

open Classical

/-! ## Stage 2: theorem statements of `mllist` (proofs are `sorry`).
  The `mergesort` theorems come before `sort_def` in the HOL4 script. -/

/- HOL4:
Theorem merge_tail_MEM:
  !negate R xs ys acc. MEM x (merge_tail negate R xs ys acc) = ((MEM x xs) \/ (MEM x ys) \/ (MEM x acc))
-/
theorem merge_tail_MEM {α : Type} (x : α) :
    ∀ (negate : Prop) (R : α → α → Prop) (xs ys acc : List α),
      MEM x (merge_tail negate R xs ys acc) = (MEM x xs ∨ MEM x ys ∨ MEM x acc) := by
  sorry

/- HOL4:
Theorem mergesortN_tail_MEM:
  !negate R length lst. (MEM x (mergesortN_tail negate R length lst) <=> MEM x (TAKE length lst))
-/
theorem mergesortN_tail_MEM {α : Type} (x : α) :
    ∀ (negate : Prop) (R : α → α → Prop) (length : Nat) (lst : List α),
      MEM x (mergesortN_tail negate R length lst) ↔ MEM x (List.take length lst) := by
  sorry

/- HOL4:
Theorem mergesort_tail_MEM:
  ∀R l. MEM x (mergesort$mergesort_tail R l) ⇔ MEM x l
-/
theorem mergesort_tail_MEM {α : Type} (x : α) :
    ∀ (R : α → α → Prop) (l : List α), MEM x (mergesort_tail R l) ↔ MEM x l := by
  sorry

/- HOL4:
Theorem merge_tail_PERM:
  !negate R xs ys acc. PERM (xs++ys++acc) (merge_tail negate R xs ys acc)
-/
theorem merge_tail_PERM {α : Type} :
    ∀ (negate : Prop) (R : α → α → Prop) (xs ys acc : List α),
      PERM (xs ++ ys ++ acc) (merge_tail negate R xs ys acc) := by
  sorry

/- HOL4:
Theorem sort2_tail_PERM:
  !neg R x y. PERM [x;y] (sort2_tail neg R x y)
-/
theorem sort2_tail_PERM {α : Type} :
    ∀ (neg : Prop) (R : α → α → Prop) (x y : α), PERM [x, y] (sort2_tail neg R x y) := by
  sorry

/- HOL4:
Theorem sort3_tail_PERM:
  !neg R x y z. PERM [x;y;z] (sort3_tail neg R x y z)
-/
theorem sort3_tail_PERM {α : Type} :
    ∀ (neg : Prop) (R : α → α → Prop) (x y z : α),
      PERM [x, y, z] (sort3_tail neg R x y z) := by
  sorry

/- HOL4:
Theorem mergesortN_tail_PERM:
  !neg R len l. PERM (TAKE len l) (mergesortN_tail neg R len l)
-/
theorem mergesortN_tail_PERM {α : Type} :
    ∀ (neg : Prop) (R : α → α → Prop) (len : Nat) (l : List α),
      PERM (List.take len l) (mergesortN_tail neg R len l) := by
  sorry

/- HOL4:
Definition sort_def:
  sort = mergesort$mergesort_tail
End -/
noncomputable def sort {α : Type u} : (α → α → Prop) → List α → List α := mergesort_tail

/- HOL4:
Theorem sort_MEM[simp]:
  !R L. MEM x (sort R L) ⇔ MEM x L
-/
theorem sort_MEM {α : Type} (x : α) :
    ∀ (R : α → α → Prop) (L : List α), MEM x (sort R L) ↔ MEM x L := by
  sorry

/- HOL4:
Theorem sort_PERM:
  !R L. sorting$PERM L (sort R L)
-/
theorem sort_PERM {α : Type} :
    ∀ (R : α → α → Prop) (L : List α), PERM L (sort R L) := by
  sorry

/- HOL4:
Theorem sort_LENGTH[simp]:
  !R l. LENGTH (sort R l) = LENGTH l
-/
theorem sort_LENGTH {α : Type} :
    ∀ (R : α → α → Prop) (l : List α), (sort R l).length = l.length := by
  sorry

/- HOL4:
Theorem sort_set[simp]:
  set (sort R ls) = set ls
-/
theorem sort_set {α : Type} (R : α → α → Prop) (ls : List α) :
    set (sort R ls) = set ls := by
  sorry
