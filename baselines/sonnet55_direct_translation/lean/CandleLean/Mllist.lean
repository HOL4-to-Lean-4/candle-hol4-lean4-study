import CandleLean.Misc
/-
  Translation of `basis/pure/mllistScript.sml` (definitions).
  Namespace `Candle.Mllist`.
-/
namespace Candle.Mllist

open HOL
universe u v

open Classical

noncomputable section

/- HOL4: Definition sort_def:
  sort = mergesort$mergesort_tail
End -/
def sort {α : Type u} (R : α → α → Prop) (l : List α) : List α := mergesort_tail R l

/- HOL4: Definition mapi_def:
  (mapi f (n: num) [] = []) /\
  (mapi f n (h::t) = (let y = f n h in (y::(mapi f (n + 1) t))))
End -/
def mapi {α : Type u} {β : Type v} (f : Nat → α → β) : Nat → List α → List β
  | _, [] => []
  | n, h :: t => let y := f n h; y :: mapi f (n + 1) t

/- HOL4: Definition partition_aux_def:
  (partition_aux f [] pos neg =
    (REVERSE pos, REVERSE neg)) /\
    (partition_aux f (h::t) pos neg = if f h then partition_aux f t (h::pos) neg
      else partition_aux f t pos (h::neg))
End -/
def partition_aux {α : Type u} (f : α → Prop) : List α → List α → List α → List α × List α
  | [], pos, neg => (REVERSE pos, REVERSE neg)
  | h :: t, pos, neg => if f h then partition_aux f t (h :: pos) neg else partition_aux f t pos (h :: neg)

/- HOL4: Definition partition_def:
  partition (f : 'a -> bool) l = partition_aux f l [] []
End -/
def partition {α : Type u} (f : α → Prop) (l : List α) : List α × List α := partition_aux f l [] []

/- HOL4: Definition foldl_def:
  (foldl f e [] = e) /\
  (foldl f e (h::t) = foldl f (f h e) t)
End -/
def foldl {α : Type u} {β : Type v} (f : α → β → β) : β → List α → β
  | e, [] => e
  | e, h :: t => foldl f (f h e) t

/- HOL4: Definition foldli_aux_def:
  (foldli_aux f e n [] = e) /\
  (foldli_aux f e n (h::t) = foldli_aux f (f n h e) (SUC n) t)
End -/
def foldli_aux {α : Type u} {β : Type v} (f : Nat → α → β → β) : β → Nat → List α → β
  | e, _, [] => e
  | e, n, h :: t => foldli_aux f (f n h e) (n + 1) t

/- HOL4: Definition collate_def:
  (collate f [] [] = EQUAL) /\
  (collate f [] (h::t) = LESS) /\
  (collate f (h::t) [] = GREATER) /\
  (collate f (h1::t1) (h2::t2) =
    if f h1 h2 = EQUAL
      then collate f t1 t2
    else f h1 h2)
End -/
def collate {α : Type u} (f : α → α → Ordering) : List α → List α → Ordering
  | [], [] => EQUAL
  | [], _ :: _ => LESS
  | _ :: _, [] => GREATER
  | h1 :: t1, h2 :: t2 => if f h1 h2 = EQUAL then collate f t1 t2 else f h1 h2

/- HOL4: Definition LENGTH_AUX_def:
  (LENGTH_AUX [] n = (n:num)) /\
  (LENGTH_AUX (x::xs) n = LENGTH_AUX xs (n+1))
End -/
def LENGTH_AUX {α : Type u} : List α → Nat → Nat
  | [], n => n
  | _ :: xs, n => LENGTH_AUX xs (n + 1)

/- HOL4: Definition map_rev'_def:
  map_rev' f [] acc = acc ∧
  map_rev' f (x :: xs) acc = map_rev' f xs (f x :: acc)
End -/
def map_rev' {α : Type u} {β : Type v} (f : α → β) : List α → List β → List β
  | [], acc => acc
  | x :: xs, acc => map_rev' f xs (f x :: acc)

/- HOL4: Definition filter_rev'_def:
  filter_rev' P [] acc = acc ∧
  filter_rev' P (h::t) acc = if P h then filter_rev' P t (h::acc) else filter_rev' P t acc
End -/
def filter_rev' {α : Type u} (P : α → Prop) : List α → List α → List α
  | [], acc => acc
  | h :: t, acc => if P h then filter_rev' P t (h :: acc) else filter_rev' P t acc

/- HOL4: Definition flat_rev'_def:
  flat_rev' [] acc = acc ∧
  flat_rev' (x::xs) acc = flat_rev' xs (REV x acc)
End -/
def flat_rev' {α : Type u} : List (List α) → List α → List α
  | [], acc => acc
  | x :: xs, acc => flat_rev' xs (REV x acc)

/-! ## Target theorems -/

/- HOL4: Theorem merge_tail_MEM:
  !negate R xs ys acc. MEM x (merge_tail negate R xs ys acc) = ((MEM x xs) \/ (MEM x ys) \/ (MEM x acc)) -/
theorem merge_tail_MEM {α : Type u} (x : α) :
    ∀ (negate : Prop) (R : α → α → Prop) (xs ys acc : List α),
      MEM x (merge_tail negate R xs ys acc) = ((MEM x xs) ∨ (MEM x ys) ∨ (MEM x acc)) := by sorry

/- HOL4: Theorem mergesortN_tail_MEM:
  !negate R length lst. (MEM x (mergesortN_tail negate R length lst) <=> MEM x (TAKE length lst)) -/
theorem mergesortN_tail_MEM {α : Type u} (x : α) :
    ∀ (negate : Prop) (R : α → α → Prop) (length : Nat) (lst : List α),
      (MEM x (mergesortN_tail negate R length lst) ↔ MEM x (TAKE length lst)) := by sorry

/- HOL4: Theorem mergesort_tail_MEM:
  ∀R l. MEM x (mergesort$mergesort_tail R l) ⇔ MEM x l -/
theorem mergesort_tail_MEM {α : Type u} (x : α) :
    ∀ (R : α → α → Prop) (l : List α), MEM x (mergesort_tail R l) ↔ MEM x l := by sorry

/- HOL4: Theorem merge_tail_PERM:
  !negate R xs ys acc. PERM (xs++ys++acc) (merge_tail negate R xs ys acc) -/
theorem merge_tail_PERM {α : Type u} :
    ∀ (negate : Prop) (R : α → α → Prop) (xs ys acc : List α),
      PERM (xs ++ ys ++ acc) (merge_tail negate R xs ys acc) := by sorry

/- HOL4: Theorem sort2_tail_PERM:
  !neg R x y. PERM [x;y] (sort2_tail neg R x y) -/
theorem sort2_tail_PERM {α : Type u} :
    ∀ (neg : Prop) (R : α → α → Prop) (x y : α), PERM [x, y] (sort2_tail neg R x y) := by sorry

/- HOL4: Theorem sort3_tail_PERM:
  !neg R x y z. PERM [x;y;z] (sort3_tail neg R x y z) -/
theorem sort3_tail_PERM {α : Type u} :
    ∀ (neg : Prop) (R : α → α → Prop) (x y z : α), PERM [x, y, z] (sort3_tail neg R x y z) := by sorry

/- HOL4: Theorem mergesortN_tail_PERM:
  !neg R len l. PERM (TAKE len l) (mergesortN_tail neg R len l) -/
theorem mergesortN_tail_PERM {α : Type u} :
    ∀ (neg : Prop) (R : α → α → Prop) (len : Nat) (l : List α),
      PERM (TAKE len l) (mergesortN_tail neg R len l) := by sorry

/- HOL4: Theorem sort_MEM[simp]:
  !R L. MEM x (sort R L) ⇔ MEM x L -/
theorem sort_MEM {α : Type u} (x : α) :
    ∀ (R : α → α → Prop) (L : List α), MEM x (sort R L) ↔ MEM x L := by sorry

/- HOL4: Theorem sort_PERM:
  !R L. sorting$PERM L (sort R L) -/
theorem sort_PERM {α : Type u} :
    ∀ (R : α → α → Prop) (L : List α), PERM L (sort R L) := by sorry

/- HOL4: Theorem sort_LENGTH[simp]:
  !R l. LENGTH (sort R l) = LENGTH l -/
theorem sort_LENGTH {α : Type u} :
    ∀ (R : α → α → Prop) (l : List α), LENGTH (sort R l) = LENGTH l := by sorry

/- HOL4: Theorem sort_set[simp]:
  set (sort R ls) = set ls -/
theorem sort_set {α : Type u} (R : α → α → Prop) (ls : List α) :
    LIST_TO_SET (sort R ls) = LIST_TO_SET ls := by sorry

end

end Candle.Mllist
