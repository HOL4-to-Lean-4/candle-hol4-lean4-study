import CandleLean.Prelude.String
/-
  HOL4 library constants, part 5: mergesortTheory (tail-recursive mergesort).
  `bool` arguments (`negate`) are Lean `Prop`; `R x y <> neg` is `¬ (R x y ↔ neg)`.
-/
namespace HOL

universe u

open Classical

noncomputable section

variable {α : Type u}

/- HOL4: mergesortTheory sort2_tail_def:
   sort2_tail neg R x y = if R x y <> neg then [x;y] else [y;x] -/
def sort2_tail (neg : Prop) (R : α → α → Prop) (x y : α) : List α :=
  if ¬ (R x y ↔ neg) then [x, y] else [y, x]

/- HOL4: mergesortTheory sort3_tail_def -/
def sort3_tail (neg : Prop) (R : α → α → Prop) (x y z : α) : List α :=
  if ¬ (R x y ↔ neg) then
    if ¬ (R y z ↔ neg) then [x, y, z]
    else if ¬ (R x z ↔ neg) then [x, z, y]
    else [z, x, y]
  else if ¬ (R y z ↔ neg) then
    if ¬ (R x z ↔ neg) then [y, x, z]
    else [y, z, x]
  else [z, y, x]

/- HOL4: mergesortTheory merge_tail_def:
   merge_tail negate R [] [] acc = acc
   merge_tail negate R l [] acc = REV l acc
   merge_tail negate R [] l acc = REV l acc
   merge_tail negate R (x::l1) (y::l2) acc =
     if R x y <> negate then merge_tail negate R l1 (y::l2) (x::acc)
     else merge_tail negate R (x::l1) l2 (y::acc) -/
def merge_tail (negate : Prop) (R : α → α → Prop) (xs ys acc : List α) : List α :=
  match xs, ys, acc with
  | [], [], acc => acc
  | x :: l, [], acc => REV (x :: l) acc
  | [], y :: l, acc => REV (y :: l) acc
  | x :: l1, y :: l2, acc =>
    if ¬ (R x y ↔ negate) then merge_tail negate R l1 (y :: l2) (x :: acc)
    else merge_tail negate R (x :: l1) l2 (y :: acc)
termination_by xs.length + ys.length

/- HOL4: mergesortTheory mergesortN_tail_def (the HOL4 clauses overlap; the last clause
   applies exactly when n >= 4, all smaller n being covered by earlier clauses):
   mergesortN_tail negate R 0 l = []
   mergesortN_tail negate R 1 (x::l) = [x]        mergesortN_tail negate R 1 [] = []
   mergesortN_tail negate R 2 (x::y::l) = sort2_tail negate R x y
   mergesortN_tail negate R 2 [x] = [x]           mergesortN_tail negate R 2 [] = []
   mergesortN_tail negate R 3 (x::y::z::l) = sort3_tail negate R x y z
   mergesortN_tail negate R 3 [x;y] = sort2_tail negate R x y
   mergesortN_tail negate R 3 [x] = [x]           mergesortN_tail negate R 3 [] = []
   mergesortN_tail negate R n l =
     let len1 = DIV2 n in let neg = ~negate in
     merge_tail neg R (mergesortN_tail neg R (DIV2 n) l)
                      (mergesortN_tail neg R (n - len1) (DROP len1 l)) [] -/
def mergesortN_tail (negate : Prop) (R : α → α → Prop) (n : Nat) (l : List α) : List α :=
  match n, l with
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
      (mergesortN_tail neg R (n + 4 - len1) (DROP len1 l)) []
termination_by n
decreasing_by
  all_goals simp_wf
  all_goals (unfold DIV2; omega)

/- HOL4: mergesortTheory mergesort_tail_def: mergesort_tail R l = mergesortN_tail F R (LENGTH l) l -/
def mergesort_tail (R : α → α → Prop) (l : List α) : List α :=
  mergesortN_tail False R (LENGTH l) l

end

end HOL
