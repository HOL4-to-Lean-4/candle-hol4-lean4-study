/-
  HOL4 library constants: mergesort (the tail-recursive merge sort).
  HOL `bool` arguments (`negate`) are `Prop`.
-/
import CandleLean.Prelude.List

namespace Candle

noncomputable section
open Classical

/- HOL4: mergesort$sort2_tail_def
   |- sort2_tail neg R x y = if R x y <> neg then [x; y] else [y; x] -/
def sort2_tail {α : Type} (neg : Prop) (R : α → α → Prop) (x y : α) : List α :=
  if R x y ≠ neg then [x, y] else [y, x]

/- HOL4: mergesort$sort3_tail_def
   |- sort3_tail neg R x y z =
        if R x y <> neg then
          if R y z <> neg then [x; y; z]
          else if R x z <> neg then [x; z; y]
          else [z; x; y]
        else if R y z <> neg then
          if R x z <> neg then [y; x; z] else [y; z; x]
        else [z; y; x] -/
def sort3_tail {α : Type} (neg : Prop) (R : α → α → Prop) (x y z : α) : List α :=
  if R x y ≠ neg then
    if R y z ≠ neg then [x, y, z]
    else if R x z ≠ neg then [x, z, y]
    else [z, x, y]
  else if R y z ≠ neg then
    if R x z ≠ neg then [y, x, z] else [y, z, x]
  else [z, y, x]

/- HOL4: mergesort$merge_tail_def
   |- (merge_tail negate R [] [] acc = acc) /\
      (merge_tail negate R l [] acc = REV l acc) /\
      (merge_tail negate R [] l acc = REV l acc) /\
      (merge_tail negate R (x::l1) (y::l2) acc =
         if R x y <> negate then merge_tail negate R l1 (y::l2) (x::acc)
         else merge_tail negate R (x::l1) l2 (y::acc)) -/
def merge_tail {α : Type} (negate : Prop) (R : α → α → Prop) :
    List α → List α → List α → List α
  | [], [], acc => acc
  | l, [], acc => REV l acc
  | [], l, acc => REV l acc
  | x :: l1, y :: l2, acc =>
    if R x y ≠ negate then merge_tail negate R l1 (y :: l2) (x :: acc)
    else merge_tail negate R (x :: l1) l2 (y :: acc)
termination_by l1 l2 _ => l1.length + l2.length

/- HOL4: mergesort$mergesortN_tail_def
   |- (mergesortN_tail negate R 0 l = []) /\
      (mergesortN_tail negate R 1 (x::l) = [x]) /\
      (mergesortN_tail negate R 1 [] = []) /\
      (mergesortN_tail negate R 2 (x::y::l) = sort2_tail negate R x y) /\
      (mergesortN_tail negate R 2 [x] = [x]) /\
      (mergesortN_tail negate R 2 [] = []) /\
      (mergesortN_tail negate R 3 (x::y::z::l) = sort3_tail negate R x y z) /\
      (mergesortN_tail negate R 3 [x; y] = sort2_tail negate R x y) /\
      (mergesortN_tail negate R 3 [x] = [x]) /\
      (mergesortN_tail negate R 3 [] = []) /\
      (mergesortN_tail negate R n l =
         let len1 = DIV2 n in
         let neg = ~negate in
           merge_tail neg R (mergesortN_tail neg R (DIV2 n) l)
                            (mergesortN_tail neg R (n - len1) (DROP len1 l)) [])
   (the last clause applies exactly when `n >= 4`) -/
def mergesortN_tail {α : Type} (negate : Prop) (R : α → α → Prop) :
    Nat → List α → List α
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
termination_by n _ => n
decreasing_by
  all_goals simp only [DIV2]
  all_goals omega

/- HOL4: mergesort$mergesort_tail_def
   |- mergesort_tail R l = mergesortN_tail F R (LENGTH l) l -/
def mergesort_tail {α : Type} (R : α → α → Prop) (l : List α) : List α :=
  mergesortN_tail False R (LENGTH l) l

end

end Candle
