import CmlTS.Prelude.ListLib

/-
HOL4 library constants from `mergesort`.
-/

namespace CmlTS

noncomputable section

open scoped Classical

variable {α : Type}

/- HOL4: mergesort$sort2_tail
   sort2_tail (neg:bool) R x y = if R x y <> neg then [x;y] else [y;x]
   (`R x y` is a proposition here, so `R x y <> neg` is `¬ (R x y ↔ neg = true)`) -/
def sort2_tail (neg : Bool) (R : α → α → Prop) (x y : α) : List α :=
  if ¬ (R x y ↔ neg = true) then [x, y] else [y, x]

/- HOL4: mergesort$sort3_tail
   sort3_tail (neg:bool) R x y z =
     if R x y <> neg then
       if R y z <> neg then [x;y;z]
       else if R x z <> neg then [x;z;y]
       else [z;x;y]
     else if R y z <> neg then
       if R x z <> neg then [y;x;z] else [y;z;x]
     else [z;y;x] -/
def sort3_tail (neg : Bool) (R : α → α → Prop) (x y z : α) : List α :=
  if ¬ (R x y ↔ neg = true) then
    if ¬ (R y z ↔ neg = true) then [x, y, z]
    else if ¬ (R x z ↔ neg = true) then [x, z, y]
    else [z, x, y]
  else if ¬ (R y z ↔ neg = true) then
    if ¬ (R x z ↔ neg = true) then [y, x, z] else [y, z, x]
  else [z, y, x]

/- HOL4: mergesort$merge_tail
   (merge_tail (negate:bool) R [] [] acc = acc) /\
   (merge_tail negate R l [] acc = REV l acc) /\
   (merge_tail negate R [] l acc = REV l acc) /\
   (merge_tail negate R (x::l1) (y::l2) acc =
     if R x y <> negate then merge_tail negate R l1 (y::l2) (x::acc)
     else merge_tail negate R (x::l1) l2 (y::acc)) -/
def merge_tail (negate : Bool) (R : α → α → Prop) : List α → List α → List α → List α
  | [], [], acc => acc
  | l, [], acc => REV l acc
  | [], l, acc => REV l acc
  | x :: l1, y :: l2, acc =>
    if ¬ (R x y ↔ negate = true) then merge_tail negate R l1 (y :: l2) (x :: acc)
    else merge_tail negate R (x :: l1) l2 (y :: acc)
termination_by l1 l2 _ => l1.length + l2.length

/- HOL4: mergesort$mergesortN_tail
   (mergesortN_tail (negate :bool) R 0 l = []) /\
   (mergesortN_tail negate R 1 (x::l) = [x]) /\
   (mergesortN_tail negate R 1 [] = []) /\
   (mergesortN_tail negate R 2 (x::y::l) = sort2_tail negate R x y) /\
   (mergesortN_tail negate R 2 [x] = [x]) /\
   (mergesortN_tail negate R 2 [] = []) /\
   (mergesortN_tail negate R 3 (x::y::z::l) = sort3_tail negate R x y z) /\
   (mergesortN_tail negate R 3 [x;y] = sort2_tail negate R x y) /\
   (mergesortN_tail negate R 3 [x] = [x]) /\
   (mergesortN_tail negate R 3 [] = []) /\
   (mergesortN_tail negate R n l =
     let len1 = DIV2 n in
     let neg = ~negate in
       merge_tail neg R (mergesortN_tail neg R (DIV2 n) l)
                        (mergesortN_tail neg R (n - len1) (DROP len1 l))
                        [])
   (the last equation applies to n >= 4, written `n + 4` here) -/
def mergesortN_tail (negate : Bool) (R : α → α → Prop) : Nat → List α → List α
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
    let len1 := (n + 4) / 2
    let neg := !negate
    merge_tail neg R (mergesortN_tail neg R ((n + 4) / 2) l)
      (mergesortN_tail neg R (n + 4 - len1) (l.drop len1)) []
termination_by n _ => n
decreasing_by
  all_goals omega

/- HOL4: mergesort$mergesort_tail
   mergesort_tail R l = mergesortN_tail F R (LENGTH l) l -/
def mergesort_tail (R : α → α → Prop) (l : List α) : List α :=
  mergesortN_tail false R l.length l

end

end CmlTS
