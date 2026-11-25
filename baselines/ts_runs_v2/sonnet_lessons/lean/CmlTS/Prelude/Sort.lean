import CmlTS.Prelude.Num

/-!
# HOL4 library prelude: `mergesort` (only the tail-recursive variant used by `mllist`)
-/

universe u v w

noncomputable section

open Classical

/- HOL4: mergesort theory, `sort2_tail neg R x y = if R x y <> neg then [x;y] else [y;x]` -/
def sort2_tail {α : Type u} (neg : Prop) (R : α → α → Prop) (x y : α) : List α :=
  if R x y ≠ neg then [x, y] else [y, x]

/- HOL4: mergesort theory, `sort3_tail` -/
def sort3_tail {α : Type u} (neg : Prop) (R : α → α → Prop) (x y z : α) : List α :=
  if R x y ≠ neg then
    if R y z ≠ neg then [x, y, z]
    else if R x z ≠ neg then [x, z, y]
    else [z, x, y]
  else if R y z ≠ neg then
    if R x z ≠ neg then [y, x, z]
    else [y, z, x]
  else [z, y, x]

/- HOL4: mergesort theory,
   `merge_tail negate R [] [] acc = acc`, `merge_tail negate R l [] acc = REV l acc`,
   `merge_tail negate R [] l acc = REV l acc`,
   `merge_tail negate R (x::l1) (y::l2) acc =
      if R x y <> negate then merge_tail negate R l1 (y::l2) (x::acc)
      else merge_tail negate R (x::l1) l2 (y::acc)` -/
def merge_tail {α : Type u} (negate : Prop) (R : α → α → Prop) :
    List α → List α → List α → List α
  | [], [], acc => acc
  | l, [], acc => REV l acc
  | [], l, acc => REV l acc
  | x :: l1, y :: l2, acc =>
    if R x y ≠ negate then merge_tail negate R l1 (y :: l2) (x :: acc)
    else merge_tail negate R (x :: l1) l2 (y :: acc)
termination_by l1 l2 _ => l1.length + l2.length
decreasing_by
  all_goals simp_wf
  all_goals omega

/- HOL4: mergesort theory,
   `mergesortN_tail negate R 0 l = []`, `mergesortN_tail negate R 1 (x::l) = [x]`,
   `mergesortN_tail negate R 1 [] = []`, `mergesortN_tail negate R 2 (x::y::l) = sort2_tail negate R x y`,
   `mergesortN_tail negate R 2 [x] = [x]`, `mergesortN_tail negate R 2 [] = []`,
   `mergesortN_tail negate R 3 (x::y::z::l) = sort3_tail negate R x y z`,
   `mergesortN_tail negate R 3 [x;y] = sort2_tail negate R x y`,
   `mergesortN_tail negate R 3 [x] = [x]`, `mergesortN_tail negate R 3 [] = []`,
   `mergesortN_tail negate R n l =
      let len1 = DIV2 n in let neg = ~negate in
      merge_tail neg R (mergesortN_tail neg R (DIV2 n) l)
                       (mergesortN_tail neg R (n - len1) (DROP len1 l)) []`
   (the last clause only applies for `n >= 4`; in Lean it is written for `n + 4`). -/
def mergesortN_tail {α : Type u} (R : α → α → Prop) : Prop → Nat → List α → List α
  | _, 0, _ => []
  | _, 1, x :: _ => [x]
  | _, 1, [] => []
  | negate, 2, x :: y :: _ => sort2_tail negate R x y
  | _, 2, [x] => [x]
  | _, 2, [] => []
  | negate, 3, x :: y :: z :: _ => sort3_tail negate R x y z
  | negate, 3, [x, y] => sort2_tail negate R x y
  | _, 3, [x] => [x]
  | _, 3, [] => []
  | negate, n + 4, l =>
    let len1 := DIV2 (n + 4)
    let neg := ¬ negate
    merge_tail neg R (mergesortN_tail R neg (DIV2 (n + 4)) l)
      (mergesortN_tail R neg (n + 4 - len1) (DROP len1 l)) []
termination_by _ n _ => n
decreasing_by
  all_goals simp_wf
  all_goals unfold DIV2
  all_goals omega

/- HOL4: mergesort theory, `mergesort_tail R l = mergesortN_tail F R (LENGTH l) l` -/
def mergesort_tail {α : Type u} (R : α → α → Prop) (l : List α) : List α :=
  mergesortN_tail R False l.length l

end
