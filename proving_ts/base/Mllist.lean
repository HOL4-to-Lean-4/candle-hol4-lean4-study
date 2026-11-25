import CmlTS.Prelude.Mergesort

/-
HOL4 theory `mllist` (mllistScript.sml).  All names are in `CmlTS.mllist`
(HOL4 `mllist$sort`, `mllist$nth`, `mllist$collate`).
-/

namespace CmlTS.mllist

noncomputable section

open scoped Classical

variable {α β : Type}

/- HOL4:
Definition sort_def:
  sort = mergesort$mergesort_tail
End -/
def sort : (α → α → Prop) → List α → List α := mergesort_tail

/- HOL4:
Definition nth_def:
  nth l i = EL i l
End -/
def nth [Nonempty α] (l : List α) (i : Nat) : α := EL i l

/- HOL4:
Definition collate_def:
  (collate f [] [] = EQUAL) /\
  (collate f [] (h::t) = LESS) /\
  (collate f (h::t) [] = GREATER) /\
  (collate f (h1::t1) (h2::t2) =
    if f h1 h2 = EQUAL
      then collate f t1 t2
    else f h1 h2)
End -/
def collate (f : α → β → ordering) : List α → List β → ordering
  | [], [] => ordering.EQUAL
  | [], _ :: _ => ordering.LESS
  | _ :: _, [] => ordering.GREATER
  | h1 :: t1, h2 :: t2 => if f h1 h2 = ordering.EQUAL then collate f t1 t2 else f h1 h2

end

end CmlTS.mllist
