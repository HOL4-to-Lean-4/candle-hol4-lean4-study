import CmlTS.Misc
import CmlTS.Prelude.Mergesort
/-
  Translation of HOL4 theory `mllist` (mllistScript.sml).
-/
set_option autoImplicit false

namespace CmlTS

universe u

/- HOL4:
Definition sort_def:
  sort = mergesort$mergesort_tail
End -/
noncomputable def sort {α : Type u} : (α → α → Prop) → List α → List α := mergesort_tail

/- HOL4:
Definition nth_def:
  nth l i = EL i l
End -/
noncomputable def nth {α : Type u} [Nonempty α] (l : List α) (i : Nat) : α := EL i l

/- HOL4:
Definition collate_def:
  (collate f [] [] = EQUAL) /\
  (collate f [] (h::t) = LESS) /\
  (collate f (h::t) [] = GREATER) /\
  (collate f (h1::t1) (h2::t2) =
    if f h1 h2 = EQUAL
      then collate f t1 t2
    else f h1 h2)
End
   (Lean name `mllist_collate`: the HOL4 theory mlstring has another `collate`) -/
def mllist_collate {α : Type u} (f : α → α → ordering) : List α → List α → ordering
  | [], [] => EQUAL
  | [], _ :: _ => LESS
  | _ :: _, [] => GREATER
  | h1 :: t1, h2 :: t2 =>
    if f h1 h2 = EQUAL then mllist_collate f t1 t2
    else f h1 h2

end CmlTS
