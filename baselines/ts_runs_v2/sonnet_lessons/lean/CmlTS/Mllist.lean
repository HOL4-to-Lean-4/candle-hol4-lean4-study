import CmlTS.Misc

/-!
# mllist (HOL4 theory `mllist`): pure functions for the List module
-/

universe u v w

noncomputable section

open Classical

/- HOL4:
   Definition sort_def:
     sort = mergesort$mergesort_tail
   End -/
def sort {α : Type u} : (α → α → Prop) → List α → List α := mergesort_tail

/- HOL4:
   Definition nth_def:
     nth l i = EL i l
   End -/
def nth {α : Type u} [Nonempty α] (l : List α) (i : Nat) : α := EL i l

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
   (Lean name `mllist.collate`, to distinguish it from `mlstring.collate`) -/
def mllist.collate {α : Type u} {β : Type v} (f : α → β → ordering) :
    List α → List β → ordering
  | [], [] => .EQUAL
  | [], _ :: _ => .LESS
  | _ :: _, [] => .GREATER
  | h1 :: t1, h2 :: t2 => if f h1 h2 = .EQUAL then mllist.collate f t1 t2 else f h1 h2

end
