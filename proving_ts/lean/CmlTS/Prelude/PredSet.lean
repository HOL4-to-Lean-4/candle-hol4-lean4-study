import CmlTS.Prelude.Core

/-
HOL4 library constants from `pred_set` (and `LIST_TO_SET` of `list`).
A HOL4 set is a predicate; so is a Lean one here.
-/

namespace CmlTS

noncomputable section

open scoped Classical

variable {α β : Type}

/- HOL4: pred_set, Type set = ``:'a -> bool`` -/
def Set (α : Type) : Type := α → Prop

/- HOL4: set comprehension `{x | P x}` (pred_set$GSPEC) -/
def setOf (P : α → Prop) : Set α := P

/- HOL4: bool$IN   x IN s = s x -/
instance : Membership α (Set α) := ⟨fun s x => s x⟩

instance : Nonempty (Set α) := ⟨fun _ => False⟩

/- HOL4: pred_set$EMPTY   EMPTY = \x. F -/
def EMPTY : Set α := fun _ => False

instance : EmptyCollection (Set α) := ⟨EMPTY⟩

/- HOL4: pred_set$UNIV   UNIV = \x. T -/
def UNIV : Set α := fun _ => True

/- HOL4: pred_set$INSERT   x INSERT s = {y | (y = x) \/ y IN s} -/
def INSERT (x : α) (s : Set α) : Set α := setOf fun y => y = x ∨ y ∈ s

instance : Insert α (Set α) := ⟨INSERT⟩

/- HOL4: the enumeration `{x}`, i.e. `x INSERT EMPTY` -/
instance : Singleton α (Set α) := ⟨fun x => INSERT x EMPTY⟩

/- HOL4: pred_set$SUBSET   s SUBSET t = !x. x IN s ==> x IN t -/
def SUBSET (s t : Set α) : Prop := ∀ x, x ∈ s → x ∈ t

instance : HasSubset (Set α) := ⟨SUBSET⟩

/- HOL4: pred_set$UNION   s UNION t = {x | x IN s \/ x IN t} -/
def UNION (s t : Set α) : Set α := setOf fun x => x ∈ s ∨ x ∈ t

instance : Union (Set α) := ⟨UNION⟩

/- HOL4: pred_set$INTER   s INTER t = {x | x IN s /\ x IN t} -/
def INTER (s t : Set α) : Set α := setOf fun x => x ∈ s ∧ x ∈ t

instance : Inter (Set α) := ⟨INTER⟩

/- HOL4: pred_set$DIFF   s DIFF t = {x | x IN s /\ ~(x IN t)} -/
def DIFF (s t : Set α) : Set α := setOf fun x => x ∈ s ∧ ¬ x ∈ t

instance : SDiff (Set α) := ⟨DIFF⟩

/- HOL4: pred_set$DISJOINT   DISJOINT s t = ((s INTER t) = EMPTY) -/
def DISJOINT (s t : Set α) : Prop := s ∩ t = ∅

/- HOL4: pred_set$IMAGE   IMAGE f s = {f x | x IN s} -/
def IMAGE (f : α → β) (s : Set α) : Set β := setOf fun y => ∃ x, y = f x ∧ x ∈ s

/- HOL4: pred_set$INJ
   INJ f s t <=> (!x. x IN s ==> (f x) IN t) /\
                 (!x y. (x IN s /\ y IN s) ==> (f x = f y) ==> (x = y)) -/
def INJ (f : α → β) (s : Set α) (t : Set β) : Prop :=
  (∀ x, x ∈ s → f x ∈ t) ∧ (∀ x y, x ∈ s ∧ y ∈ s → f x = f y → x = y)

/- HOL4: pred_set$SURJ
   SURJ f s t <=> (!x. x IN s ==> (f x) IN t) /\
                  (!x. (x IN t) ==> ?y. y IN s /\ (f y = x)) -/
def SURJ (f : α → β) (s : Set α) (t : Set β) : Prop :=
  (∀ x, x ∈ s → f x ∈ t) ∧ (∀ x, x ∈ t → ∃ y, y ∈ s ∧ f y = x)

/- HOL4: pred_set$BIJ   BIJ f s t <=> INJ f s t /\ SURJ f s t -/
def BIJ (f : α → β) (s : Set α) (t : Set β) : Prop := INJ f s t ∧ SURJ f s t

/- HOL4: pred_set$FINITE
   FINITE s = !P. P EMPTY /\ (!s. P s ==> !e. P (e INSERT s)) ==> P s -/
def FINITE (s : Set α) : Prop :=
  ∀ P : Set α → Prop, (P ∅ ∧ ∀ s, P s → ∀ e, P (insert e s)) → P s

/- HOL4: pred_set$CARD, the specification
     (CARD EMPTY = 0) /\
     (!s. FINITE s ==>
        !x. CARD (x INSERT s) = (if x IN s then CARD s else SUC (CARD s)))
   CARD of an infinite set is unspecified.  Here: the length of a
   duplicate-free list enumerating the set, chosen with Hilbert choice. -/
def CARD (s : Set α) : Nat :=
  select fun n => ∃ l : List α, l.Nodup ∧ l.length = n ∧ ∀ x, x ∈ l ↔ x ∈ s

/- HOL4: pred_set$BIGUNION   BIGUNION P = { x | ?s. s IN P /\ x IN s} -/
def BIGUNION (P : Set (Set α)) : Set α := setOf fun x => ∃ s, s ∈ P ∧ x ∈ s

/- HOL4: list$LIST_TO_SET (overloaded as `set`)
   LIST_TO_SET [] = {} /\ LIST_TO_SET (h::t) = h INSERT LIST_TO_SET t.
   `MEM x l` is HOL4's abbreviation for `x IN LIST_TO_SET l`. -/
def LIST_TO_SET (l : List α) : Set α := setOf fun x => x ∈ l

end

end CmlTS
