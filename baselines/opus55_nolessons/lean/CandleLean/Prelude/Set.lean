/-
  HOL4 library constants from the theory `pred_set` (sets as predicates).
-/
import CandleLean.Prelude.Basic

open Classical

/- HOL4: pred_set type `'a set` = `'a -> bool` -/
def Set (α : Type u) : Type u := α → Prop

/- HOL4: bool$IN   `x IN s = s x`  (Lean notation `x ∈ s`, `x ∉ s`) -/
instance {α : Type u} : Membership α (Set α) := ⟨fun s x => s x⟩

/- HOL4: pred_set$GSPEC (new_specification GSPECIFICATION)
   `!f v. v IN GSPEC f <=> ?x. (v,T) = f x`
   Set comprehension `{ t | P }` is `GSPEC (\x. (t, P))`.  GSPEC is uniquely
   determined by its specification, so we define it directly. -/
def GSPEC {α : Type u} {β : Sort v} (f : β → α × Prop) : Set α := fun v => ∃ x, (v, True) = f x

/-- Set comprehension `{ x | P x }` (HOL4 `{x | P x}` = `GSPEC (\x. (x, P x))`). -/
syntax "{" ident " | " term "}" : term
/-- Set comprehension `{ (x, y) | P x y }` (HOL4 `{(x,y) | P}` = `GSPEC (\(x,y). ((x,y), P))`). -/
syntax "{" "(" ident ", " ident ")" " | " term "}" : term
macro_rules
  | `({ $x:ident | $p }) => `(GSPEC (fun $x:ident => ($x, $p)))
  | `({ ($x:ident, $y:ident) | $p }) => `(GSPEC (fun ($x, $y) => (($x, $y), $p)))

/- HOL4: pred_set$EMPTY   `EMPTY = (\x:'a.F)` -/
def EMPTY {α : Type u} : Set α := fun _ => False

/- HOL4: pred_set$UNIV   `UNIV = (\x:'a.T)` -/
def UNIV {α : Type u} : Set α := fun _ => True

/- HOL4: pred_set$INSERT   `INSERT (x:'a) s = {y | (y = x) \/ y IN s}` -/
def INSERT {α : Type u} (x : α) (s : Set α) : Set α := {y | y = x ∨ y ∈ s}

/- HOL4: pred_set$UNION   `UNION s t = {x:'a | x IN s \/ x IN t}` -/
def UNION {α : Type u} (s t : Set α) : Set α := {x | x ∈ s ∨ x ∈ t}

/- HOL4: pred_set$INTER   `INTER s t = {x:'a | x IN s /\ x IN t}` -/
def INTER {α : Type u} (s t : Set α) : Set α := {x | x ∈ s ∧ x ∈ t}

/- HOL4: pred_set$SUBSET   `$SUBSET s t = !x:'a. x IN s ==> x IN t` -/
def SUBSET {α : Type u} (s t : Set α) : Prop := ∀ x, x ∈ s → x ∈ t

/- HOL4: pred_set$DISJOINT   `DISJOINT (s:'a set) t = ((s INTER t) = EMPTY)` -/
def DISJOINT {α : Type u} (s t : Set α) : Prop := INTER s t = EMPTY

/- HOL4: pred_set$IMAGE   `IMAGE (f:'a->'b) s = {f x | x IN s}` -/
def IMAGE {α : Type u} {β : Type v} (f : α → β) (s : Set α) : Set β :=
  GSPEC (fun x => (f x, x ∈ s))

/- HOL4: pred_set$FINITE
   `!s:'a set. FINITE s = !P. P EMPTY /\ (!s. P s ==> !e. P (e INSERT s)) ==> P s` -/
def FINITE {α : Type u} (s : Set α) : Prop :=
  ∀ P : Set α → Prop, P EMPTY ∧ (∀ s, P s → ∀ e, P (INSERT e s)) → P s

/- HOL4: pred_set$INFINITE   `Overload INFINITE = ``\s. ~FINITE s``` -/
abbrev INFINITE {α : Type u} (s : Set α) : Prop := ¬ FINITE s

/- HOL4: pred_set$INJ
   `INJ (f:'a->'b) s t <=> (!x. x IN s ==> (f x) IN t) /\
                           (!x y. (x IN s /\ y IN s) ==> (f x = f y) ==> (x = y))` -/
def INJ {α : Type u} {β : Type v} (f : α → β) (s : Set α) (t : Set β) : Prop :=
  (∀ x, x ∈ s → f x ∈ t) ∧ (∀ x y, (x ∈ s ∧ y ∈ s) → f x = f y → x = y)

/- HOL4: pred_set$SURJ
   `SURJ (f:'a->'b) s t <=> (!x. x IN s ==> (f x) IN t) /\
                            (!x. (x IN t) ==> ?y. y IN s /\ (f y = x))` -/
def SURJ {α : Type u} {β : Type v} (f : α → β) (s : Set α) (t : Set β) : Prop :=
  (∀ x, x ∈ s → f x ∈ t) ∧ (∀ x, x ∈ t → ∃ y, y ∈ s ∧ f y = x)

/- HOL4: pred_set$BIJ   `BIJ (f:'a->'b) s t <=> INJ f s t /\ SURJ f s t` -/
def BIJ {α : Type u} {β : Type v} (f : α → β) (s : Set α) (t : Set β) : Prop :=
  INJ f s t ∧ SURJ f s t

/- HOL4: pred_set$PERMUTES   `Overload PERMUTES = ``\f s. BIJ f s s``` -/
abbrev PERMUTES {α : Type u} (f : α → α) (s : Set α) : Prop := BIJ f s s

/-! Lean notation for the HOL4 set operations:
  `∅` = EMPTY, `{a}` = `a INSERT EMPTY`, `{a, b}` = `a INSERT b INSERT EMPTY`,
  `s ∪ t` = UNION, `s ∩ t` = INTER. -/
instance {α : Type u} : EmptyCollection (Set α) := ⟨EMPTY⟩
instance {α : Type u} : Insert α (Set α) := ⟨INSERT⟩
instance {α : Type u} : Singleton α (Set α) := ⟨fun a => INSERT a EMPTY⟩
instance {α : Type u} : Union (Set α) := ⟨UNION⟩
instance {α : Type u} : Inter (Set α) := ⟨INTER⟩
