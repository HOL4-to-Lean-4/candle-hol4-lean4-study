/-
  HOL4 library constants: `bool`, `combin`, `pair`, `relation`, `pred_set`.
-/
set_option autoImplicit false

namespace CmlTS
open Classical

universe u v w

/- HOL4: bool$ARB : 'a   (an unspecified value of every type)
   All HOL4 types are nonempty, so the Lean version asks for `Nonempty α`. -/
noncomputable def ARB {α : Type u} [Nonempty α] : α := Classical.choice inferInstance

/- HOL4: min$@ (Hilbert choice).  `@x. P x` is `SELECT P`. -/
noncomputable def SELECT {α : Type u} [Nonempty α] (P : α → Prop) : α := Classical.epsilon P

/- HOL4: combin$K:  K x y = x -/
def K {α : Type u} {β : Type v} (x : α) (_y : β) : α := x

/- HOL4: combin$I:  I x = x -/
abbrev I {α : Type u} (x : α) : α := x

/- HOL4: combin$C:  C = \f x y. f y x -/
def C {α : Type u} {β : Type v} {γ : Type w} (f : α → β → γ) (x : β) (y : α) : γ := f y x

/- HOL4: combin$UPDATE:  UPDATE a b = \f c. if a = c then b else f c -/
noncomputable def UPDATE {α : Type u} {β : Type v} (a : α) (b : β) (f : α → β) (c : α) : β :=
  if a = c then b else f c

/- HOL4: pair$UNCURRY:  UNCURRY f v = f (FST v) (SND v) -/
def UNCURRY {α : Type u} {β : Type v} {γ : Type w} (f : α → β → γ) (p : α × β) : γ := f p.1 p.2

/- HOL4: relation$RTC
   Inductive RTC:
     (!x. RTC R x x) /\ (!x y z. R x y /\ RTC R y z ==> RTC R x z)
   End -/
inductive RTC {α : Type u} (R : α → α → Prop) : α → α → Prop
  | refl (x : α) : RTC R x x
  | step (x y z : α) : R x y → RTC R y z → RTC R x z

/- HOL4: 'a set = 'a -> bool -/
def Set (α : Type u) : Type u := α → Prop

namespace Set
variable {α : Type u}

/-- Set comprehension: HOL4 `{x | P x}` (GSPEC). -/
def of (P : α → Prop) : Set α := P

/- HOL4: bool$IN:  x IN s = s x -/
instance : Membership α (Set α) := ⟨fun s x => s x⟩

/- HOL4: pred_set$EMPTY:  EMPTY = \x. F -/
instance : EmptyCollection (Set α) := ⟨fun _ => False⟩

/- HOL4: pred_set$UNION:  s UNION t = {x | x IN s \/ x IN t} -/
instance : Union (Set α) := ⟨fun s t x => x ∈ s ∨ x ∈ t⟩

/- HOL4: pred_set$INTER:  s INTER t = {x | x IN s /\ x IN t} -/
instance : Inter (Set α) := ⟨fun s t x => x ∈ s ∧ x ∈ t⟩

/- HOL4: pred_set$DIFF:  s DIFF t = {x | x IN s /\ ~(x IN t)} -/
instance : SDiff (Set α) := ⟨fun s t x => x ∈ s ∧ ¬ x ∈ t⟩

/- HOL4: pred_set$INSERT:  x INSERT s = {y | (y = x) \/ y IN s} -/
instance : Insert α (Set α) := ⟨fun a s x => x = a ∨ x ∈ s⟩

/- HOL4: {x}  (x INSERT EMPTY) -/
instance : Singleton α (Set α) := ⟨fun a x => x = a⟩

/- HOL4: pred_set$SUBSET:  s SUBSET t = !x. x IN s ==> x IN t -/
instance : HasSubset (Set α) := ⟨fun s t => ∀ x, x ∈ s → x ∈ t⟩

instance : Inhabited (Set α) := ⟨∅⟩

/-- Two sets with the same members are equal (HOL4 `EXTENSION`). -/
theorem ext {s t : Set α} (h : ∀ x, x ∈ s ↔ x ∈ t) : s = t :=
  funext fun x => propext (h x)

/-- `{x | P x}` notation for `CmlTS.Set`. -/
syntax (name := setBuilder) "{" ident (" : " term)? " | " term "}" : term
macro_rules
  | `({$x:ident | $p}) => `(Set.of fun $x:ident => $p)
  | `({$x:ident : $t | $p}) => `(Set.of fun ($x:ident : $t) => $p)

theorem mem_of {P : α → Prop} {x : α} : x ∈ Set.of P ↔ P x := Iff.rfl

end Set

/- HOL4: pred_set$UNIV:  UNIV = \x. T -/
def UNIV {α : Type u} : Set α := fun _ => True

/- HOL4: pred_set$DISJOINT:  DISJOINT s t = ((s INTER t) = EMPTY) -/
def DISJOINT {α : Type u} (s t : Set α) : Prop := s ∩ t = ∅

/- HOL4: pred_set$IMAGE:  IMAGE f s = {f x | x IN s} -/
def IMAGE {α : Type u} {β : Type v} (f : α → β) (s : Set α) : Set β :=
  {y | ∃ x, y = f x ∧ x ∈ s}

/- HOL4: pred_set$BIGUNION:  BIGUNION P = { x | ?s. s IN P /\ x IN s} -/
def BIGUNION {α : Type u} (P : Set (Set α)) : Set α :=
  {x | ∃ s, s ∈ P ∧ x ∈ s}

/- HOL4: pred_set$INJ:
   INJ f s t <=> (!x. x IN s ==> (f x) IN t) /\
                 (!x y. (x IN s /\ y IN s) ==> (f x = f y) ==> (x = y)) -/
def INJ {α : Type u} {β : Type v} (f : α → β) (s : Set α) (t : Set β) : Prop :=
  (∀ x, x ∈ s → f x ∈ t) ∧ (∀ x y, x ∈ s ∧ y ∈ s → f x = f y → x = y)

/- HOL4: pred_set$SURJ:
   SURJ f s t <=> (!x. x IN s ==> (f x) IN t) /\
                  (!x. (x IN t) ==> ?y. y IN s /\ (f y = x)) -/
def SURJ {α : Type u} {β : Type v} (f : α → β) (s : Set α) (t : Set β) : Prop :=
  (∀ x, x ∈ s → f x ∈ t) ∧ (∀ x, x ∈ t → ∃ y, y ∈ s ∧ f y = x)

/- HOL4: pred_set$BIJ:  BIJ f s t <=> INJ f s t /\ SURJ f s t -/
def BIJ {α : Type u} {β : Type v} (f : α → β) (s : Set α) (t : Set β) : Prop :=
  INJ f s t ∧ SURJ f s t

/- HOL4: pred_set$FINITE:
   FINITE s = !P. P EMPTY /\ (!s. P s ==> !e. P (e INSERT s)) ==> P s -/
def FINITE {α : Type u} (s : Set α) : Prop :=
  ∀ P : Set α → Prop, P ∅ ∧ (∀ s, P s → ∀ e, P (insert e s)) → P s

/- HOL4: pred_set$CARD (new_specification):
   (CARD EMPTY = 0) /\
   (!s. FINITE s ==> !x. CARD (x INSERT s) = if x IN s then CARD s else SUC (CARD s))
   Unspecified on infinite sets.  Lean: the length of any duplicate-free enumeration of `s`
   (unspecified, by `SELECT`, if there is none). -/
noncomputable def CARD {α : Type u} (s : Set α) : Nat :=
  SELECT fun n => ∃ l : List α, l.Nodup ∧ (∀ x, x ∈ l ↔ x ∈ s) ∧ l.length = n

/- HOL4: bool$RES_FORALL:  RES_FORALL = \p m. !x. x IN p ==> m x
   (`!x :: p. m x` is `RES_FORALL p (\x. m x)`) -/
def RES_FORALL {α : Type u} (p : Set α) (m : α → Prop) : Prop := ∀ x, x ∈ p → m x

/- HOL4: ternaryComparisons$ordering (also called toto$cpn)
   Datatype: ordering = LESS | EQUAL | GREATER End -/
inductive ordering
  | LESS | EQUAL | GREATER
  deriving DecidableEq, Inhabited

export ordering (LESS EQUAL GREATER)

/- HOL4: arithmetic$EVEN, bit$DIV2 (DIV2 n = n DIV 2) -/
def EVEN (n : Nat) : Prop := n % 2 = 0
instance (n : Nat) : Decidable (EVEN n) := inferInstanceAs (Decidable (n % 2 = 0))
def DIV2 (n : Nat) : Nat := n / 2

end CmlTS
