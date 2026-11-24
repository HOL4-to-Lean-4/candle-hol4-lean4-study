import Batteries

/-!
# HOL4 library constants: bool, combin, pair, option, arithmetic, relation,
# ternaryComparisons, toto

Conventions (see `CONVENTIONS.md`): HOL4 `bool` is Lean `Prop`; HOL4 `num` is `Nat`;
HOL4 type variables are Lean type variables; every HOL4 type is non-empty, so we
require `[Nonempty α]` wherever an unspecified value (`ARB`, Hilbert choice) is needed.
-/

universe u v w x

namespace HOL

open Classical

noncomputable section

/-! ## bool -/

/- HOL4: bool$ARB    new_constant("ARB", alpha): no defining theorem. -/
opaque ARB {α : Sort u} [Nonempty α] : α

/- HOL4: bool$?! (EXISTS_UNIQUE, binder `?!x. P x`, written `∃!`)
     ?! = \P:'a->bool. $? P /\ !x y. P x /\ P y ==> (x=y) -/
def EXISTS_UNIQUE {α : Sort u} (P : α → Prop) : Prop :=
  (∃ x, P x) ∧ ∀ x y, P x ∧ P y → x = y

/-! ## combin -/

/- HOL4: combin$I    I = S K (K:'a->'a->'a)    (so I x = x) -/
@[reducible] def I {α : Sort u} (x : α) : α := x

/- HOL4: combin$K    K = \x y. x -/
@[reducible] def K {α : Sort u} {β : Sort v} (x : α) (_y : β) : α := x

/- HOL4: combin$C    C = \f x y. f y x -/
@[reducible] def C {α : Sort u} {β : Sort v} {γ : Sort w} (f : α → β → γ) (x : β) (y : α) : γ :=
  f y x

/- HOL4: combin$UPDATE    UPDATE a b = \f c. if a = c then b else f c
   (written `(a =+ b) f` in HOL4) -/
def UPDATE {α : Type u} {β : Sort v} (a : α) (b : β) (f : α → β) (c : α) : β :=
  if a = c then b else f c

/-! ## pair -/

/- HOL4: pair$UNCURRY    UNCURRY f v = f (FST v) (SND v) -/
@[reducible] def UNCURRY {α : Type u} {β : Type v} {γ : Sort w} (f : α → β → γ) (p : α × β) : γ :=
  f p.1 p.2

/- HOL4: pair$PAIR_MAP (infix ##)
     $## (f:'a->'c) (g:'b->'d) p = (f (FST p), g (SND p)) -/
@[reducible] def PAIR_MAP {α : Type u} {β : Type v} {γ : Type w} {δ : Type x}
    (f : α → γ) (g : β → δ) (p : α × β) : γ × δ :=
  (f p.1, g p.2)

/- HOL4: pair$LEX (infix LEX)
     $LEX (R1:'a->'a->bool) (R2:'b->'b->bool) = \(s,t) (u,v). R1 s u \/ (s=u) /\ R2 t v -/
def LEX {α : Type u} {β : Type v} (R1 : α → α → Prop) (R2 : β → β → Prop)
    (p q : α × β) : Prop :=
  R1 p.1 q.1 ∨ (p.1 = q.1 ∧ R2 p.2 q.2)

/-! ## option
HOL4 `OPTION_MAP` is Lean `Option.map`, `OPTION_BIND` is `Option.bind`
(same equations: `OPTION_MAP f (SOME x) = SOME (f x)`, `OPTION_MAP f NONE = NONE`). -/

/-! ## arithmetic -/

/- HOL4: arithmetic$EVEN
     (EVEN 0 = T) /\ (!n. EVEN (SUC n) = ~EVEN n) -/
def EVEN : Nat → Prop
  | 0 => True
  | n + 1 => ¬ EVEN n

/- HOL4: arithmetic$ODD
     (ODD 0 = F) /\ (!n. ODD (SUC n) = ~ODD n) -/
def ODD : Nat → Prop
  | 0 => False
  | n + 1 => ¬ ODD n

/- HOL4: arithmetic$DIV2    DIV2 n = n DIV 2
   (HOL4 `DIV`/`MOD` at this commit: `k DIV 0 = 0`, `k MOD 0 = k`, the same as Lean `/`, `%`) -/
def DIV2 (n : Nat) : Nat := n / 2

/- HOL4: arithmetic$MAX    MAX m n = if m < n then n else m -/
def MAX (m n : Nat) : Nat := if m < n then n else m

/- HOL4: arithmetic$MIN    MIN m n = if m < n then m else n -/
def MIN (m n : Nat) : Nat := if m < n then m else n

/-! ## relation -/

/- HOL4: relation$transitive    transitive (R:'a->'a->bool) = !x y z. R x y /\ R y z ==> R x z -/
def transitive {α : Type u} (R : α → α → Prop) : Prop := ∀ x y z, R x y ∧ R y z → R x z

/- HOL4: relation$reflexive    reflexive (R:'a->'a->bool) = !x. R x x -/
def reflexive {α : Type u} (R : α → α → Prop) : Prop := ∀ x, R x x

/- HOL4: relation$irreflexive    irreflexive (R:'a->'a->bool) = !x. ~R x x -/
def irreflexive {α : Type u} (R : α → α → Prop) : Prop := ∀ x, ¬ R x x

/- HOL4: relation$symmetric    symmetric (R:'a->'a->bool) = !x y. R x y = R y x -/
def symmetric {α : Type u} (R : α → α → Prop) : Prop := ∀ x y, R x y = R y x

/- HOL4: relation$antisymmetric    antisymmetric (R:'a->'a->bool) = !x y. R x y /\ R y x ==> (x = y) -/
def antisymmetric {α : Type u} (R : α → α → Prop) : Prop := ∀ x y, R x y ∧ R y x → x = y

/- HOL4: relation$trichotomous    trichotomous (R:'a->'a->bool) = !a b. R a b \/ R b a \/ (a = b) -/
def trichotomous {α : Type u} (R : α → α → Prop) : Prop := ∀ a b, R a b ∨ R b a ∨ a = b

/- HOL4: relation$StrongOrder    StrongOrder (Z:'g->'g->bool) <=> irreflexive Z /\ transitive Z -/
def StrongOrder {α : Type u} (Z : α → α → Prop) : Prop := irreflexive Z ∧ transitive Z

/- HOL4: relation$StrongLinearOrder
     StrongLinearOrder (R:'a->'a->bool) <=> StrongOrder R /\ trichotomous R -/
def StrongLinearOrder {α : Type u} (R : α → α → Prop) : Prop := StrongOrder R ∧ trichotomous R

/- HOL4: relation$Order    Order (Z:'g->'g->bool) <=> antisymmetric Z /\ transitive Z -/
def Order {α : Type u} (Z : α → α → Prop) : Prop := antisymmetric Z ∧ transitive Z

/- HOL4: relation$LinearOrder    LinearOrder (R:'a->'a->bool) <=> Order R /\ trichotomous R -/
def LinearOrder {α : Type u} (R : α → α → Prop) : Prop := Order R ∧ trichotomous R

/- HOL4: relation$RC    RC (R:'a->'a->bool) x y <=> (x = y) \/ R x y -/
def RC {α : Type u} (R : α → α → Prop) (x y : α) : Prop := x = y ∨ R x y

/- HOL4: relation$RTC
     Inductive RTC:
       (!x. RTC R x x) /\
       (!x y z. R x y /\ RTC R y z ==> RTC R x z)
     End -/
inductive RTC {α : Type u} (R : α → α → Prop) : α → α → Prop where
  | refl (x : α) : RTC R x x
  | step (x y z : α) : R x y → RTC R y z → RTC R x z

/- HOL4: relation$inv_image    inv_image R (f:'a->'b) = \x y. R (f x) (f y):bool -/
def inv_image {α : Type u} {β : Type v} (R : β → β → Prop) (f : α → β) : α → α → Prop :=
  fun x y => R (f x) (f y)

/-! ## ternaryComparisons -/

/- HOL4: ternaryComparisons$ordering
     Datatype: ordering = LESS | EQUAL | GREATER End
   (toto calls this type `cpn`) -/
inductive ordering where
  | LESS
  | EQUAL
  | GREATER
  deriving DecidableEq, Inhabited, Repr

export ordering (LESS EQUAL GREATER)

/- HOL4: toto$cpn    Type cpn = ``:ordering`` -/
abbrev cpn := ordering

/- HOL4: ternaryComparisons$invert_comparison (overloaded as `flip_ord` in mlstring)
     (invert_comparison GREATER = LESS) /\
     (invert_comparison LESS = GREATER) /\
     (invert_comparison EQUAL = EQUAL) -/
def invert_comparison : ordering → ordering
  | GREATER => LESS
  | LESS => GREATER
  | EQUAL => EQUAL

/-! ## toto -/

/- HOL4: toto$comp    Type comp = “:'a->'a->cpn” -/
abbrev comp (α : Type u) := α → α → cpn

/- HOL4: toto$TotOrd
     TotOrd (c: 'a comp) =
       (!x y. (c x y = EQUAL) <=> (x = y)) /\
       (!x y. (c x y = GREATER) <=> (c y x = LESS)) /\
       (!x y z. (c x y = LESS) /\ (c y z = LESS) ==> (c x z = LESS)) -/
def TotOrd {α : Type u} (c : comp α) : Prop :=
  (∀ x y, c x y = EQUAL ↔ x = y) ∧
  (∀ x y, c x y = GREATER ↔ c y x = LESS) ∧
  (∀ x y z, c x y = LESS ∧ c y z = LESS → c x z = LESS)

/- HOL4: toto$TO_of_LinearOrder
     TO_of_LinearOrder (r:'a->'a->bool) x y =
       if x = y then EQUAL else if r x y then LESS else GREATER -/
def TO_of_LinearOrder {α : Type u} (r : α → α → Prop) (x y : α) : ordering :=
  if x = y then EQUAL else if r x y then LESS else GREATER

end

end HOL
