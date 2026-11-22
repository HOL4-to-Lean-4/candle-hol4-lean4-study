/-
  HOL4 library constants from the theories `bool`, `combin`, `pair`, `sum`,
  `arithmetic`, `relation`, `ternaryComparisons` and `toto`.

  Global conventions (see CONVENTIONS.md):
  * HOL4 `bool` is Lean `Prop` everywhere (T = True, F = False); `if` on a
    proposition uses classical decidability (`open Classical`).
  * HOL4 `num` is Lean `Nat`.
  * Type variables that need a witness (ARB, Hilbert choice) carry `[Nonempty α]`.
-/
open Classical

/- HOL4: bool$ARB
   `val arb = new_constant("ARB",alpha);  (* Doesn't have to be defined at all. *)`
   ARB is a completely unspecified constant (one per type), hence `opaque`.
   HOL4's `Define` also fills the missing cases of a non-exhaustive pattern match
   with ARB; we do the same in the translated definitions. -/
noncomputable opaque ARB {α : Sort u} [Nonempty α] : α

/-! ## combin -/

/- HOL4: combin$I   `I = S K (K:'a->'a->'a)`   (so `I x = x`) -/
def I {α : Sort u} (x : α) : α := x

/- HOL4: combin$K   `K = \x y. x` -/
def K {α : Sort u} {β : Sort v} (x : α) (_y : β) : α := x

/- HOL4: combin$C   `C = \f x y. f y x` -/
def C {α : Sort u} {β : Sort v} {γ : Sort w} (f : α → β → γ) (x : β) (y : α) : γ := f y x

/- HOL4: combin$UPDATE   `UPDATE a b = \f c. if a = c then b else f c`
   (HOL4 notation `(a =+ b) f`) -/
noncomputable def UPDATE {α : Sort u} {β : Sort v} (a : α) (b : β) (f : α → β) : α → β :=
  fun c => if a = c then b else f c

/-! ## pair -/

/- HOL4: pair$UNCURRY   `UNCURRY f (v:'a#'b) = f (FST v) (SND v)` -/
def UNCURRY {α β γ : Type _} (f : α → β → γ) (v : α × β) : γ := f v.1 v.2

/- HOL4: pair$PAIR_MAP   `$## (f:'a->'c) (g:'b->'d) p = (f (FST p), g (SND p))` -/
def PAIR_MAP {α β γ δ : Type _} (f : α → γ) (g : β → δ) (p : α × β) : γ × δ :=
  (f p.1, g p.2)

/- HOL4: pair$LEX
   `$LEX (R1:'a->'a->bool) (R2:'b->'b->bool) = \(s,t) (u,v). R1 s u \/ (s=u) /\ R2 t v` -/
def LEX {α β : Type _} (R1 : α → α → Prop) (R2 : β → β → Prop) : α × β → α × β → Prop :=
  fun p q => R1 p.1 q.1 ∨ (p.1 = q.1 ∧ R2 p.2 q.2)

/-! ## sum -/

/- HOL4: sum$ISL   `ISL (INL x) = T /\ ISL (INR y) = F` -/
def ISL {α β : Type _} : α ⊕ β → Prop
  | .inl _ => True
  | .inr _ => False

/- HOL4: sum$OUTL
   `new_recursive_definition {def = “OUTL (INL x) = x”, rec_axiom = sum_Axiom}`
   Only the `INL` case is specified; the value on `INR` is unspecified.  Encoded
   as a choice over all functions satisfying the specification. -/
noncomputable def OUTL {α β : Type _} [Nonempty α] : α ⊕ β → α :=
  Classical.epsilon (fun f : α ⊕ β → α => ∀ x, f (.inl x) = x)

/-! ## arithmetic -/

/- HOL4: arithmetic$EVEN   `(EVEN 0 = T) /\ (EVEN (SUC n) = ~EVEN n)` -/
def EVEN : Nat → Prop
  | 0 => True
  | n + 1 => ¬ EVEN n

/- HOL4: arithmetic$DIV2   `DIV2 n = n DIV 2`
   (HOL4 `DIV`/`MOD` agree with Lean `/`/`%` on `Nat`, including division by 0.) -/
def DIV2 (n : Nat) : Nat := n / 2

/- HOL4: arithmetic$MAX   `MAX m n = if m < n then n else m` -/
def MAX (m n : Nat) : Nat := if m < n then n else m

/-! ## relation -/

/- HOL4: relation$transitive   `transitive (R:'a->'a->bool) = !x y z. R x y /\ R y z ==> R x z` -/
def transitive {α : Sort u} (R : α → α → Prop) : Prop := ∀ x y z, R x y ∧ R y z → R x z

/- HOL4: relation$reflexive   `reflexive (R:'a->'a->bool) = !x. R x x` -/
def reflexive {α : Sort u} (R : α → α → Prop) : Prop := ∀ x, R x x

/- HOL4: relation$irreflexive   `irreflexive (R:'a->'a->bool) = !x. ~R x x` -/
def irreflexive {α : Sort u} (R : α → α → Prop) : Prop := ∀ x, ¬ R x x

/- HOL4: relation$antisymmetric   `antisymmetric (R:'a->'a->bool) = !x y. R x y /\ R y x ==> (x = y)` -/
def antisymmetric {α : Sort u} (R : α → α → Prop) : Prop := ∀ x y, R x y ∧ R y x → x = y

/- HOL4: relation$trichotomous   `trichotomous (R:'a->'a->bool) = !a b. R a b \/ R b a \/ (a = b)` -/
def trichotomous {α : Sort u} (R : α → α → Prop) : Prop := ∀ a b, R a b ∨ R b a ∨ a = b

/- HOL4: relation$StrongOrder   `StrongOrder (Z:'g->'g->bool) <=> irreflexive Z /\ transitive Z` -/
def StrongOrder {α : Sort u} (Z : α → α → Prop) : Prop := irreflexive Z ∧ transitive Z

/- HOL4: relation$StrongLinearOrder
   `StrongLinearOrder (R:'a->'a->bool) <=> StrongOrder R /\ trichotomous R` -/
def StrongLinearOrder {α : Sort u} (R : α → α → Prop) : Prop := StrongOrder R ∧ trichotomous R

/- HOL4: relation$inv_image   `inv_image R (f:'a->'b) = \x y. R (f x) (f y):bool` -/
def inv_image {α : Sort u} {β : Sort v} (R : β → β → Prop) (f : α → β) : α → α → Prop :=
  fun x y => R (f x) (f y)

/- HOL4: relation$RC   `RC (R:'a->'a->bool) x y <=> (x = y) \/ R x y` -/
def RC {α : Sort u} (R : α → α → Prop) (x y : α) : Prop := x = y ∨ R x y

/- HOL4: relation$RTC
   Inductive RTC:
     (!x. RTC R x x) /\
     (!x y z. R x y /\ RTC R y z ==> RTC R x z)
   End -/
inductive RTC {α : Sort u} (R : α → α → Prop) : α → α → Prop
  | refl (x : α) : RTC R x x
  | step (x y z : α) : R x y → RTC R y z → RTC R x z

/-! ## ternaryComparisons / toto -/

/- HOL4: ternaryComparisons$ordering   `Datatype: ordering = LESS | EQUAL | GREATER End`
   (toto calls this type `cpn`) -/
inductive ordering where
  | LESS
  | EQUAL
  | GREATER
  deriving DecidableEq, Inhabited, Repr

export ordering (LESS EQUAL GREATER)

/- HOL4: toto$cpn   `Type cpn = ``:ordering``` -/
abbrev cpn := ordering

/- HOL4: ternaryComparisons$invert_comparison
   (invert_comparison GREATER = LESS) /\
   (invert_comparison LESS = GREATER) /\
   (invert_comparison EQUAL = EQUAL) -/
def invert_comparison : ordering → ordering
  | GREATER => LESS
  | LESS => GREATER
  | EQUAL => EQUAL

/- HOL4: toto$TotOrd
   TotOrd (c: 'a comp) =
     (!x y. (c x y = EQUAL) <=> (x = y)) /\
     (!x y. (c x y = GREATER) <=> (c y x = LESS)) /\
     (!x y z. (c x y = LESS) /\ (c y z = LESS) ==> (c x z = LESS)) -/
def TotOrd {α : Sort u} (c : α → α → ordering) : Prop :=
  (∀ x y, c x y = EQUAL ↔ x = y) ∧
  (∀ x y, c x y = GREATER ↔ c y x = LESS) ∧
  (∀ x y z, c x y = LESS ∧ c y z = LESS → c x z = LESS)

/- HOL4: toto$TO_of_LinearOrder
   TO_of_LinearOrder (r:'a->'a->bool) x y =
     if x = y then EQUAL else if r x y then LESS else GREATER -/
noncomputable def TO_of_LinearOrder {α : Sort u} (r : α → α → Prop) (x y : α) : ordering :=
  if x = y then EQUAL else if r x y then LESS else GREATER
