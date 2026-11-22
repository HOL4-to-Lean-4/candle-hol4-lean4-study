/-
  HOL4 theory `setSpec` (candle/set-theory/setSpecScript.sml).

  HOL4 hides `mem` behind overloads (`x <: y`, `suchthat`, `Pow`, `+`, `∅`, `Unit`, `One`,
  `Two`, `(a,b)`, `∪`, `×`, `Relspace`, `Funspace`, `'`, `boolset`, `True`, `False`,
  `Boolean`, `Abstract`).  In Lean every constant takes `mem` explicitly as its first
  argument, and there is no notation: see CONVENTIONS.md.
  `true ^mem` / `false ^mem` are named `true0 mem` / `false0 mem` in Lean.
-/
import CandleLean.Prelude.Basic

namespace Candle

noncomputable section
open Classical

variable {U : Type}

/- HOL4:
val mem = ``mem:'U->'U->bool``
val _ = Parse.add_infix("<:",425,Parse.NONASSOC)
Overload "<:" = ``mem:'U->'U->bool``
   (HOL `x <: y` is `mem x y`) -/

/- HOL4:
Definition extensional_def:
  extensional ^mem ⇔ ∀x y. x = y ⇔ ∀a. mem a x ⇔ mem a y
End -/
def extensional (mem : U → U → Prop) : Prop :=
  ∀ x y, x = y ↔ ∀ a, mem a x ↔ mem a y

/- HOL4:
Definition is_separation_def:
  is_separation ^mem sub ⇔ ∀x P. ∀a. mem a (sub x P) ⇔ mem a x ∧ P a
End -/
def is_separation (mem : U → U → Prop) (sub : U → (U → Prop) → U) : Prop :=
  ∀ x P, ∀ a, mem a (sub x P) ↔ mem a x ∧ P a

/- HOL4:
Definition is_power_def:
  is_power ^mem power ⇔ ∀x. ∀a. mem a (power x) ⇔ ∀b. mem b a ⇒ mem b x
End -/
def is_power (mem : U → U → Prop) (power : U → U) : Prop :=
  ∀ x, ∀ a, mem a (power x) ↔ ∀ b, mem b a → mem b x

/- HOL4:
Definition is_union_def:
  is_union ^mem union ⇔ ∀x. ∀a. mem a (union x) ⇔ ∃b. mem a b ∧ mem b x
End -/
def is_union (mem : U → U → Prop) (union : U → U) : Prop :=
  ∀ x, ∀ a, mem a (union x) ↔ ∃ b, mem a b ∧ mem b x

/- HOL4:
Definition is_upair_def:
  is_upair ^mem upair ⇔ ∀x y. ∀a. mem a (upair x y) ⇔ a = x ∨ a = y
End -/
def is_upair (mem : U → U → Prop) (upair : U → U → U) : Prop :=
  ∀ x y, ∀ a, mem a (upair x y) ↔ a = x ∨ a = y

/- HOL4:
Definition is_set_theory_def:
  is_set_theory ^mem ⇔
    extensional mem ∧
    (∃sub. is_separation mem sub) ∧
    (∃power. is_power mem power) ∧
    (∃union. is_union mem union) ∧
    (∃upair. is_upair mem upair)
End -/
def is_set_theory (mem : U → U → Prop) : Prop :=
  extensional mem ∧
  (∃ sub, is_separation mem sub) ∧
  (∃ power, is_power mem power) ∧
  (∃ union, is_union mem union) ∧
  (∃ upair, is_upair mem upair)

/- HOL4:
Definition sub_def:
  sub ^mem = @sub. is_separation mem sub
End
Overload suchthat = ``sub ^mem``     (infixl 9: `s suchthat P` is `sub mem s P`) -/
def sub [Nonempty U] (mem : U → U → Prop) : U → (U → Prop) → U :=
  select (fun sub => is_separation mem sub)

/- HOL4:
Definition power_def:
  power ^mem = @power. is_power mem power
End
Overload Pow = ``power ^mem`` -/
def power [Nonempty U] (mem : U → U → Prop) : U → U :=
  select (fun power => is_power mem power)

/- HOL4:
Definition union_def:
  union ^mem = @union. is_union mem union
End -/
def union [Nonempty U] (mem : U → U → Prop) : U → U :=
  select (fun union => is_union mem union)

/- HOL4:
Definition upair_def:
  upair ^mem = @upair. is_upair mem upair
End
Overload "+" = ``upair ^mem``     (HOL `x + y` on sets is `upair mem x y`) -/
def upair [Nonempty U] (mem : U → U → Prop) : U → U → U :=
  select (fun upair => is_upair mem upair)

/- HOL4:
Definition empty_def:
  empty ^mem = sub mem ARB (K F)
End
Overload "∅" = ``empty ^mem`` -/
def empty [Nonempty U] (mem : U → U → Prop) : U := sub mem ARB (K False)

/- HOL4:
Definition unit_def:
  unit ^mem x = x + x
End
Overload Unit = ``unit ^mem`` -/
def unit [Nonempty U] (mem : U → U → Prop) (x : U) : U := upair mem x x

/- HOL4:
Definition one_def:
  one ^mem = Unit ∅
End
Overload One = ``one ^mem`` -/
def one [Nonempty U] (mem : U → U → Prop) : U := unit mem (empty mem)

/- HOL4:
Definition two_def:
  two ^mem = ∅ + One
End
Overload Two = ``two ^mem``
Overload boolset = ``Two`` -/
def two [Nonempty U] (mem : U → U → Prop) : U := upair mem (empty mem) (one mem)

/- HOL4:
Overload boolset = ``Two``     (HOL `boolset` is `boolset mem`, which is `two mem`) -/
abbrev boolset [Nonempty U] (mem : U → U → Prop) : U := two mem

/- HOL4:
Definition pair_def:
  pair ^mem x y = (Unit x) + (x + y)
End
Overload "," = ``pair ^mem``     (HOL `(x,y)` on sets is `pair mem x y`) -/
def pair [Nonempty U] (mem : U → U → Prop) (x y : U) : U :=
  upair mem (unit mem x) (upair mem x y)

/- HOL4:
Definition binary_union_def:
  binary_union ^mem x y = union mem (upair mem x y)
End
Overload UNION = ``binary_union ^mem``     (HOL `x ∪ y` on sets is `binary_union mem x y`) -/
def binary_union [Nonempty U] (mem : U → U → Prop) (x y : U) : U :=
  union mem (upair mem x y)

/- HOL4:
Definition product_def:
  product ^mem x y =
    (Pow (Pow (x ∪ y)) suchthat
     λa. ∃b c. b <: x ∧ c <: y ∧ a = (b,c))
End
Overload CROSS = ``product ^mem``     (HOL `x × y` on sets is `product mem x y`) -/
def product [Nonempty U] (mem : U → U → Prop) (x y : U) : U :=
  sub mem (power mem (power mem (binary_union mem x y)))
    (fun a => ∃ b c, mem b x ∧ mem c y ∧ a = pair mem b c)

/- HOL4:
Definition relspace_def:
  relspace ^mem x y = Pow (x × y)
End
Overload Relspace = ``relspace ^mem`` -/
def relspace [Nonempty U] (mem : U → U → Prop) (x y : U) : U :=
  power mem (product mem x y)

/- HOL4:
Definition funspace_def:
  funspace ^mem x y =
    (Relspace x y suchthat
     λf. ∀a. a <: x ⇒ ∃!b. (a,b) <: f)
End
Overload Funspace = ``funspace ^mem`` -/
def funspace [Nonempty U] (mem : U → U → Prop) (x y : U) : U :=
  sub mem (relspace mem x y)
    (fun f => ∀ a, mem a x → EXISTS_UNIQUE (fun b => mem (pair mem a b) f))

/- HOL4:
Definition apply_def:
  apply ^mem x y = @a. (y,a) <: x
End
val _ = Parse.add_infix("'",2000,Parse.LEFT);
Overload "'" = ``apply ^mem``     (HOL `x ' y` on sets is `apply mem x y`) -/
def apply [Nonempty U] (mem : U → U → Prop) (x y : U) : U :=
  select (fun a => mem (pair mem y a) x)

/- HOL4:
Definition true_def:
  true ^mem = ∅
End
Overload True = ``true ^mem``
   (renamed: HOL `true ^mem`, i.e. the overload `True`, is `true0 mem`) -/
def true0 [Nonempty U] (mem : U → U → Prop) : U := empty mem

/- HOL4:
Definition false_def:
  false ^mem = One
End
Overload False = ``false ^mem``
   (renamed: HOL `false ^mem`, i.e. the overload `False`, is `false0 mem`) -/
def false0 [Nonempty U] (mem : U → U → Prop) : U := one mem

/- HOL4:
Definition boolean_def:
  boolean ^mem b = if b then True else False
End
Overload Boolean = ``boolean ^mem`` -/
def boolean [Nonempty U] (mem : U → U → Prop) (b : Prop) : U :=
  if b then true0 mem else false0 mem

/- HOL4:
Definition abstract_def:
  abstract ^mem dom rng f = (dom × rng suchthat λx. ∃a. x = (a,f a))
End
Overload Abstract = ``abstract ^mem`` -/
def abstract [Nonempty U] (mem : U → U → Prop) (dom rng : U) (f : U → U) : U :=
  sub mem (product mem dom rng) (fun x => ∃ a, x = pair mem a (f a))

end

end Candle

/-! ## Stage 2: the target theorems of the HOL4 theory `setSpec` (statements only, proofs `sorry`) -/

namespace Candle

noncomputable section
open Classical
set_option autoImplicit false

/- HOL4:
Theorem is_extensional:
   is_set_theory ^mem ⇒ extensional mem
-/
theorem is_extensional {U : Type} [Nonempty U] (mem : U → U → Prop) :
    is_set_theory mem → extensional mem := by
  sorry

/- HOL4:
Theorem is_separation_sub:
   is_set_theory ^mem ⇒ is_separation mem (sub mem)
-/
theorem is_separation_sub {U : Type} [Nonempty U] (mem : U → U → Prop) :
    is_set_theory mem → is_separation mem (sub mem) := by
  sorry

/- HOL4:
Theorem is_power_power:
   is_set_theory ^mem ⇒ is_power mem (power mem)
-/
theorem is_power_power {U : Type} [Nonempty U] (mem : U → U → Prop) :
    is_set_theory mem → is_power mem (power mem) := by
  sorry

/- HOL4:
Theorem is_union_union:
   is_set_theory ^mem ⇒ is_union mem (union mem)
-/
theorem is_union_union {U : Type} [Nonempty U] (mem : U → U → Prop) :
    is_set_theory mem → is_union mem (union mem) := by
  sorry

/- HOL4:
Theorem is_upair_upair:
   is_set_theory ^mem ⇒ is_upair mem (upair mem)
-/
theorem is_upair_upair {U : Type} [Nonempty U] (mem : U → U → Prop) :
    is_set_theory mem → is_upair mem (upair mem) := by
  sorry

/- HOL4:
Theorem mem_sub:
   is_set_theory ^mem ⇒ ∀x s P. x <: (s suchthat P) ⇔ x <: s ∧ P x
-/
theorem mem_sub {U : Type} [Nonempty U] (mem : U → U → Prop) :
    is_set_theory mem →
    ∀ (x s : U) (P : U → Prop), mem x (sub mem s P) ↔ mem x s ∧ P x := by
  sorry

/- HOL4:
Theorem mem_power:
   is_set_theory ^mem ⇒
    ∀x y. x <: (Pow y) ⇔ (∀b. b <: x ⇒ b <: y)
-/
theorem mem_power {U : Type} [Nonempty U] (mem : U → U → Prop) :
    is_set_theory mem →
    ∀ (x y : U), mem x (power mem y) ↔ (∀ b, mem b x → mem b y) := by
  sorry

/- HOL4:
Theorem mem_union:
   is_set_theory ^mem ⇒
    ∀x s. x <: (union mem s) ⇔ ∃a. x <: a ∧ a <: s
-/
theorem mem_union {U : Type} [Nonempty U] (mem : U → U → Prop) :
    is_set_theory mem →
    ∀ (x s : U), mem x (union mem s) ↔ ∃ a, mem x a ∧ mem a s := by
  sorry

/- HOL4:
Theorem mem_upair:
   is_set_theory ^mem ⇒ ∀a x y. a <: (x + y) ⇔ a = x ∨ a = y
-/
theorem mem_upair {U : Type} [Nonempty U] (mem : U → U → Prop) :
    is_set_theory mem → ∀ (a x y : U), mem a (upair mem x y) ↔ a = x ∨ a = y := by
  sorry

/- HOL4:
Theorem mem_empty:
   is_set_theory ^mem ⇒ ∀x. ¬(x <: ∅)
-/
theorem mem_empty {U : Type} [Nonempty U] (mem : U → U → Prop) :
    is_set_theory mem → ∀ (x : U), ¬ (mem x (empty mem)) := by
  sorry

/- HOL4:
Theorem mem_unit:
   is_set_theory ^mem ⇒
    ∀x y. x <: (Unit y) ⇔ x = y
-/
theorem mem_unit {U : Type} [Nonempty U] (mem : U → U → Prop) :
    is_set_theory mem →
    ∀ (x y : U), mem x (unit mem y) ↔ x = y := by
  sorry

/- HOL4:
Theorem unit_inj:
   is_set_theory ^mem ⇒
    ∀x y. Unit x = Unit y ⇔ x = y
-/
theorem unit_inj {U : Type} [Nonempty U] (mem : U → U → Prop) :
    is_set_theory mem →
    ∀ (x y : U), unit mem x = unit mem y ↔ x = y := by
  sorry

/- HOL4:
Theorem mem_one:
   is_set_theory ^mem ⇒
    ∀x. x <: One ⇔ x = ∅
-/
theorem mem_one {U : Type} [Nonempty U] (mem : U → U → Prop) :
    is_set_theory mem →
    ∀ (x : U), mem x (one mem) ↔ x = empty mem := by
  sorry

/- HOL4:
Theorem mem_two:
   is_set_theory ^mem ⇒
    ∀x. x <: Two ⇔ x = ∅ ∨ x = One
-/
theorem mem_two {U : Type} [Nonempty U] (mem : U → U → Prop) :
    is_set_theory mem →
    ∀ (x : U), mem x (two mem) ↔ x = empty mem ∨ x = one mem := by
  sorry

/- HOL4:
Theorem upair_inj:
   is_set_theory ^mem ⇒
    ∀a b c d. a + b = c + d ⇔ a = c ∧ b = d ∨ a = d ∧ b = c
-/
theorem upair_inj {U : Type} [Nonempty U] (mem : U → U → Prop) :
    is_set_theory mem →
    ∀ (a b c d : U), upair mem a b = upair mem c d ↔ a = c ∧ b = d ∨ a = d ∧ b = c := by
  sorry

/- HOL4:
Theorem unit_eq_upair:
   is_set_theory ^mem ⇒
    ∀x y z. Unit x = y + z ⇔ x = y ∧ y = z
-/
theorem unit_eq_upair {U : Type} [Nonempty U] (mem : U → U → Prop) :
    is_set_theory mem →
    ∀ (x y z : U), unit mem x = upair mem y z ↔ x = y ∧ y = z := by
  sorry

/- HOL4:
Theorem pair_inj:
   is_set_theory ^mem ⇒
    ∀a b c d. (a,b) = (c,d) ⇔ a = c ∧ b = d
-/
theorem pair_inj {U : Type} [Nonempty U] (mem : U → U → Prop) :
    is_set_theory mem →
    ∀ (a b c d : U), pair mem a b = pair mem c d ↔ a = c ∧ b = d := by
  sorry

/- HOL4:
Theorem mem_binary_union:
   is_set_theory ^mem ⇒
    ∀a x y. a <: (x ∪ y) ⇔ a <: x ∨ a <: y
-/
theorem mem_binary_union {U : Type} [Nonempty U] (mem : U → U → Prop) :
    is_set_theory mem →
    ∀ (a x y : U), mem a (binary_union mem x y) ↔ mem a x ∨ mem a y := by
  sorry

/- HOL4:
Theorem mem_product:
   is_set_theory ^mem ⇒
    ∀a x y. a <: (x × y) ⇔ ∃b c. a = (b,c) ∧ b <: x ∧ c <: y
-/
theorem mem_product {U : Type} [Nonempty U] (mem : U → U → Prop) :
    is_set_theory mem →
    ∀ (a x y : U), mem a (product mem x y) ↔ ∃ b c, a = pair mem b c ∧ mem b x ∧ mem c y := by
  sorry

/- HOL4:
Theorem true_neq_false:
   is_set_theory ^mem ⇒ True ≠ False
-/
theorem true_neq_false {U : Type} [Nonempty U] (mem : U → U → Prop) :
    is_set_theory mem → true0 mem ≠ false0 mem := by
  sorry

/- HOL4:
Theorem mem_boolset:
   is_set_theory ^mem ⇒
    ∀x. x <: boolset ⇔ ((x = True) ∨ (x = False))
-/
theorem mem_boolset {U : Type} [Nonempty U] (mem : U → U → Prop) :
    is_set_theory mem →
    ∀ (x : U), mem x (boolset mem) ↔ ((x = true0 mem) ∨ (x = false0 mem)) := by
  sorry

/- HOL4:
Theorem boolean_in_boolset:
   is_set_theory ^mem ⇒
    ∀b. Boolean b <: boolset
-/
theorem boolean_in_boolset {U : Type} [Nonempty U] (mem : U → U → Prop) :
    is_set_theory mem →
    ∀ (b : Prop), mem (boolean mem b) (boolset mem) := by
  sorry

/- HOL4:
Theorem boolean_eq_true:
   is_set_theory ^mem ⇒ ∀b. Boolean b = True ⇔ b
-/
theorem boolean_eq_true {U : Type} [Nonempty U] (mem : U → U → Prop) :
    is_set_theory mem → ∀ (b : Prop), boolean mem b = true0 mem ↔ b := by
  sorry

/- HOL4:
Theorem apply_abstract:
   is_set_theory ^mem ⇒
    ∀f x s t. x <: s ∧ f x <: t ⇒ (Abstract s t f) ' x = f x
-/
theorem apply_abstract {U : Type} [Nonempty U] (mem : U → U → Prop) :
    is_set_theory mem →
    ∀ (f : U → U) (x s t : U),
      mem x s ∧ mem (f x) t → apply mem (abstract mem s t f) x = f x := by
  sorry

/- HOL4:
Theorem apply_in_rng:
   is_set_theory ^mem ⇒
    ∀f x s t. x <: s ∧ f <: Funspace s t ⇒
    f ' x <: t
-/
theorem apply_in_rng {U : Type} [Nonempty U] (mem : U → U → Prop) :
    is_set_theory mem →
    ∀ (f x s t : U), mem x s ∧ mem f (funspace mem s t) →
      mem (apply mem f x) t := by
  sorry

/- HOL4:
Theorem abstract_in_funspace:
   is_set_theory ^mem ⇒
    ∀f s t. (∀x. x <: s ⇒ f x <: t) ⇒ Abstract s t f <: Funspace s t
-/
theorem abstract_in_funspace {U : Type} [Nonempty U] (mem : U → U → Prop) :
    is_set_theory mem →
    ∀ (f : U → U) (s t : U),
      (∀ x, mem x s → mem (f x) t) → mem (abstract mem s t f) (funspace mem s t) := by
  sorry

/- HOL4:
Theorem abstract_eq:
   is_set_theory ^mem ⇒
    ∀s t1 t2 f g.
    (∀x. x <: s ⇒ f x <: t1 ∧ g x <: t2 ∧ f x = g x)
    ⇒ Abstract s t1 f = Abstract s t2 g
-/
theorem abstract_eq {U : Type} [Nonempty U] (mem : U → U → Prop) :
    is_set_theory mem →
    ∀ (s t1 t2 : U) (f g : U → U),
      (∀ x, mem x s → mem (f x) t1 ∧ mem (g x) t2 ∧ f x = g x)
      → abstract mem s t1 f = abstract mem s t2 g := by
  sorry

end

end Candle
