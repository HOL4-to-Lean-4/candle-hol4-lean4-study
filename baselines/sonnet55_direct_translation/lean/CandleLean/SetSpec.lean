import CandleLean.Mlstring
/-
  Translation of `candle/set-theory/setSpecScript.sml`.
  Namespace `Candle.SetSpec`.
  The universe type is `U` and the membership relation is the explicit argument `mem : U → U → Prop`
  (HOL4: `mem:'U->'U->bool`, written `x <: s`).  Definitions that use HOL4's `ARB` or `@` on
  `U` take `[Inhabited U]`.
-/
namespace Candle.SetSpec

open HOL
universe u

open Classical

noncomputable section

variable {U : Type u}

/- HOL4: Definition extensional_def:
  extensional ^mem ⇔ ∀x y. x = y ⇔ ∀a. mem a x ⇔ mem a y
End -/
def extensional (mem : U → U → Prop) : Prop := ∀ x y, x = y ↔ ∀ a, mem a x ↔ mem a y

/- HOL4: Definition is_separation_def:
  is_separation ^mem sub ⇔ ∀x P. ∀a. mem a (sub x P) ⇔ mem a x ∧ P a
End -/
def is_separation (mem : U → U → Prop) (sub : U → (U → Prop) → U) : Prop :=
  ∀ x P, ∀ a, mem a (sub x P) ↔ mem a x ∧ P a

/- HOL4: Definition is_power_def:
  is_power ^mem power ⇔ ∀x. ∀a. mem a (power x) ⇔ ∀b. mem b a ⇒ mem b x
End -/
def is_power (mem : U → U → Prop) (power : U → U) : Prop :=
  ∀ x, ∀ a, mem a (power x) ↔ ∀ b, mem b a → mem b x

/- HOL4: Definition is_union_def:
  is_union ^mem union ⇔ ∀x. ∀a. mem a (union x) ⇔ ∃b. mem a b ∧ mem b x
End -/
def is_union (mem : U → U → Prop) (union : U → U) : Prop :=
  ∀ x, ∀ a, mem a (union x) ↔ ∃ b, mem a b ∧ mem b x

/- HOL4: Definition is_upair_def:
  is_upair ^mem upair ⇔ ∀x y. ∀a. mem a (upair x y) ⇔ a = x ∨ a = y
End -/
def is_upair (mem : U → U → Prop) (upair : U → U → U) : Prop :=
  ∀ x y, ∀ a, mem a (upair x y) ↔ a = x ∨ a = y

/- HOL4: Definition is_set_theory_def:
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

/- HOL4: Definition sub_def:
  sub ^mem = @sub. is_separation mem sub
End   (Hilbert choice; when no such function exists HOL4's value is unspecified, here the
       projection `fun x _ => x`.)  Overload suchthat = sub ^mem (infix, 9). -/
def sub (mem : U → U → Prop) : U → (U → Prop) → U :=
  if h : ∃ sub, is_separation mem sub then Classical.choose h else fun x _ => x

/- HOL4: Definition power_def:
  power ^mem = @power. is_power mem power
End   (Overload Pow = power ^mem.  Default `fun x => x`.) -/
def power (mem : U → U → Prop) : U → U :=
  if h : ∃ power, is_power mem power then Classical.choose h else fun x => x

/- HOL4: Definition union_def:
  union ^mem = @union. is_union mem union
End   (Default `fun x => x`.) -/
def union (mem : U → U → Prop) : U → U :=
  if h : ∃ union, is_union mem union then Classical.choose h else fun x => x

/- HOL4: Definition upair_def:
  upair ^mem = @upair. is_upair mem upair
End   (Overload "+" = upair ^mem.  Default `fun x _ => x`.) -/
def upair (mem : U → U → Prop) : U → U → U :=
  if h : ∃ upair, is_upair mem upair then Classical.choose h else fun x _ => x

/- HOL4: Definition empty_def:
  empty ^mem = sub mem ARB (K F)
End   (Overload "∅" = empty ^mem) -/
def empty [Inhabited U] (mem : U → U → Prop) : U := sub mem ARB (K False)

/- HOL4: Definition unit_def:
  unit ^mem x = x + x
End   (Overload Unit = unit ^mem) -/
def unit (mem : U → U → Prop) (x : U) : U := upair mem x x

/- HOL4: Definition one_def:
  one ^mem = Unit ∅
End   (Overload One = one ^mem) -/
def one [Inhabited U] (mem : U → U → Prop) : U := unit mem (empty mem)

/- HOL4: Definition two_def:
  two ^mem = ∅ + One
End   (Overload Two = two ^mem; Overload boolset = Two) -/
def two [Inhabited U] (mem : U → U → Prop) : U := upair mem (empty mem) (one mem)

/- HOL4: Definition pair_def:
  pair ^mem x y = (Unit x) + (x + y)
End   (Overload "," = pair ^mem) -/
def pair (mem : U → U → Prop) (x y : U) : U := upair mem (unit mem x) (upair mem x y)

/- HOL4: Definition binary_union_def:
  binary_union ^mem x y = union mem (upair mem x y)
End   (Overload UNION = binary_union ^mem, written `x ∪ y`) -/
def binary_union (mem : U → U → Prop) (x y : U) : U := union mem (upair mem x y)

/- HOL4: Definition product_def:
  product ^mem x y =
    (Pow (Pow (x ∪ y)) suchthat
     λa. ∃b c. b <: x ∧ c <: y ∧ a = (b,c))
End   (Overload CROSS = product ^mem, written `x × y`) -/
def product (mem : U → U → Prop) (x y : U) : U :=
  sub mem (power mem (power mem (binary_union mem x y)))
    (fun a => ∃ b c, mem b x ∧ mem c y ∧ a = pair mem b c)

/- HOL4: Definition relspace_def:
  relspace ^mem x y = Pow (x × y)
End   (Overload Relspace = relspace ^mem) -/
def relspace (mem : U → U → Prop) (x y : U) : U := power mem (product mem x y)

/- HOL4: Definition funspace_def:
  funspace ^mem x y =
    (Relspace x y suchthat
     λf. ∀a. a <: x ⇒ ∃!b. (a,b) <: f)
End   (Overload Funspace = funspace ^mem) -/
def funspace (mem : U → U → Prop) (x y : U) : U :=
  sub mem (relspace mem x y) (fun f => ∀ a, mem a x → EXISTS_UNIQUE (fun b => mem (pair mem a b) f))

/- HOL4: Definition apply_def:
  apply ^mem x y = @a. (y,a) <: x
End   (Overload "'" = apply ^mem: `f ' x` is `apply mem f x`) -/
def apply [Inhabited U] (mem : U → U → Prop) (x y : U) : U := ε (fun a => mem (pair mem y a) x)

/- HOL4: Definition true_def:
  true ^mem = ∅
End   (Lean name `mtrue`; Overload True = true ^mem) -/
def mtrue [Inhabited U] (mem : U → U → Prop) : U := empty mem

/- HOL4: Definition false_def:
  false ^mem = One
End   (Lean name `mfalse`; Overload False = false ^mem) -/
def mfalse [Inhabited U] (mem : U → U → Prop) : U := one mem

/- HOL4: Overload boolset = ``Two`` -/
def boolset [Inhabited U] (mem : U → U → Prop) : U := two mem

/- HOL4: Definition boolean_def:
  boolean ^mem b = if b then True else False
End   (Overload Boolean = boolean ^mem) -/
def boolean [Inhabited U] (mem : U → U → Prop) (b : Prop) : U := if b then mtrue mem else mfalse mem

/- HOL4: Definition abstract_def:
  abstract ^mem dom rng f = (dom × rng suchthat λx. ∃a. x = (a,f a))
End   (Overload Abstract = abstract ^mem) -/
def abstract (mem : U → U → Prop) (dom rng : U) (f : U → U) : U :=
  sub mem (product mem dom rng) (fun x => ∃ a, x = pair mem a (f a))


/- HOL4: Theorem is_extensional:
   is_set_theory ^mem ⇒ extensional mem -/
theorem is_extensional (mem : U → U → Prop) : is_set_theory mem → extensional mem := by sorry

/- HOL4: Theorem is_separation_sub:
   is_set_theory ^mem ⇒ is_separation mem (sub mem) -/
theorem is_separation_sub (mem : U → U → Prop) : is_set_theory mem → is_separation mem (sub mem) := by sorry

/- HOL4: Theorem is_power_power:
   is_set_theory ^mem ⇒ is_power mem (power mem) -/
theorem is_power_power (mem : U → U → Prop) : is_set_theory mem → is_power mem (power mem) := by sorry

/- HOL4: Theorem is_union_union:
   is_set_theory ^mem ⇒ is_union mem (union mem) -/
theorem is_union_union (mem : U → U → Prop) : is_set_theory mem → is_union mem (union mem) := by sorry

/- HOL4: Theorem is_upair_upair:
   is_set_theory ^mem ⇒ is_upair mem (upair mem) -/
theorem is_upair_upair (mem : U → U → Prop) : is_set_theory mem → is_upair mem (upair mem) := by sorry

/- HOL4: Theorem mem_sub:
   is_set_theory ^mem ⇒ ∀x s P. x <: (s suchthat P) ⇔ x <: s ∧ P x -/
theorem mem_sub (mem : U → U → Prop) : is_set_theory mem →
    ∀ x s P, mem x (sub mem s P) ↔ mem x s ∧ P x := by sorry

/- HOL4: Theorem mem_power:
   is_set_theory ^mem ⇒
    ∀x y. x <: (Pow y) ⇔ (∀b. b <: x ⇒ b <: y) -/
theorem mem_power (mem : U → U → Prop) : is_set_theory mem →
    ∀ x y, mem x (power mem y) ↔ (∀ b, mem b x → mem b y) := by sorry

/- HOL4: Theorem mem_union:
   is_set_theory ^mem ⇒
    ∀x s. x <: (union mem s) ⇔ ∃a. x <: a ∧ a <: s -/
theorem mem_union (mem : U → U → Prop) : is_set_theory mem →
    ∀ x s, mem x (union mem s) ↔ ∃ a, mem x a ∧ mem a s := by sorry

/- HOL4: Theorem mem_upair:
   is_set_theory ^mem ⇒ ∀a x y. a <: (x + y) ⇔ a = x ∨ a = y -/
theorem mem_upair (mem : U → U → Prop) : is_set_theory mem →
    ∀ a x y, mem a (upair mem x y) ↔ a = x ∨ a = y := by sorry

/- HOL4: Theorem mem_empty:
   is_set_theory ^mem ⇒ ∀x. ¬(x <: ∅) -/
theorem mem_empty [Inhabited U] (mem : U → U → Prop) : is_set_theory mem →
    ∀ x, ¬ mem x (empty mem) := by sorry

/- HOL4: Theorem mem_unit:
   is_set_theory ^mem ⇒
    ∀x y. x <: (Unit y) ⇔ x = y -/
theorem mem_unit (mem : U → U → Prop) : is_set_theory mem →
    ∀ x y, mem x (unit mem y) ↔ x = y := by sorry

/- HOL4: Theorem unit_inj:
   is_set_theory ^mem ⇒
    ∀x y. Unit x = Unit y ⇔ x = y -/
theorem unit_inj (mem : U → U → Prop) : is_set_theory mem →
    ∀ x y, unit mem x = unit mem y ↔ x = y := by sorry

/- HOL4: Theorem mem_one:
   is_set_theory ^mem ⇒
    ∀x. x <: One ⇔ x = ∅ -/
theorem mem_one [Inhabited U] (mem : U → U → Prop) : is_set_theory mem →
    ∀ x, mem x (one mem) ↔ x = empty mem := by sorry

/- HOL4: Theorem mem_two:
   is_set_theory ^mem ⇒
    ∀x. x <: Two ⇔ x = ∅ ∨ x = One -/
theorem mem_two [Inhabited U] (mem : U → U → Prop) : is_set_theory mem →
    ∀ x, mem x (two mem) ↔ x = empty mem ∨ x = one mem := by sorry

/- HOL4: Theorem upair_inj:
   is_set_theory ^mem ⇒
    ∀a b c d. a + b = c + d ⇔ a = c ∧ b = d ∨ a = d ∧ b = c -/
theorem upair_inj (mem : U → U → Prop) : is_set_theory mem →
    ∀ a b c d, upair mem a b = upair mem c d ↔ (a = c ∧ b = d ∨ a = d ∧ b = c) := by sorry

/- HOL4: Theorem unit_eq_upair:
   is_set_theory ^mem ⇒
    ∀x y z. Unit x = y + z ⇔ x = y ∧ y = z -/
theorem unit_eq_upair (mem : U → U → Prop) : is_set_theory mem →
    ∀ x y z, unit mem x = upair mem y z ↔ (x = y ∧ y = z) := by sorry

/- HOL4: Theorem pair_inj:
   is_set_theory ^mem ⇒
    ∀a b c d. (a,b) = (c,d) ⇔ a = c ∧ b = d -/
theorem pair_inj (mem : U → U → Prop) : is_set_theory mem →
    ∀ a b c d, pair mem a b = pair mem c d ↔ (a = c ∧ b = d) := by sorry

/- HOL4: Theorem mem_binary_union:
   is_set_theory ^mem ⇒
    ∀a x y. a <: (x ∪ y) ⇔ a <: x ∨ a <: y -/
theorem mem_binary_union (mem : U → U → Prop) : is_set_theory mem →
    ∀ a x y, mem a (binary_union mem x y) ↔ (mem a x ∨ mem a y) := by sorry

/- HOL4: Theorem mem_product:
   is_set_theory ^mem ⇒
    ∀a x y. a <: (x × y) ⇔ ∃b c. a = (b,c) ∧ b <: x ∧ c <: y -/
theorem mem_product (mem : U → U → Prop) : is_set_theory mem →
    ∀ a x y, mem a (product mem x y) ↔ ∃ b c, a = pair mem b c ∧ mem b x ∧ mem c y := by sorry

/- HOL4: Theorem true_neq_false:
   is_set_theory ^mem ⇒ True ≠ False -/
theorem true_neq_false [Inhabited U] (mem : U → U → Prop) : is_set_theory mem →
    mtrue mem ≠ mfalse mem := by sorry

/- HOL4: Theorem mem_boolset:
   is_set_theory ^mem ⇒
    ∀x. x <: boolset ⇔ ((x = True) ∨ (x = False)) -/
theorem mem_boolset [Inhabited U] (mem : U → U → Prop) : is_set_theory mem →
    ∀ x, mem x (boolset mem) ↔ (x = mtrue mem ∨ x = mfalse mem) := by sorry

/- HOL4: Theorem boolean_in_boolset:
   is_set_theory ^mem ⇒
    ∀b. Boolean b <: boolset -/
theorem boolean_in_boolset [Inhabited U] (mem : U → U → Prop) : is_set_theory mem →
    ∀ b, mem (boolean mem b) (boolset mem) := by sorry

/- HOL4: Theorem boolean_eq_true:
   is_set_theory ^mem ⇒ ∀b. Boolean b = True ⇔ b -/
theorem boolean_eq_true [Inhabited U] (mem : U → U → Prop) : is_set_theory mem →
    ∀ b, boolean mem b = mtrue mem ↔ b := by sorry

/- HOL4: Theorem apply_abstract:
   is_set_theory ^mem ⇒
    ∀f x s t. x <: s ∧ f x <: t ⇒ (Abstract s t f) ' x = f x -/
theorem apply_abstract [Inhabited U] (mem : U → U → Prop) : is_set_theory mem →
    ∀ f x s t, mem x s ∧ mem (f x) t → apply mem (abstract mem s t f) x = f x := by sorry

/- HOL4: Theorem apply_in_rng:
   is_set_theory ^mem ⇒
    ∀f x s t. x <: s ∧ f <: Funspace s t ⇒
    f ' x <: t -/
theorem apply_in_rng [Inhabited U] (mem : U → U → Prop) : is_set_theory mem →
    ∀ f x s t, mem x s ∧ mem f (funspace mem s t) → mem (apply mem f x) t := by sorry

/- HOL4: Theorem abstract_in_funspace:
   is_set_theory ^mem ⇒
    ∀f s t. (∀x. x <: s ⇒ f x <: t) ⇒ Abstract s t f <: Funspace s t -/
theorem abstract_in_funspace (mem : U → U → Prop) : is_set_theory mem →
    ∀ f s t, (∀ x, mem x s → mem (f x) t) → mem (abstract mem s t f) (funspace mem s t) := by sorry

/- HOL4: Theorem abstract_eq:
   is_set_theory ^mem ⇒
    ∀s t1 t2 f g.
    (∀x. x <: s ⇒ f x <: t1 ∧ g x <: t2 ∧ f x = g x)
    ⇒ Abstract s t1 f = Abstract s t2 g -/
theorem abstract_eq (mem : U → U → Prop) : is_set_theory mem →
    ∀ s t1 t2 f g, (∀ x, mem x s → mem (f x) t1 ∧ mem (g x) t2 ∧ f x = g x) →
      abstract mem s t1 f = abstract mem s t2 g := by sorry

end

end Candle.SetSpec
