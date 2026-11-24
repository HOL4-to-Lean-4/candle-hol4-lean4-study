import CandleLean.Misc

/-!
# setSpec (CakeML `candle/set-theory/setSpecScript.sml`)

The membership relation `mem : U → U → Prop` is an explicit argument, as in HOL4 (`^mem`).
HOL4 overloads that hide `mem` are written with `mem` explicit:
`x <: y` = `mem x y`, `s suchthat P` = `sub mem s P`, `Pow` = `power mem`, `x + y` = `upair mem x y`,
`∅` = `empty mem`, `Unit` = `unit mem`, `One` = `one mem`, `Two`/`boolset` = `two mem`,
`(x,y)` = `pair mem x y`, `x ∪ y` = `binary_union mem x y`, `x × y` = `product mem x y`,
`Relspace` = `relspace mem`, `Funspace` = `funspace mem`, `f ' x` = `apply mem f x`,
`True` = `true_ mem`, `False` = `false_ mem`, `Boolean` = `boolean mem`, `Abstract` = `abstract mem`.
Constants that need an unspecified element of `U` (`empty` uses `ARB`) take `[Nonempty U]`
(every HOL4 type is non-empty).
-/

universe u

namespace Candle

open HOL Classical

noncomputable section

variable {U : Type u}

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
   (Hilbert choice; the function type is inhabited, e.g. by `\x P. x`) -/
def sub (mem : U → U → Prop) : U → (U → Prop) → U :=
  @Classical.epsilon _ ⟨fun x _ => x⟩ (fun sub => is_separation mem sub)

/- HOL4:
Definition power_def:
  power ^mem = @power. is_power mem power
End -/
def power (mem : U → U → Prop) : U → U :=
  @Classical.epsilon _ ⟨fun x => x⟩ (fun power => is_power mem power)

/- HOL4:
Definition union_def:
  union ^mem = @union. is_union mem union
End -/
def union (mem : U → U → Prop) : U → U :=
  @Classical.epsilon _ ⟨fun x => x⟩ (fun union => is_union mem union)

/- HOL4:
Definition upair_def:
  upair ^mem = @upair. is_upair mem upair
End -/
def upair (mem : U → U → Prop) : U → U → U :=
  @Classical.epsilon _ ⟨fun x _ => x⟩ (fun upair => is_upair mem upair)

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
def unit (mem : U → U → Prop) (x : U) : U := upair mem x x

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
Overload Two = ``two ^mem`` -/
def two [Nonempty U] (mem : U → U → Prop) : U := upair mem (empty mem) (one mem)

/- HOL4:
Definition pair_def:
  pair ^mem x y = (Unit x) + (x + y)
End
Overload "," = ``pair ^mem`` -/
def pair (mem : U → U → Prop) (x y : U) : U := upair mem (unit mem x) (upair mem x y)

/- HOL4:
Definition binary_union_def:
  binary_union ^mem x y = union mem (upair mem x y)
End
Overload UNION = ``binary_union ^mem`` -/
def binary_union (mem : U → U → Prop) (x y : U) : U := union mem (upair mem x y)

/- HOL4:
Definition product_def:
  product ^mem x y =
    (Pow (Pow (x ∪ y)) suchthat
     λa. ∃b c. b <: x ∧ c <: y ∧ a = (b,c))
End
Overload CROSS = ``product ^mem`` -/
def product (mem : U → U → Prop) (x y : U) : U :=
  sub mem (power mem (power mem (binary_union mem x y)))
    (fun a => ∃ b c, mem b x ∧ mem c y ∧ a = pair mem b c)

/- HOL4:
Definition relspace_def:
  relspace ^mem x y = Pow (x × y)
End
Overload Relspace = ``relspace ^mem`` -/
def relspace (mem : U → U → Prop) (x y : U) : U := power mem (product mem x y)

/- HOL4:
Definition funspace_def:
  funspace ^mem x y =
    (Relspace x y suchthat
     λf. ∀a. a <: x ⇒ ∃!b. (a,b) <: f)
End
Overload Funspace = ``funspace ^mem`` -/
def funspace (mem : U → U → Prop) (x y : U) : U :=
  sub mem (relspace mem x y)
    (fun f => ∀ a, mem a x → EXISTS_UNIQUE (fun b => mem (pair mem a b) f))

/- HOL4:
Definition apply_def:
  apply ^mem x y = @a. (y,a) <: x
End
val _ = Parse.add_infix("'",2000,Parse.LEFT);
Overload "'" = ``apply ^mem``
   (`x ' y` is `apply mem x y`; the Hilbert choice is over `U`, inhabited by `x`) -/
def apply (mem : U → U → Prop) (x y : U) : U :=
  @Classical.epsilon U ⟨x⟩ (fun a => mem (pair mem y a) x)

/- HOL4: Overload boolset = ``Two`` -/
@[reducible] def boolset [Nonempty U] (mem : U → U → Prop) : U := two mem

/- HOL4:
Definition true_def:
  true ^mem = ∅
End
Overload True = ``true ^mem``
   (Lean name `true_`, to avoid Lean's `true`) -/
def true_ [Nonempty U] (mem : U → U → Prop) : U := empty mem

/- HOL4:
Definition false_def:
  false ^mem = One
End
Overload False = ``false ^mem``
   (Lean name `false_`, to avoid Lean's `false`) -/
def false_ [Nonempty U] (mem : U → U → Prop) : U := one mem

/- HOL4:
Definition boolean_def:
  boolean ^mem b = if b then True else False
End
Overload Boolean = ``boolean ^mem`` -/
def boolean [Nonempty U] (mem : U → U → Prop) (b : Prop) : U :=
  if b then true_ mem else false_ mem

/- HOL4:
Definition abstract_def:
  abstract ^mem dom rng f = (dom × rng suchthat λx. ∃a. x = (a,f a))
End
Overload Abstract = ``abstract ^mem`` -/
def abstract (mem : U → U → Prop) (dom rng : U) (f : U → U) : U :=
  sub mem (product mem dom rng) (fun x => ∃ a, x = pair mem a (f a))

/-! ## Theorems (stage 2) -/

/- HOL4:
Theorem is_extensional:
   is_set_theory ^mem ⇒ extensional mem
-/
theorem is_extensional (mem : U → U → Prop) :
    is_set_theory mem → extensional mem := by
  intro h
  exact h.1

/- HOL4:
Theorem is_separation_sub:
   is_set_theory ^mem ⇒ is_separation mem (sub mem)
-/
theorem is_separation_sub (mem : U → U → Prop) :
    is_set_theory mem → is_separation mem (sub mem) := by
  intro h
  exact Classical.epsilon_spec h.2.1

/- HOL4:
Theorem is_power_power:
   is_set_theory ^mem ⇒ is_power mem (power mem)
-/
theorem is_power_power (mem : U → U → Prop) :
    is_set_theory mem → is_power mem (power mem) := by
  intro h
  exact Classical.epsilon_spec h.2.2.1

/- HOL4:
Theorem is_union_union:
   is_set_theory ^mem ⇒ is_union mem (union mem)
-/
theorem is_union_union (mem : U → U → Prop) :
    is_set_theory mem → is_union mem (union mem) := by
  intro h
  exact Classical.epsilon_spec h.2.2.2.1

/- HOL4:
Theorem is_upair_upair:
   is_set_theory ^mem ⇒ is_upair mem (upair mem)
-/
theorem is_upair_upair (mem : U → U → Prop) :
    is_set_theory mem → is_upair mem (upair mem) := by
  intro h
  exact Classical.epsilon_spec h.2.2.2.2

/- HOL4:
Theorem mem_sub:
   is_set_theory ^mem ⇒ ∀x s P. x <: (s suchthat P) ⇔ x <: s ∧ P x
-/
theorem mem_sub (mem : U → U → Prop) :
    is_set_theory mem → ∀ x s P, mem x (sub mem s P) ↔ mem x s ∧ P x := by
  intro h x s P
  exact is_separation_sub mem h s P x

/- HOL4:
Theorem mem_power:
   is_set_theory ^mem ⇒
    ∀x y. x <: (Pow y) ⇔ (∀b. b <: x ⇒ b <: y)
-/
theorem mem_power (mem : U → U → Prop) :
    is_set_theory mem →
      ∀ x y, mem x (power mem y) ↔ (∀ b, mem b x → mem b y) := by
  intro h x y
  exact is_power_power mem h y x

/- HOL4:
Theorem mem_union:
   is_set_theory ^mem ⇒
    ∀x s. x <: (union mem s) ⇔ ∃a. x <: a ∧ a <: s
-/
theorem mem_union (mem : U → U → Prop) :
    is_set_theory mem →
      ∀ x s, mem x (union mem s) ↔ ∃ a, mem x a ∧ mem a s := by
  intro h x s
  exact is_union_union mem h s x

/- HOL4:
Theorem mem_upair:
   is_set_theory ^mem ⇒ ∀a x y. a <: (x + y) ⇔ a = x ∨ a = y
-/
theorem mem_upair (mem : U → U → Prop) :
    is_set_theory mem → ∀ a x y, mem a (upair mem x y) ↔ a = x ∨ a = y := by
  intro h a x y
  exact is_upair_upair mem h x y a

theorem Aux.ext_mem (mem : U → U → Prop) (h : is_set_theory mem) {x y : U}
    (he : ∀ a, mem a x ↔ mem a y) : x = y := (is_extensional mem h x y).mpr he

/- HOL4:
Theorem mem_empty:
   is_set_theory ^mem ⇒ ∀x. ¬(x <: ∅)
-/
theorem mem_empty [Nonempty U] (mem : U → U → Prop) :
    is_set_theory mem → ∀ x, ¬ mem x (empty mem) := by
  intro h x hx
  exact ((mem_sub mem h x ARB (K False)).mp hx).2

/- HOL4:
Theorem mem_unit:
   is_set_theory ^mem ⇒
    ∀x y. x <: (Unit y) ⇔ x = y
-/
theorem mem_unit (mem : U → U → Prop) :
    is_set_theory mem → ∀ x y, mem x (unit mem y) ↔ x = y := by
  intro h x y
  rw [unit, mem_upair mem h]
  exact or_self_iff

/- HOL4:
Theorem unit_inj:
   is_set_theory ^mem ⇒
    ∀x y. Unit x = Unit y ⇔ x = y
-/
theorem unit_inj (mem : U → U → Prop) :
    is_set_theory mem → ∀ x y, unit mem x = unit mem y ↔ x = y := by
  intro h x y
  constructor
  · intro e
    have h1 : mem x (unit mem x) := (mem_unit mem h x x).mpr rfl
    rw [e] at h1
    exact (mem_unit mem h x y).mp h1
  · rintro rfl; rfl

/- HOL4:
Theorem mem_one:
   is_set_theory ^mem ⇒
    ∀x. x <: One ⇔ x = ∅
-/
theorem mem_one [Nonempty U] (mem : U → U → Prop) :
    is_set_theory mem → ∀ x, mem x (one mem) ↔ x = empty mem := by
  intro h x
  exact mem_unit mem h x (empty mem)

/- HOL4:
Theorem mem_two:
   is_set_theory ^mem ⇒
    ∀x. x <: Two ⇔ x = ∅ ∨ x = One
-/
theorem mem_two [Nonempty U] (mem : U → U → Prop) :
    is_set_theory mem → ∀ x, mem x (two mem) ↔ x = empty mem ∨ x = one mem := by
  intro h x
  exact mem_upair mem h x (empty mem) (one mem)

/- HOL4:
Theorem upair_inj:
   is_set_theory ^mem ⇒
    ∀a b c d. a + b = c + d ⇔ a = c ∧ b = d ∨ a = d ∧ b = c
-/
theorem upair_inj (mem : U → U → Prop) :
    is_set_theory mem →
      ∀ a b c d, upair mem a b = upair mem c d ↔ (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  intro h a b c d
  constructor
  · intro e
    have ha : a = c ∨ a = d := by
      rw [← mem_upair mem h, ← e, mem_upair mem h]; exact Or.inl rfl
    have hb : b = c ∨ b = d := by
      rw [← mem_upair mem h, ← e, mem_upair mem h]; exact Or.inr rfl
    have hc : c = a ∨ c = b := by
      rw [← mem_upair mem h, e, mem_upair mem h]; exact Or.inl rfl
    have hd : d = a ∨ d = b := by
      rw [← mem_upair mem h, e, mem_upair mem h]; exact Or.inr rfl
    grind
  · intro hh
    apply Aux.ext_mem mem h
    intro x
    rw [mem_upair mem h, mem_upair mem h]
    grind

/- HOL4:
Theorem unit_eq_upair:
   is_set_theory ^mem ⇒
    ∀x y z. Unit x = y + z ⇔ x = y ∧ y = z
-/
theorem unit_eq_upair (mem : U → U → Prop) :
    is_set_theory mem → ∀ x y z, unit mem x = upair mem y z ↔ x = y ∧ y = z := by
  intro h x y z
  rw [unit, upair_inj mem h]
  grind

/- HOL4:
Theorem pair_inj:
   is_set_theory ^mem ⇒
    ∀a b c d. (a,b) = (c,d) ⇔ a = c ∧ b = d
-/
theorem pair_inj (mem : U → U → Prop) :
    is_set_theory mem → ∀ a b c d, pair mem a b = pair mem c d ↔ a = c ∧ b = d := by
  intro h a b c d
  simp only [pair]
  rw [upair_inj mem h, unit_inj mem h, upair_inj mem h, unit_eq_upair mem h,
    eq_comm (a := upair mem a b), unit_eq_upair mem h]
  grind

/- HOL4:
Theorem mem_binary_union:
   is_set_theory ^mem ⇒
    ∀a x y. a <: (x ∪ y) ⇔ a <: x ∨ a <: y
-/
theorem mem_binary_union (mem : U → U → Prop) :
    is_set_theory mem → ∀ a x y, mem a (binary_union mem x y) ↔ mem a x ∨ mem a y := by
  intro h a x y
  rw [binary_union, mem_union mem h]
  constructor
  · rintro ⟨b, hb, hb2⟩
    rw [mem_upair mem h] at hb2
    rcases hb2 with rfl | rfl
    · exact Or.inl hb
    · exact Or.inr hb
  · rintro (h1 | h1)
    · exact ⟨x, h1, (mem_upair mem h x x y).mpr (Or.inl rfl)⟩
    · exact ⟨y, h1, (mem_upair mem h y x y).mpr (Or.inr rfl)⟩

/- HOL4:
Theorem mem_product:
   is_set_theory ^mem ⇒
    ∀a x y. a <: (x × y) ⇔ ∃b c. a = (b,c) ∧ b <: x ∧ c <: y
-/
theorem mem_product (mem : U → U → Prop) :
    is_set_theory mem →
      ∀ a x y, mem a (product mem x y) ↔ ∃ b c, a = pair mem b c ∧ mem b x ∧ mem c y := by
  intro h a x y
  rw [product, mem_sub mem h]
  constructor
  · rintro ⟨_, b, c, hb, hc, e⟩
    exact ⟨b, c, e, hb, hc⟩
  · rintro ⟨b, c, rfl, hb, hc⟩
    refine ⟨?_, b, c, hb, hc, rfl⟩
    rw [mem_power mem h]
    intro e he
    rw [mem_power mem h]
    intro f hf
    rw [mem_binary_union mem h]
    rw [pair, mem_upair mem h] at he
    rcases he with rfl | rfl
    · rw [mem_unit mem h] at hf
      subst hf; exact Or.inl hb
    · rw [mem_upair mem h] at hf
      rcases hf with rfl | rfl
      · exact Or.inl hb
      · exact Or.inr hc

/- HOL4:
Theorem true_neq_false:
   is_set_theory ^mem ⇒ True ≠ False
-/
theorem true_neq_false [Nonempty U] (mem : U → U → Prop) :
    is_set_theory mem → true_ mem ≠ false_ mem := by
  intro h e
  have h1 : mem (empty mem) (one mem) := (mem_one mem h _).mpr rfl
  have e' : empty mem = one mem := e
  rw [← e'] at h1
  exact mem_empty mem h _ h1

/- HOL4:
Theorem mem_boolset:
   is_set_theory ^mem ⇒
    ∀x. x <: boolset ⇔ ((x = True) ∨ (x = False))
-/
theorem mem_boolset [Nonempty U] (mem : U → U → Prop) :
    is_set_theory mem → ∀ x, mem x (boolset mem) ↔ (x = true_ mem ∨ x = false_ mem) := by
  intro h x
  exact mem_two mem h x

/- HOL4:
Theorem boolean_in_boolset:
   is_set_theory ^mem ⇒
    ∀b. Boolean b <: boolset
-/
theorem boolean_in_boolset [Nonempty U] (mem : U → U → Prop) :
    is_set_theory mem → ∀ b : Prop, mem (boolean mem b) (boolset mem) := by
  intro h b
  rw [mem_boolset mem h, boolean]
  by_cases hb : b
  · exact Or.inl (if_pos hb)
  · exact Or.inr (if_neg hb)

/- HOL4:
Theorem boolean_eq_true:
   is_set_theory ^mem ⇒ ∀b. Boolean b = True ⇔ b
-/
theorem boolean_eq_true [Nonempty U] (mem : U → U → Prop) :
    is_set_theory mem → ∀ b : Prop, boolean mem b = true_ mem ↔ b := by
  intro h b
  by_cases hb : b
  · exact ⟨fun _ => hb, fun _ => if_pos hb⟩
  · rw [boolean, if_neg hb]
    exact ⟨fun e => absurd e.symm (true_neq_false mem h), fun h' => absurd h' hb⟩

theorem Aux.mem_abstract (mem : U → U → Prop) (h : is_set_theory mem) (p s t : U) (f : U → U) :
    mem p (abstract mem s t f) ↔ ∃ a, p = pair mem a (f a) ∧ mem a s ∧ mem (f a) t := by
  rw [abstract, mem_sub mem h, mem_product mem h]
  constructor
  · rintro ⟨⟨b, c, e1, hb, hc⟩, a, rfl⟩
    rw [pair_inj mem h] at e1
    obtain ⟨rfl, rfl⟩ := e1
    exact ⟨a, rfl, hb, hc⟩
  · rintro ⟨a, rfl, ha, hf⟩
    exact ⟨⟨a, f a, rfl, ha, hf⟩, a, rfl⟩

theorem Aux.apply_spec (mem : U → U → Prop) (f x : U) (h : ∃ a, mem (pair mem x a) f) :
    mem (pair mem x (apply mem f x)) f := Classical.epsilon_spec (p := fun a => mem (pair mem x a) f) h

/- HOL4:
Theorem apply_abstract:
   is_set_theory ^mem ⇒
    ∀f x s t. x <: s ∧ f x <: t ⇒ (Abstract s t f) ' x = f x
-/
theorem apply_abstract (mem : U → U → Prop) :
    is_set_theory mem →
      ∀ (f : U → U) x s t, mem x s ∧ mem (f x) t → apply mem (abstract mem s t f) x = f x := by
  intro h f x s t ⟨hx, hf⟩
  have h1 := Aux.apply_spec mem (abstract mem s t f) x
    ⟨f x, (Aux.mem_abstract mem h _ s t f).mpr ⟨x, rfl, hx, hf⟩⟩
  obtain ⟨a, e, _, _⟩ := (Aux.mem_abstract mem h _ s t f).mp h1
  rw [pair_inj mem h] at e
  rw [e.2, ← e.1]

/- HOL4:
Theorem apply_in_rng:
   is_set_theory ^mem ⇒
    ∀f x s t. x <: s ∧ f <: Funspace s t ⇒
    f ' x <: t
-/
theorem apply_in_rng (mem : U → U → Prop) :
    is_set_theory mem →
      ∀ f x s t, mem x s ∧ mem f (funspace mem s t) → mem (apply mem f x) t := by
  intro h f x s t ⟨hx, hf⟩
  rw [funspace, mem_sub mem h, relspace, mem_power mem h] at hf
  have h1 := Aux.apply_spec mem f x (hf.2 x hx).1
  obtain ⟨b, c, e, _, hc⟩ := (mem_product mem h _ s t).mp (hf.1 _ h1)
  rw [pair_inj mem h] at e
  rw [e.2]; exact hc

/- HOL4:
Theorem abstract_in_funspace:
   is_set_theory ^mem ⇒
    ∀f s t. (∀x. x <: s ⇒ f x <: t) ⇒ Abstract s t f <: Funspace s t
-/
theorem abstract_in_funspace (mem : U → U → Prop) :
    is_set_theory mem →
      ∀ (f : U → U) s t, (∀ x, mem x s → mem (f x) t) →
        mem (abstract mem s t f) (funspace mem s t) := by
  intro h f s t hf
  rw [funspace, mem_sub mem h, relspace, mem_power mem h]
  constructor
  · intro b hb
    rw [Aux.mem_abstract mem h] at hb
    obtain ⟨a, rfl, ha, hfa⟩ := hb
    exact (mem_product mem h _ s t).mpr ⟨a, f a, rfl, ha, hfa⟩
  · intro a ha
    refine ⟨⟨f a, (Aux.mem_abstract mem h _ s t f).mpr ⟨a, rfl, ha, hf a ha⟩⟩, ?_⟩
    rintro x y ⟨hx, hy⟩
    obtain ⟨b, e, _, _⟩ := (Aux.mem_abstract mem h _ s t f).mp hx
    obtain ⟨c, e2, _, _⟩ := (Aux.mem_abstract mem h _ s t f).mp hy
    rw [pair_inj mem h] at e e2
    rw [e.2, e2.2, ← e.1, ← e2.1]

/- HOL4:
Theorem abstract_eq:
   is_set_theory ^mem ⇒
    ∀s t1 t2 f g.
    (∀x. x <: s ⇒ f x <: t1 ∧ g x <: t2 ∧ f x = g x)
    ⇒ Abstract s t1 f = Abstract s t2 g
-/
theorem abstract_eq (mem : U → U → Prop) :
    is_set_theory mem →
      ∀ s t1 t2 (f g : U → U),
        (∀ x, mem x s → mem (f x) t1 ∧ mem (g x) t2 ∧ f x = g x) →
        abstract mem s t1 f = abstract mem s t2 g := by
  intro h s t1 t2 f g hfg
  apply Aux.ext_mem mem h
  intro p
  rw [Aux.mem_abstract mem h, Aux.mem_abstract mem h]
  constructor
  · rintro ⟨a, rfl, ha, _⟩
    obtain ⟨_, h2, e⟩ := hfg a ha
    exact ⟨a, by rw [e], ha, h2⟩
  · rintro ⟨a, rfl, ha, _⟩
    obtain ⟨h1, _, e⟩ := hfg a ha
    exact ⟨a, by rw [e], ha, h1⟩

end

end Candle
