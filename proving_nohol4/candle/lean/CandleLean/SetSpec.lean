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
  exact Classical.epsilon_spec (p := fun s => is_separation mem s) h.2.1

/- HOL4:
Theorem is_power_power:
   is_set_theory ^mem ⇒ is_power mem (power mem)
-/
theorem is_power_power (mem : U → U → Prop) :
    is_set_theory mem → is_power mem (power mem) := by
  intro h
  exact Classical.epsilon_spec (p := fun s => is_power mem s) h.2.2.1

/- HOL4:
Theorem is_union_union:
   is_set_theory ^mem ⇒ is_union mem (union mem)
-/
theorem is_union_union (mem : U → U → Prop) :
    is_set_theory mem → is_union mem (union mem) := by
  intro h
  exact Classical.epsilon_spec (p := fun s => is_union mem s) h.2.2.2.1

/- HOL4:
Theorem is_upair_upair:
   is_set_theory ^mem ⇒ is_upair mem (upair mem)
-/
theorem is_upair_upair (mem : U → U → Prop) :
    is_set_theory mem → is_upair mem (upair mem) := by
  intro h
  exact Classical.epsilon_spec (p := fun s => is_upair mem s) h.2.2.2.2

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

theorem Aux.mem_ext (mem : U → U → Prop) (h : is_set_theory mem) {x y : U}
    (hxy : ∀ a, mem a x ↔ mem a y) : x = y := (h.1 x y).mpr hxy

/- HOL4:
Theorem mem_empty:
   is_set_theory ^mem ⇒ ∀x. ¬(x <: ∅)
-/
theorem mem_empty [Nonempty U] (mem : U → U → Prop) :
    is_set_theory mem → ∀ x, ¬ mem x (empty mem) := by
  intro h x hx
  exact ((mem_sub mem h x _ _).mp hx).2

/- HOL4:
Theorem mem_unit:
   is_set_theory ^mem ⇒
    ∀x y. x <: (Unit y) ⇔ x = y
-/
theorem mem_unit (mem : U → U → Prop) :
    is_set_theory mem → ∀ x y, mem x (unit mem y) ↔ x = y := by
  intro h x y
  unfold unit
  rw [mem_upair mem h]
  simp

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
    rw [← mem_unit mem h, ← e, mem_unit mem h]
  · rintro rfl; rfl

/- HOL4:
Theorem mem_one:
   is_set_theory ^mem ⇒
    ∀x. x <: One ⇔ x = ∅
-/
theorem mem_one [Nonempty U] (mem : U → U → Prop) :
    is_set_theory mem → ∀ x, mem x (one mem) ↔ x = empty mem := by
  intro h x
  exact mem_unit mem h x _

/- HOL4:
Theorem mem_two:
   is_set_theory ^mem ⇒
    ∀x. x <: Two ⇔ x = ∅ ∨ x = One
-/
theorem mem_two [Nonempty U] (mem : U → U → Prop) :
    is_set_theory mem → ∀ x, mem x (two mem) ↔ x = empty mem ∨ x = one mem := by
  intro h x
  exact mem_upair mem h x _ _

/- HOL4:
Theorem upair_inj:
   is_set_theory ^mem ⇒
    ∀a b c d. a + b = c + d ⇔ a = c ∧ b = d ∨ a = d ∧ b = c
-/
theorem upair_inj (mem : U → U → Prop) :
    is_set_theory mem →
      ∀ a b c d, upair mem a b = upair mem c d ↔ (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  intro h a b c d
  have hm := mem_upair mem h
  constructor
  · intro e
    have h1 := hm a a b
    have h2 := hm b a b
    have h3 := hm c c d
    have h4 := hm d c d
    have h5 := hm c a b
    have h6 := hm d a b
    have h7 := hm a c d
    have h8 := hm b c d
    rw [e] at h1 h2 h5 h6
    grind
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rfl
    · apply Aux.mem_ext mem h
      intro x
      rw [hm, hm]
      exact Or.comm

/- HOL4:
Theorem unit_eq_upair:
   is_set_theory ^mem ⇒
    ∀x y z. Unit x = y + z ⇔ x = y ∧ y = z
-/
theorem unit_eq_upair (mem : U → U → Prop) :
    is_set_theory mem → ∀ x y z, unit mem x = upair mem y z ↔ x = y ∧ y = z := by
  intro h x y z
  unfold unit
  rw [upair_inj mem h]
  grind

/- HOL4:
Theorem pair_inj:
   is_set_theory ^mem ⇒
    ∀a b c d. (a,b) = (c,d) ⇔ a = c ∧ b = d
-/
theorem pair_inj (mem : U → U → Prop) :
    is_set_theory mem → ∀ a b c d, pair mem a b = pair mem c d ↔ a = c ∧ b = d := by
  intro h a b c d
  unfold pair
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
  unfold binary_union
  rw [mem_union mem h]
  simp only [mem_upair mem h]
  grind

/- HOL4:
Theorem mem_product:
   is_set_theory ^mem ⇒
    ∀a x y. a <: (x × y) ⇔ ∃b c. a = (b,c) ∧ b <: x ∧ c <: y
-/
theorem mem_product (mem : U → U → Prop) :
    is_set_theory mem →
      ∀ a x y, mem a (product mem x y) ↔ ∃ b c, a = pair mem b c ∧ mem b x ∧ mem c y := by
  intro h a x y
  unfold product
  rw [mem_sub mem h]
  constructor
  · rintro ⟨_, b, c, h1, h2, h3⟩
    exact ⟨b, c, h3, h1, h2⟩
  · rintro ⟨b, c, rfl, h1, h2⟩
    refine ⟨?_, b, c, h1, h2, rfl⟩
    rw [mem_power mem h]
    intro s hs
    rw [mem_power mem h]
    intro t ht
    rw [mem_binary_union mem h]
    unfold pair at hs
    rw [mem_upair mem h] at hs
    rcases hs with rfl | rfl
    · rw [mem_unit mem h] at ht
      exact Or.inl (ht ▸ h1)
    · rw [mem_upair mem h] at ht
      rcases ht with rfl | rfl
      · exact Or.inl h1
      · exact Or.inr h2

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
  rw [mem_boolset mem h]
  unfold boolean
  split
  · exact Or.inl rfl
  · exact Or.inr rfl

/- HOL4:
Theorem boolean_eq_true:
   is_set_theory ^mem ⇒ ∀b. Boolean b = True ⇔ b
-/
theorem boolean_eq_true [Nonempty U] (mem : U → U → Prop) :
    is_set_theory mem → ∀ b : Prop, boolean mem b = true_ mem ↔ b := by
  intro h b
  have := true_neq_false mem h
  unfold boolean
  by_cases hb : b
  · simp [hb]
  · simp [hb, this.symm]

theorem Aux.mem_abstract (mem : U → U → Prop) (h : is_set_theory mem) (s t : U) (f : U → U)
    (x y : U) : mem (pair mem x y) (abstract mem s t f) ↔ mem x s ∧ mem y t ∧ y = f x := by
  unfold abstract
  rw [mem_sub mem h, mem_product mem h]
  constructor
  · rintro ⟨⟨b, c, e, h1, h2⟩, a, e'⟩
    rw [pair_inj mem h] at e e'
    obtain ⟨rfl, rfl⟩ := e
    obtain ⟨rfl, rfl⟩ := e'
    exact ⟨h1, h2, rfl⟩
  · rintro ⟨h1, h2, rfl⟩
    exact ⟨⟨x, f x, rfl, h1, h2⟩, x, rfl⟩

theorem Aux.apply_spec (mem : U → U → Prop) (f x : U) (h : ∃ a, mem (pair mem x a) f) :
    mem (pair mem x (apply mem f x)) f :=
  @Classical.epsilon_spec U (fun a => mem (pair mem x a) f) h

/- HOL4:
Theorem apply_abstract:
   is_set_theory ^mem ⇒
    ∀f x s t. x <: s ∧ f x <: t ⇒ (Abstract s t f) ' x = f x
-/
theorem apply_abstract (mem : U → U → Prop) :
    is_set_theory mem →
      ∀ (f : U → U) x s t, mem x s ∧ mem (f x) t → apply mem (abstract mem s t f) x = f x := by
  rintro h f x s t ⟨h1, h2⟩
  have := Aux.apply_spec mem (abstract mem s t f) x
    ⟨f x, (Aux.mem_abstract mem h _ _ _ _ _).mpr ⟨h1, h2, rfl⟩⟩
  exact ((Aux.mem_abstract mem h _ _ _ _ _).mp this).2.2

/- HOL4:
Theorem apply_in_rng:
   is_set_theory ^mem ⇒
    ∀f x s t. x <: s ∧ f <: Funspace s t ⇒
    f ' x <: t
-/
theorem apply_in_rng (mem : U → U → Prop) :
    is_set_theory mem →
      ∀ f x s t, mem x s ∧ mem f (funspace mem s t) → mem (apply mem f x) t := by
  rintro h f x s t ⟨h1, h2⟩
  unfold funspace at h2
  rw [mem_sub mem h] at h2
  obtain ⟨h3, h4⟩ := h2
  have h5 := Aux.apply_spec mem f x (h4 x h1).1
  unfold relspace at h3
  rw [mem_power mem h] at h3
  obtain ⟨b, c, e, _, h6⟩ := (mem_product mem h _ _ _).mp (h3 _ h5)
  rw [pair_inj mem h] at e
  exact e.2 ▸ h6

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
  unfold funspace relspace
  rw [mem_sub mem h, mem_power mem h]
  refine ⟨fun b hb => ?_, fun a ha => ⟨⟨f a, ?_⟩, ?_⟩⟩
  · unfold abstract at hb
    exact ((mem_sub mem h _ _ _).mp hb).1
  · exact (Aux.mem_abstract mem h _ _ _ _ _).mpr ⟨ha, hf a ha, rfl⟩
  · rintro x y ⟨h1, h2⟩
    rw [Aux.mem_abstract mem h] at h1 h2
    rw [h1.2.2, h2.2.2]

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
  have key : is_set_theory mem → ∀ s t1 t2 (f g : U → U),
      (∀ x, mem x s → mem (f x) t1 ∧ mem (g x) t2 ∧ f x = g x) →
      ∀ a, mem a (abstract mem s t1 f) → mem a (abstract mem s t2 g) := by
    intro h s t1 t2 f g hfg a ha
    have ha' := ha
    unfold abstract at ha'
    rw [mem_sub mem h, mem_product mem h] at ha'
    obtain ⟨⟨b, c, rfl, _, _⟩, _⟩ := ha'
    rw [Aux.mem_abstract mem h] at ha ⊢
    obtain ⟨h1, h2, rfl⟩ := ha
    obtain ⟨h3, h4, h5⟩ := hfg b h1
    exact ⟨h1, h5 ▸ h4, h5⟩
  intro h s t1 t2 f g hfg
  apply Aux.mem_ext mem h
  intro a
  exact ⟨key h s t1 t2 f g hfg a,
    key h s t2 t1 g f (fun x hx => ⟨(hfg x hx).2.1, (hfg x hx).1, (hfg x hx).2.2.symm⟩) a⟩

end

end Candle
