import CmlTS.Prelude.Core

/-
The real numbers, as needed by the HOL4 theory `binary_ieee`.

There are no real numbers in Lean core or Batteries, so they are built here as
Dedekind cuts of rationals (the lower sets that are nonempty, bounded, downward
closed and without a greatest element).  Each operation is given by its set of
smaller rationals, with a proof that this set is a cut.
-/

namespace CmlTS

noncomputable section

open scoped Classical

/-- `S` is the set of rationals strictly below some real. -/
def IsCut (S : Rat → Prop) : Prop :=
  (∃ q, S q) ∧ (∃ q, ¬ S q) ∧ (∀ p q, S q → p < q → S p) ∧ (∀ q, S q → ∃ r, S r ∧ q < r)

theorem isCut_rat (r : Rat) : IsCut (fun q => q < r) := by
  refine ⟨⟨r - 1, ?_⟩, ⟨r, ?_⟩, ?_, ?_⟩
  · grind
  · grind
  · intro p q hq hp; grind
  · intro q hq; exact ⟨(q + r) / 2, by grind, by grind⟩

/- HOL4: realax$real -/
structure real where
  below : Rat → Prop
  isCut : IsCut below

namespace real

/-- The real number equal to a rational. -/
def ofRat (r : Rat) : real := ⟨fun q => q < r, isCut_rat r⟩

instance : Nonempty real := ⟨ofRat 0⟩

/- HOL4: realax$real_of_num (written `&n`, and numerals such as `2r`) -/
def ofNum (n : Nat) : real := ofRat (n : Rat)

instance (n : Nat) : OfNat real n := ⟨ofNum n⟩

/- HOL4: realax$real_lte (infix `<=`) -/
instance : LE real := ⟨fun x y => ∀ q, x.below q → y.below q⟩

/- HOL4: realax$real_lt (infix `<`)   x < y is the negation of y <= x -/
instance : LT real := ⟨fun x y => ¬ y ≤ x⟩

/-! Helper lemmas (not HOL4 constants): the sets below are cuts. -/

theorem rat_lt_or_le_aux (a b : Rat) : a < b ∨ b ≤ a := by grind

theorem below_lt_aux {x : real} {a b : Rat} (ha : x.below a) (hb : ¬ x.below b) : a < b := by
  rcases rat_lt_or_le_aux a b with h | h
  · exact h
  · exfalso
    by_cases hab : a = b
    · exact hb (hab ▸ ha)
    · exact hb (x.isCut.2.2.1 b a ha (by grind))

theorem isCut_add (x y : real) :
    IsCut fun q => ∃ a b, x.below a ∧ y.below b ∧ q = a + b := by
  obtain ⟨⟨a0, ha0⟩, ⟨a1, ha1⟩, hx, hx'⟩ := x.isCut
  obtain ⟨⟨b0, hb0⟩, ⟨b1, hb1⟩, hy, hy'⟩ := y.isCut
  refine ⟨⟨a0 + b0, a0, b0, ha0, hb0, rfl⟩, ⟨a1 + b1, ?_⟩, ?_, ?_⟩
  · rintro ⟨a, b, ha, hb, h⟩
    have h1 := below_lt_aux ha ha1
    have h2 := below_lt_aux hb hb1
    grind
  · rintro p q ⟨a, b, ha, hb, h⟩ hp
    exact ⟨p - b, b, hx _ a ha (by grind), hb, by grind⟩
  · rintro q ⟨a, b, ha, hb, h⟩
    obtain ⟨a', ha', hlt⟩ := hx' a ha
    exact ⟨a' + b, ⟨a', b, ha', hb, rfl⟩, by grind⟩

theorem isCut_neg (x : real) : IsCut fun q => ∃ r, q < r ∧ ¬ x.below (-r) := by
  obtain ⟨⟨a0, ha0⟩, ⟨a1, ha1⟩, hx, hx'⟩ := x.isCut
  have hnn : - -a1 = a1 := by grind
  refine ⟨⟨-a1 - 1, -a1, by grind, by rw [hnn]; exact ha1⟩, ⟨-a0, ?_⟩, ?_, ?_⟩
  · rintro ⟨r, hr, h⟩
    exact h (hx _ a0 ha0 (by grind))
  · rintro p q ⟨r, hr, h⟩ hp
    exact ⟨r, by grind, h⟩
  · rintro q ⟨r, hr, h⟩
    exact ⟨(q + r) / 2, ⟨r, by grind, h⟩, by grind⟩

theorem isCut_mulNonneg (x y : real) (hx0 : 0 ≤ x) (hy0 : 0 ≤ y) :
    IsCut fun q => q < 0 ∨ ∃ a b, 0 ≤ a ∧ 0 ≤ b ∧ x.below a ∧ y.below b ∧ q = a * b := by
  obtain ⟨_, ⟨a1, ha1⟩, hx, hx'⟩ := x.isCut
  obtain ⟨_, ⟨b1, hb1⟩, hy, hy'⟩ := y.isCut
  have ha1' : 0 ≤ a1 := by
    rcases rat_lt_or_le_aux a1 0 with h | h
    · exact absurd (hx0 a1 h) ha1
    · exact h
  have hb1' : 0 ≤ b1 := by
    rcases rat_lt_or_le_aux b1 0 with h | h
    · exact absurd (hy0 b1 h) hb1
    · exact h
  refine ⟨⟨-1, Or.inl (by grind)⟩, ⟨a1 * b1, ?_⟩, ?_, ?_⟩
  · rintro (h | ⟨a, b, ha, hb, hxa, hyb, h⟩)
    · have := Rat.mul_nonneg ha1' hb1'
      grind
    · have h1 := below_lt_aux hxa ha1
      have h2 := below_lt_aux hyb hb1
      have h3 : a * b ≤ a * b1 := Rat.mul_le_mul_of_nonneg_left (by grind) ha
      have h4 : a * b1 < a1 * b1 := Rat.mul_lt_mul_of_pos_right h1 (by grind)
      grind
  · rintro p q hq hp
    rcases rat_lt_or_le_aux p 0 with h0 | h0
    · exact Or.inl h0
    · rcases hq with h | ⟨a, b, ha, hb, hxa, hyb, h⟩
      · exact Or.inl (by grind)
      · have hb' : 0 < b := by
          rcases rat_lt_or_le_aux 0 b with hh | hh
          · exact hh
          · have : b = 0 := by grind
            subst this
            grind
        have hbne : b ≠ 0 := by grind
        have hpb : p / b < a := (Rat.div_lt_iff hb').mpr (by grind)
        have hpb0 : 0 ≤ p / b := by
          rw [Rat.div_def]
          exact Rat.mul_nonneg h0 (by have := Rat.inv_pos.mpr hb'; grind)
        exact Or.inr ⟨p / b, b, hpb0, hb, hx _ a hxa hpb, hyb, by grind⟩
  · rintro q (h | ⟨a, b, ha, hb, hxa, hyb, h⟩)
    · exact ⟨q / 2, Or.inl (by grind), by grind⟩
    · obtain ⟨a', ha', hlt⟩ := hx' a hxa
      obtain ⟨b', hb', hlt'⟩ := hy' b hyb
      refine ⟨a' * b', Or.inr ⟨a', b', by grind, by grind, ha', hb', rfl⟩, ?_⟩
      have h3 : a * b ≤ a * b' := Rat.mul_le_mul_of_nonneg_left (by grind) ha
      have h4 : a * b' < a' * b' := Rat.mul_lt_mul_of_pos_right hlt (by grind)
      grind

theorem isCut_invPos (x : real) (hx0 : 0 < x) :
    IsCut fun q => q ≤ 0 ∨ ∃ r, 0 < r ∧ ¬ x.below r ∧ q * r < 1 := by
  obtain ⟨_, ⟨a1, ha1⟩, hx, hx'⟩ := x.isCut
  have hz : x.below 0 := by
    apply Classical.byContradiction
    intro h
    apply hx0
    intro q hq
    exact below_lt_aux hq h
  obtain ⟨c, hc, hc0⟩ := hx' 0 hz
  have hcr : ∀ r, ¬ x.below r → c < r := fun r hr => below_lt_aux hc hr
  refine ⟨⟨0, Or.inl (by grind)⟩, ⟨1 / c, ?_⟩, ?_, ?_⟩
  · rintro (h | ⟨r, hr, hxr, h⟩)
    · have : 0 < 1 / c := (Rat.lt_div_iff hc0).mpr (by grind)
      grind
    · have h1 := hcr r hxr
      have h2 : 1 / c * c < 1 / c * r :=
        Rat.mul_lt_mul_of_pos_left h1 ((Rat.lt_div_iff hc0).mpr (by grind))
      have h3 : 1 / c * c = 1 := by grind
      grind
  · rintro p q (h | ⟨r, hr, hxr, h⟩) hp
    · exact Or.inl (by grind)
    · refine Or.inr ⟨r, hr, hxr, ?_⟩
      have := Rat.mul_lt_mul_of_pos_right hp hr
      grind
  · have key : ∀ q r : Rat, 0 < r → q * r < 1 → ∃ q', q < q' ∧ q' * r < 1 := by
      intro q r hr h
      refine ⟨(q + 1 / r) / 2, ?_, ?_⟩
      · have : q < 1 / r := (Rat.lt_div_iff hr).mpr h
        grind
      · have : (q + 1 / r) / 2 * r = (q * r + 1) / 2 := by grind
        grind
    rintro q (h | ⟨r, hr, hxr, h⟩)
    · have hpos : 0 < a1 := by have := hcr a1 ha1; grind
      obtain ⟨q', h1, h2⟩ := key 0 a1 hpos (by grind)
      exact ⟨q', Or.inr ⟨a1, hpos, ha1, h2⟩, by grind⟩
    · obtain ⟨q', h1, h2⟩ := key q r hr h
      exact ⟨q', Or.inr ⟨r, hr, hxr, h2⟩, h1⟩

/- HOL4: realax$real_add: the rationals a + b with a < x and b < y -/
instance : Add real :=
  ⟨fun x y => ⟨fun q => ∃ a b, x.below a ∧ y.below b ∧ q = a + b, isCut_add x y⟩⟩

/- HOL4: realax$real_neg: the rationals q with q < r <= -x for some rational r -/
instance : Neg real := ⟨fun x => ⟨fun q => ∃ r, q < r ∧ ¬ x.below (-r), isCut_neg x⟩⟩

/- HOL4: realax$real_sub   x - y = x + ~y -/
instance : Sub real := ⟨fun x y => x + -y⟩

/- HOL4: realax$abs   abs(x) = (if (0 <= x) then x else ~x) -/
def abs (x : real) : real := if 0 ≤ x then x else -x

/-- Product of two nonnegative reals: the negative rationals, and the products
`a * b` with `0 ≤ a < x`, `0 ≤ b < y`.  (Only used on nonnegative reals.) -/
def mulNonneg (x y : real) : real :=
  if h : 0 ≤ x ∧ 0 ≤ y then
    ⟨fun q => q < 0 ∨ ∃ a b, 0 ≤ a ∧ 0 ≤ b ∧ x.below a ∧ y.below b ∧ q = a * b,
      isCut_mulNonneg x y h.1 h.2⟩
  else 0

/- HOL4: realax$real_mul -/
instance : Mul real :=
  ⟨fun x y =>
    if (0 ≤ x ↔ 0 ≤ y) then mulNonneg (abs x) (abs y) else -(mulNonneg (abs x) (abs y))⟩

/-- Inverse of a positive real: the rationals `q ≤ 0`, and the `q > 0` with
`q * r < 1` for some rational `r ≥ x`.  (Only used on positive reals.) -/
def invPos (x : real) : real :=
  if h : 0 < x then
    ⟨fun q => q ≤ 0 ∨ ∃ r, 0 < r ∧ ¬ x.below r ∧ q * r < 1, isCut_invPos x h⟩
  else 0

/- HOL4: realax$inv   (with inv 0 = 0) -/
def inv (x : real) : real :=
  if x = 0 then 0 else if 0 ≤ x then invPos x else -(invPos (-x))

/- HOL4: realax$/   x / y = x * inv y -/
instance : Div real := ⟨fun x y => x * inv y⟩

/- HOL4: realax$pow   ($pow x 0 = &1) /\ ($pow x (SUC n) = x * ($pow x n)) -/
def pow (x : real) : Nat → real
  | 0 => 1
  | n + 1 => x * pow x n

/- HOL4: real$sqrt   sqrt x = @u. (0 < x ==> 0 < u) /\ (u pow 2 = x) -/
def sqrt (x : real) : real := select fun u => (0 < x → 0 < u) ∧ pow u 2 = x

end real

end

end CmlTS
