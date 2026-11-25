import CmlTS.Prelude.Set
/-
  HOL4 library constants: `realax`, `real`, `transc` (the part used by `binary_ieee`).

  Mathlib is not available, so the HOL4 type `real` (the complete ordered field) is built here as
  Dedekind cuts of the rationals.  Only the operations that `binary_ieee` uses are given.
-/
set_option autoImplicit false

namespace CmlTS
open Classical

/- HOL4: realax$real.  `x.lower q` means `q < x`. -/
structure real where
  lower : Rat → Prop
  nonempty : ∃ q, lower q
  bounded : ∃ q, ¬ lower q
  down : ∀ p q, p < q → lower q → lower p
  noMax : ∀ p, lower p → ∃ q, p < q ∧ lower q

namespace real

theorem ext {x y : real} (h : ∀ q, x.lower q ↔ y.lower q) : x = y := by
  cases x; cases y
  simp at h
  congr
  exact funext fun q => propext (h q)

/-- The embedding of the rationals. -/
def ofRat (r : Rat) : real where
  lower q := q < r
  nonempty := ⟨r - 1, by grind⟩
  bounded := ⟨r, by grind⟩
  down p q h1 h2 := by grind
  noMax p h := ⟨(p + r) / 2, by grind, by grind⟩

instance : Inhabited real := ⟨ofRat 0⟩

/- HOL4: real$real_of_num (written &n) -/
def ofNat (n : Nat) : real := ofRat (n : Rat)

instance (n : Nat) : OfNat real n := ⟨ofNat n⟩

/- HOL4: realax$real_lte, real_lt, real_ge, real_gt -/
protected def le (x y : real) : Prop := ∀ q, x.lower q → y.lower q
instance : LE real := ⟨real.le⟩
instance : LT real := ⟨fun x y => ¬ y ≤ x⟩

/- HOL4: realax$real_add -/
protected def add (x y : real) : real where
  lower q := ∃ a b, x.lower a ∧ y.lower b ∧ q = a + b
  nonempty := by
    obtain ⟨a, ha⟩ := x.nonempty
    obtain ⟨b, hb⟩ := y.nonempty
    exact ⟨a + b, a, b, ha, hb, rfl⟩
  bounded := by
    obtain ⟨a, ha⟩ := x.bounded
    obtain ⟨b, hb⟩ := y.bounded
    refine ⟨a + b, ?_⟩
    rintro ⟨a', b', ha', hb', h⟩
    have h1 : a' < a := Classical.byContradiction fun hn => by
      by_cases he : a' = a
      · exact ha (he ▸ ha')
      · exact ha (x.down a a' (by grind) ha')
    have h2 : b' < b := Classical.byContradiction fun hn => by
      by_cases he : b' = b
      · exact hb (he ▸ hb')
      · exact hb (y.down b b' (by grind) hb')
    grind
  down p q h := by
    rintro ⟨a, b, ha, hb, rfl⟩
    exact ⟨a - (a + b - p), b, x.down _ a (by grind) ha, hb, by grind⟩
  noMax p := by
    rintro ⟨a, b, ha, hb, rfl⟩
    obtain ⟨a', h1, h2⟩ := x.noMax a ha
    exact ⟨a' + b, by grind, a', b, h2, hb, rfl⟩
instance : Add real := ⟨real.add⟩

/- HOL4: realax$real_neg  (`q < -x` iff `x <= r < -q` for some rational `r`) -/
protected def neg (x : real) : real where
  lower q := ∃ r, r < -q ∧ ¬ x.lower r
  nonempty := by
    obtain ⟨r, hr⟩ := x.bounded
    exact ⟨-r - 1, r, by grind, hr⟩
  bounded := by
    obtain ⟨a, ha⟩ := x.nonempty
    refine ⟨-a, ?_⟩
    rintro ⟨r, h1, h2⟩
    exact h2 (x.down r a (by grind) ha)
  down p q h := by
    rintro ⟨r, h1, h2⟩
    exact ⟨r, by grind, h2⟩
  noMax p := by
    rintro ⟨r, h1, h2⟩
    exact ⟨(p + -r) / 2, by grind, r, by grind, h2⟩
instance : Neg real := ⟨real.neg⟩

/- HOL4: realax$real_sub:  x - y = x + ~y -/
instance : Sub real := ⟨fun x y => x + -y⟩

/- HOL4: real$sup (least upper bound) of a nonempty set that is bounded above (0 otherwise; only
   used below on sets for which it is the least upper bound). -/
noncomputable def lub (S : real → Prop) : real :=
  if h : (∃ x, S x) ∧ (∃ u, ∀ x, S x → x ≤ u) then
    { lower := fun q => ∃ x, S x ∧ x.lower q
      nonempty := by
        obtain ⟨x, hx⟩ := h.1
        obtain ⟨q, hq⟩ := x.nonempty
        exact ⟨q, x, hx, hq⟩
      bounded := by
        obtain ⟨u, hu⟩ := h.2
        obtain ⟨q, hq⟩ := u.bounded
        refine ⟨q, ?_⟩
        rintro ⟨x, hx, hxq⟩
        exact hq (hu x hx q hxq)
      down := by
        rintro p q hpq ⟨x, hx, hxq⟩
        exact ⟨x, hx, x.down p q hpq hxq⟩
      noMax := by
        rintro p ⟨x, hx, hxp⟩
        obtain ⟨q, h1, h2⟩ := x.noMax p hxp
        exact ⟨q, h1, x, hx, h2⟩ }
  else 0

/-- The product of two positive reals: the supremum of the products of positive rationals below
    them. -/
noncomputable def mulPos (x y : real) : real :=
  lub fun z => ∃ a b : Rat, 0 < a ∧ 0 < b ∧ x.lower a ∧ y.lower b ∧ z = ofRat (a * b)

/- HOL4: realax$real_mul -/
protected noncomputable def mul (x y : real) : real :=
  if x = 0 ∨ y = 0 then 0
  else if 0 < x then
    if 0 < y then mulPos x y else -(mulPos x (-y))
  else
    if 0 < y then -(mulPos (-x) y) else mulPos (-x) (-y)
noncomputable instance : Mul real := ⟨real.mul⟩

/-- The inverse of a positive real: the supremum of the inverses of the rationals above it. -/
noncomputable def invPos (x : real) : real :=
  lub fun z => ∃ a : Rat, 0 < a ∧ ¬ x.lower a ∧ z = ofRat a⁻¹

/- HOL4: realax$inv  (inv 0 = 0) -/
protected noncomputable def inv (x : real) : real :=
  if x = 0 then 0 else if 0 < x then invPos x else -(invPos (-x))
noncomputable instance : Inv real := ⟨real.inv⟩

/- HOL4: realax$real_div:  x / y = x * inv y -/
noncomputable instance : Div real := ⟨fun x y => x * y⁻¹⟩

/- HOL4: real$pow:  (x pow 0 = 1) /\ (x pow (SUC n) = x * (x pow n)) -/
noncomputable def pow (x : real) : Nat → real
  | 0 => 1
  | n + 1 => x * pow x n
noncomputable instance : HPow real Nat real := ⟨real.pow⟩

/- HOL4: real$abs:  abs x = if 0 <= x then x else ~x -/
noncomputable def abs (x : real) : real := if 0 ≤ x then x else -x

/- HOL4: transc$root:  root n x = @u. (&0 < x ==> &0 < u) /\ (u pow n = x)
         real$sqrt:    sqrt x = root 2 x -/
noncomputable def root (n : Nat) (x : real) : real := SELECT fun u => (0 < x → 0 < u) ∧ u ^ n = x
noncomputable def sqrt (x : real) : real := root 2 x

/-! Sanity checks: the operations agree with the rational ones on rationals. -/

theorem ofRat_le {a b : Rat} : ofRat a ≤ ofRat b ↔ a ≤ b := by
  constructor
  · intro h
    refine Classical.byContradiction fun hn => ?_
    have : b < b := h b (by show b < a; grind)
    grind
  · intro h q hq
    have hq : q < a := hq
    show q < b
    grind

theorem ofRat_lt {a b : Rat} : ofRat a < ofRat b ↔ a < b := by
  show ¬ (ofRat b ≤ ofRat a) ↔ a < b
  rw [ofRat_le]; grind

theorem ofRat_inj {a b : Rat} : ofRat a = ofRat b ↔ a = b := by
  constructor
  · intro h
    have h1 : ofRat a ≤ ofRat b := by rw [h]; intro q hq; exact hq
    have h2 : ofRat b ≤ ofRat a := by rw [h]; intro q hq; exact hq
    rw [ofRat_le] at h1 h2
    grind
  · rintro rfl; rfl

theorem ofRat_add (a b : Rat) : ofRat a + ofRat b = ofRat (a + b) := by
  apply ext
  intro q
  show (∃ x y, x < a ∧ y < b ∧ q = x + y) ↔ q < a + b
  constructor
  · rintro ⟨x, y, h1, h2, rfl⟩; grind
  · intro h
    exact ⟨a - (a + b - q) / 2, b - (a + b - q) / 2, by grind, by grind, by grind⟩

theorem ofRat_neg (a : Rat) : -(ofRat a) = ofRat (-a) := by
  apply ext
  intro q
  show (∃ r, r < -q ∧ ¬ r < a) ↔ q < -a
  constructor
  · rintro ⟨r, h1, h2⟩; grind
  · intro h; exact ⟨a, by grind, by grind⟩

theorem lub_lower {S : real → Prop} (h : (∃ x, S x) ∧ (∃ u, ∀ x, S x → x ≤ u)) (q : Rat) :
    (lub S).lower q ↔ ∃ x, S x ∧ x.lower q := by
  unfold lub
  rw [dif_pos h]

theorem rat_mul_lt {a b c d : Rat} (ha : 0 < a) (hb : 0 < b) (h1 : a < c) (h2 : b < d) :
    a * b < c * d := by
  have e1 := Rat.mul_lt_mul_of_pos_right h1 hb
  have e2 := Rat.mul_lt_mul_of_pos_left h2 (show 0 < c by grind)
  grind

theorem small {a b e : Rat} (ha : 0 < a) (hb : 0 < b) (he : 0 < e) :
    ∃ δ, 0 < δ ∧ δ < a ∧ δ * b < e / 2 := by
  have hab : 0 < a * b := by have := Rat.mul_lt_mul_of_pos_right ha hb; grind
  have hs : 0 < 2 * (a * b + e) := by grind
  have hk : 0 < (2 * (a * b + e))⁻¹ := Rat.inv_pos.mpr hs
  have hk1 : (2 * (a * b + e)) * (2 * (a * b + e))⁻¹ = 1 := Rat.mul_inv_cancel _ (by grind)
  generalize (2 * (a * b + e))⁻¹ = k at hk hk1
  have h1 : 0 < e * k := by have := Rat.mul_lt_mul_of_pos_right he hk; grind
  have h2 : 0 < a * b * k := by have := Rat.mul_lt_mul_of_pos_right hab hk; grind
  have h3 : 2 * (a * b * k) + 2 * (e * k) = 1 := by grind
  have h4 : e * k < 1 := by grind
  have h5 : a * b * k < 1 / 2 := by grind
  have h6 := Rat.mul_lt_mul_of_pos_left h4 ha
  have h7 := Rat.mul_lt_mul_of_pos_left h5 he
  have h8 := Rat.mul_lt_mul_of_pos_left h1 ha
  exact ⟨a * (e * k), by grind, by grind, by grind⟩

theorem ofRat_mulPos {a b : Rat} (ha : 0 < a) (hb : 0 < b) :
    mulPos (ofRat a) (ofRat b) = ofRat (a * b) := by
  apply ext
  intro q
  unfold mulPos
  rw [lub_lower]
  · constructor
    · rintro ⟨x, ⟨c, d, hc, hd, hca, hdb, rfl⟩, hq⟩
      have hq : q < c * d := hq
      have := rat_mul_lt hc hd hca hdb
      show q < a * b
      grind
    · intro hq
      have hq : q < a * b := hq
      obtain ⟨d1, p1, l1, m1⟩ := small ha hb (show 0 < a * b - q by grind)
      obtain ⟨d2, p2, l2, m2⟩ := small hb ha (show 0 < a * b - q by grind)
      refine ⟨_, ⟨a - d1, b - d2, by grind, by grind, ?_, ?_, rfl⟩, ?_⟩
      · show a - d1 < a; grind
      · show b - d2 < b; grind
      · show q < (a - d1) * (b - d2)
        have p3 := Rat.mul_lt_mul_of_pos_right p1 p2
        grind
  · refine ⟨⟨_, a / 2, b / 2, by grind, by grind, ?_, ?_, rfl⟩, ofRat (a * b), ?_⟩
    · show a / 2 < a; grind
    · show b / 2 < b; grind
    · rintro x ⟨c, d, hc, hd, hca, hdb, rfl⟩
      rw [ofRat_le]
      exact Rat.le_of_lt (rat_mul_lt hc hd hca hdb)

theorem ofRat_zero : (0 : real) = ofRat 0 := rfl

theorem ofRat_mul (a b : Rat) : ofRat a * ofRat b = ofRat (a * b) := by
  show real.mul (ofRat a) (ofRat b) = _
  unfold real.mul
  simp only [ofRat_zero, ofRat_inj, ofRat_lt, ofRat_neg]
  by_cases ha0 : a = 0
  · subst ha0; simp
  by_cases hb0 : b = 0
  · subst hb0; simp
  simp only [ha0, hb0, or_self, if_false]
  split
  · split
    · rw [ofRat_mulPos (by assumption) (by assumption)]
    · rw [ofRat_mulPos (by assumption) (by grind), ofRat_neg, ofRat_inj]; grind
  · split
    · rw [ofRat_mulPos (by grind) (by assumption), ofRat_neg, ofRat_inj]; grind
    · rw [ofRat_mulPos (by grind) (by grind), ofRat_inj]; grind

theorem ofRat_invPos {a : Rat} (ha : 0 < a) : invPos (ofRat a) = ofRat a⁻¹ := by
  have key : ∀ c : Rat, 0 < c → ¬ c < a → c⁻¹ ≤ a⁻¹ := by
    intro c hc hca
    have h1 := Rat.inv_pos.mpr ha
    have h2 := Rat.inv_pos.mpr hc
    have h3 : a * a⁻¹ = 1 := Rat.mul_inv_cancel _ (by grind)
    have h4 : c * c⁻¹ = 1 := Rat.mul_inv_cancel _ (by grind)
    refine Classical.byContradiction fun hn => ?_
    have h5 := rat_mul_lt ha h1 (c := c) (d := c⁻¹)
    by_cases he : a = c
    · subst he; grind
    · have := h5 (by grind) (by grind)
      grind
  apply ext
  intro q
  unfold invPos
  rw [lub_lower]
  · constructor
    · rintro ⟨x, ⟨c, hc, hca, rfl⟩, hq⟩
      have hq : q < c⁻¹ := hq
      have := key c hc hca
      show q < a⁻¹
      grind
    · intro hq
      exact ⟨_, ⟨a, ha, Rat.lt_irrefl, rfl⟩, hq⟩
  · refine ⟨⟨_, a, ha, Rat.lt_irrefl, rfl⟩, ofRat a⁻¹, ?_⟩
    rintro x ⟨c, hc, hca, rfl⟩
    rw [ofRat_le]
    exact key c hc hca

theorem ofRat_inv (a : Rat) : (ofRat a)⁻¹ = ofRat a⁻¹ := by
  show real.inv (ofRat a) = _
  unfold real.inv
  simp only [ofRat_zero, ofRat_inj, ofRat_lt, ofRat_neg]
  split
  · subst a; simp
  · split
    · rw [ofRat_invPos (by assumption)]
    · rw [ofRat_invPos (by grind), ofRat_neg, ofRat_inj]
      have h3 : a * a⁻¹ = 1 := Rat.mul_inv_cancel _ (by assumption)
      have : (-a)⁻¹ = -a⁻¹ := Rat.inv_eq_of_mul_eq_one (by grind)
      grind

end real

end CmlTS
