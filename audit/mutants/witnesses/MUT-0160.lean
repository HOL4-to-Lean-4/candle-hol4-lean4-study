import CandleLean
open HOL Candle Classical
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
noncomputable section
/-! A non-extensional structure on `Nat` that has separation, power, union and upair:
    `mem a x` iff bit `a` of `x / 2` is set.  `2*s` and `2*s+1` are two copies of the same set. -/
namespace NonExt

def mem1 (a x : Nat) : Prop := (x / 2).testBit a = true

theorem bit_lt {x i : Nat} (h : x.testBit i = true) : i < x := by
  by_contra hc
  have h1 : x < 2 ^ i :=
    Nat.lt_of_lt_of_le (Nat.lt_two_pow_self (n := x)) (Nat.pow_le_pow_right (by decide) (by omega))
  rw [Nat.testBit_lt_two_pow h1] at h
  cases h

theorem fin_exists (p : Nat → Prop) : ∀ n : Nat, ∃ s : Nat, ∀ a, s.testBit a = true ↔ (a < n ∧ p a) := by
  intro n
  induction n with
  | zero => exact ⟨0, fun a => by simp⟩
  | succ n ih =>
    obtain ⟨s, hs⟩ := ih
    by_cases hp : p n
    · refine ⟨s ||| 2 ^ n, fun a => ?_⟩
      rw [Nat.testBit_or, Nat.testBit_two_pow]
      by_cases han : n = a
      · subst han; simp [hp]
      · have h1 := hs a
        simp only [Bool.or_eq_true, decide_eq_true_eq, han, or_false, h1]
        constructor
        · rintro ⟨h1, h2⟩; exact ⟨by omega, h2⟩
        · rintro ⟨h1, h2⟩
          exact ⟨by omega, h2⟩
    · refine ⟨s, fun a => ?_⟩
      rw [hs a]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨by omega, h2⟩
      · rintro ⟨h1, h2⟩
        refine ⟨?_, h2⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp h1 with h | h
        · exact h
        · subst h; exact absurd h2 hp

theorem mem1_lt {a x : Nat} (h : mem1 a x) : a < x := by
  have := bit_lt h
  omega

theorem mem1_two_mul (a s : Nat) : mem1 a (2 * s) ↔ s.testBit a = true := by
  unfold mem1
  have : 2 * s / 2 = s := by omega
  rw [this]

theorem sep : is_separation mem1 (fun x P => 2 * Classical.choose (fin_exists (fun a => mem1 a x ∧ P a) (x + 1))) := by
  intro x P a
  rw [mem1_two_mul, (Classical.choose_spec (fin_exists (fun a => mem1 a x ∧ P a) (x + 1))) a]
  constructor
  · rintro ⟨_, h⟩; exact h
  · intro h; exact ⟨by have := mem1_lt h.1; omega, h⟩

theorem sub_le {u w : Nat} (h : ∀ b, u.testBit b = true → w.testBit b = true) : u ≤ w := by
  have : u &&& w = u := by
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_and]
    cases hu : u.testBit i
    · simp
    · simp [h i hu]
  rw [← this]
  exact Nat.and_le_right

theorem pow_ok : is_power mem1 (fun x => 2 * Classical.choose (fin_exists (fun a => ∀ b, mem1 b a → mem1 b x) (x + 2))) := by
  intro x a
  rw [mem1_two_mul, (Classical.choose_spec (fin_exists (fun a => ∀ b, mem1 b a → mem1 b x) (x + 2))) a]
  constructor
  · rintro ⟨_, h⟩; exact h
  · intro h
    refine ⟨?_, h⟩
    have : a / 2 ≤ x / 2 := sub_le (fun b hb => h b hb)
    omega

theorem union_ok : is_union mem1 (fun x => 2 * Classical.choose (fin_exists (fun a => ∃ b, mem1 a b ∧ mem1 b x) (x + 1))) := by
  intro x a
  rw [mem1_two_mul, (Classical.choose_spec (fin_exists (fun a => ∃ b, mem1 a b ∧ mem1 b x) (x + 1))) a]
  constructor
  · rintro ⟨_, h⟩; exact h
  · intro h
    refine ⟨?_, h⟩
    obtain ⟨b, h1, h2⟩ := h
    have := mem1_lt h1
    have := mem1_lt h2
    omega

theorem upair_ok : is_upair mem1 (fun x y => 2 * (2 ^ x ||| 2 ^ y)) := by
  intro x y a
  rw [mem1_two_mul, Nat.testBit_or, Nat.testBit_two_pow, Nat.testBit_two_pow]
  simp only [Bool.or_eq_true, decide_eq_true_eq]
  constructor
  · rintro (h | h)
    · exact Or.inl h.symm
    · exact Or.inr h.symm
  · rintro (h | h)
    · exact Or.inl h.symm
    · exact Or.inr h.symm

theorem not_ext : ¬ extensional mem1 := by
  intro h
  have := (h 0 1).mpr (fun a => by simp [mem1])
  cases this

end NonExt


namespace Mut
def product {U : Type u} (mem : U → U → Prop) (x y : U) : U :=
  sub mem (power mem (power mem (binary_union mem x y)))
    (fun a => ∃ b c, mem b x ∧ mem c y ∧ a = upair mem b c)
end Mut

namespace NonExt
theorem upair_spec : is_upair mem1 (upair mem1) :=
  Classical.epsilon_spec (p := fun u => is_upair mem1 u) ⟨_, upair_ok⟩
theorem sub_spec : is_separation mem1 (sub mem1) :=
  Classical.epsilon_spec (p := fun u => is_separation mem1 u) ⟨_, sep⟩
theorem power_spec : is_power mem1 (power mem1) :=
  Classical.epsilon_spec (p := fun u => is_power mem1 u) ⟨_, pow_ok⟩
theorem mem1_zero (a : Nat) : ¬ mem1 a 0 := by simp [mem1]
end NonExt

/-- In the model `NonExt.mem1`, take `e = 0` (no members) and `s = {e}`. The mutated product of `s` with itself contains
`s = upair e e`; the base product only contains pairs `(b,c) = {{b},{b,c}}`, and `s = (e,e)` would force `e ∈ e`. -/
theorem witness : ∃ (mem : Nat → Nat → Prop) (x y : Nat), Mut.product mem x y ≠ Candle.product mem x y := by
  refine ⟨NonExt.mem1, upair NonExt.mem1 0 0, upair NonExt.mem1 0 0, ?_⟩
  intro h
  obtain ⟨s, hs⟩ : ∃ s, s = upair NonExt.mem1 0 0 := ⟨_, rfl⟩
  rw [← hs] at h
  have hu := NonExt.upair_spec
  have hp := NonExt.power_spec
  have hsub := NonExt.sub_spec
  have h0s : NonExt.mem1 0 s := by rw [hs]; exact (hu 0 0 0).mpr (Or.inl rfl)
  -- the mutant product contains s
  have m1 : NonExt.mem1 s (Mut.product NonExt.mem1 s s) := by
    unfold Mut.product
    refine (hsub _ _ _).mpr ⟨?_, 0, 0, h0s, h0s, hs⟩
    refine (hp _ _).mpr (fun b hb => ?_)
    rw [hs] at hb
    rcases (hu 0 0 b).mp hb with rfl | rfl
    all_goals
      refine (hp _ _).mpr (fun c hc => ?_)
      exact absurd hc (NonExt.mem1_zero c)
  -- so the base product contains s as well
  have m2 : NonExt.mem1 s (Candle.product NonExt.mem1 s s) := by rw [← h]; exact m1
  unfold Candle.product at m2
  obtain ⟨_, b, c, hb, hc, hbc⟩ := (hsub _ _ _).mp m2
  have hb0 : b = 0 := by rw [hs] at hb; rcases (hu 0 0 b).mp hb with h | h <;> exact h
  have hc0 : c = 0 := by rw [hs] at hc; rcases (hu 0 0 c).mp hc with h | h <;> exact h
  subst hb0; subst hc0
  -- s = pair 0 0 = upair s s
  have e1 : s = upair NonExt.mem1 s s := by
    have h' := hbc
    unfold pair unit at h'
    rw [← hs] at h'
    exact h'
  have : NonExt.mem1 0 (upair NonExt.mem1 s s) := by rw [← e1]; exact h0s
  rcases (hu s s 0).mp this with h1 | h1
  all_goals
    have h2 : NonExt.mem1 0 0 := by rw [← h1] at h0s; exact h0s
    exact NonExt.mem1_zero 0 h2

#print axioms witness
