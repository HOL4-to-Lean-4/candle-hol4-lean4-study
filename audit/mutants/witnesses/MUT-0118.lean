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
/-- mutated `is_set_theory` (the conjunct `extensional mem` is dropped) -/
def is_set_theory {U : Type u} (mem : U → U → Prop) : Prop :=
  (∃ sub, is_separation mem sub) ∧
  (∃ power, is_power mem power) ∧
  (∃ union, is_union mem union) ∧
  (∃ upair, is_upair mem upair)
end Mut

/-- `mem a x := bit a of x/2`: separation, power, union and upair exist, but the elements `0` and `1`
both have no members, so extensionality fails. -/
theorem witness : ∃ mem : Nat → Nat → Prop, Mut.is_set_theory mem ∧ ¬ is_set_theory mem := by
  refine ⟨NonExt.mem1, ⟨⟨_, NonExt.sep⟩, ⟨_, NonExt.pow_ok⟩, ⟨_, NonExt.union_ok⟩, ⟨_, NonExt.upair_ok⟩⟩, ?_⟩
  intro h
  exact NonExt.not_ext h.1

#print axioms witness
