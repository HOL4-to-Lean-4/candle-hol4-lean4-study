import CandleLean

universe u v

open HOL Candle Classical

noncomputable section

namespace Mut

variable {U : Type u}

def is_std_type_assignment0 [Nonempty U] (mem : U → U → Prop) (δ : tyass U) : Prop :=
  (∀ dom rng, δ (mls "fun") [dom, rng] = funspace mem rng dom) ∧
  δ (mls "bool") [] = boolset mem

/-! A model of the hereditarily finite sets on `Nat`: `a ∈ b` iff bit `a` of `b` is set.
Only the separation and power axioms are needed. -/

def hfmem (a b : Nat) : Prop := b.testBit a = true

theorem G (S : Nat → Prop) : ∀ n : Nat, ∃ y : Nat, ∀ a, y.testBit a = true ↔ (a < n ∧ S a) := by
  intro n
  induction n with
  | zero => exact ⟨0, fun a => by simp⟩
  | succ n ih =>
    obtain ⟨y, hy⟩ := ih
    by_cases hS : S n
    · refine ⟨y ||| 2 ^ n, fun a => ?_⟩
      rw [Nat.testBit_or, Nat.testBit_two_pow]
      simp only [Bool.or_eq_true, decide_eq_true_eq, hy]
      constructor
      · rintro (⟨h1, h2⟩ | h)
        · exact ⟨by omega, h2⟩
        · subst h; exact ⟨by omega, hS⟩
      · rintro ⟨h1, h2⟩
        by_cases h : n = a
        · exact Or.inr h
        · exact Or.inl ⟨by omega, h2⟩
    · refine ⟨y, fun a => ?_⟩
      rw [hy]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨by omega, h2⟩
      · rintro ⟨h1, h2⟩
        refine ⟨?_, h2⟩
        by_cases h : a = n
        · subst h; exact absurd h2 hS
        · omega

theorem bit_le {x a : Nat} (h : x.testBit a = true) : a ≤ x := by
  by_contra hc
  have : x < 2 ^ a := Nat.lt_trans (by omega) Nat.lt_two_pow_self
  rw [Nat.testBit_lt_two_pow this] at h
  cases h

theorem subset_le {a x : Nat} (h : ∀ b, a.testBit b = true → x.testBit b = true) : a ≤ x := by
  have : a &&& x = a := by
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_and]
    cases ha : a.testBit i
    · simp
    · simp [h i ha]
  calc a = a &&& x := this.symm
    _ ≤ x := Nat.and_le_right

theorem hf_sep : ∃ s : Nat → (Nat → Prop) → Nat, is_separation hfmem s := by
  have : ∀ x (P : Nat → Prop), ∃ y, ∀ a, hfmem a y ↔ hfmem a x ∧ P a := by
    intro x P
    obtain ⟨y, hy⟩ := G (fun a => hfmem a x ∧ P a) (x + 1)
    refine ⟨y, fun a => ?_⟩
    show y.testBit a = true ↔ _
    rw [hy]
    constructor
    · exact fun ⟨_, h⟩ => h
    · intro h; exact ⟨Nat.lt_succ_of_le (bit_le h.1), h⟩
  exact ⟨fun x P => Classical.choose (this x P), fun x P => Classical.choose_spec (this x P)⟩

theorem hf_pow : ∃ p : Nat → Nat, is_power hfmem p := by
  have : ∀ x, ∃ y, ∀ a, hfmem a y ↔ ∀ b, hfmem b a → hfmem b x := by
    intro x
    obtain ⟨y, hy⟩ := G (fun a => ∀ b, hfmem b a → hfmem b x) (x + 1)
    refine ⟨y, fun a => ?_⟩
    show y.testBit a = true ↔ _
    rw [hy]
    constructor
    · exact fun ⟨_, h⟩ => h
    · intro h; exact ⟨Nat.lt_succ_of_le (subset_le h), h⟩
  exact ⟨fun x => Classical.choose (this x), fun x => Classical.choose_spec (this x)⟩

/-- In this model the empty set is in `funspace ∅ {∅}` but not in `funspace {∅} ∅`. -/
theorem key : hfmem 0 (funspace hfmem 0 1) ∧ ¬ hfmem 0 (funspace hfmem 1 0) := by
  have hs : is_separation hfmem (Candle.sub hfmem) := by
    unfold Candle.sub; exact Classical.epsilon_spec hf_sep
  have hp : is_power hfmem (power hfmem) := by
    unfold power; exact Classical.epsilon_spec hf_pow
  have h0 : ∀ b, ¬ hfmem b 0 := by intro b; simp [hfmem]
  constructor
  · unfold funspace
    rw [hs]
    refine ⟨?_, fun a ha => absurd ha (h0 a)⟩
    unfold relspace
    rw [hp]
    intro b hb
    exact absurd hb (h0 b)
  · unfold funspace
    rw [hs]
    rintro ⟨_, h⟩
    obtain ⟨⟨b, hb⟩, _⟩ := h 0 (by simp [hfmem])
    exact h0 _ hb

def δ0 : tyass Nat := fun n l =>
  if n = mls "fun" then (match l with | [d, r] => funspace hfmem r d | _ => 0) else boolset hfmem

theorem witness : ¬ ∀ (mem : Nat → Nat → Prop) (δ : tyass Nat),
    (Mut.is_std_type_assignment0 mem δ ↔ Candle.is_std_type_assignment0 mem δ) := by
  intro h
  have hbf : mls "bool" ≠ mls "fun" := by decide
  have hm : Mut.is_std_type_assignment0 hfmem δ0 := by
    refine ⟨fun dom rng => ?_, ?_⟩
    · simp [δ0]
    · simp [δ0, hbf]
  have hb := (h hfmem δ0).1 hm
  have h1 := hb.1 0 1
  simp only [δ0, if_true] at h1
  have k1 := key.1
  rw [← h1] at k1
  exact key.2 k1

end Mut

#print axioms Mut.witness
