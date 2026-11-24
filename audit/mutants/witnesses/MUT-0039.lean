import CandleLean

open Candle HOL Classical

universe u

namespace Mut
noncomputable section

variable {U : Type u}

def product (mem : U → U → Prop) (x y : U) : U :=
  sub mem (power mem (power mem (binary_union mem x y)))
    (fun a => ∃ b c, mem b x ∧ mem c y ∧ a = pair mem c b)

end
end Mut

/-! A model of `is_set_theory`: hereditarily finite sets coded by natural numbers,
    `vmem a b := (bit a of b is set)`. -/

def vmem (a b : Nat) : Prop := b.testBit a = true

theorem vmem_lt {n a : Nat} (h : n.testBit a = true) : a < n := by
  by_contra hc
  have h1 : n < 2 ^ a := Nat.lt_of_le_of_lt (Nat.le_of_not_lt hc) Nat.lt_two_pow_self
  rw [Nat.testBit_lt_two_pow h1] at h
  exact Bool.false_ne_true h

theorem vmem_exists (P : Nat → Prop) : ∀ N : Nat, ∃ n : Nat, ∀ a, n.testBit a = true ↔ (a < N ∧ P a)
  | 0 => ⟨0, fun a => by simp⟩
  | N + 1 => by
    obtain ⟨n, hn⟩ := vmem_exists P N
    by_cases hP : P N
    · refine ⟨n ||| 2 ^ N, fun a => ?_⟩
      rw [Nat.testBit_or, Nat.testBit_two_pow]
      have := hn a
      by_cases ha : a = N
      · subst ha; simp [hP]
      · have ha' : ¬ N = a := fun e => ha e.symm
        simp only [Bool.or_eq_true, decide_eq_true_eq, ha', or_false]
        rw [this]
        constructor
        · rintro ⟨h1, h2⟩; exact ⟨by omega, h2⟩
        · rintro ⟨h1, h2⟩; exact ⟨by omega, h2⟩
    · refine ⟨n, fun a => ?_⟩
      rw [hn a]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨by omega, h2⟩
      · rintro ⟨h1, h2⟩
        have : a ≠ N := fun e => hP (e ▸ h2)
        exact ⟨by omega, h2⟩

theorem vmem_ext : Candle.extensional vmem := by
  intro x y
  constructor
  · rintro rfl a; exact Iff.rfl
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    have := h i
    unfold vmem at this
    cases hx : x.testBit i <;> cases hy : y.testBit i <;> simp_all

theorem vomega : Candle.is_set_theory vmem := by
  refine ⟨vmem_ext, ?_, ?_, ?_, ?_⟩
  · -- separation
    have : ∀ x : Nat, ∀ P : Nat → Prop, ∃ n : Nat, ∀ a, vmem a n ↔ vmem a x ∧ P a := by
      intro x P
      obtain ⟨n, hn⟩ := vmem_exists (fun a => x.testBit a = true ∧ P a) x
      refine ⟨n, fun a => ?_⟩
      show n.testBit a = true ↔ x.testBit a = true ∧ P a
      rw [hn a]
      constructor
      · rintro ⟨_, h⟩; exact h
      · rintro ⟨h1, h2⟩; exact ⟨vmem_lt h1, h1, h2⟩
    exact ⟨fun x P => Classical.choose (this x P), fun x P a => Classical.choose_spec (this x P) a⟩
  · -- power set
    have : ∀ x : Nat, ∃ n : Nat, ∀ a, vmem a n ↔ ∀ b, vmem b a → vmem b x := by
      intro x
      obtain ⟨n, hn⟩ := vmem_exists (fun a => ∀ b, a.testBit b = true → x.testBit b = true) (x + 1)
      refine ⟨n, fun a => ?_⟩
      show n.testBit a = true ↔ ∀ b, a.testBit b = true → x.testBit b = true
      rw [hn a]
      constructor
      · rintro ⟨_, h⟩; exact h
      · intro h
        refine ⟨?_, h⟩
        have e : a &&& x = a := by
          apply Nat.eq_of_testBit_eq
          intro i
          rw [Nat.testBit_and]
          cases hai : a.testBit i
          · simp
          · simp [h i hai]
        have : a ≤ x := e ▸ Nat.and_le_right
        omega
    exact ⟨fun x => Classical.choose (this x), fun x a => Classical.choose_spec (this x) a⟩
  · -- union
    have : ∀ x : Nat, ∃ n : Nat, ∀ a, vmem a n ↔ ∃ b, vmem a b ∧ vmem b x := by
      intro x
      obtain ⟨n, hn⟩ := vmem_exists (fun a => ∃ b, b.testBit a = true ∧ x.testBit b = true) x
      refine ⟨n, fun a => ?_⟩
      show n.testBit a = true ↔ ∃ b, b.testBit a = true ∧ x.testBit b = true
      rw [hn a]
      constructor
      · rintro ⟨_, h⟩; exact h
      · rintro ⟨b, h1, h2⟩
        exact ⟨Nat.lt_trans (vmem_lt h1) (vmem_lt h2), b, h1, h2⟩
    exact ⟨fun x => Classical.choose (this x), fun x a => Classical.choose_spec (this x) a⟩
  · -- unordered pair
    have : ∀ x y : Nat, ∃ n : Nat, ∀ a, vmem a n ↔ a = x ∨ a = y := by
      intro x y
      obtain ⟨n, hn⟩ := vmem_exists (fun a => a = x ∨ a = y) (x + y + 1)
      refine ⟨n, fun a => ?_⟩
      show n.testBit a = true ↔ a = x ∨ a = y
      rw [hn a]
      constructor
      · rintro ⟨_, h⟩; exact h
      · intro h
        exact ⟨by omega, h⟩
    exact ⟨fun x y => Classical.choose (this x y), fun x y a => Classical.choose_spec (this x y) a⟩

theorem sp_sub : is_separation vmem (Candle.sub vmem) :=
  Classical.epsilon_spec (p := fun u => is_separation vmem u) vomega.2.1
theorem sp_power : is_power vmem (Candle.power vmem) :=
  Classical.epsilon_spec (p := fun u => is_power vmem u) vomega.2.2.1
theorem sp_union : is_union vmem (Candle.union vmem) :=
  Classical.epsilon_spec (p := fun u => is_union vmem u) vomega.2.2.2.1
theorem sp_upair : is_upair vmem (Candle.upair vmem) :=
  Classical.epsilon_spec (p := fun u => is_upair vmem u) vomega.2.2.2.2

theorem vm_unit (x a : Nat) : vmem a (Candle.unit vmem x) ↔ a = x := by
  show vmem a (Candle.upair vmem x x) ↔ a = x
  rw [sp_upair x x a]; simp

theorem vm_pair (x y a : Nat) :
    vmem a (Candle.pair vmem x y) ↔ a = Candle.unit vmem x ∨ a = Candle.upair vmem x y :=
  sp_upair _ _ a

theorem vm_bu (x y a : Nat) : vmem a (Candle.binary_union vmem x y) ↔ vmem a x ∨ vmem a y := by
  show vmem a (Candle.union vmem (Candle.upair vmem x y)) ↔ _
  rw [sp_union]
  constructor
  · rintro ⟨b, h1, h2⟩
    rcases (sp_upair x y b).1 h2 with rfl | rfl
    · exact Or.inl h1
    · exact Or.inr h1
  · rintro (h | h)
    · exact ⟨x, h, (sp_upair x y x).2 (Or.inl rfl)⟩
    · exact ⟨y, h, (sp_upair x y y).2 (Or.inr rfl)⟩

theorem vm_prod (x y a : Nat) :
    vmem a (Candle.product vmem x y) ↔
      vmem a (Candle.power vmem (Candle.power vmem (Candle.binary_union vmem x y))) ∧
        ∃ b c, vmem b x ∧ vmem c y ∧ a = Candle.pair vmem b c :=
  sp_sub _ _ a

theorem vm_prod' (x y a : Nat) :
    vmem a (Mut.product vmem x y) ↔
      vmem a (Candle.power vmem (Candle.power vmem (Candle.binary_union vmem x y))) ∧
        ∃ b c, vmem b x ∧ vmem c y ∧ a = Candle.pair vmem c b :=
  sp_sub _ _ a

-- x = {0} (code 1), y = {1} (code 2).  The ordered pair (0,1) is in the base product x × y.
-- The mutant builds `pair c b`, so its only member is the pair (1,0), and (0,1) ≠ (1,0).
theorem witness : ∃ x y : Nat, Mut.product vmem x y ≠ Candle.product vmem x y := by
  refine ⟨1, 2, ?_⟩
  intro h
  have h01 : vmem 0 1 := by unfold vmem; decide
  have h12 : vmem 1 2 := by unfold vmem; decide
  have hppu : vmem (Candle.pair vmem 0 1)
      (Candle.power vmem (Candle.power vmem (Candle.binary_union vmem 1 2))) := by
    rw [sp_power]
    intro b hb
    rw [sp_power]
    intro c hc
    rw [vm_bu]
    rcases (vm_pair 0 1 b).1 hb with rfl | rfl
    · rw [vm_unit] at hc; subst hc; exact Or.inl h01
    · rcases (sp_upair 0 1 c).1 hc with rfl | rfl
      · exact Or.inl h01
      · exact Or.inr h12
  have hbase : vmem (Candle.pair vmem 0 1) (Candle.product vmem 1 2) :=
    (vm_prod 1 2 _).2 ⟨hppu, 0, 1, h01, h12, rfl⟩
  rw [← h] at hbase
  obtain ⟨_, b, c, hb, hc, e⟩ := (vm_prod' 1 2 _).1 hbase
  have hb0 : b = 0 := by have := vmem_lt hb; omega
  have hc1 : c = 1 := by
    have := vmem_lt hc
    have hc' : c = 0 ∨ c = 1 := by omega
    rcases hc' with rfl | rfl
    · exact absurd hc (by unfold vmem; decide)
    · rfl
  subst hb0 hc1
  -- pair 0 1 = pair 1 0 is impossible: unit 0 is a member of the left but not of the right
  have hl : vmem (Candle.unit vmem 0) (Candle.pair vmem 0 1) := (vm_pair 0 1 _).2 (Or.inl rfl)
  rw [e] at hl
  rcases (vm_pair 1 0 _).1 hl with h1 | h1
  · have : vmem 0 (Candle.unit vmem 0) := (vm_unit 0 0).2 rfl
    rw [h1, vm_unit] at this
    exact absurd this (by decide)
  · have : vmem 1 (Candle.upair vmem 1 0) := (sp_upair 1 0 1).2 (Or.inl rfl)
    rw [← h1, vm_unit] at this
    exact absurd this (by decide)

#print axioms witness
