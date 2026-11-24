import CandleLean
open Candle HOL Classical
noncomputable section
namespace SM

def memN (a b : Nat) : Prop := b.testBit a = true

def sepAux (x : Nat) (P : Nat → Prop) : Nat → Nat
  | 0 => 0
  | k+1 => sepAux x P k ||| (if x.testBit k = true ∧ P k then 2^k else 0)

theorem testBit_sepAux (x : Nat) (P : Nat → Prop) :
    ∀ k a, (sepAux x P k).testBit a = true ↔ a < k ∧ x.testBit a = true ∧ P a
  | 0, a => by simp [sepAux]
  | k+1, a => by
    simp only [sepAux, Nat.testBit_or, Bool.or_eq_true, testBit_sepAux x P k a]
    by_cases h : x.testBit k = true ∧ P k
    · simp only [h, and_self, if_true, Nat.testBit_two_pow, decide_eq_true_eq]
      constructor
      · rintro (h1 | h1)
        · exact ⟨by omega, h1.2⟩
        · subst h1; exact ⟨by omega, h⟩
      · rintro ⟨h1, h2⟩
        by_cases hk : a = k
        · right; exact hk.symm
        · left; exact ⟨by omega, h2⟩
    · rw [if_neg h]
      simp only [Nat.zero_testBit, Bool.false_eq_true, or_false]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨by omega, h2⟩
      · rintro ⟨h1, h2⟩
        refine ⟨?_, h2⟩
        by_cases hk : a = k
        · subst hk; exact absurd h2 h
        · omega

theorem lt_of_testBit {x a : Nat} (h : x.testBit a = true) : a < x + 1 := by
  have := Nat.ge_two_pow_of_testBit h
  have := Nat.lt_two_pow_self (n := a)
  omega

theorem sep_ex : ∃ sub : Nat → (Nat → Prop) → Nat, is_separation memN sub := by
  refine ⟨fun x P => sepAux x P (x+1), fun x P a => ?_⟩
  simp only [memN, testBit_sepAux]
  constructor
  · rintro ⟨_, h1, h2⟩; exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨lt_of_testBit h1, h1, h2⟩

def unionAux (x : Nat) : Nat → Nat
  | 0 => 0
  | k+1 => unionAux x k ||| (if x.testBit k = true then k else 0)

theorem testBit_unionAux (x : Nat) :
    ∀ k a, (unionAux x k).testBit a = true ↔ ∃ b, b < k ∧ x.testBit b = true ∧ b.testBit a = true
  | 0, a => by simp [unionAux]
  | k+1, a => by
    simp only [unionAux, Nat.testBit_or, Bool.or_eq_true, testBit_unionAux x k a]
    by_cases h : x.testBit k = true
    · simp only [h, if_true]
      constructor
      · rintro (⟨b, hb, h1, h2⟩ | h1)
        · exact ⟨b, by omega, h1, h2⟩
        · exact ⟨k, by omega, h, h1⟩
      · rintro ⟨b, hb, h1, h2⟩
        by_cases hk : b = k
        · subst hk; right; exact h2
        · left; exact ⟨b, by omega, h1, h2⟩
    · simp only [h, if_false, Nat.zero_testBit, Bool.false_eq_true, or_false]
      constructor
      · rintro ⟨b, hb, h1, h2⟩; exact ⟨b, by omega, h1, h2⟩
      · rintro ⟨b, hb, h1, h2⟩
        refine ⟨b, ?_, h1, h2⟩
        by_cases hk : b = k
        · subst hk; exact absurd h1 h
        · omega

theorem union_ex : ∃ u : Nat → Nat, is_union memN u := by
  refine ⟨fun x => unionAux x (x+1), fun x a => ?_⟩
  simp only [memN, testBit_unionAux]
  constructor
  · rintro ⟨b, _, h1, h2⟩; exact ⟨b, h2, h1⟩
  · rintro ⟨b, h2, h1⟩; exact ⟨b, lt_of_testBit h1, h1, h2⟩

def powerAux (x : Nat) : Nat → Nat
  | 0 => 0
  | k+1 => powerAux x k ||| (if ∀ b, k.testBit b = true → x.testBit b = true then 2^k else 0)

theorem testBit_powerAux (x : Nat) :
    ∀ k a, (powerAux x k).testBit a = true ↔ a < k ∧ ∀ b, a.testBit b = true → x.testBit b = true
  | 0, a => by simp [powerAux]
  | k+1, a => by
    simp only [powerAux, Nat.testBit_or, Bool.or_eq_true, testBit_powerAux x k a]
    by_cases h : ∀ b, k.testBit b = true → x.testBit b = true
    · rw [if_pos h]
      simp only [Nat.testBit_two_pow, decide_eq_true_eq]
      constructor
      · rintro (h1 | h1)
        · exact ⟨by omega, h1.2⟩
        · subst h1; exact ⟨by omega, h⟩
      · rintro ⟨h1, h2⟩
        by_cases hk : a = k
        · right; exact hk.symm
        · left; exact ⟨by omega, h2⟩
    · rw [if_neg h]
      simp only [Nat.zero_testBit, Bool.false_eq_true, or_false]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨by omega, h2⟩
      · rintro ⟨h1, h2⟩
        refine ⟨?_, h2⟩
        by_cases hk : a = k
        · subst hk; exact absurd h2 h
        · omega

theorem subset_le {a x : Nat} (h : ∀ b, a.testBit b = true → x.testBit b = true) : a ≤ x := by
  have : a &&& x = a := by
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_and]
    cases hi : a.testBit i
    · simp
    · simp [h i hi]
  rw [← this]; exact Nat.and_le_right

theorem power_ex : ∃ p : Nat → Nat, is_power memN p := by
  refine ⟨fun x => powerAux x (x+1), fun x a => ?_⟩
  simp only [memN, testBit_powerAux]
  constructor
  · rintro ⟨_, h⟩ b hb; exact h b hb
  · intro h; exact ⟨by have := subset_le h; omega, h⟩

theorem upair_ex : ∃ u : Nat → Nat → Nat, is_upair memN u := by
  refine ⟨fun x y => 2^x ||| 2^y, fun x y a => ?_⟩
  simp only [memN, Nat.testBit_or, Nat.testBit_two_pow, Bool.or_eq_true, decide_eq_true_eq]
  constructor <;> rintro (h | h) <;> simp [h]

theorem ext_N : extensional memN := by
  intro x y
  constructor
  · rintro rfl a; exact Iff.rfl
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    have := h i
    simp only [memN] at this
    cases h1 : x.testBit i <;> cases h2 : y.testBit i <;> simp_all

theorem set_theory_N : is_set_theory memN :=
  ⟨ext_N, sep_ex, power_ex, union_ex, upair_ex⟩

theorem sub_spec : is_separation memN (sub memN) := Classical.epsilon_spec sep_ex
theorem power_spec : is_power memN (power memN) := Classical.epsilon_spec power_ex
theorem union_spec : is_union memN (union memN) := Classical.epsilon_spec union_ex
theorem upair_spec : is_upair memN (upair memN) := Classical.epsilon_spec upair_ex

end SM

namespace SM
theorem m_sub {x : Nat} {P : Nat → Prop} {a : Nat} : memN a (sub memN x P) ↔ memN a x ∧ P a := sub_spec x P a
theorem m_power {x a : Nat} : memN a (power memN x) ↔ ∀ b, memN b a → memN b x := power_spec x a
theorem m_union {x a : Nat} : memN a (union memN x) ↔ ∃ b, memN a b ∧ memN b x := union_spec x a
theorem m_upair {x y a : Nat} : memN a (upair memN x y) ↔ a = x ∨ a = y := upair_spec x y a
theorem m_abstract {d r : Nat} {f : Nat → Nat} {p : Nat} :
    memN p (abstract memN d r f) ↔ memN p (product memN d r) ∧ ∃ a, p = pair memN a (f a) := m_sub
theorem m_product {x y p : Nat} :
    memN p (product memN x y) ↔ memN p (power memN (power memN (binary_union memN x y))) ∧
      ∃ b c, memN b x ∧ memN c y ∧ p = pair memN b c := m_sub
theorem mem_zero_one : memN 0 1 := by simp [memN]
theorem not_mem_zero (c : Nat) : ¬ memN c 0 := by simp [memN]
end SM

-- The mutated statement (hypothesis `mem (f x) t1 ∨ mem (g x) t2 ∧ f x = g x`).
theorem witness :
    ¬ (∀ {U : Type} (mem : U → U → Prop), is_set_theory mem →
        ∀ s t1 t2 (f g : U → U),
          (∀ x, mem x s → mem (f x) t1 ∨ mem (g x) t2 ∧ f x = g x) →
          abstract mem s t1 f = abstract mem s t2 g) := by
  intro h
  open SM in
  have key := h (U := Nat) memN set_theory_N 1 1 0 (fun _ => 0) (fun _ => 0)
    (fun x _ => Or.inl mem_zero_one)
  -- the pair (0,0) belongs to the left abstraction ...
  have hl : memN (pair memN 0 0) (abstract memN 1 1 (fun _ => 0)) := by
    rw [m_abstract, m_product]
    refine ⟨⟨?_, 0, 0, mem_zero_one, mem_zero_one, rfl⟩, 0, rfl⟩
    rw [m_power]
    intro b hb
    have hb' : b = unit memN 0 := by
      unfold pair at hb
      rcases m_upair.1 hb with h1 | h1 <;> exact h1
    subst hb'
    rw [m_power]
    intro c hc
    have hc' : c = 0 := by
      rcases m_upair.1 hc with h1 | h1 <;> exact h1
    subst hc'
    unfold binary_union
    rw [m_union]
    exact ⟨1, mem_zero_one, m_upair.2 (Or.inl rfl)⟩
  -- ... but the right abstraction has no members (its range is empty).
  rw [key] at hl
  rw [m_abstract, m_product] at hl
  obtain ⟨⟨_, b, c, _, hc, _⟩, _⟩ := hl
  exact not_mem_zero c hc

#print axioms witness
