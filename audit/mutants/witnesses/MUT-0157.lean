import CandleLean
open HOL Candle Classical
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
universe u
variable {U : Type u}
noncomputable section

/-! A model of `is_set_theory`: hereditarily finite sets coded by natural numbers (Ackermann coding). -/
namespace HFModel
open Classical

/-- `mem a x`: bit `a` of `x` is set. -/
def hfmem (a x : Nat) : Prop := x.testBit a = true

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
      have := hs a
      by_cases han : n = a
      · subst han; simp [hp]
      · have : ¬ (n = a) := han
        simp only [Bool.or_eq_true, decide_eq_true_eq, this, or_false, hs a]
        constructor
        · rintro ⟨h1, h2⟩; exact ⟨by omega, h2⟩
        · rintro ⟨h1, h2⟩
          have : a ≠ n := fun h => han h.symm
          exact ⟨by omega, h2⟩
    · refine ⟨s, fun a => ?_⟩
      rw [hs a]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨by omega, h2⟩
      · rintro ⟨h1, h2⟩
        have : a ≠ n := fun h => hp (h ▸ h2)
        exact ⟨by omega, h2⟩

theorem is_set_theory_hf : is_set_theory hfmem := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x y
    constructor
    · rintro rfl a; exact Iff.rfl
    · intro h
      apply Nat.eq_of_testBit_eq
      intro i
      have := h i
      unfold hfmem at this
      cases hx : y.testBit i <;> cases hy : x.testBit i <;> simp_all
  · -- separation
    have : ∀ x : Nat, ∀ P : Nat → Prop, ∃ s : Nat, ∀ a, hfmem a s ↔ hfmem a x ∧ P a := by
      intro x P
      obtain ⟨s, hs⟩ := fin_exists (fun a => hfmem a x ∧ P a) x
      exact ⟨s, fun a => by
        unfold hfmem at *
        rw [hs a]
        exact ⟨fun h => h.2, fun h => ⟨bit_lt h.1, h⟩⟩⟩
    exact ⟨fun x P => Classical.choose (this x P), fun x P => Classical.choose_spec (this x P)⟩
  · -- power
    have : ∀ x : Nat, ∃ s : Nat, ∀ a, hfmem a s ↔ ∀ b, hfmem b a → hfmem b x := by
      intro x
      obtain ⟨s, hs⟩ := fin_exists (fun a => ∀ b, hfmem b a → hfmem b x) (2 ^ x)
      refine ⟨s, fun a => ?_⟩
      unfold hfmem at *
      rw [hs a]
      constructor
      · exact fun h => h.2
      · intro h
        refine ⟨Nat.lt_pow_two_of_testBit a ?_, h⟩
        intro i hi
        by_contra hne
        have := h i (by simpa using hne)
        have := bit_lt this
        omega
    exact ⟨fun x => Classical.choose (this x), fun x => Classical.choose_spec (this x)⟩
  · -- union
    have : ∀ x : Nat, ∃ s : Nat, ∀ a, hfmem a s ↔ ∃ b, hfmem a b ∧ hfmem b x := by
      intro x
      obtain ⟨s, hs⟩ := fin_exists (fun a => ∃ b, hfmem a b ∧ hfmem b x) x
      refine ⟨s, fun a => ?_⟩
      unfold hfmem at *
      rw [hs a]
      constructor
      · exact fun h => h.2
      · intro h
        obtain ⟨b, h1, h2⟩ := h
        exact ⟨Nat.lt_trans (bit_lt h1) (bit_lt h2), b, h1, h2⟩
    exact ⟨fun x => Classical.choose (this x), fun x => Classical.choose_spec (this x)⟩
  · -- unordered pair
    have : ∀ x y : Nat, ∃ s : Nat, ∀ a, hfmem a s ↔ a = x ∨ a = y := by
      intro x y
      obtain ⟨s, hs⟩ := fin_exists (fun a => a = x ∨ a = y) (x + y + 1)
      refine ⟨s, fun a => ?_⟩
      unfold hfmem
      rw [hs a]
      constructor
      · exact fun h => h.2
      · intro h
        exact ⟨by omega, h⟩
    exact ⟨fun x y => Classical.choose (this x y), fun x y => Classical.choose_spec (this x y)⟩

end HFModel

namespace Mut
def apply (mem : U → U → Prop) (x y : U) : U :=
  @Classical.epsilon U ⟨x⟩ (fun a => mem (pair mem a y) x)
end Mut

/-- Kuratowski pairs are injective for any `u` with the `upair` specification (only the forward direction of the spec is used). -/
theorem kpair_inj {mem : Nat → Nat → Prop} {u : Nat → Nat → Nat}
    (hs : ∀ x y a, mem a (u x y) ↔ a = x ∨ a = y) {x1 y1 x2 y2 : Nat}
    (h : u (u x1 x1) (u x1 y1) = u (u x2 x2) (u x2 y2)) : x1 = x2 ∧ y1 = y2 := by
  have mm : ∀ p q p' q', u p q = u p' q' → ∀ a, (a = p ∨ a = q) ↔ (a = p' ∨ a = q') := by
    intro p q p' q' e a
    rw [← hs, ← hs, e]
  have m1 := mm _ _ _ _ h
  -- x1 = x2
  have hx : x1 = x2 := by
    have c1 := (m1 (u x1 x1)).1 (Or.inl rfl)
    rcases c1 with c1 | c1
    · have := (mm _ _ _ _ c1 x1).1 (Or.inl rfl)
      rcases this with h' | h' <;> exact h'
    · have := (mm _ _ _ _ c1 x2).2 (Or.inl rfl)
      rcases this with h' | h' <;> exact h'.symm
  subst hx
  refine ⟨rfl, ?_⟩
  -- y1 = y2
  have c2 := (m1 (u x1 y1)).1 (Or.inr rfl)
  have c4 := (m1 (u x1 y2)).2 (Or.inr rfl)
  rcases c2 with c2 | c2
  · -- u x1 y1 = u x1 x1
    have y1x : y1 = x1 := by
      have := (mm _ _ _ _ c2 y1).1 (Or.inr rfl)
      rcases this with h' | h' <;> exact h'
    rcases c4 with c4 | c4
    · have y2x : y2 = x1 := by
        have := (mm _ _ _ _ c4 y2).1 (Or.inr rfl)
        rcases this with h' | h' <;> exact h'
      rw [y1x, y2x]
    · have y2x : y2 = x1 := by
        have := (mm _ _ _ _ c4 y2).1 (Or.inr rfl)
        rcases this with h' | h'
        · exact h'
        · rw [h', y1x]
      rw [y1x, y2x]
  · -- u x1 y1 = u x1 y2
    have := (mm _ _ _ _ c2 y1).1 (Or.inr rfl)
    rcases this with h' | h'
    · -- y1 = x1
      have := (mm _ _ _ _ c2 y2).2 (Or.inr rfl)
      rcases this with h'' | h''
      · rw [h', h'']
      · exact h''.symm
    · exact h'


open HFModel in
theorem witness : ∃ (x y : Nat), Mut.apply hfmem x y ≠ Candle.apply hfmem x y := by
  have hex : ∃ f, is_upair hfmem f := is_set_theory_hf.2.2.2.2
  have hs : ∀ x y a, hfmem a (upair hfmem x y) ↔ a = x ∨ a = y :=
    fun x y a => (Classical.epsilon_spec hex : is_upair hfmem (upair hfmem)) x y a
  have hp : ∀ x y, Candle.pair hfmem x y = upair hfmem (upair hfmem x x) (upair hfmem x y) := fun _ _ => rfl
  let p1 : Nat := Candle.pair hfmem 0 1
  let p2 : Nat := Candle.pair hfmem 2 0
  let X : Nat := upair hfmem p1 p2
  have hX : ∀ z, hfmem z X ↔ z = p1 ∨ z = p2 := fun z => hs p1 p2 z
  have inj : ∀ a b c d, Candle.pair hfmem a b = Candle.pair hfmem c d → a = c ∧ b = d := by
    intro a b c d h
    rw [hp, hp] at h
    exact kpair_inj hs h
  refine ⟨X, 0, ?_⟩
  -- base value is 1
  have hb : Candle.apply hfmem X 0 = 1 := by
    unfold Candle.apply
    have hex1 : ∃ a, hfmem (Candle.pair hfmem 0 a) X := ⟨1, (hX _).2 (Or.inl rfl)⟩
    have h1 := Classical.epsilon_spec hex1
    rcases (hX _).1 h1 with h | h
    · exact (inj _ _ _ _ h).2
    · exact absurd (inj _ _ _ _ h).1 (by omega)
  have hm : Mut.apply hfmem X 0 = 2 := by
    unfold Mut.apply
    have hex2 : ∃ a, hfmem (Candle.pair hfmem a 0) X := ⟨2, (hX _).2 (Or.inr rfl)⟩
    have h2 := Classical.epsilon_spec hex2
    rcases (hX _).1 h2 with h | h
    · exact absurd (inj _ _ _ _ h).2 (by omega)
    · exact (inj _ _ _ _ h).1
  rw [hb, hm]
  omega

#print axioms witness
