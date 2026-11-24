import CandleLean
open HOL Candle
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

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
universe u
/-- mutated statement of `Candle.REFL_correct` (premise `theory_ok thy` dropped) -/
def REFL_correct_stmt : Prop :=
  ∀ (U : Type u) [Nonempty U] (mem : U → U → Prop),
    is_set_theory mem →
      ∀ (thy : thy) (t : term),
        term_ok (sigof thy) t →
        entails0 mem (thy, []) (equation t t)
end Mut

theorem flookup_empty {α : Type} {β : Type} [Nonempty β] (x : α) :
    FLOOKUP (FEMPTY : fmap α β) x = none := by
  unfold FLOOKUP
  rw [if_neg]
  intro h
  exact h rfl

/-- with a genuine set-theory model (hereditarily finite sets) and the empty theory (which is not
`theory_ok`), the mutated statement fails -/
theorem witness : ¬ Mut.REFL_correct_stmt.{0} := by
  intro h
  have := h Nat HFModel.hfmem HFModel.is_set_theory_hf ((FEMPTY, FEMPTY), fun _ => False)
    (Var (mls "x") (Tyvar (mls "a"))) (by simp [term_ok, type_ok])
  have h3 := this.1.2.2.1
  have h4 : FLOOKUP (tysof (sigof (((FEMPTY : tysig), (FEMPTY : tmsig)), (fun _ => False : Set term)))) (mls "fun") = none :=
    flookup_empty _
  rw [h4] at h3
  cases h3

#print axioms witness
