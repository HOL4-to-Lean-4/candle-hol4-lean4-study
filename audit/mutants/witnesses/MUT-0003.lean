import CandleLean

open Candle HOL Classical

universe u

namespace Mut
noncomputable section

variable {U : Type u}

-- The mutated statement of `binary_inference_rule` (the premise `has_type q Bool ∧ … ∧ entails0 … p1 ∧ entails0 … p2 →`
-- is removed), as a Prop.
def binary_inference_rule_stmt [Nonempty U] (mem : U → U → Prop) : Prop :=
    is_set_theory mem →
      ∀ (thy : thy) (h1 h2 : List term) (p1 p2 q : term),
        entails0 mem (thy, term_union h1 h2) q

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

-- Instance of the mutated statement at U = Nat, mem = vmem.  The hypothesis `is_set_theory vmem`
-- holds (vomega), so the mutated claim would give `entails0` for an ill-typed conclusion q, which
-- is false because `entails0` requires `has_type q BoolTy`.
theorem witness : ¬ Mut.binary_inference_rule_stmt vmem := by
  intro h
  let thy0 : thy := ((FEMPTY, FEMPTY), fun _ => False)
  have := h vomega thy0 [] [] (Var (mls "x") (Tyvar (mls "a"))) (Var (mls "x") (Tyvar (mls "a")))
    (Var (mls "x") (Tyvar (mls "a")))
  have h3 : EVERY (fun p => has_type p BoolTy)
      (Var (mls "x") (Tyvar (mls "a")) :: (thy0, term_union [] []).2) := this.2.2.1
  have hq : has_type (Var (mls "x") (Tyvar (mls "a"))) BoolTy := h3.1
  cases hq

#print axioms witness
