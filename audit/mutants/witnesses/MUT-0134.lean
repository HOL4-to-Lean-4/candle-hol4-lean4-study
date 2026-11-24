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

theorem m_two {a : Nat} : memN a 2 ↔ a = 1 := by
  show (2 ^ 1 : Nat).testBit a = true ↔ a = 1
  rw [Nat.testBit_two_pow]
  simp only [decide_eq_true_eq]
  exact ⟨fun h => h.symm, fun h => h.symm⟩

theorem no_mem_empty (a : Nat) : ¬ memN a (empty memN) := by
  intro h
  exact (m_sub.1 h).2

theorem empty_eq_zero : empty memN = 0 := by
  apply Nat.eq_of_testBit_eq
  intro i
  have := no_mem_empty i
  simp only [memN] at this
  simpa using this

theorem up_inj {x y x' y' : Nat} (h : upair memN x y = upair memN x' y') :
    (x = x' ∧ y = y') ∨ (x = y' ∧ y = x') := by
  have a1 : x = x' ∨ x = y' := by
    have := (m_upair (x := x) (y := y) (a := x)).2 (Or.inl rfl); rw [h] at this; exact m_upair.1 this
  have a2 : y = x' ∨ y = y' := by
    have := (m_upair (x := x) (y := y) (a := y)).2 (Or.inr rfl); rw [h] at this; exact m_upair.1 this
  have a3 : x' = x ∨ x' = y := by
    have := (m_upair (x := x') (y := y') (a := x')).2 (Or.inl rfl); rw [← h] at this; exact m_upair.1 this
  have a4 : y' = x ∨ y' = y := by
    have := (m_upair (x := x') (y := y') (a := y')).2 (Or.inr rfl); rw [← h] at this; exact m_upair.1 this
  omega

theorem pair_inj {a b c d : Nat} (h : pair memN a b = pair memN c d) : a = c ∧ b = d := by
  unfold pair unit at h
  rcases up_inj h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rcases up_inj h1 with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;> rcases up_inj h2 with ⟨h5, h6⟩ | ⟨h5, h6⟩ <;> omega
  · rcases up_inj h1 with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;> rcases up_inj h2 with ⟨h5, h6⟩ | ⟨h5, h6⟩ <;> omega

theorem pair_in_product {x y a b : Nat} (ha : memN a x) (hb : memN b y) :
    memN (pair memN a b) (product memN x y) := by
  rw [m_product]
  refine ⟨?_, a, b, ha, hb, rfl⟩
  have hY : ∀ c, memN c x ∨ memN c y → memN c (binary_union memN x y) := by
    intro c hc
    unfold binary_union
    rw [m_union]
    rcases hc with hc | hc
    · exact ⟨x, hc, m_upair.2 (Or.inl rfl)⟩
    · exact ⟨y, hc, m_upair.2 (Or.inr rfl)⟩
  rw [m_power]
  intro s hs
  unfold pair at hs
  rw [m_power]
  intro c hc
  rcases m_upair.1 hs with rfl | rfl
  · unfold unit at hc
    rcases m_upair.1 hc with rfl | rfl <;> exact hY _ (Or.inl ha)
  · rcases m_upair.1 hc with rfl | rfl
    · exact hY _ (Or.inl ha)
    · exact hY _ (Or.inr hb)
end SM

namespace Mut
def is_std_interpretation0 [Nonempty U] (mem : U → U → Prop) (i : interpretation U) : Prop :=
  is_std_type_assignment0 mem (tyaof i) ∧
  interprets0 mem (tmaof i) (mls "=") [mls "A"]
    (fun l => abstract mem (HD l) (funspace mem (HD l) (boolset mem))
      (fun x => abstract mem (boolset mem) (HD l) (fun y => boolean mem (x = y))))
end Mut

namespace SM
/-- In the model, with D = {1} (the number 2) and Bl = boolset, the two abstractions differ. -/
theorem core :
    abstract memN 2 (funspace memN 2 (boolset memN))
      (fun x => abstract memN 2 (boolset memN) (fun y => boolean memN (x = y))) ≠
    abstract memN 2 (funspace memN 2 (boolset memN))
      (fun x => abstract memN (boolset memN) 2 (fun y => boolean memN (x = y))) := by
  intro heq
  let g1 : Nat → Nat := fun y => boolean memN (1 = y)
  let A1 : Nat := abstract memN 2 (boolset memN) g1
  have h1_2 : memN 1 2 := m_two.2 rfl
  have he_bl : memN (empty memN) (boolset memN) := m_upair.2 (Or.inl rfl)
  have g11 : g1 1 = empty memN := by simp [g1, boolean, true_]
  have hA1_mem : memN (pair memN 1 (empty memN)) A1 :=
    m_abstract.2 ⟨pair_in_product h1_2 he_bl, 1, by rw [g11]⟩
  have uniq : ∀ b, memN (pair memN 1 b) A1 → b = empty memN := by
    intro b hb
    obtain ⟨_, a', ha'⟩ := m_abstract.1 hb
    obtain ⟨e1, e2⟩ := pair_inj ha'
    subst e1
    rw [e2, g11]
  have hA1_fun : memN A1 (funspace memN 2 (boolset memN)) := by
    refine m_sub.2 ⟨?_, ?_⟩
    · show memN A1 (power memN (product memN 2 (boolset memN)))
      rw [m_power]
      intro s hs
      exact (m_abstract.1 hs).1
    · intro a ha
      have := m_two.1 ha
      subst this
      exact ⟨⟨empty memN, hA1_mem⟩, fun x y ⟨hx, hy⟩ => (uniq x hx).trans (uniq y hy).symm⟩
  have hq : memN (pair memN 1 A1) (abstract memN 2 (funspace memN 2 (boolset memN))
      (fun x => abstract memN 2 (boolset memN) (fun y => boolean memN (x = y)))) :=
    m_abstract.2 ⟨pair_in_product h1_2 hA1_fun, 1, rfl⟩
  rw [heq] at hq
  obtain ⟨_, a, ha⟩ := m_abstract.1 hq
  obtain ⟨e1, e2⟩ := pair_inj ha
  subst e1
  -- A1 = abstract Bl 2 g1, so (1, empty) would lie in product Bl 2, forcing empty ∈ 2
  have hmem : memN (pair memN 1 (empty memN)) (abstract memN (boolset memN) 2 g1) := by
    have := hA1_mem
    rw [e2] at this
    exact this
  obtain ⟨_, b, c, _, hc, hbc⟩ := m_product.1 (m_abstract.1 hmem).1
  have := (pair_inj hbc).2
  subst this
  rw [empty_eq_zero] at hc
  exact absurd hc (by simp [memN])
end SM

theorem witness : ¬ ∀ (mem : Nat → Nat → Prop) (i : interpretation Nat),
    (Mut.is_std_interpretation0 mem i ↔ Candle.is_std_interpretation0 mem i) := by
  intro h
  have hfb : mls "fun" ≠ mls "bool" := by simp [mls, str]; decide
  let δ0 : tyass Nat := fun n l => if n = mls "bool" then boolset SM.memN
    else match l with | [d, r] => funspace SM.memN d r | _ => 0
  let Fb : List Nat → Nat := fun l => abstract SM.memN (HD l) (funspace SM.memN (HD l) (boolset SM.memN))
      (fun x => abstract SM.memN (HD l) (boolset SM.memN) (fun y => boolean SM.memN (x = y)))
  let i : interpretation Nat := (δ0, fun _ l => Fb l)
  have h1 : Candle.is_std_interpretation0 SM.memN i := by
    refine ⟨⟨fun dom rng => ?_, ?_⟩, fun τ _ => rfl⟩
    · simp [i, δ0, hfb, tyaof]
    · simp [i, δ0, tyaof]
  have hv : is_type_valuation0 SM.memN (fun _ => (2 : Nat)) := fun _ => ⟨1, SM.m_two.2 rfl⟩
  have h2 := ((h SM.memN i).2 h1).2 (fun _ => 2) hv
  simp only [i, Fb, List.map, HD_def, tmaof] at h2
  exact SM.core h2

#print axioms witness
