import CandleLean
open HOL Candle Classical
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
noncomputable section
theorem mem_fdom {α β : Type} (f : fmap α β) (x : α) : x ∈ FDOM f ↔ f.rep x ≠ none := Iff.rfl

theorem flookup_eq {α β : Type} [Nonempty β] (f : fmap α β) (k : α) : FLOOKUP f k = f.rep k := by
  unfold FLOOKUP FAPPLY
  cases h : f.rep k <;> simp [h, mem_fdom]

theorem frange_iff {α β : Type} [Nonempty β] (f : fmap α β) (y : β) :
    y ∈ FRANGE f ↔ ∃ x, f.rep x = some y := by
  unfold FRANGE FAPPLY
  constructor
  · rintro ⟨x, hx, hy⟩
    refine ⟨x, ?_⟩
    have hx' : f.rep x ≠ none := hx
    cases h : f.rep x
    · exact absurd h hx'
    · simp [h] at hy; rw [hy]
  · rintro ⟨x, hx⟩
    exact ⟨x, by simp [mem_fdom, hx], by simp [hx]⟩

/-- the standard signature -/
def stdsig : sig :=
  (FUPDATE (FUPDATE FEMPTY (mls "fun", 2)) (mls "bool", 0),
   FUPDATE FEMPTY (mls "=", Fun (Tyvar (mls "A")) (Fun (Tyvar (mls "A")) BoolTy)))

theorem fun_ne_bool : mls "fun" ≠ mls "bool" := by decide

theorem stdsig_fun : FLOOKUP (tysof stdsig) (mls "fun") = some 2 := by
  simp [flookup_eq, stdsig, tysof, FUPDATE, FEMPTY, fun_ne_bool]
theorem stdsig_bool : FLOOKUP (tysof stdsig) (mls "bool") = some 0 := by
  simp [flookup_eq, stdsig, tysof, FUPDATE, FEMPTY]
theorem stdsig_eq : FLOOKUP (tmsof stdsig) (mls "=") =
    some (Fun (Tyvar (mls "A")) (Fun (Tyvar (mls "A")) BoolTy)) := by
  simp [flookup_eq, stdsig, tmsof, FUPDATE, FEMPTY]

theorem stdsig_std : is_std_sig stdsig := ⟨stdsig_fun, stdsig_bool, stdsig_eq⟩

theorem stdsig_type_ok_Bool : type_ok (tysof stdsig) BoolTy := by
  simp [BoolTy, type_ok, stdsig_bool, EVERY]

theorem stdsig_type_ok_eq : type_ok (tysof stdsig) (Fun (Tyvar (mls "A")) (Fun (Tyvar (mls "A")) BoolTy)) := by
  have := stdsig_type_ok_Bool
  simp [Fun, type_ok, stdsig_fun, EVERY] at this ⊢
  exact this

/-- a theory over the standard signature with axioms `P` -/
theorem stdsig_theory_ok (P : term → Prop) (hP : ∀ p, P p → term_ok stdsig p ∧ has_type p BoolTy) :
    theory_ok (stdsig, P) := by
  refine ⟨?_, hP, stdsig_std⟩
  intro ty hty
  rw [thy_tmsof] at hty
  obtain ⟨x, hx⟩ := (frange_iff _ _).mp hty
  simp [tmsof, sigof, stdsig, FUPDATE, FEMPTY] at hx
  by_cases h : x = mls "="
  · simp [h] at hx
    rw [← hx]
    exact stdsig_type_ok_eq
  · simp [h] at hx


namespace Mut
/-- mutated `entails0`; the last `∧` became `∨`, which (as `∧` binds tighter) makes the whole definition
`(theory_ok ∧ … ∧ hypset_ok) ∨ (∀ i, models → satisfies)` -/
def entails0 {U : Type u} [Nonempty U] (mem : U → U → Prop) (thyh : thy × List term) (c : term) : Prop :=
  theory_ok thyh.1 ∧
  EVERY (term_ok (sigof thyh.1)) (c :: thyh.2) ∧
  EVERY (fun p => has_type p BoolTy) (c :: thyh.2) ∧
  hypset_ok thyh.2 ∨
  ∀ i : interpretation U, models0 mem i thyh.1 → satisfies0 mem i (sigof thyh.1, thyh.2, c)
end Mut

/-- With the empty membership relation there are no valuations, so `satisfies0` is vacuous and the mutant holds
for the empty (non-`theory_ok`) theory, where the base fails. -/
theorem witness : ∃ (mem : Nat → Nat → Prop) (thyh : thy × List term) (c : term),
    Mut.entails0 mem thyh c ∧ ¬ entails0 mem thyh c := by
  refine ⟨fun _ _ => False, ((((FEMPTY : tysig), (FEMPTY : tmsig)), fun _ => False), []),
    Var (mls "x") (Tyvar (mls "a")), Or.inr ?_, ?_⟩
  · intro i _ v hv
    obtain ⟨⟨h1, _⟩, _⟩ := hv
    obtain ⟨a, ha⟩ := h1 (mls "x")
    exact ha.elim
  · intro h
    have h1 := h.1.2.2.1
    have h4 : FLOOKUP (tysof (sigof ((((FEMPTY : tysig), (FEMPTY : tmsig)), fun _ => False) : thy))) (mls "fun") = none :=
      by rw [flookup_eq]; rfl
    rw [h4] at h1
    cases h1

#print axioms witness
