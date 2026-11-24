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
/-- mutated `theory_ok` (the `has_type p BoolTy` conjunct on axioms is dropped) -/
def theory_ok (thy : thy) : Prop :=
  (∀ ty, ty ∈ FRANGE (thy_tmsof thy) → type_ok (thy_tysof thy) ty) ∧
  (∀ p, p ∈ axsof thy → term_ok (sigof thy) p) ∧
  is_std_sig (sigof thy)
end Mut

theorem stdsig_range_ok (P : term → Prop) :
    ∀ ty, ty ∈ FRANGE (thy_tmsof (stdsig, P)) → type_ok (thy_tysof (stdsig, P)) ty := by
  intro ty hty
  rw [thy_tmsof] at hty
  obtain ⟨x, hx⟩ := (frange_iff _ _).mp hty
  simp [tmsof, sigof, stdsig, FUPDATE, FEMPTY] at hx
  by_cases h : x = mls "="
  · simp [h] at hx
    rw [← hx]
    exact stdsig_type_ok_eq
  · simp [h] at hx

theorem no_bool_tyvar (x a : mlstring) : ¬ has_type (Var x (Tyvar a)) BoolTy := by
  intro h
  cases h

/-- the axiom `x : a` (a type variable) is accepted by the mutant but is not a boolean term. -/
theorem witness : ∃ t : thy, Mut.theory_ok t ∧ ¬ Candle.theory_ok t := by
  refine ⟨(stdsig, fun t => t = Var (mls "x") (Tyvar (mls "a"))), ⟨stdsig_range_ok _, ?_, stdsig_std⟩, ?_⟩
  · intro q hq
    have hq' : q = Var (mls "x") (Tyvar (mls "a")) := hq
    subst hq'
    simp [term_ok, type_ok]
  · intro h
    exact no_bool_tyvar _ _ (h.2.1 _ rfl).2

#print axioms witness
