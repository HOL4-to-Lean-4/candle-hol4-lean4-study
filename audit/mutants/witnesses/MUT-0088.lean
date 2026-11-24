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
/-- mutated `updates`: in `new_specification` the premise `VFREE_IN (Var x ty) prop →` is dropped -/
inductive updates : update → List update → Prop where
  | new_axiom {prop : term} {ctxt : List update} :
      has_type prop BoolTy → term_ok (ctxt_sigof ctxt) prop →
      updates (NewAxiom prop) ctxt
  | new_constant {name : mlstring} {ctxt : List update} {ty : type} :
      ¬ name ∈ FDOM (ctxt_tmsof ctxt) → type_ok (ctxt_tysof ctxt) ty →
      updates (NewConst name ty) ctxt
  | new_specification {ctxt : List update} {eqs : List (mlstring × term)} {prop : term} :
      proves (thyof ctxt, eqs.map (fun st => equation (Var st.1 (typeof st.2)) st.2)) prop →
      EVERY (fun t => CLOSED t ∧ (∀ v, v ∈ tvars t → v ∈ tyvars (typeof t))) (eqs.map Prod.snd) →
      (∀ x ty, (x, ty) ∈ eqs.map (fun st => (st.1, typeof st.2))) →
      (∀ s, s ∈ eqs.map Prod.fst → ¬ s ∈ FDOM (ctxt_tmsof ctxt)) →
      ALL_DISTINCT (eqs.map Prod.fst) →
      updates (ConstSpec eqs prop) ctxt
  | new_type {name : mlstring} {ctxt : List update} {arity : Nat} :
      ¬ name ∈ FDOM (ctxt_tysof ctxt) →
      updates (NewType name arity) ctxt
  | new_type_definition {ctxt : List update} {pred witness : term} {name abs rep : mlstring} :
      proves (thyof ctxt, []) (Comb pred witness) →
      CLOSED pred →
      ¬ name ∈ FDOM (ctxt_tysof ctxt) →
      ¬ abs ∈ FDOM (ctxt_tmsof ctxt) →
      ¬ rep ∈ FDOM (ctxt_tmsof ctxt) →
      abs ≠ rep →
      updates (TypeDefn name pred abs rep) ctxt
end Mut

def eqty : type := Fun (Tyvar (mls "A")) (Fun (Tyvar (mls "A")) BoolTy)

/-- context with `fun`, `bool` and `=` -/
def ctx0 : List update := [NewType (mls "fun") 2, NewType (mls "bool") 0, NewConst (mls "=") eqty]

theorem ctx0_tysof_rep (a : mlstring) :
    (ctxt_tysof ctx0).rep a = if a = mls "fun" then some 2 else if a = mls "bool" then some 0 else none := by
  simp [ctxt_tysof, type_list, ctx0, types_of_upd, alist_to_fmap, FUPDATE, FEMPTY]

theorem ctx0_tmsof_rep (a : mlstring) :
    (ctxt_tmsof ctx0).rep a = if a = mls "=" then some eqty else none := by
  simp [ctxt_tmsof, const_list, ctx0, consts_of_upd, alist_to_fmap, FUPDATE, FEMPTY]

theorem ctx0_fun : FLOOKUP (ctxt_tysof ctx0) (mls "fun") = some 2 := by
  rw [flookup_eq, ctx0_tysof_rep]; simp
theorem ctx0_bool : FLOOKUP (ctxt_tysof ctx0) (mls "bool") = some 0 := by
  rw [flookup_eq, ctx0_tysof_rep]; simp [fun_ne_bool.symm]
theorem ctx0_eq : FLOOKUP (ctxt_tmsof ctx0) (mls "=") = some eqty := by
  rw [flookup_eq, ctx0_tmsof_rep]; simp

theorem ctx0_type_ok_Bool : type_ok (ctxt_tysof ctx0) BoolTy := by
  simp [BoolTy, type_ok, ctx0_bool, EVERY]

theorem ctx0_type_ok_eqty : type_ok (ctxt_tysof ctx0) eqty := by
  have := ctx0_type_ok_Bool
  simp [eqty, Fun, type_ok, ctx0_fun, EVERY] at this ⊢
  exact this

theorem ctx0_theory_ok : theory_ok (thyof ctx0) := by
  refine ⟨?_, ?_, ⟨ctx0_fun, ctx0_bool, ctx0_eq⟩⟩
  · intro ty hty
    obtain ⟨x, hx⟩ := (frange_iff _ _).mp hty
    have hx' : (ctxt_tmsof ctx0).rep x = some ty := hx
    rw [ctx0_tmsof_rep] at hx'
    by_cases h : x = mls "="
    · simp [h] at hx'
      rw [← hx']
      exact ctx0_type_ok_eqty
    · simp [h] at hx'
  · intro p hp
    simp [thyof, ctxt_axsof, axiom_list, ctx0, axioms_of_upd, axexts_of_upd, conexts_of_upd, LIST_TO_SET, axsof] at hp
    exact (by exact hp : False).elim

/-- `ConstSpec [] (λx.x = λx.x)` is a legal update in the base (by REFL; no free variables), but the mutant's
premise `∀ x ty, (x,ty) ∈ []` is unsatisfiable. -/
theorem witness : ∃ (u : update) (ctxt : List update), Candle.updates u ctxt ∧ ¬ Mut.updates u ctxt := by
  let t : term := Abs (Var (mls "x") (Tyvar (mls "a"))) (Var (mls "x") (Tyvar (mls "a")))
  have ht : term_ok (sigof (thyof ctx0)) t := by
    refine ⟨mls "x", Tyvar (mls "a"), rfl, ?_, ?_⟩ <;> simp [term_ok, type_ok]
  refine ⟨ConstSpec [] (equation t t), ctx0, ?_, ?_⟩
  · refine updates.new_specification ?_ ?_ ?_ ?_ ?_
    · exact proves.REFL ctx0_theory_ok ht
    · simp [EVERY]
    · intro x ty h
      exfalso
      simp [equation, Equal, t, VFREE_IN, typeof] at h
      exact h.1 h.2.1 h.2.2
    · simp
    · simp [ALL_DISTINCT]
  · intro h
    cases h with
    | new_specification _ _ h3 _ _ =>
      have := h3 (mls "x") (Tyvar (mls "a"))
      simp at this

#print axioms witness
