import CandleLean

open Candle HOL Classical

namespace Mut
noncomputable section

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
      (∀ x ty, VFREE_IN prop (Var x ty) → (x, ty) ∈ eqs.map (fun st => (st.1, typeof st.2))) →
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

end
end Mut

theorem rep_alist {α : Type} {β : Type} (l : List (α × β)) :
    (alist_to_fmap l).rep = fun a => ALOOKUP l a := by
  induction l with
  | nil => rfl
  | cons p t ih =>
    obtain ⟨k, v⟩ := p
    funext a
    show (if a = k then some v else (alist_to_fmap t).rep a) = ALOOKUP ((k, v) :: t) a
    rw [ih]
    simp [ALOOKUP, eq_comm]

theorem flookup_alist {α : Type} {β : Type} [Nonempty β] (l : List (α × β)) (x : α) :
    FLOOKUP (alist_to_fmap l) x = ALOOKUP l x := by
  unfold FLOOKUP FAPPLY
  rw [rep_alist]
  cases h : ALOOKUP l x <;> simp [FDOM, Aux.mem_def, rep_alist, h]
  

abbrev eqty : type := Fun (Tyvar (mls "A")) (Fun (Tyvar (mls "A")) BoolTy)

/-- A context with fun/2, bool/0 and the standard equality. -/
abbrev ctxt0 : List update :=
  [NewConst (mls "=") eqty, NewType (mls "bool") 0, NewType (mls "fun") 2]

theorem hbf : mls "bool" ≠ mls "fun" := by decide

theorem tys_bool : FLOOKUP (ctxt_tysof ctxt0) (mls "bool") = some 0 := by
  have : ctxt_tysof ctxt0 = alist_to_fmap [(mls "bool", 0), (mls "fun", 2)] := rfl
  rw [this, flookup_alist]; simp [ALOOKUP]

theorem tys_fun : FLOOKUP (ctxt_tysof ctxt0) (mls "fun") = some 2 := by
  have : ctxt_tysof ctxt0 = alist_to_fmap [(mls "bool", 0), (mls "fun", 2)] := rfl
  rw [this, flookup_alist]; simp [ALOOKUP, hbf]

theorem tms_eq : FLOOKUP (ctxt_tmsof ctxt0) (mls "=") = some eqty := by
  have : ctxt_tmsof ctxt0 = alist_to_fmap [(mls "=", eqty)] := rfl
  rw [this, flookup_alist]; simp [ALOOKUP]

theorem ok_bool : type_ok (ctxt_tysof ctxt0) BoolTy := by
  simp [type_ok, tys_bool, EVERY]

theorem ok_eqty : type_ok (ctxt_tysof ctxt0) eqty := by
  simp [type_ok, tys_fun, tys_bool, EVERY, Fun, BoolTy]

theorem theory_ok0 : theory_ok (thyof ctxt0) := by
  refine ⟨?_, ?_, ?_⟩
  · intro ty hty
    obtain ⟨x, hx, rfl⟩ := hty
    have h1 : (ctxt_tmsof ctxt0).rep = fun a => ALOOKUP [(mls "=", eqty)] a := rep_alist _
    have hx' : (ctxt_tmsof ctxt0).rep x ≠ none := hx
    rw [h1] at hx'
    have hx2 : x = mls "=" := by
      by_contra hne
      apply hx'
      simp [ALOOKUP, Ne.symm hne]
    subst hx2
    have : FAPPLY (ctxt_tmsof ctxt0) (mls "=") = eqty := by
      have h3 := tms_eq
      have hmem : mls "=" ∈ FDOM (ctxt_tmsof ctxt0) := hx
      unfold FLOOKUP at h3
      rw [if_pos hmem] at h3
      exact Option.some.inj h3
    rw [this]
    exact ok_eqty
  · intro p hp
    exact absurd hp (by simp [thyof, ctxt_axsof, axiom_list, axioms_of_upd, axexts_of_upd, conexts_of_upd, LIST_TO_SET, axsof, Aux.mem_def, IN])
  · exact ⟨tys_fun, tys_bool, tms_eq⟩

abbrev prop0 : term := equation (Var (mls "x") BoolTy) (Var (mls "x") BoolTy)

theorem proves0 : proves (thyof ctxt0, []) prop0 :=
  proves.REFL theory_ok0 ok_bool

-- The specification ConstSpec [] (x = x) over ctxt0.  Its proposition has a free variable x : bool.
-- Base: new_specification requires every free variable of prop to be one of the defined names
-- (none here), so it fails.  Mutant: the swapped VFREE_IN only tests `prop = Var x ty`, which is
-- false for a Comb, so the condition is vacuous and the update is accepted.
theorem witness : ∃ (u : update) (ctxt : List update),
    Mut.updates u ctxt ∧ ¬ Candle.updates u ctxt := by
  refine ⟨ConstSpec [] prop0, ctxt0, ?_, ?_⟩
  · refine Mut.updates.new_specification (eqs := []) (prop := prop0) proves0 trivial ?_ ?_ trivial
    · intro x ty h
      simp [VFREE_IN, equation] at h
    · intro s hs
      simp at hs
  · intro h
    cases h with
    | new_specification _ _ hfree _ _ =>
      have := hfree (mls "x") BoolTy (by simp [VFREE_IN, equation])
      simp at this

#print axioms witness
