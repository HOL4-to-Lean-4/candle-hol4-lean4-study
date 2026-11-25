import CandleLean.HolSemantics
import CandleLean.Proofs.SemBase

/-!
# holSemanticsExtra (CakeML `candle/standard/semantics/holSemanticsExtraScript.sml`)

This theory defines no constants.  The ML value used in the statement of `termsem_Equal`,

    val Equalsem =
      is_std_interpretation_def
      |> SPEC_ALL |> concl |> rhs
      |> strip_conj |> last
      |> strip_comb |> snd |> last

is the last argument of `interprets` in `is_std_interpretation_def`, i.e. the term

    λl. Abstract (HD l) (Funspace (HD l) boolset)
          (λx. Abstract (HD l) boolset (λy. Boolean (x = y)))

which in Lean is written
`fun l => abstract mem (HD l) (funspace mem (HD l) (boolset mem))
            (fun x => abstract mem (HD l) (boolset mem) (fun y => boolean mem (x = y)))`.
-/

universe u

namespace Candle

open HOL Classical

noncomputable section

variable {U : Type u}

/- HOL4:
Theorem is_std_interpretation_is_type:
   is_std_interpretation i ⇒ is_std_type_assignment (FST i)
-/
theorem is_std_interpretation_is_type [Nonempty U] (mem : U → U → Prop) (i : interpretation U) :
    is_std_interpretation0 mem i → is_std_type_assignment0 mem i.1 := by
  intro h
  exact h.1

/- HOL4:
Theorem typesem_inhabited:
   is_set_theory ^mem ⇒
    ∀tyenv δ τ ty.
    is_type_valuation τ ∧
    is_type_assignment tyenv δ ∧
    type_ok tyenv ty
    ⇒
    inhabited (typesem δ τ ty)
-/
theorem typesem_inhabited (mem : U → U → Prop) :
    is_set_theory mem →
      ∀ (tyenv : tysig) (δ : tyass U) (τ : tyval U) (ty : type),
        is_type_valuation0 mem τ ∧
        is_type_assignment0 mem tyenv δ ∧
        type_ok tyenv ty →
        inhabited mem (typesem δ τ ty) := by
  rintro _ tyenv δ τ ty ⟨h1, h2, h3⟩
  induction ty using Aux.type_ind with
  | hv v => rw [typesem]; exact h1 v
  | ha n args ih =>
    rw [type_ok, Aux.EVERY_iff] at h3
    rw [typesem]
    obtain ⟨h4, h5⟩ := Aux.FLOOKUP_eq_some.mp h3.1
    refine h2 n h4 _ ⟨?_, ?_⟩
    · rw [List.length_map]; exact h5.symm
    · rw [Aux.EVERY_iff]
      intro x hx
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
      exact ih a ha (h3.2 a ha)

/- HOL4:
Theorem typesem_Fun:
   ∀δ τ dom rng.
    is_std_type_assignment δ ⇒
    typesem δ τ (Fun dom rng) =
    Funspace (typesem δ τ dom) (typesem δ τ rng)
-/
theorem typesem_Fun [Nonempty U] (mem : U → U → Prop) :
    ∀ (δ : tyass U) (τ : tyval U) (dom rng : type),
      is_std_type_assignment0 mem δ →
      typesem δ τ (Fun dom rng) =
        funspace mem (typesem δ τ dom) (typesem δ τ rng) := by
  intro δ τ dom rng h
  rw [typesem]
  exact h.1 _ _

/- HOL4:
Theorem typesem_Bool:
   ∀δ τ.
    is_std_type_assignment δ ⇒
    typesem δ τ Bool = boolset
-/
theorem typesem_Bool [Nonempty U] (mem : U → U → Prop) :
    ∀ (δ : tyass U) (τ : tyval U),
      is_std_type_assignment0 mem δ →
      typesem δ τ BoolTy = boolset mem := by
  intro δ τ h
  rw [typesem]
  exact h.2

/- HOL4:
Theorem typesem_TYPE_SUBST:
   ∀tyin ty δ τ.
      typesem δ τ (TYPE_SUBST tyin ty) =
      typesem δ (λx. typesem δ τ (TYPE_SUBST tyin (Tyvar x))) ty
-/
theorem typesem_TYPE_SUBST :
    ∀ (tyin : List (type × type)) (ty : type) (δ : tyass U) (τ : tyval U),
      typesem δ τ (TYPE_SUBST tyin ty) =
        typesem δ (fun x => typesem δ τ (TYPE_SUBST tyin (Tyvar x))) ty := by
  intro tyin ty δ τ
  induction ty using Aux.type_ind with
  | hv v => rw [typesem]
  | ha n args ih =>
    rw [TYPE_SUBST, typesem, typesem, List.map_map]
    congr 1
    exact List.map_congr_left ih

/- HOL4:
Theorem typesem_tyvars:
   ∀δ τ ty τ'.
    (∀x. MEM x (tyvars ty) ⇒ τ' x = τ x) ⇒
    typesem δ τ' ty = typesem δ τ ty
-/
theorem typesem_tyvars :
    ∀ (δ : tyass U) (τ : tyval U) (ty : type) (τ' : tyval U),
      (∀ x, x ∈ tyvars ty → τ' x = τ x) →
      typesem δ τ' ty = typesem δ τ ty := by
  intro δ τ ty τ'
  induction ty using Aux.type_ind with
  | hv v =>
    intro h
    rw [typesem, typesem]
    exact h v (by simp [tyvars])
  | ha n args ih =>
    intro h
    rw [typesem, typesem]
    congr 1
    apply List.map_congr_left
    intro a ha
    exact ih a ha (fun x hx => h x ((Aux.mem_tyvars_Tyapp x n args).mpr ⟨a, ha, hx⟩))

theorem Aux.is_valuation_UPDATE (mem : U → U → Prop) {tysig : tysig} {δ : tyass U}
    {v : valuation U} (h : is_valuation0 mem tysig δ v) {x : mlstring} {ty : type} {m : U}
    (hm : mem m (typesem δ v.1 ty)) :
    is_valuation0 mem tysig δ (v.1, UPDATE (x, ty) m v.2) := by
  refine ⟨h.1, fun y yty hy => ?_⟩
  by_cases e : (x, ty) = (y, yty)
  · cases e
    rw [show tmvof (v.1, UPDATE (x, ty) m v.2) = UPDATE (x, ty) m v.2 from rfl, Aux.UPDATE_same]
    exact hm
  · rw [show tmvof (v.1, UPDATE (x, ty) m v.2) = UPDATE (x, ty) m v.2 from rfl,
      Aux.UPDATE_ne _ _ e]
    exact h.2 y yty hy

/- HOL4:
Theorem termsem_typesem:
   is_set_theory ^mem ⇒
    ∀sig i tm v δ τ tmenv.
      δ = FST i ∧ τ = FST v ∧
      is_valuation (tysof sig) δ v ∧
      is_interpretation sig i ∧
      is_std_type_assignment δ ∧
      term_ok sig tm ∧ tmenv = tmsof sig
      ⇒
      termsem tmenv i v tm <: typesem δ τ (typeof tm)
-/
theorem termsem_typesem [Nonempty U] (mem : U → U → Prop) :
    is_set_theory mem →
      ∀ (sig : sig) (i : interpretation U) (tm : term) (v : valuation U) (δ : tyass U)
        (τ : tyval U) (tmenv : tmsig),
        δ = i.1 ∧ τ = v.1 ∧
        is_valuation0 mem (tysof sig) δ v ∧
        is_interpretation0 mem sig i ∧
        is_std_type_assignment0 mem δ ∧
        term_ok sig tm ∧ tmenv = tmsof sig →
        mem (termsem0 mem tmenv i v tm) (typesem δ τ (typeof tm)) := by
  rintro hst sig i tm v _ _ _ ⟨rfl, rfl, hv, hi, hstd, hok, rfl⟩
  induction tm generalizing v with
  | Var x ty =>
    rw [Aux.termsem_Var]
    exact hv.2 x ty hok
  | Const name ty =>
    obtain ⟨ty0, h1, h2, tyin, rfl⟩ := hok
    rw [Aux.termsem_Const, Aux.instance_eq h1]
    simp only [typeof]
    obtain ⟨h3, h4⟩ := Aux.FLOOKUP_eq_some.mp h1
    have hτ : ∀ x, x ∈ tyvars ty0 → inhabited mem (typesem i.1 v.1 (TYPE_SUBST tyin (Tyvar x))) :=
      fun x hx => typesem_inhabited mem hst (tysof sig) i.1 v.1 _
        ⟨hv.1, hi.1, type_ok_TYPE_SUBST_imp _ _ _ h2 x hx⟩
    have key := hi.2 name h3
      (fun x => if x ∈ tyvars ty0 then typesem i.1 v.1 (TYPE_SUBST tyin (Tyvar x)) else v.1 x)
      (fun x => by
        by_cases hx : x ∈ tyvars ty0
        · simp only [hx, if_true]; exact hτ x hx
        · simp only [hx, if_false]; exact hv.1 x)
    simp only [h4] at key
    rw [typesem_TYPE_SUBST, ← typesem_tyvars i.1
      (fun x => typesem i.1 v.1 (TYPE_SUBST tyin (Tyvar x))) ty0
      (fun x => if x ∈ tyvars ty0 then typesem i.1 v.1 (TYPE_SUBST tyin (Tyvar x)) else v.1 x)
      (fun x hx => by simp only [hx, if_true])]
    have e : ((STRING_SORT ((tyvars ty0).map explode)).map implode).map
        (fun x => typesem i.1 v.1 (TYPE_SUBST tyin (Tyvar x))) =
        ((STRING_SORT ((tyvars ty0).map explode)).map implode).map
        (fun x => if x ∈ tyvars ty0 then typesem i.1 v.1 (TYPE_SUBST tyin (Tyvar x)) else v.1 x) := by
      apply List.map_congr_left
      intro x hx
      rw [Aux.mem_sorted_tyvars] at hx
      simp only [hx, if_true]
    rw [e]
    exact key
  | Comb s t ihs iht =>
    obtain ⟨h1, h2, h3⟩ := hok
    obtain ⟨_, _, rty, e⟩ := Aux.welltyped_Comb h3
    have hs := ihs v hv h1
    have ht := iht v hv h2
    rw [e, typesem_Fun mem _ _ _ _ hstd] at hs
    rw [Aux.termsem_Comb]
    simp only [typeof, e, codomain_def]
    exact apply_in_rng mem hst _ _ _ _ ⟨ht, hs⟩
  | Abs w b _ ihb =>
    obtain ⟨x, ty, rfl, h1, h2⟩ := hok
    rw [Aux.termsem_Abs]
    simp only [typeof]
    rw [typesem_Fun mem _ _ _ _ hstd]
    apply abstract_in_funspace mem hst
    intro m hm
    exact ihb (v.1, UPDATE (x, ty) m v.2) (Aux.is_valuation_UPDATE mem hv hm) h2

/- HOL4:
Theorem termsem_Equal:
   is_set_theory ^mem ⇒
    ∀Γ i v ty.
      is_structure Γ i v ∧ type_ok (tysof Γ) ty ⇒
      termsem (tmsof Γ) i v (Equal ty) = ^Equalsem [typesem (FST i) (FST v) ty]
   (`^Equalsem` is the term given in CONVENTIONS.md §8) -/
theorem termsem_Equal [Nonempty U] (mem : U → U → Prop) :
    is_set_theory mem →
      ∀ (Γ : sig) (i : interpretation U) (v : valuation U) (ty : type),
        is_structure0 mem Γ i v ∧ type_ok (tysof Γ) ty →
        termsem0 mem (tmsof Γ) i v (Equal ty) =
          (fun l => abstract mem (HD l) (funspace mem (HD l) (boolset mem))
            (fun x => abstract mem (HD l) (boolset mem) (fun y => boolean mem (x = y))))
            [typesem i.1 v.1 ty] := by
  rintro hst Γ i v ty ⟨⟨h1, h2, h3, h4⟩, h5⟩
  have hty : Fun ty (Fun ty BoolTy) = TYPE_SUBST [(ty, Tyvar (mls "A"))]
      (Fun (Tyvar (mls "A")) (Fun (Tyvar (mls "A")) BoolTy)) := by
    simp [TYPE_SUBST, REV_ASSOCD]
  rw [Aux.termsem_Const, hty, Aux.instance_eq h1.2.2]
  have hs : ((STRING_SORT ((tyvars (Fun (Tyvar (mls "A"))
      (Fun (Tyvar (mls "A")) BoolTy))).map explode)).map implode) = [mls "A"] := by
    simp [tyvars, LIST_UNION, LIST_INSERT, STRING_SORT, INORDER_INSERT, FILTER, implode_explode]
  rw [hs]
  have hA : TYPE_SUBST [(ty, Tyvar (mls "A"))] (Tyvar (mls "A")) = ty := by
    simp [TYPE_SUBST, REV_ASSOCD]
  simp only [List.map_cons, List.map_nil, hA]
  exact h2.2 (fun _ => typesem i.1 v.1 ty)
    (fun _ => typesem_inhabited mem hst (tysof Γ) i.1 v.1 ty ⟨h4.1, h3.1, h5⟩)

/- HOL4:
Theorem termsem_equation:
   is_set_theory ^mem ⇒
    ∀sig i v s t tmenv.
    is_structure sig i v ∧
    term_ok sig (s === t) ∧
    tmenv = tmsof sig
    ⇒ termsem tmenv i v (s === t) = Boolean (termsem tmenv i v s = termsem tmenv i v t)
-/
theorem termsem_equation [Nonempty U] (mem : U → U → Prop) :
    is_set_theory mem →
      ∀ (sig : sig) (i : interpretation U) (v : valuation U) (s t : term) (tmenv : tmsig),
        is_structure0 mem sig i v ∧
        term_ok sig (equation s t) ∧
        tmenv = tmsof sig →
        termsem0 mem tmenv i v (equation s t) =
          boolean mem (termsem0 mem tmenv i v s = termsem0 mem tmenv i v t) := by
  rintro hst sig i v s t _ ⟨hstr, hok, rfl⟩
  obtain ⟨h1, h2, h3, h4⟩ := id hstr
  obtain ⟨hs, ht, hty⟩ := (term_ok_equation sig s t h1).mp hok
  have ms := termsem_typesem mem hst sig i s v _ _ _ ⟨rfl, rfl, h4, h3, h2.1, hs, rfl⟩
  have mt := termsem_typesem mem hst sig i t v _ _ _ ⟨rfl, rfl, h4, h3, h2.1, ht, rfl⟩
  rw [hty] at mt
  unfold equation
  rw [Aux.termsem_Comb, Aux.termsem_Comb,
    termsem_Equal mem hst sig i v _ ⟨hstr, term_ok_type_ok sig s ⟨h1, hs⟩⟩]
  simp only [HD_def]
  rw [apply_abstract mem hst]
  · rw [apply_abstract mem hst]
    exact ⟨mt, boolean_in_boolset mem hst _⟩
  · refine ⟨ms, ?_⟩
    apply abstract_in_funspace mem hst
    intro x _
    exact boolean_in_boolset mem hst _

/- HOL4:
Theorem termsem_raconv:
   ∀env tp. RACONV env tp ⇒
      ∀Γ i v1 v2.
        (FST v1 = FST v2) ∧
        (∀x1 ty1 x2 ty2.
          ALPHAVARS env (Var x1 ty1,Var x2 ty2) ⇒
            (termsem Γ i v1 (Var x1 ty1) =
             termsem Γ i v2 (Var x2 ty2))) ∧
        EVERY (λ(x,y). welltyped x ∧ welltyped y ∧ typeof x = typeof y) env ∧
        welltyped (FST tp) ∧ welltyped (SND tp)
        ⇒
        termsem Γ i v1 (FST tp) = termsem Γ i v2 (SND tp)
-/
theorem termsem_raconv (mem : U → U → Prop) :
    ∀ (env : List (term × term)) (tp : term × term), RACONV env tp →
      ∀ (Γ : tmsig) (i : interpretation U) (v1 v2 : valuation U),
        v1.1 = v2.1 ∧
        (∀ x1 ty1 x2 ty2,
          ALPHAVARS env (Var x1 ty1, Var x2 ty2) →
            termsem0 mem Γ i v1 (Var x1 ty1) = termsem0 mem Γ i v2 (Var x2 ty2)) ∧
        EVERY (fun (x, y) => welltyped x ∧ welltyped y ∧ typeof x = typeof y) env ∧
        welltyped tp.1 ∧ welltyped tp.2 →
        termsem0 mem Γ i v1 tp.1 = termsem0 mem Γ i v2 tp.2 := by
  intro env tp h
  induction h with
  | Var ha =>
    rintro Γ i v1 v2 ⟨_, h2, _⟩
    exact h2 _ _ _ _ ha
  | Const =>
    rintro Γ i v1 v2 ⟨h1, _⟩
    simp only [Aux.termsem_Const, h1]
  | Comb _ _ ih1 ih2 =>
    rintro Γ i v1 v2 ⟨h1, h2, h3, h4, h5⟩
    obtain ⟨w1, w2, _⟩ := Aux.welltyped_Comb h4
    obtain ⟨w3, w4, _⟩ := Aux.welltyped_Comb h5
    have e1 := ih1 Γ i v1 v2 ⟨h1, h2, h3, w1, w3⟩
    have e2 := ih2 Γ i v1 v2 ⟨h1, h2, h3, w2, w4⟩
    simp only [Aux.termsem_Comb] at e1 e2 ⊢
    rw [e1, e2]
  | Abs hty hr ih =>
    rintro Γ i v1 v2 ⟨h1, h2, h3, h4, h5⟩
    obtain ⟨n1, ty1, rfl, w1⟩ := Aux.welltyped_Abs h4
    obtain ⟨n2, ty2, rfl, w2⟩ := Aux.welltyped_Abs h5
    have hty' : ty1 = ty2 := hty
    subst hty'
    have henv := And.intro (And.intro (⟨_, has_type.Var⟩ : welltyped (Var n1 ty1))
      (And.intro (⟨_, has_type.Var⟩ : welltyped (Var n2 ty1)) hty)) h3
    have e := RACONV_TYPE _ _ hr ⟨henv, w1, w2⟩
    simp only [Aux.termsem_Abs]
    rw [h1, show typeof _ = typeof _ from e]
    congr 1
    funext m
    refine ih Γ i (v2.1, UPDATE (n1, ty1) m v1.2) (v2.1, UPDATE (n2, ty1) m v2.2)
      ⟨rfl, ?_, henv, w1, w2⟩
    intro x1 t1 x2 t2 ha
    simp only [Aux.termsem_Var]
    rcases ha with ha | ⟨ha1, ha2, ha3⟩
    · cases ha
      rw [Aux.UPDATE_same, Aux.UPDATE_same]
    · rw [Aux.UPDATE_ne _ _ (fun e => ha1 (by cases e; rfl)),
        Aux.UPDATE_ne _ _ (fun e => ha2 (by cases e; rfl))]
      have := h2 x1 t1 x2 t2 ha3
      simp only [Aux.termsem_Var] at this
      exact this

/- HOL4:
Theorem termsem_aconv:
   ∀Γ i v t1 t2. ACONV t1 t2 ∧ welltyped t1 ∧ welltyped t2 ⇒ termsem Γ i v t1 = termsem Γ i v t2
-/
theorem termsem_aconv (mem : U → U → Prop) :
    ∀ (Γ : tmsig) (i : interpretation U) (v : valuation U) (t1 t2 : term),
      ACONV t1 t2 ∧ welltyped t1 ∧ welltyped t2 →
      termsem0 mem Γ i v t1 = termsem0 mem Γ i v t2 := by
  rintro Γ i v t1 t2 ⟨h1, h2, h3⟩
  refine termsem_raconv mem [] (t1, t2) h1 Γ i v v ⟨rfl, ?_, trivial, h2, h3⟩
  intro x1 ty1 x2 ty2 ha
  rw [show Var x1 ty1 = Var x2 ty2 from ha]

/- HOL4:
Theorem termsem_frees:
   ∀Γ i t v1 v2.
      welltyped t ∧ FST v1 = FST v2 ∧
      (∀x ty. VFREE_IN (Var x ty) t ⇒ SND v1 (x,ty) = SND v2 (x,ty))
      ⇒ termsem Γ i v1 t = termsem Γ i v2 t
-/
theorem termsem_frees (mem : U → U → Prop) :
    ∀ (Γ : tmsig) (i : interpretation U) (t : term) (v1 v2 : valuation U),
      welltyped t ∧ v1.1 = v2.1 ∧
      (∀ x ty, VFREE_IN (Var x ty) t → v1.2 (x, ty) = v2.2 (x, ty)) →
      termsem0 mem Γ i v1 t = termsem0 mem Γ i v2 t := by
  intro Γ i t
  induction t with
  | Var x ty =>
    rintro v1 v2 ⟨_, _, h⟩
    rw [Aux.termsem_Var, Aux.termsem_Var]
    exact h x ty rfl
  | Const x ty =>
    rintro v1 v2 ⟨_, h, _⟩
    rw [Aux.termsem_Const, Aux.termsem_Const, h]
  | Comb s t ihs iht =>
    rintro v1 v2 ⟨h1, h2, h3⟩
    obtain ⟨w1, w2, _⟩ := Aux.welltyped_Comb h1
    rw [Aux.termsem_Comb, Aux.termsem_Comb,
      ihs v1 v2 ⟨w1, h2, fun x ty h => h3 x ty (Or.inl h)⟩,
      iht v1 v2 ⟨w2, h2, fun x ty h => h3 x ty (Or.inr h)⟩]
  | Abs w b _ ihb =>
    rintro v1 v2 ⟨h1, h2, h3⟩
    obtain ⟨n, nty, rfl, w1⟩ := Aux.welltyped_Abs h1
    rw [Aux.termsem_Abs, Aux.termsem_Abs, h2]
    congr 1
    funext m
    refine ihb _ _ ⟨w1, rfl, fun x ty hf => ?_⟩
    by_cases e : (n, nty) = (x, ty)
    · cases e
      simp only [Aux.UPDATE_same]
    · simp only [Aux.UPDATE_ne _ _ e]
      exact h3 x ty ⟨fun e' => e (by cases e'; rfl), hf⟩

/-- `termsem_frees` for a valuation updated at a variable that is not free. -/
theorem Aux.termsem_UPDATE (mem : U → U → Prop) (Γ : tmsig) (i : interpretation U) (t : term)
    (v : valuation U) (x : mlstring) (ty : type) (m : U) (hw : welltyped t)
    (h : ¬ VFREE_IN (Var x ty) t) :
    termsem0 mem Γ i (v.1, UPDATE (x, ty) m v.2) t = termsem0 mem Γ i v t := by
  refine termsem_frees mem Γ i t _ _ ⟨hw, rfl, fun y yty hf => ?_⟩
  exact Aux.UPDATE_ne _ _ (fun e => h (by cases e; exact hf))

theorem Aux.upd_congr (mem : U → U → Prop) (Γ : tmsig) (i : interpretation U) (v : valuation U)
    (b : term) (n : mlstring) (nty : type) (ilist il2 : List (term × term)) (z : mlstring) (m : U)
    (hw : welltyped b)
    (hil : ∀ s s', (s', s) ∈ ilist → ∃ x ty, s = Var x ty)
    (hil2 : ∀ s s', (s', s) ∈ il2 → ∃ x ty, s = Var x ty)
    (h1 : termsem0 mem Γ i (v.1, UPDATE (z, nty) m v.2)
      (REV_ASSOCD (Var n nty) il2 (Var n nty)) = m)
    (h2 : ∀ x ty, VFREE_IN (Var x ty) b → ¬ Var x ty = Var n nty →
      REV_ASSOCD (Var x ty) il2 (Var x ty) = REV_ASSOCD (Var x ty) ilist (Var x ty) ∧
      welltyped (REV_ASSOCD (Var x ty) ilist (Var x ty)) ∧
      ¬ VFREE_IN (Var z nty) (REV_ASSOCD (Var x ty) ilist (Var x ty))) :
    termsem0 mem Γ i (v.1, Aux.upd mem Γ i (v.1, UPDATE (z, nty) m v.2) il2) b =
      termsem0 mem Γ i (v.1, UPDATE (n, nty) m (Aux.upd mem Γ i v ilist)) b := by
  refine termsem_frees mem Γ i b _ _ ⟨hw, rfl, fun x ty hf => ?_⟩
  simp only []
  rw [Aux.upd_val mem Γ i _ _ hil2]
  by_cases e : (n, nty) = (x, ty)
  · cases e
    rw [Aux.UPDATE_same]
    exact h1
  · rw [Aux.UPDATE_ne _ _ e, Aux.upd_val mem Γ i _ _ hil]
    obtain ⟨e1, e2, e3⟩ := h2 x ty hf (fun e' => e (by cases e'; rfl))
    rw [e1]
    exact Aux.termsem_UPDATE mem Γ i _ v z nty m e2 e3

theorem Aux.REV_ASSOCD_welltyped {ilist : List (term × term)}
    (h : ∀ s s', (s', s) ∈ ilist → ∃ x ty, s = Var x ty ∧ has_type s' ty) (x : mlstring)
    (ty : type) : welltyped (REV_ASSOCD (Var x ty) ilist (Var x ty)) := by
  rcases REV_ASSOCD_MEM ilist (Var x ty) (Var x ty) with hm | hm
  · obtain ⟨_, ty', _, ht⟩ := h _ _ hm
    exact ⟨ty', ht⟩
  · rw [hm]; exact ⟨_, has_type.Var⟩

theorem Aux.REV_ASSOCD_FILTER_self (v : term) (ilist : List (term × term)) :
    REV_ASSOCD v (FILTER (fun p : term × term => ¬ p.2 = v) ilist) v = v := by
  refine (REV_ASSOCD_FILTER (fun s => ¬ s = v) ilist v v ()).trans ?_
  rw [if_neg (by simp)]

/- HOL4:
Theorem termsem_simple_subst:
   ∀tm ilist.
      welltyped tm ∧
      DISJOINT (set (bv_names tm)) {y | ∃ty u. VFREE_IN (Var y ty) u ∧ MEM u (MAP FST ilist)} ∧
      (∀s s'. MEM (s',s) ilist ⇒ ∃x ty. s = Var x ty ∧ s' has_type ty)
      ⇒
      ∀Γ i v.
        termsem Γ i v (simple_subst ilist tm) =
        termsem Γ i
          (FST v, SND v =++
                  MAP ((dest_var ## termsem Γ i v) o (λ(s',s). (s,s')))
                      (REVERSE ilist))
          tm
-/
theorem termsem_simple_subst (mem : U → U → Prop) :
    ∀ (tm : term) (ilist : List (term × term)),
      welltyped tm ∧
      DISJOINT (LIST_TO_SET (bv_names tm))
        (setOf (fun y => ∃ ty u, VFREE_IN (Var y ty) u ∧ u ∈ ilist.map Prod.fst)) ∧
      (∀ s s', (s', s) ∈ ilist → ∃ x ty, s = Var x ty ∧ has_type s' ty) →
      ∀ (Γ : tmsig) (i : interpretation U) (v : valuation U),
        termsem0 mem Γ i v (simple_subst ilist tm) =
          termsem0 mem Γ i
            (v.1, UPDATE_LIST v.2
                    ((ilist.reverse).map
                      (PAIR_MAP dest_var (termsem0 mem Γ i v) ∘ (fun (s', s) => (s, s')))))
            tm := by
  intro tm
  induction tm with
  | Var x ty =>
    rintro ilist ⟨_, _, h⟩ Γ i v
    change _ = termsem0 mem Γ i (v.1, Aux.upd mem Γ i v ilist) _
    rw [Aux.termsem_Var]
    change _ = Aux.upd mem Γ i v ilist (x, ty)
    rw [Aux.upd_val mem Γ i v ilist (fun s s' hm => by
      obtain ⟨x, ty, e, _⟩ := h s s' hm
      exact ⟨x, ty, e⟩)]
    rfl
  | Const x ty =>
    rintro ilist _ Γ i v
    rw [simple_subst, Aux.termsem_Const, Aux.termsem_Const]
  | Comb s t ihs iht =>
    rintro ilist ⟨h1, h2, h3⟩ Γ i v
    obtain ⟨w1, w2, _⟩ := Aux.welltyped_Comb h1
    rw [Aux.DISJOINT_iff] at h2
    rw [simple_subst, Aux.termsem_Comb, Aux.termsem_Comb,
      ihs ilist ⟨w1, Aux.DISJOINT_iff.mpr fun x hx => h2 x ?_, h3⟩ Γ i v,
      iht ilist ⟨w2, Aux.DISJOINT_iff.mpr fun x hx => h2 x ?_, h3⟩ Γ i v]
    · rw [Aux.mem_LIST_TO_SET] at hx ⊢
      exact List.mem_append_right _ hx
    · rw [Aux.mem_LIST_TO_SET] at hx ⊢
      exact List.mem_append_left _ hx
  | Abs w b _ ihb =>
    rintro ilist ⟨h1, h2, h3⟩ Γ i v
    obtain ⟨n, nty, rfl, w1⟩ := Aux.welltyped_Abs h1
    rw [Aux.DISJOINT_iff] at h2
    have h3' : ∀ s s', (s', s) ∈ FILTER (fun p : term × term => ¬ p.2 = Var n nty) ilist →
        ∃ x ty, s = Var x ty ∧ has_type s' ty := fun s s' hm => h3 s s' (Aux.mem_FILTER.mp hm).1
    have hty : typeof (simple_subst (FILTER (fun p : term × term => ¬ p.2 = Var n nty) ilist) b) =
        typeof b := by
      apply WELLTYPED_LEMMA
      refine simple_subst_has_type b _ ((WELLTYPED b).mp w1) _ ?_
      rw [Aux.EVERY_iff]
      intro p hp
      obtain ⟨x, ty, e, ht⟩ := h3' p.2 p.1 hp
      rw [e]
      exact ht
    change _ = termsem0 mem Γ i (v.1, Aux.upd mem Γ i v ilist) _
    rw [simple_subst, Aux.termsem_Abs, Aux.termsem_Abs]
    change abstract mem _ (typesem i.1 v.1 (typeof (simple_subst
      (FILTER (fun p : term × term => ¬ p.2 = Var n nty) ilist) b))) _ = _
    rw [hty]
    congr 1
    funext m
    refine (ihb (FILTER (fun p : term × term => ¬ p.2 = Var n nty) ilist) ⟨w1, ?_, h3'⟩ Γ i
      (v.1, UPDATE (n, nty) m v.2)).trans ?_
    · refine Aux.DISJOINT_iff.mpr fun x hx hm => ?_
      obtain ⟨ty, u, hf, hu⟩ := hm
      rw [Aux.mem_LIST_TO_SET] at hx
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hu
      refine h2 x ?_ ⟨ty, p.1, hf, List.mem_map.mpr ⟨p, (Aux.mem_FILTER.mp hp).1, rfl⟩⟩
      rw [Aux.mem_LIST_TO_SET]
      exact List.mem_cons_of_mem _ hx
    · refine Aux.upd_congr mem Γ i v b n nty ilist
        (FILTER (fun p : term × term => ¬ p.2 = Var n nty) ilist) n m w1 ?_ ?_ ?_ ?_
      · intro s s' hm
        obtain ⟨x, ty, e, _⟩ := h3 s s' hm
        exact ⟨x, ty, e⟩
      · intro s s' hm
        obtain ⟨x, ty, e, _⟩ := h3' s s' hm
        exact ⟨x, ty, e⟩
      · rw [Aux.REV_ASSOCD_FILTER_self, Aux.termsem_Var]
        exact Aux.UPDATE_same _ _ _
      · intro x ty hf hne
        refine ⟨Aux.REV_ASSOCD_FILTER_ne _ _ _ _ hne, Aux.REV_ASSOCD_welltyped h3 x ty, ?_⟩
        intro hf'
        rcases REV_ASSOCD_MEM ilist (Var x ty) (Var x ty) with hm | hm
        · refine h2 n ?_ ⟨nty, _, hf', List.mem_map.mpr ⟨_, hm, rfl⟩⟩
          rw [Aux.mem_LIST_TO_SET]
          simp [bv_names, dest_var_def]
        · rw [hm] at hf'
          exact hne hf'

/- HOL4:
Theorem termsem_VSUBST:
    ∀tm ilist.
      welltyped tm ∧
      (∀s s'. MEM (s',s) ilist ⇒ ∃x ty. s = Var x ty ∧ s' has_type ty) ⇒
      ∀Γ i v.
       termsem Γ i v (VSUBST ilist tm) =
       termsem Γ i (FST v,
                    SND v =++
                    MAP ((dest_var ## termsem Γ i v) o (λ(s',s). (s,s')))
                      (REVERSE ilist)) tm
-/
theorem termsem_VSUBST (mem : U → U → Prop) :
    ∀ (tm : term) (ilist : List (term × term)),
      welltyped tm ∧
      (∀ s s', (s', s) ∈ ilist → ∃ x ty, s = Var x ty ∧ has_type s' ty) →
      ∀ (Γ : tmsig) (i : interpretation U) (v : valuation U),
        termsem0 mem Γ i v (VSUBST ilist tm) =
          termsem0 mem Γ i
            (v.1, UPDATE_LIST v.2
                    ((ilist.reverse).map
                      (PAIR_MAP dest_var (termsem0 mem Γ i v) ∘ (fun (s', s) => (s, s')))))
            tm := by
  intro tm
  induction tm with
  | Var x ty =>
    rintro ilist ⟨_, h⟩ Γ i v
    change _ = termsem0 mem Γ i (v.1, Aux.upd mem Γ i v ilist) _
    rw [Aux.termsem_Var]
    change _ = Aux.upd mem Γ i v ilist (x, ty)
    rw [Aux.upd_val mem Γ i v ilist (fun s s' hm => by
      obtain ⟨x, ty, e, _⟩ := h s s' hm
      exact ⟨x, ty, e⟩)]
    rfl
  | Const x ty =>
    rintro ilist _ Γ i v
    rw [VSUBST, Aux.termsem_Const, Aux.termsem_Const]
  | Comb s t ihs iht =>
    rintro ilist ⟨h1, h3⟩ Γ i v
    obtain ⟨w1, w2, _⟩ := Aux.welltyped_Comb h1
    rw [VSUBST, Aux.termsem_Comb, Aux.termsem_Comb, ihs ilist ⟨w1, h3⟩ Γ i v,
      iht ilist ⟨w2, h3⟩ Γ i v]
  | Abs w b _ ihb =>
    rintro ilist ⟨h1, h3⟩ Γ i v
    obtain ⟨n, nty, rfl, w1⟩ := Aux.welltyped_Abs h1
    have hb := (WELLTYPED b).mp w1
    have h3' : ∀ s s', (s', s) ∈ FILTER (fun p : term × term => ¬ p.2 = Var n nty) ilist →
        ∃ x ty, s = Var x ty ∧ has_type s' ty := fun s s' hm => h3 s s' (Aux.mem_FILTER.mp hm).1
    have k1 : ∀ s s', (s', s) ∈ ilist → ∃ x ty, s = Var x ty := by
      intro s s' hm
      obtain ⟨x, ty, e, _⟩ := h3 s s' hm
      exact ⟨x, ty, e⟩
    change _ = termsem0 mem Γ i (v.1, Aux.upd mem Γ i v ilist) _
    simp only [VSUBST, dest_var_def]
    split
    · have hvar := VARIANT_THM (VSUBST (FILTER (fun p : term × term => ¬ p.2 = Var n nty) ilist) b)
        (explode n) nty
      generalize VARIANT (VSUBST (FILTER (fun p : term × term => ¬ p.2 = Var n nty) ilist) b)
        (explode n) nty = z at hvar ⊢
      have h4 : ∀ s s', (s', s) ∈ (Var z nty, Var n nty) ::
          FILTER (fun p : term × term => ¬ p.2 = Var n nty) ilist →
          ∃ x ty, s = Var x ty ∧ has_type s' ty := by
        intro s s' hm
        rcases List.mem_cons.mp hm with hm | hm
        · cases hm; exact ⟨n, nty, rfl, has_type.Var⟩
        · exact h3' s s' hm
      rw [Aux.termsem_Abs, Aux.termsem_Abs, WELLTYPED_LEMMA _ _ (VSUBST_HAS_TYPE b _ _ ⟨hb, h4⟩)]
      congr 1
      funext m
      refine (ihb _ ⟨w1, h4⟩ Γ i (v.1, UPDATE (z, nty) m v.2)).trans ?_
      refine Aux.upd_congr mem Γ i v b n nty ilist _ z m w1 k1 ?_ ?_ ?_
      · intro s s' hm
        obtain ⟨x, ty, e, _⟩ := h4 s s' hm
        exact ⟨x, ty, e⟩
      · simp only [REV_ASSOCD, if_true]
        rw [Aux.termsem_Var]
        exact Aux.UPDATE_same _ _ _
      · intro x ty hf hne
        have hne' : ¬ Var n nty = Var x ty := fun e => hne e.symm
        simp only [REV_ASSOCD, hne', if_false]
        refine ⟨Aux.REV_ASSOCD_FILTER_ne _ _ _ _ hne, Aux.REV_ASSOCD_welltyped h3 x ty, ?_⟩
        intro hf'
        refine hvar ((VFREE_IN_VSUBST b _ _ _ w1).mpr ⟨x, ty, hf, ?_⟩)
        rw [Aux.REV_ASSOCD_FILTER_ne _ _ _ _ hne]
        exact hf'
    · rename_i hc
      rw [Aux.EXISTS_iff] at hc
      rw [Aux.termsem_Abs, Aux.termsem_Abs, WELLTYPED_LEMMA _ _ (VSUBST_HAS_TYPE b _ _ ⟨hb, h3'⟩)]
      congr 1
      funext m
      refine (ihb _ ⟨w1, h3'⟩ Γ i (v.1, UPDATE (n, nty) m v.2)).trans ?_
      refine Aux.upd_congr mem Γ i v b n nty ilist _ n m w1 k1 ?_ ?_ ?_
      · intro s s' hm
        obtain ⟨x, ty, e, _⟩ := h3' s s' hm
        exact ⟨x, ty, e⟩
      · rw [Aux.REV_ASSOCD_FILTER_self, Aux.termsem_Var]
        exact Aux.UPDATE_same _ _ _
      · intro x ty hf hne
        refine ⟨Aux.REV_ASSOCD_FILTER_ne _ _ _ _ hne, Aux.REV_ASSOCD_welltyped h3 x ty, ?_⟩
        intro hf'
        rcases REV_ASSOCD_MEM ilist (Var x ty) (Var x ty) with hm | hm
        · exact hc ⟨_, Aux.mem_FILTER.mpr ⟨hm, hne⟩, hf', hf⟩
        · rw [hm] at hf'
          exact hne hf'

/-- the valuation used in `termsem_INST` -/
noncomputable def Aux.ival (i : interpretation U) (tyin : List (type × type)) (v : valuation U) :
    valuation U :=
  ((fun x => typesem i.1 v.1 (TYPE_SUBST tyin (Tyvar x))),
   (fun (x, ty) => v.2 (x, TYPE_SUBST tyin ty)))

theorem Aux.termsem_simple_inst (mem : U → U → Prop) (Γ : sig) (tyin : List (type × type))
    (i : interpretation U) : ∀ (tm : term) (v : valuation U), term_ok Γ tm → (bv_names tm).Nodup →
      (∀ x, x ∈ bv_names tm → ∀ ty, ¬ VFREE_IN (Var x ty) tm) →
      termsem0 mem (tmsof Γ) i v (simple_inst tyin tm) =
        termsem0 mem (tmsof Γ) i (Aux.ival i tyin v) tm := by
  intro tm
  induction tm with
  | Var x ty =>
    intro v _ _ _
    rw [simple_inst, Aux.termsem_Var, Aux.termsem_Var]
    rfl
  | Const x ty =>
    intro v hok _ _
    obtain ⟨ty0, h1, _, i0, rfl⟩ := hok
    rw [simple_inst, Aux.termsem_Const, Aux.termsem_Const, TYPE_SUBST_compose,
      Aux.instance_eq h1, Aux.instance_eq h1]
    refine congrArg _ (List.map_congr_left ?_)
    intro a _
    rw [← TYPE_SUBST_compose]
    exact typesem_TYPE_SUBST tyin _ i.1 v.1
  | Comb s t ihs iht =>
    intro v hok h1 h2
    obtain ⟨o1, o2, _⟩ := hok
    simp only [bv_names] at h1 h2
    rw [simple_inst, Aux.termsem_Comb, Aux.termsem_Comb,
      ihs v o1 (List.Nodup.sublist (List.sublist_append_left _ _) h1)
        (fun x hx ty hf => h2 x (List.mem_append_left _ hx) ty (Or.inl hf)),
      iht v o2 (List.Nodup.sublist (List.sublist_append_right _ _) h1)
        (fun x hx ty hf => h2 x (List.mem_append_right _ hx) ty (Or.inr hf))]
  | Abs w b _ ihb =>
    intro v hok h1 h2
    obtain ⟨n, nty, rfl, _, o1⟩ := hok
    have w1 := term_ok_welltyped _ _ o1
    simp only [bv_names, dest_var_def] at h1 h2
    rw [List.nodup_cons] at h1
    rw [simple_inst, simple_inst, Aux.termsem_Abs, Aux.termsem_Abs,
      WELLTYPED_LEMMA _ _ (simple_inst_has_type b tyin w1), typesem_TYPE_SUBST,
      typesem_TYPE_SUBST tyin (typeof b)]
    change abstract mem (typesem i.1 (Aux.ival i tyin v).1 nty)
      (typesem i.1 (Aux.ival i tyin v).1 (typeof b)) _ = _
    congr 1
    funext m
    refine (ihb (v.1, UPDATE (n, TYPE_SUBST tyin nty) m v.2) o1 h1.2 ?_).trans ?_
    · intro x hx ty hf
      refine h2 x (List.mem_cons_of_mem _ hx) ty ⟨fun e => ?_, hf⟩
      injection e with e _
      subst e
      exact h1.1 hx
    · refine termsem_frees mem _ i b _ _ ⟨w1, rfl, fun x ty hf => ?_⟩
      change UPDATE (n, TYPE_SUBST tyin nty) m v.2 (x, TYPE_SUBST tyin ty) =
        UPDATE (n, nty) m (Aux.ival i tyin v).2 (x, ty)
      by_cases e : (n, nty) = (x, ty)
      · cases e
        rw [Aux.UPDATE_same, Aux.UPDATE_same]
      · by_cases hx : n = x
        · subst hx
          exact absurd ⟨fun e' => e (by cases e'; rfl), hf⟩ (h2 n List.mem_cons_self ty)
        · rw [Aux.UPDATE_ne _ _ e, Aux.UPDATE_ne _ _ (fun e' => hx (congrArg Prod.fst e'))]
          rfl

/- HOL4:
Theorem termsem_simple_inst:
   ∀Γ tm tyin tmenv.
      welltyped tm ∧ term_ok Γ tm ∧
      ALL_DISTINCT (bv_names tm) ∧
      DISJOINT (set (bv_names tm)) {x | ∃ty. VFREE_IN (Var x ty) tm} ∧
      tmenv = tmsof Γ
      ⇒
      ∀i v.
        termsem tmenv i v (simple_inst tyin tm) =
        termsem tmenv i
          ((λx. typesem (FST i) (FST v) (TYPE_SUBST tyin (Tyvar x))),
           (λ(x,ty). SND v (x, TYPE_SUBST tyin ty)))
          tm
-/
theorem termsem_simple_inst (mem : U → U → Prop) :
    ∀ (Γ : sig) (tm : term) (tyin : List (type × type)) (tmenv : tmsig),
      welltyped tm ∧ term_ok Γ tm ∧
      ALL_DISTINCT (bv_names tm) ∧
      DISJOINT (LIST_TO_SET (bv_names tm)) (setOf (fun x => ∃ ty, VFREE_IN (Var x ty) tm)) ∧
      tmenv = tmsof Γ →
      ∀ (i : interpretation U) (v : valuation U),
        termsem0 mem tmenv i v (simple_inst tyin tm) =
          termsem0 mem tmenv i
            ((fun x => typesem i.1 v.1 (TYPE_SUBST tyin (Tyvar x))),
             (fun (x, ty) => v.2 (x, TYPE_SUBST tyin ty)))
            tm := by
  rintro Γ tm tyin _ ⟨_, h1, h2, h3, rfl⟩ i v
  rw [Aux.DISJOINT_iff] at h3
  exact Aux.termsem_simple_inst mem Γ tyin i tm v h1 (Aux.ALL_DISTINCT_iff.mp h2)
    (fun x hx ty hf => h3 x (Aux.mem_LIST_TO_SET.mpr hx) ⟨ty, hf⟩)

/-- every well-typed term has an alpha-variant with distinct, fresh bound names -/
theorem Aux.rename_exists (tm : term) (hw : welltyped tm) :
    ∃ tm', ACONV tm tm' ∧ welltyped tm' ∧ (bv_names tm').Nodup ∧
      (∀ x, x ∈ bv_names tm' → ∀ ty, ¬ VFREE_IN (Var x ty) tm') := by
  obtain ⟨l, hl⟩ := Aux.VFREE_IN_bound tm
  have hfin : FINITE (setOf (fun s : string => implode s ∈ bv_names tm ∨
      ∃ ty, VFREE_IN (Var (implode s) ty) tm)) := by
    refine Aux.FINITE_iff.mpr
      ⟨(bv_names tm).map explode ++ l.map (fun t => explode (dest_var t).1), fun s hs => ?_⟩
    rcases hs with h | ⟨ty, h⟩
    · exact List.mem_append_left _ (List.mem_map.mpr ⟨_, h, explode_thm s⟩)
    · refine List.mem_append_right _ (List.mem_map.mpr ⟨_, hl _ h, ?_⟩)
      rw [dest_var_def]
      exact explode_thm s
  obtain ⟨names, h1, h2, h3⟩ := fresh_names_exist _ (bv_names tm).length hfin
  rw [Aux.DISJOINT_iff] at h3
  have hd := ALL_DISTINCT_MAP_implode names h2
  have hlen : (bv_names tm).length ≤ (names.map implode).length := by
    rw [List.length_map, h1]; exact Nat.le_refl _
  have hac := rename_bvars_ACONV (names.map implode) tm ⟨hlen, hd, by
    refine Aux.DISJOINT_iff.mpr fun x hx hm => ?_
    rw [Aux.mem_LIST_TO_SET] at hx
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hx
    exact h3 s (Aux.mem_LIST_TO_SET.mpr hs) hm, hw⟩
  have hbv := Aux.bv_names_rename_bvars tm (names.map implode) [] hlen
  refine ⟨_, hac, rename_bvars_welltyped _ [] tm hw, ?_, ?_⟩
  · rw [hbv]
    exact List.Nodup.sublist (List.take_sublist _ _) (Aux.ALL_DISTINCT_iff.mp hd)
  · intro x hx ty hf
    rw [hbv] at hx
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp (List.mem_of_mem_take hx)
    exact h3 s (Aux.mem_LIST_TO_SET.mpr hs)
      (Or.inr ⟨ty, (VFREE_IN_ACONV _ _ _ _ hac).mpr hf⟩)

/- HOL4:
Theorem termsem_INST:
   ∀Γ tm tyin tmenv.
      term_ok Γ tm ∧ tmenv = tmsof Γ ⇒
      ∀i v.
        termsem tmenv i v (INST tyin tm) =
        termsem tmenv i
          ((λx. typesem (FST i) (FST v) (TYPE_SUBST tyin (Tyvar x))),
           (λ(x,ty). SND v (x, TYPE_SUBST tyin ty)))
          tm
-/
theorem termsem_INST (mem : U → U → Prop) :
    ∀ (Γ : sig) (tm : term) (tyin : List (type × type)) (tmenv : tmsig),
      term_ok Γ tm ∧ tmenv = tmsof Γ →
      ∀ (i : interpretation U) (v : valuation U),
        termsem0 mem tmenv i v (INST tyin tm) =
          termsem0 mem tmenv i
            ((fun x => typesem i.1 v.1 (TYPE_SUBST tyin (Tyvar x))),
             (fun (x, ty) => v.2 (x, TYPE_SUBST tyin ty)))
            tm := by
  rintro Γ tm tyin _ ⟨hok, rfl⟩ i v
  have hw := term_ok_welltyped _ _ hok
  obtain ⟨tm', hac, hw', hd, hf⟩ := Aux.rename_exists tm hw
  have hdis : DISJOINT (LIST_TO_SET (bv_names tm')) (setOf (fun x => ∃ ty, VFREE_IN (Var x ty) tm')) :=
    Aux.DISJOINT_iff.mpr fun x hx ⟨ty, h⟩ => hf x (Aux.mem_LIST_TO_SET.mp hx) ty h
  change _ = termsem0 mem (tmsof Γ) i (Aux.ival i tyin v) tm
  rw [termsem_aconv mem _ i v _ _ ⟨ACONV_INST tm tm' tyin ⟨hw, hw', hac⟩, INST_WELLTYPED _ _ hw,
    INST_WELLTYPED _ _ hw'⟩,
    INST_simple_inst tyin tm' ⟨Aux.ALL_DISTINCT_iff.mpr hd, hdis, hw'⟩,
    Aux.termsem_simple_inst mem Γ tyin i tm' v (term_ok_aconv Γ tm tm' ⟨hac, hok, hw'⟩) hd hf,
    termsem_aconv mem _ i _ tm tm' ⟨hac, hw, hw'⟩]

end

end Candle
