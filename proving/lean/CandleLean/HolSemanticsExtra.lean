import CandleLean.HolSemantics
import CandleLean.HolSyntaxExtra2

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

/-! Auxiliary lemmas (namespace `Candle.Aux`). -/

theorem Aux.FLOOKUP_some {α : Type u} {β : Type u} [Nonempty β] {f : fmap α β} {x : α} {y : β}
    (h : FLOOKUP f x = some y) : x ∈ FDOM f ∧ FAPPLY f x = y := by
  unfold FLOOKUP at h
  by_cases hx : x ∈ FDOM f
  · rw [if_pos hx] at h
    exact ⟨hx, Option.some.inj h⟩
  · rw [if_neg hx] at h; cases h

theorem Aux.mem_sorted_tyvars (x : mlstring) (ty : type) :
    x ∈ (STRING_SORT ((tyvars ty).map explode)).map implode ↔ x ∈ tyvars ty := by
  constructor
  · intro h
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp h
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp ((Aux.mem_STRING_SORT_iff _ _).mp hs)
    rw [implode_explode]; exact hy
  · intro h
    refine List.mem_map.mpr ⟨explode x, (Aux.mem_STRING_SORT_iff _ _).mpr ?_, implode_explode x⟩
    exact List.mem_map.mpr ⟨x, h, rfl⟩

theorem Aux.termsem_Var (mem : U → U → Prop) (Γ : tmsig) (i : interpretation U) (v : valuation U)
    (x : mlstring) (ty : type) : termsem0 mem Γ i v (Var x ty) = v.2 (x, ty) :=
  (termsem0_def mem Γ i).1 v x ty

theorem Aux.termsem_Const (mem : U → U → Prop) (Γ : tmsig) (i : interpretation U) (v : valuation U)
    (x : mlstring) (ty : type) : termsem0 mem Γ i v (Const x ty) = instance_ Γ i x ty v.1 :=
  (termsem0_def mem Γ i).2.1 v x ty

theorem Aux.termsem_Comb (mem : U → U → Prop) (Γ : tmsig) (i : interpretation U) (v : valuation U)
    (s t : term) : termsem0 mem Γ i v (Comb s t) =
      apply mem (termsem0 mem Γ i v s) (termsem0 mem Γ i v t) :=
  (termsem0_def mem Γ i).2.2.1 v s t

theorem Aux.termsem_Abs (mem : U → U → Prop) (Γ : tmsig) (i : interpretation U) (v : valuation U)
    (x : mlstring) (ty : type) (b : term) : termsem0 mem Γ i v (Abs (Var x ty) b) =
      abstract mem (typesem i.1 v.1 ty) (typesem i.1 v.1 (typeof b))
        (fun m => termsem0 mem Γ i (v.1, UPDATE (x, ty) m v.2) b) :=
  (termsem0_def mem Γ i).2.2.2 v x ty b

theorem Aux.UPDATE_eq {α : Type u} {β : Type v} (a : α) (b : β) (f : α → β) :
    UPDATE a b f a = b := if_pos rfl

theorem Aux.UPDATE_ne {α : Type u} {β : Type v} {a c : α} (b : β) (f : α → β) (h : a ≠ c) :
    UPDATE a b f c = f c := if_neg h

theorem Aux.is_valuation_update {mem : U → U → Prop} {tysig : tysig} {δ : tyass U} {v : valuation U}
    {x : mlstring} {ty : type} {m : U} (hv : is_valuation0 mem tysig δ v)
    (hm : mem m (typesem δ v.1 ty)) :
    is_valuation0 mem tysig δ (v.1, UPDATE (x, ty) m v.2) := by
  refine ⟨hv.1, fun y uy hok => ?_⟩
  show mem (UPDATE (x, ty) m v.2 (y, uy)) (typesem δ v.1 uy)
  by_cases e : (x, ty) = (y, uy)
  · cases e; rw [Aux.UPDATE_eq]; exact hm
  · rw [Aux.UPDATE_ne _ _ e]; exact hv.2 y uy hok

/-- Existence of an alpha-equivalent term with fresh distinct bound variable names
(HOL4 `fresh_term_def`). -/
theorem Aux.fresh_term (s : Set mlstring) (tm : term) (hs : FINITE s) (hw : welltyped tm) :
    ∃ fm, welltyped fm ∧ ACONV tm fm ∧ ALL_DISTINCT (bv_names fm) ∧
      DISJOINT (LIST_TO_SET (bv_names fm)) s := by
  obtain ⟨l1, h1⟩ := Aux.FINITE_list_bound s hs
  obtain ⟨l2, h2⟩ := Aux.FINITE_list_bound _ (FINITE_VFREE_IN tm)
  obtain ⟨names, hl, hd, hj⟩ := fresh_names_exist
    (LIST_TO_SET ((l1 ++ (l2 ++ bv_names tm)).map explode)) (bv_names tm).length
    (Aux.FINITE_LIST_TO_SET _)
  rw [Aux.DISJOINT_iff] at hj
  have hfr : ∀ x, x ∈ names.map implode → ¬ x ∈ l1 ++ (l2 ++ bv_names tm) := by
    intro x hx hm
    obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hx
    refine hj n ((Aux.mem_LIST_TO_SET _ _).mpr hn) ((Aux.mem_LIST_TO_SET _ _).mpr ?_)
    exact List.mem_map.mpr ⟨_, hm, explode_thm n⟩
  have hlen : (bv_names tm).length ≤ (names.map implode).length := by
    rw [List.length_map, hl]; exact Nat.le_refl _
  have hbv : bv_names (rename_bvars (names.map implode) [] tm).2 = names.map implode := by
    rw [bv_names_rename_bvars _ _ _ hlen]
    apply List.take_of_length_le
    rw [List.length_map, hl]; exact Nat.le_refl _
  refine ⟨(rename_bvars (names.map implode) [] tm).2, rename_bvars_welltyped _ _ _ hw,
    rename_bvars_ACONV _ _ ⟨hlen, ALL_DISTINCT_MAP_implode _ hd, ?_, hw⟩, ?_, ?_⟩
  · rw [Aux.DISJOINT_iff]
    rintro x hx (hm | hm)
    · exact hfr x ((Aux.mem_LIST_TO_SET _ _).mp hx)
        (List.mem_append_right _ (List.mem_append_right _ hm))
    · exact hfr x ((Aux.mem_LIST_TO_SET _ _).mp hx)
        (List.mem_append_right _ (List.mem_append_left _ (h2 x hm)))
  · rw [hbv]; exact ALL_DISTINCT_MAP_implode _ hd
  · rw [hbv, Aux.DISJOINT_iff]
    intro x hx hm
    exact hfr x ((Aux.mem_LIST_TO_SET _ _).mp hx) (List.mem_append_left _ (h1 x hm))

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
  | h1 v => rw [typesem]; exact h1 v
  | h2 n tys ih =>
    rw [type_ok, Aux.EVERY_iff] at h3
    obtain ⟨hd, hf⟩ := Aux.FLOOKUP_some h3.1
    rw [typesem]
    refine h2 n hd _ ⟨?_, ?_⟩
    · rw [List.length_map]; exact hf.symm
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
  | h1 v => rw [typesem.eq_1]
  | h2 n tys ih =>
    rw [TYPE_SUBST.eq_2, typesem.eq_2, typesem.eq_2, List.map_map]
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
  | h1 v =>
    intro h
    rw [typesem.eq_1, typesem.eq_1]
    exact h v (by simp [tyvars])
  | h2 n tys ih =>
    intro h
    rw [typesem.eq_2, typesem.eq_2]
    congr 1
    apply List.map_congr_left
    intro a ha
    exact ih a ha (fun x hx => h x ((Aux.mem_tyvars_Tyapp x n tys).mpr ⟨a, ha, hx⟩))

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
  rintro hm sig i tm v δ τ tmenv ⟨rfl, rfl, hv, hi, hs, hok, rfl⟩
  induction tm generalizing v with
  | Var x ty => rw [Aux.termsem_Var]; exact hv.2 x ty hok
  | Const name ty =>
    rw [Aux.termsem_Const]
    obtain ⟨ty0, hf, htok, tyin, rfl⟩ := hok
    have hinst := instance_def (tmsof sig) i name (TYPE_SUBST tyin ty0) ty0 tyin ⟨hf, rfl⟩
    rw [hinst]
    show mem _ (typesem i.1 v.1 (TYPE_SUBST tyin ty0))
    rw [typesem_TYPE_SUBST]
    obtain ⟨hd, hfa⟩ := Aux.FLOOKUP_some hf
    have hta := hi.2 name hd
    simp only [hfa] at hta
    have h := hta (fun x => if x ∈ tyvars ty0 then typesem i.1 v.1 (TYPE_SUBST tyin (Tyvar x))
      else boolset mem) (by
        intro x
        by_cases hx : x ∈ tyvars ty0
        · simp only [hx, if_true]
          exact typesem_inhabited mem hm (tysof sig) i.1 v.1 _
            ⟨hv.1, hi.1, type_ok_TYPE_SUBST_imp _ tyin ty0 htok x hx⟩
        · simp only [hx, if_false]
          exact ⟨_, boolean_in_boolset mem hm True⟩)
    rw [typesem_tyvars i.1 (fun x => typesem i.1 v.1 (TYPE_SUBST tyin (Tyvar x))) ty0 _
      (fun x hx => by simp only [hx, if_true])] at h
    have e : ((STRING_SORT ((tyvars ty0).map explode)).map implode).map
        (typesem (tyaof i) v.1 ∘ TYPE_SUBST tyin ∘ Tyvar) =
        ((STRING_SORT ((tyvars ty0).map explode)).map implode).map
        (fun x => if x ∈ tyvars ty0 then typesem i.1 v.1 (TYPE_SUBST tyin (Tyvar x))
          else boolset mem) := by
      apply List.map_congr_left
      intro x hx
      have hx' := (Aux.mem_sorted_tyvars x ty0).mp hx
      simp only [hx', if_true]
      rfl
    simp only [e]
    exact h
  | Comb s t ihs iht =>
    obtain ⟨h1, h2, h3⟩ := hok
    obtain ⟨_, _, rty, e⟩ := Aux.welltyped_Comb.mp h3
    rw [Aux.termsem_Comb]
    have hfs := ihs v hv h1
    rw [e, typesem_Fun mem i.1 v.1 _ _ hs] at hfs
    have e2 : typeof (Comb s t) = rty := by rw [typeof, e]; rfl
    rw [e2]
    exact apply_in_rng mem hm _ _ _ _ ⟨iht v hv h2, hfs⟩
  | Abs w b _ ihb =>
    obtain ⟨x, ty, rfl, h1, h2⟩ := hok
    rw [Aux.termsem_Abs]
    have e : typeof (Abs (Var x ty) b) = Fun ty (typeof b) := rfl
    rw [e, typesem_Fun mem i.1 v.1 _ _ hs]
    apply abstract_in_funspace mem hm
    intro m hmm
    exact ihb (v.1, UPDATE (x, ty) m v.2) (Aux.is_valuation_update hv hmm) h2

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
  rintro hm Γ i v ty ⟨⟨hsig, hstd, hint, hval⟩, hty⟩
  rw [Aux.termsem_Const]
  have hts : Fun ty (Fun ty BoolTy) = TYPE_SUBST [(ty, Tyvar (mls "A"))]
      (Fun (Tyvar (mls "A")) (Fun (Tyvar (mls "A")) BoolTy)) := by
    rw [Aux.TYPE_SUBST_Fun, Aux.TYPE_SUBST_Fun, TYPE_SUBST_Bool, TYPE_SUBST]
    simp [REV_ASSOCD]
  have hinst := instance_def (tmsof Γ) i (mls "=") _ _ [(ty, Tyvar (mls "A"))] ⟨hsig.2.2, hts⟩
  rw [hinst]
  have hvars : (STRING_SORT ((tyvars (Fun (Tyvar (mls "A")) (Fun (Tyvar (mls "A")) BoolTy))).map
      explode)).map implode = [mls "A"] := by
    have e1 : tyvars (Fun (Tyvar (mls "A")) (Fun (Tyvar (mls "A")) BoolTy)) = [mls "A"] := by
      simp [tyvars, LIST_UNION, LIST_INSERT]
    rw [e1]
    simp [STRING_SORT, INORDER_INSERT, FILTER, implode_explode]
  rw [hvars]
  have hA : TYPE_SUBST [(ty, Tyvar (mls "A"))] (Tyvar (mls "A")) = ty := by
    simp [TYPE_SUBST, REV_ASSOCD]
  have hτ : is_type_valuation0 mem
      (typesem (tyaof i) v.1 ∘ TYPE_SUBST [(ty, Tyvar (mls "A"))] ∘ Tyvar) := by
    intro x
    refine typesem_inhabited mem hm (tysof Γ) i.1 v.1 _ ⟨hval.1, hint.1, ?_⟩
    apply type_ok_TYPE_SUBST
    refine ⟨by rw [type_ok]; trivial, ?_⟩
    exact ⟨hty, trivial⟩
  have h := hstd.2 _ hτ
  have hl : [mls "A"].map (typesem (tyaof i) v.1 ∘ TYPE_SUBST [(ty, Tyvar (mls "A"))] ∘ Tyvar) =
      [typesem i.1 v.1 ty] := by
    simp only [List.map_cons, List.map_nil, Function.comp, hA]
  rw [hl] at h
  show tmaof i (mls "=") ([mls "A"].map _) = _
  rw [hl]
  exact h

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
  rintro hm sig i v s t tmenv ⟨hst, hok, rfl⟩
  have hsig := hst.1
  have hint := hst.2.2.1
  have hval := hst.2.2.2
  have hta := is_std_interpretation_is_type mem i hst.2.1
  obtain ⟨h1, h2, h3⟩ := (term_ok_equation sig s t hsig).mp hok
  have hty := term_ok_type_ok sig s ⟨hsig, h1⟩
  have m1 := termsem_typesem mem hm sig i s v i.1 v.1 (tmsof sig) ⟨rfl, rfl, hval, hint, hta, h1, rfl⟩
  have m2 := termsem_typesem mem hm sig i t v i.1 v.1 (tmsof sig) ⟨rfl, rfl, hval, hint, hta, h2, rfl⟩
  rw [h3] at m2
  rw [equation, Aux.termsem_Comb, Aux.termsem_Comb, termsem_Equal mem hm sig i v _ ⟨hst, hty⟩]
  simp only [HD_def]
  rw [apply_abstract mem hm
    (fun x => abstract mem (typesem i.1 v.1 (typeof s)) (boolset mem) (fun y => boolean mem (x = y)))
    _ _ _ ⟨m1, abstract_in_funspace mem hm _ _ _ (fun y _ => boolean_in_boolset mem hm _)⟩]
  exact apply_abstract mem hm (fun y => boolean mem (termsem0 mem (tmsof sig) i v s = y)) _ _ _
    ⟨m2, boolean_in_boolset mem hm _⟩

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
  | Var ha => rintro Γ i v1 v2 ⟨_, hv, _⟩; exact hv _ _ _ _ ha
  | Const =>
    rintro Γ i v1 v2 ⟨he, _⟩
    simp only [Aux.termsem_Const, he]
  | Comb _ _ ih1 ih2 =>
    rintro Γ i v1 v2 ⟨he, hv, hE, w1, w2⟩
    obtain ⟨wa, wb, _⟩ := Aux.welltyped_Comb.mp w1
    obtain ⟨wc, wd, _⟩ := Aux.welltyped_Comb.mp w2
    simp only [Aux.termsem_Comb]
    rw [ih1 Γ i v1 v2 ⟨he, hv, hE, wa, wc⟩, ih2 Γ i v1 v2 ⟨he, hv, hE, wb, wd⟩]
  | Abs e hr ih =>
    rintro Γ i v1 v2 ⟨he, hv, hE, w1, w2⟩
    obtain ⟨x, tx, rfl, wb⟩ := Aux.welltyped_Abs.mp w1
    obtain ⟨y, ty, rfl, wd⟩ := Aux.welltyped_Abs.mp w2
    have e' : tx = ty := e
    subst e'
    have ht := RACONV_TYPE _ _ hr ⟨⟨⟨Aux.welltyped_Var, Aux.welltyped_Var, e⟩, hE⟩, wb, wd⟩
    simp only at ht
    simp only [Aux.termsem_Abs]
    rw [he, ht]
    congr 1
    funext m
    refine ih Γ i (v2.1, UPDATE (x, tx) m v1.2) (v2.1, UPDATE (y, tx) m v2.2) ⟨rfl, ?_,
      ⟨⟨Aux.welltyped_Var, Aux.welltyped_Var, e⟩, hE⟩, wb, wd⟩
    intro x1 ty1 x2 ty2 ha
    simp only [Aux.termsem_Var]
    simp only [ALPHAVARS, Prod.mk.injEq] at ha
    rcases ha with ⟨h1, h2⟩ | ⟨h1, h2, h3⟩
    · obtain ⟨rfl, rfl⟩ := term.Var.inj h1
      obtain ⟨rfl, _⟩ := term.Var.inj h2
      rw [Aux.UPDATE_eq]
      cases h2
      rw [Aux.UPDATE_eq]
    · rw [Aux.UPDATE_ne _ _ (fun e => h1 (by cases e; rfl)),
        Aux.UPDATE_ne _ _ (fun e => h2 (by cases e; rfl))]
      have := hv _ _ _ _ h3
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
  rintro Γ i v t1 t2 ⟨h, w1, w2⟩
  refine termsem_raconv mem [] (t1, t2) h Γ i v v ⟨rfl, ?_, trivial, w1, w2⟩
  intro x1 ty1 x2 ty2 ha
  have ha' : Var x1 ty1 = Var x2 ty2 := ha
  rw [ha']

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
    rintro v1 v2 ⟨_, _, hf⟩
    simp only [Aux.termsem_Var]
    exact hf x ty rfl
  | Const x ty =>
    rintro v1 v2 ⟨_, he, _⟩
    simp only [Aux.termsem_Const, he]
  | Comb a b iha ihb =>
    rintro v1 v2 ⟨hw, he, hf⟩
    obtain ⟨wa, wb, _⟩ := Aux.welltyped_Comb.mp hw
    simp only [Aux.termsem_Comb]
    rw [iha v1 v2 ⟨wa, he, fun x ty h => hf x ty (Or.inl h)⟩,
      ihb v1 v2 ⟨wb, he, fun x ty h => hf x ty (Or.inr h)⟩]
  | Abs v b _ ihb =>
    rintro v1 v2 ⟨hw, he, hf⟩
    obtain ⟨x, ty, rfl, wb⟩ := Aux.welltyped_Abs.mp hw
    simp only [Aux.termsem_Abs, he]
    congr 1
    funext m
    refine ihb _ _ ⟨wb, rfl, fun y uy h => ?_⟩
    simp only [UPDATE]
    by_cases e : (x, ty) = (y, uy)
    · rw [if_pos e, if_pos e]
    · rw [if_neg e, if_neg e]
      refine hf y uy ⟨fun e2 => e ?_, h⟩
      cases e2; rfl

theorem Aux.UPDATE_LIST_ilist (mem : U → U → Prop) (Γ : tmsig) (i : interpretation U) (v : valuation U)
    (x : mlstring) (ty : type) (ilist : List (term × term))
    (hi : ∀ s s', (s', s) ∈ ilist → ∃ x ty, s = Var x ty) :
    UPDATE_LIST v.2 ((ilist.reverse).map
      (PAIR_MAP dest_var (termsem0 mem Γ i v) ∘ (fun (s', s) => (s, s')))) (x, ty) =
      termsem0 mem Γ i v (REV_ASSOCD (Var x ty) ilist (Var x ty)) := by
  rw [APPLY_UPDATE_LIST_ALOOKUP, ← List.map_reverse, List.reverse_reverse]
  induction ilist with
  | nil => simp only [List.map_nil, ALOOKUP, REV_ASSOCD, Aux.termsem_Var]
  | cons p t ih =>
    obtain ⟨s', s⟩ := p
    obtain ⟨y, uy, rfl⟩ := hi s s' List.mem_cons_self
    simp only [List.map_cons, Function.comp, PAIR_MAP, dest_var_def, ALOOKUP, REV_ASSOCD]
    by_cases e : (y, uy) = (x, ty)
    · cases e; simp
    · have e2 : ¬ Var y uy = Var x ty := fun h => e (by cases h; rfl)
      rw [if_neg e, if_neg e2]
      exact ih (fun s s' hm => hi s s' (List.mem_cons_of_mem _ hm))

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
    rintro ilist ⟨_, _, hi⟩ Γ i v
    rw [Aux.termsem_Var]
    refine (Aux.UPDATE_LIST_ilist mem Γ i v x ty ilist (fun s s' hm => ?_)).symm
    obtain ⟨x, ty, e, _⟩ := hi s s' hm
    exact ⟨x, ty, e⟩
  | Const x ty =>
    rintro ilist _ Γ i v
    simp only [simple_subst, Aux.termsem_Const]
  | Comb a b iha ihb =>
    rintro ilist ⟨hw, hd, hi⟩ Γ i v
    obtain ⟨wa, wb, _⟩ := Aux.welltyped_Comb.mp hw
    rw [Aux.DISJOINT_iff] at hd
    simp only [Aux.mem_LIST_TO_SET, bv_names, List.mem_append] at hd
    simp only [simple_subst, Aux.termsem_Comb]
    rw [iha ilist ⟨wa, ?_, hi⟩ Γ i v, ihb ilist ⟨wb, ?_, hi⟩ Γ i v]
    · rw [Aux.DISJOINT_iff]
      intro x hx
      exact hd x (Or.inr ((Aux.mem_LIST_TO_SET _ _).mp hx))
    · rw [Aux.DISJOINT_iff]
      intro x hx
      exact hd x (Or.inl ((Aux.mem_LIST_TO_SET _ _).mp hx))
  | Abs w b _ ihb =>
    rintro ilist ⟨hw, hd, hi⟩ Γ i v
    obtain ⟨x, ty, rfl, wb⟩ := Aux.welltyped_Abs.mp hw
    rw [Aux.DISJOINT_iff] at hd
    simp only [Aux.mem_LIST_TO_SET, bv_names, dest_var_def, List.mem_cons] at hd
    have hif : ∀ s s', (s', s) ∈ FILTER (fun p => p.2 ≠ Var x ty) ilist →
        ∃ x ty, s = Var x ty ∧ has_type s' ty :=
      fun s s' hm => hi s s' (Aux.mem_FILTER_imp _ _ _ hm)
    have hi0 : ∀ s s', (s', s) ∈ ilist → ∃ x ty, s = Var x ty := fun s s' hm => by
      obtain ⟨x, ty, e, _⟩ := hi s s' hm
      exact ⟨x, ty, e⟩
    have hif0 : ∀ s s', (s', s) ∈ FILTER (fun p => p.2 ≠ Var x ty) ilist → ∃ x ty, s = Var x ty :=
      fun s s' hm => hi0 s s' (Aux.mem_FILTER_imp _ _ _ hm)
    have hty : typeof (simple_subst (FILTER (fun p => p.2 ≠ Var x ty) ilist) b) = typeof b := by
      refine WELLTYPED_LEMMA _ _ (simple_subst_has_type b _ ((WELLTYPED b).mp wb) _ ?_)
      rw [Aux.EVERY_iff]
      rintro ⟨s', s⟩ hm
      obtain ⟨y, uy, rfl, h⟩ := hif s s' hm
      exact h
    simp only [simple_subst, Aux.termsem_Abs, hty]
    congr 1
    funext m
    rw [ihb (FILTER (fun p => p.2 ≠ Var x ty) ilist) ⟨wb, ?_, hif⟩ Γ i (v.1, UPDATE (x, ty) m v.2)]
    · congr 1
      refine Prod.ext rfl ?_
      funext z
      obtain ⟨z, tz⟩ := z
      show UPDATE_LIST (v.1, UPDATE (x, ty) m v.2).2 _ (z, tz) = _
      rw [Aux.UPDATE_LIST_ilist mem Γ i (v.1, UPDATE (x, ty) m v.2) z tz _ hif0]
      rw [Aux.REV_ASSOCD_FILTER' (fun s => s ≠ Var x ty)]
      by_cases e : (x, ty) = (z, tz)
      · cases e
        rw [if_neg (fun h => h rfl), Aux.termsem_Var]
        show UPDATE (x, ty) m v.2 (x, ty) = UPDATE (x, ty) m _ (x, ty)
        rw [Aux.UPDATE_eq, Aux.UPDATE_eq]
      · have e2 : Var z tz ≠ Var x ty := fun h => e (by cases h; rfl)
        rw [if_pos e2]
        show _ = UPDATE (x, ty) m _ (z, tz)
        rw [Aux.UPDATE_ne _ _ e, Aux.UPDATE_LIST_ilist mem Γ i v z tz ilist hi0]
        rcases REV_ASSOCD_MEM ilist (Var z tz) (Var z tz) with hm | hm
        · obtain ⟨_, t, _, ht⟩ := hi _ _ hm
          refine termsem_frees mem Γ i _ _ _ ⟨⟨t, ht⟩, rfl, fun a ta hf => ?_⟩
          refine Aux.UPDATE_ne _ _ (fun h => ?_)
          cases h
          exact hd x (Or.inl rfl) ⟨ty, _, hf, List.mem_map.mpr ⟨_, hm, rfl⟩⟩
        · rw [hm, Aux.termsem_Var, Aux.termsem_Var]
          exact Aux.UPDATE_ne _ _ e
    · rw [Aux.DISJOINT_iff]
      rintro y hy ⟨t, u, h1, h2⟩
      refine hd y (Or.inr ((Aux.mem_LIST_TO_SET _ _).mp hy)) ⟨t, u, h1, ?_⟩
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp h2
      exact List.mem_map.mpr ⟨p, Aux.mem_FILTER_imp _ _ _ hp, rfl⟩

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
  rintro tm ilist ⟨hw, hi⟩ Γ i v
  obtain ⟨fm, wf, ha, hd, hj⟩ := Aux.fresh_term
    (setOf (fun y => ∃ ty u, VFREE_IN (Var y ty) u ∧ u ∈ ilist.map Prod.fst)) tm
    (FINITE_VFREE_IN_list _) hw
  have hi0 : ∀ s s', (s', s) ∈ ilist → ∃ x ty, s = Var x ty := fun s s' hm => by
    obtain ⟨x, ty, e, _⟩ := hi s s' hm
    exact ⟨x, ty, e⟩
  rw [termsem_aconv mem Γ i v _ _ ⟨ACONV_VSUBST tm fm ilist ⟨hw, wf, hi, ha⟩,
      VSUBST_WELLTYPED tm (Tyvar default) ilist ⟨hw, hi⟩,
      VSUBST_WELLTYPED fm (Tyvar default) ilist ⟨wf, hi⟩⟩,
    VSUBST_simple_subst fm ilist ⟨hj, hi0, wf⟩,
    termsem_simple_subst mem fm ilist ⟨wf, hj, hi⟩ Γ i v]
  exact (termsem_aconv mem Γ i _ _ _ ⟨ha, hw, wf⟩).symm

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
  rintro Γ tm tyin tmenv ⟨hw, hok, hd, hj, rfl⟩ i v
  induction tm generalizing v with
  | Var x ty => simp only [simple_inst, Aux.termsem_Var]
  | Const name ty =>
    obtain ⟨ty0, hf, _, tyin0, rfl⟩ := hok
    simp only [simple_inst, Aux.termsem_Const]
    rw [instance_def (tmsof Γ) i name _ ty0 _ ⟨hf, TYPE_SUBST_compose tyin0 ty0 tyin⟩,
      instance_def (tmsof Γ) i name _ ty0 tyin0 ⟨hf, rfl⟩]
    show tmaof i name _ = tmaof i name _
    congr 1
    apply List.map_congr_left
    intro x _
    simp only [Function.comp]
    rw [← TYPE_SUBST_compose]
    exact typesem_TYPE_SUBST tyin (TYPE_SUBST tyin0 (Tyvar x)) i.1 v.1
  | Comb a b iha ihb =>
    obtain ⟨wa, wb, _⟩ := Aux.welltyped_Comb.mp hw
    rw [Aux.ALL_DISTINCT_iff_nodup] at hd
    simp only [bv_names] at hd
    obtain ⟨d1, d2, _⟩ := List.nodup_append.mp hd
    rw [Aux.DISJOINT_iff] at hj
    simp only [Aux.mem_LIST_TO_SET, bv_names, List.mem_append] at hj
    simp only [simple_inst, Aux.termsem_Comb]
    rw [iha wa hok.1 ((Aux.ALL_DISTINCT_iff_nodup _).mpr d1) ?_ v,
      ihb wb hok.2.1 ((Aux.ALL_DISTINCT_iff_nodup _).mpr d2) ?_ v]
    · rw [Aux.DISJOINT_iff]
      rintro x hx ⟨t, h⟩
      exact hj x (Or.inr ((Aux.mem_LIST_TO_SET _ _).mp hx)) ⟨t, Or.inr h⟩
    · rw [Aux.DISJOINT_iff]
      rintro x hx ⟨t, h⟩
      exact hj x (Or.inl ((Aux.mem_LIST_TO_SET _ _).mp hx)) ⟨t, Or.inl h⟩
  | Abs w b _ ihb =>
    obtain ⟨x, ty, rfl, h1, h2⟩ := hok
    have wb := term_ok_welltyped _ _ h2
    simp only [bv_names, dest_var_def, ALL_DISTINCT] at hd
    rw [Aux.DISJOINT_iff] at hj
    simp only [Aux.mem_LIST_TO_SET, bv_names, dest_var_def, List.mem_cons] at hj
    have hty : typeof (simple_inst tyin b) = TYPE_SUBST tyin (typeof b) :=
      WELLTYPED_LEMMA _ _ (simple_inst_has_type b tyin wb)
    have hj' : DISJOINT (LIST_TO_SET (bv_names b))
        (setOf (fun x => ∃ ty, VFREE_IN (Var x ty) b)) := by
      rw [Aux.DISJOINT_iff]
      rintro y hy ⟨t, h⟩
      have hy' := (Aux.mem_LIST_TO_SET _ _).mp hy
      by_cases e : Var x ty = Var y t
      · cases e; exact hd.1 hy'
      · exact hj y (Or.inr hy') ⟨t, e, h⟩
    simp only [simple_inst, Aux.termsem_Abs, hty]
    rw [typesem_TYPE_SUBST tyin ty, typesem_TYPE_SUBST tyin (typeof b)]
    congr 1
    funext m
    rw [ihb wb h2 hd.2 hj' (v.1, UPDATE (x, TYPE_SUBST tyin ty) m v.2)]
    refine termsem_frees mem _ i b _ _ ⟨wb, rfl, fun y t hf => ?_⟩
    simp only [UPDATE]
    by_cases e : (x, ty) = (y, t)
    · cases e; rw [if_pos rfl, if_pos rfl]
    · rw [if_neg e, if_neg]
      intro e2
      rw [Prod.mk.injEq] at e2
      obtain ⟨rfl, _⟩ := e2
      refine hj x (Or.inl rfl) ⟨t, fun e3 => e ?_, hf⟩
      cases e3; rfl

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
  rintro Γ tm tyin tmenv ⟨hok, rfl⟩ i v
  have hw := term_ok_welltyped _ _ hok
  obtain ⟨fm, wf, ha, hd, hj⟩ := Aux.fresh_term
    (setOf (fun x => ∃ ty, VFREE_IN (Var x ty) tm)) tm (FINITE_VFREE_IN tm) hw
  have hj' : DISJOINT (LIST_TO_SET (bv_names fm))
      (setOf (fun x => ∃ ty, VFREE_IN (Var x ty) fm)) := by
    rw [Aux.DISJOINT_iff] at hj ⊢
    rintro x hx ⟨t, h⟩
    exact hj x hx ⟨t, (VFREE_IN_ACONV tm fm x t ha).mpr h⟩
  rw [termsem_aconv mem _ i v _ _ ⟨ACONV_INST tm fm tyin ⟨hw, wf, ha⟩, INST_WELLTYPED tm tyin hw,
      INST_WELLTYPED fm tyin wf⟩,
    INST_simple_inst tyin fm ⟨hd, hj', wf⟩,
    termsem_simple_inst mem Γ fm tyin _ ⟨wf, term_ok_aconv Γ tm fm ⟨ha, hok, wf⟩, hd, hj', rfl⟩ i v]
  exact (termsem_aconv mem _ i _ _ _ ⟨ha, hw, wf⟩).symm

end

end Candle
