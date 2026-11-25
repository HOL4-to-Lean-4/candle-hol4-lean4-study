import CandleLean.HolSemanticsExtra

/-!
# holSoundness (CakeML `candle/standard/semantics/holSoundnessScript.sml`)

This theory defines no constants; its theorems (stage 2) use the constants of
`HolSyntax`, `HolSemantics` and `SetSpec`.
-/

universe u

namespace Candle

open HOL Classical

noncomputable section

variable {U : Type u}

theorem Aux.structure [Nonempty U] {mem : U → U → Prop} {thy : thy} {i : interpretation U}
    {v : valuation U} (h1 : theory_ok thy) (h2 : models0 mem i thy)
    (h3 : is_valuation0 mem (tysof (sigof thy)) i.1 v) : is_structure0 mem (sigof thy) i v :=
  ⟨h1.2.2, h2.2.1, h2.1, h3⟩

theorem Aux.termsem_mem [Nonempty U] {mem : U → U → Prop} (hst : is_set_theory mem) {sig : sig}
    {i : interpretation U} {v : valuation U} (hs : is_structure0 mem sig i v) {t : term}
    (ht : term_ok sig t) : mem (termsem0 mem (tmsof sig) i v t) (typesem i.1 v.1 (typeof t)) :=
  termsem_typesem mem hst sig i t v _ _ _ ⟨rfl, rfl, hs.2.2.2, hs.2.2.1, hs.2.1.1, ht, rfl⟩

theorem Aux.equation_true [Nonempty U] {mem : U → U → Prop} (hst : is_set_theory mem) {sig : sig}
    {i : interpretation U} {v : valuation U} (hs : is_structure0 mem sig i v) {s t : term}
    (ht : term_ok sig (equation s t)) :
    termsem0 mem (tmsof sig) i v (equation s t) = true_ mem ↔
      termsem0 mem (tmsof sig) i v s = termsem0 mem (tmsof sig) i v t := by
  rw [termsem_equation mem hst sig i v s t _ ⟨hs, ht, rfl⟩, boolean_eq_true mem hst]

theorem Aux.bool_cases [Nonempty U] {mem : U → U → Prop} (hst : is_set_theory mem) {sig : sig}
    {i : interpretation U} {v : valuation U} (hs : is_structure0 mem sig i v) {t : term}
    (ht : term_ok sig t) (hty : has_type t BoolTy) :
    termsem0 mem (tmsof sig) i v t = true_ mem ∨ termsem0 mem (tmsof sig) i v t = false_ mem := by
  have h := Aux.termsem_mem hst hs ht
  rw [WELLTYPED_LEMMA _ _ hty, typesem_Bool mem _ _ hs.2.1.1, mem_boolset mem hst] at h
  exact h

/-- a hypothesis that has an alpha-equivalent in a list of true terms is true -/
theorem Aux.hyp_true [Nonempty U] {mem : U → U → Prop} {sig : sig} {i : interpretation U}
    {v : valuation U} {l : List term} (hl : EVERY (term_ok sig) l)
    (htr : EVERY (fun t => termsem0 mem (tmsof sig) i v t = true_ mem) l) {t : term}
    (ht : welltyped t) (h : ∃ y, y ∈ l ∧ ACONV t y) :
    termsem0 mem (tmsof sig) i v t = true_ mem := by
  obtain ⟨y, hy, ha⟩ := h
  rw [termsem_aconv mem _ i v t y
    ⟨ha, ht, term_ok_welltyped _ _ (Aux.EVERY_iff.mp hl y hy)⟩]
  exact Aux.EVERY_iff.mp htr y hy

/- HOL4:
Theorem binary_inference_rule:
   is_set_theory ^mem ⇒
    ∀thy h1 h2 p1 p2 q.
    q has_type Bool ∧ term_ok (sigof thy) q ∧
    (∀i v. is_structure (sigof thy) i v ∧
           termsem (tmsof thy) i v p1 = True ∧
           termsem (tmsof thy) i v p2 = True ⇒
           termsem (tmsof thy) i v q = True) ∧
    (thy,h1) |= p1 ∧ (thy,h2) |= p2
    ⇒ (thy, term_union h1 h2) |= q
-/
theorem binary_inference_rule [Nonempty U] (mem : U → U → Prop) :
    is_set_theory mem →
      ∀ (thy : thy) (h1 h2 : List term) (p1 p2 q : term),
        has_type q BoolTy ∧ term_ok (sigof thy) q ∧
        (∀ (i : interpretation U) (v : valuation U),
          is_structure0 mem (sigof thy) i v ∧
          termsem0 mem (thy_tmsof thy) i v p1 = true_ mem ∧
          termsem0 mem (thy_tmsof thy) i v p2 = true_ mem →
          termsem0 mem (thy_tmsof thy) i v q = true_ mem) ∧
        entails0 mem (thy, h1) p1 ∧ entails0 mem (thy, h2) p2 →
        entails0 mem (thy, term_union h1 h2) q := by
  rintro hst thy h1 h2 p1 p2 q ⟨hq1, hq2, hsem, ⟨a1, a2, a3, a4, a5⟩, ⟨_, b2, b3, b4, b5⟩⟩
  have hok := EVERY_term_union _ h1 h2 ⟨a2.2, b2.2⟩
  refine ⟨a1, ⟨hq2, hok⟩, ⟨hq1, EVERY_term_union _ h1 h2 ⟨a3.2, b3.2⟩⟩,
    hypset_ok_term_union h1 h2 ⟨a4, b4⟩, fun i hi v hv => ?_⟩
  obtain ⟨hv1, hv2⟩ := hv
  refine hsem i v ⟨Aux.structure a1 hi hv1, a5 i hi v ⟨hv1, ?_⟩, b5 i hi v ⟨hv1, ?_⟩⟩
  · refine Aux.EVERY_iff.mpr fun t ht => Aux.hyp_true hok hv2 ?_
      (Aux.MEM_term_union h1 h2 t (Or.inl ht))
    exact term_ok_welltyped _ _ (Aux.EVERY_iff.mp a2.2 t ht)
  · refine Aux.EVERY_iff.mpr fun t ht => Aux.hyp_true hok hv2 ?_
      (Aux.MEM_term_union h1 h2 t (Or.inr ht))
    exact term_ok_welltyped _ _ (Aux.EVERY_iff.mp b2.2 t ht)

/- HOL4:
Theorem ABS_correct:
   is_set_theory ^mem ⇒
    ∀thy x ty h l r.
    ¬EXISTS (VFREE_IN (Var x ty)) h ∧ type_ok (tysof thy) ty ∧
    (thy,h) |= l === r
    ⇒ (thy,h) |= Abs (Var x ty) l === Abs (Var x ty) r
-/
theorem ABS_correct [Nonempty U] (mem : U → U → Prop) :
    is_set_theory mem →
      ∀ (thy : thy) (x : mlstring) (ty : type) (h : List term) (l r : term),
        ¬ EXISTS (VFREE_IN (Var x ty)) h ∧ type_ok (thy_tysof thy) ty ∧
        entails0 mem (thy, h) (equation l r) →
        entails0 mem (thy, h) (equation (Abs (Var x ty) l) (Abs (Var x ty) r)) := by
  rintro hst thy x ty h l r ⟨hx, hty, ⟨a1, a2, a3, a4, a5⟩⟩
  have hstd := a1.2.2
  obtain ⟨ol, or, e⟩ := (term_ok_equation _ l r hstd).mp a2.1
  have hok : term_ok (sigof thy) (equation (Abs (Var x ty) l) (Abs (Var x ty) r)) := by
    refine (term_ok_equation _ _ _ hstd).mpr
      ⟨⟨x, ty, rfl, hty, ol⟩, ⟨x, ty, rfl, hty, or⟩, ?_⟩
    simp only [typeof, e]
  refine ⟨a1, ⟨hok, a2.2⟩, ⟨Aux.welltyped_equation (term_ok_welltyped _ _ hok), a3.2⟩, a4,
    fun i hi v hv => ?_⟩
  obtain ⟨hv1, hv2⟩ := hv
  have hs := Aux.structure a1 hi hv1
  refine (Aux.equation_true hst hs hok).mpr ?_
  rw [Aux.termsem_Abs, Aux.termsem_Abs]
  apply abstract_eq mem hst
  intro m hm
  have hv' := Aux.is_valuation_UPDATE mem hv1 (x := x) hm
  have hs' := Aux.structure a1 hi hv'
  refine ⟨Aux.termsem_mem hst hs' ol, Aux.termsem_mem hst hs' or, ?_⟩
  refine (Aux.equation_true hst hs' a2.1).mp (a5 i hi _ ⟨hv', ?_⟩)
  refine Aux.EVERY_iff.mpr fun t ht => ?_
  rw [Aux.EXISTS_iff] at hx
  refine (Aux.termsem_UPDATE mem _ i t v x ty m
    (term_ok_welltyped _ _ (Aux.EVERY_iff.mp a2.2 t ht)) (fun hf => hx ⟨t, ht, hf⟩)).trans ?_
  exact Aux.EVERY_iff.mp hv2 t ht

/- HOL4:
Theorem ASSUME_correct:
   ∀thy p.
      theory_ok thy ∧ p has_type Bool ∧ term_ok (sigof thy) p
      ⇒ (thy,[p]) |= p
-/
theorem ASSUME_correct [Nonempty U] (mem : U → U → Prop) :
    ∀ (thy : thy) (p : term),
      theory_ok thy ∧ has_type p BoolTy ∧ term_ok (sigof thy) p →
      entails0 mem (thy, [p]) p := by
  rintro thy p ⟨h1, h2, h3⟩
  exact ⟨h1, ⟨h3, h3, trivial⟩, ⟨h2, h2, trivial⟩, hypset_ok_sing p, fun i _ v hv => hv.2.1⟩

/- HOL4:
Theorem BETA_correct:
   is_set_theory ^mem ⇒
    ∀thy x ty t.
      theory_ok thy ∧ type_ok (tysof thy) ty ∧ term_ok (sigof thy) t ⇒
      (thy,[]) |= Comb (Abs (Var x ty) t) (Var x ty) === t
-/
theorem BETA_correct [Nonempty U] (mem : U → U → Prop) :
    is_set_theory mem →
      ∀ (thy : thy) (x : mlstring) (ty : type) (t : term),
        theory_ok thy ∧ type_ok (thy_tysof thy) ty ∧ term_ok (sigof thy) t →
        entails0 mem (thy, []) (equation (Comb (Abs (Var x ty) t) (Var x ty)) t) := by
  rintro hst thy x ty t ⟨h1, h2, h3⟩
  have hw := term_ok_welltyped _ _ h3
  have hok : term_ok (sigof thy) (equation (Comb (Abs (Var x ty) t) (Var x ty)) t) := by
    refine (term_ok_equation _ _ _ h1.2.2).mpr
      ⟨⟨⟨x, ty, rfl, h2, h3⟩, h2, ⟨_, has_type.Comb (has_type.Abs ((WELLTYPED t).mp hw))
        has_type.Var⟩⟩, h3, ?_⟩
    simp only [typeof, codomain_def]
  refine ⟨h1, ⟨hok, trivial⟩, ⟨Aux.welltyped_equation (term_ok_welltyped _ _ hok), trivial⟩,
    hypset_ok_nil, fun i hi v hv => ?_⟩
  obtain ⟨hv1, _⟩ := hv
  have hs := Aux.structure h1 hi hv1
  refine (Aux.equation_true hst hs hok).mpr ?_
  have hu : UPDATE (x, ty) (v.2 (x, ty)) v.2 = v.2 := by
    funext p
    by_cases e : (x, ty) = p
    · subst e; exact Aux.UPDATE_same _ _ _
    · exact Aux.UPDATE_ne _ _ e
  rw [Aux.termsem_Comb, Aux.termsem_Abs, Aux.termsem_Var, apply_abstract mem hst]
  · simp only [hu]
  · simp only [hu]
    exact ⟨hv1.2 x ty h2, Aux.termsem_mem hst hs h3⟩

/- HOL4:
Theorem DEDUCT_ANTISYM_correct:
   is_set_theory ^mem ⇒
    ∀thy h1 p1 h2 p2.
      (thy,h1) |= p1 ∧ (thy,h2) |= p2 ⇒
      (thy,
       term_union (term_remove p2 h1)
                  (term_remove p1 h2))
      |= p1 === p2
-/
theorem DEDUCT_ANTISYM_correct [Nonempty U] (mem : U → U → Prop) :
    is_set_theory mem →
      ∀ (thy : thy) (h1 : List term) (p1 : term) (h2 : List term) (p2 : term),
        entails0 mem (thy, h1) p1 ∧ entails0 mem (thy, h2) p2 →
        entails0 mem
          (thy, term_union (term_remove p2 h1) (term_remove p1 h2))
          (equation p1 p2) := by
  rintro hst thy h1 p1 h2 p2 ⟨⟨a1, a2, a3, a4, a5⟩, ⟨_, b2, b3, b4, b5⟩⟩
  have e1 := WELLTYPED_LEMMA _ _ a3.1
  have e2 := WELLTYPED_LEMMA _ _ b3.1
  have hok : term_ok (sigof thy) (equation p1 p2) :=
    (term_ok_equation _ _ _ a1.2.2).mpr ⟨a2.1, b2.1, e2.trans e1.symm⟩
  have hu : EVERY (term_ok (sigof thy)) (term_union (term_remove p2 h1) (term_remove p1 h2)) :=
    EVERY_term_union _ _ _ ⟨EVERY_term_remove _ _ _ a2.2, EVERY_term_remove _ _ _ b2.2⟩
  refine ⟨a1, ⟨hok, hu⟩, ⟨Aux.welltyped_equation (term_ok_welltyped _ _ hok),
    EVERY_term_union _ _ _ ⟨EVERY_term_remove _ _ _ a3.2, EVERY_term_remove _ _ _ b3.2⟩⟩,
    hypset_ok_term_union _ _ ⟨hypset_ok_term_remove _ a4 _, hypset_ok_term_remove _ b4 _⟩,
    fun i hi v hv => ?_⟩
  obtain ⟨hv1, hv2⟩ := hv
  have hs := Aux.structure a1 hi hv1
  refine (Aux.equation_true hst hs hok).mpr ?_
  have w1 := term_ok_welltyped _ _ a2.1
  have w2 := term_ok_welltyped _ _ b2.1
  have d1 : termsem0 mem (tmsof (sigof thy)) i v p2 = true_ mem →
      termsem0 mem (tmsof (sigof thy)) i v p1 = true_ mem := by
    intro htrue
    refine a5 i hi v ⟨hv1, Aux.EVERY_iff.mpr fun t ht => ?_⟩
    have wt := term_ok_welltyped _ _ (Aux.EVERY_iff.mp a2.2 t ht)
    by_cases ha : ACONV p2 t
    · exact (termsem_aconv mem _ i v p2 t ⟨ha, w2, wt⟩).symm.trans htrue
    · exact Aux.hyp_true hu hv2 wt
        (Aux.MEM_term_union _ _ t (Or.inl (Aux.MEM_term_remove p2 t ha h1 ht)))
  have d2 : termsem0 mem (tmsof (sigof thy)) i v p1 = true_ mem →
      termsem0 mem (tmsof (sigof thy)) i v p2 = true_ mem := by
    intro htrue
    refine b5 i hi v ⟨hv1, Aux.EVERY_iff.mpr fun t ht => ?_⟩
    have wt := term_ok_welltyped _ _ (Aux.EVERY_iff.mp b2.2 t ht)
    by_cases ha : ACONV p1 t
    · exact (termsem_aconv mem _ i v p1 t ⟨ha, w1, wt⟩).symm.trans htrue
    · exact Aux.hyp_true hu hv2 wt
        (Aux.MEM_term_union _ _ t (Or.inr (Aux.MEM_term_remove p1 t ha h2 ht)))
  rcases Aux.bool_cases hst hs a2.1 a3.1 with c1 | c1
  · rw [c1, d2 c1]
  · rcases Aux.bool_cases hst hs b2.1 b3.1 with c2 | c2
    · rw [c2, d1 c2]
    · rw [c1, c2]

/- HOL4:
Theorem EQ_MP_correct:
   is_set_theory ^mem ⇒
    ∀thy h1 h2 p q p'.
      (thy,h1) |= p === q ∧ (thy,h2) |= p' ∧ ACONV p p' ⇒
      (thy,term_union h1 h2) |= q
-/
theorem EQ_MP_correct [Nonempty U] (mem : U → U → Prop) :
    is_set_theory mem →
      ∀ (thy : thy) (h1 h2 : List term) (p q p' : term),
        entails0 mem (thy, h1) (equation p q) ∧ entails0 mem (thy, h2) p' ∧ ACONV p p' →
        entails0 mem (thy, term_union h1 h2) q := by
  rintro hst thy h1 h2 p q p' ⟨ha, hb, hac⟩
  obtain ⟨op, oq, e⟩ := (term_ok_equation _ p q ha.1.2.2).mp ha.2.1.1
  have wp := term_ok_welltyped _ _ op
  have wq := term_ok_welltyped _ _ oq
  have hb3 := hb.2.2.1.1
  have wp' : welltyped p' := ⟨_, hb3⟩
  have hty : typeof q = BoolTy :=
    e.trans ((ACONV_TYPE p p' hac ⟨wp, wp'⟩).trans (WELLTYPED_LEMMA _ _ hb3))
  refine binary_inference_rule mem hst thy h1 h2 (equation p q) p' q
    ⟨hty ▸ (WELLTYPED q).mp wq, oq, ?_, ha, hb⟩
  rintro i v ⟨hs, t1, t2⟩
  have e1 := (Aux.equation_true hst hs ha.2.1.1).mp t1
  exact e1.symm.trans ((termsem_aconv mem _ i v p p' ⟨hac, wp, wp'⟩).trans t2)

/- HOL4:
Theorem INST_correct:
   is_set_theory ^mem ⇒
    ∀thy h c.
      (∀s s'. MEM (s',s) ilist ⇒
              ∃x ty. (s = Var x ty) ∧ s' has_type ty ∧ term_ok (sigof thy) s') ∧
      (thy, h) |= c
    ⇒ (thy, term_image (VSUBST ilist) h) |= VSUBST ilist c
-/
theorem INST_correct [Nonempty U] (mem : U → U → Prop) (ilist : List (term × term)) :
    is_set_theory mem →
      ∀ (thy : thy) (h : List term) (c : term),
        (∀ s s', (s', s) ∈ ilist →
          ∃ x ty, s = Var x ty ∧ has_type s' ty ∧ term_ok (sigof thy) s') ∧
        entails0 mem (thy, h) c →
        entails0 mem (thy, term_image (VSUBST ilist) h) (VSUBST ilist c) := by
  rintro hst thy h c ⟨hil, ⟨a1, a2, a3, a4, a5⟩⟩
  have hil' : ∀ s s', (s', s) ∈ ilist → ∃ x ty, s = Var x ty ∧ has_type s' ty := by
    intro s s' hm
    obtain ⟨x, ty, e, ht, _⟩ := hil s s' hm
    exact ⟨x, ty, e, ht⟩
  have hil2 : ∀ s s', (s', s) ∈ ilist → ∃ x ty, s = Var x ty := by
    intro s s' hm
    obtain ⟨x, ty, e, _⟩ := hil s s' hm
    exact ⟨x, ty, e⟩
  have hok : EVERY (term_ok (sigof thy)) (term_image (VSUBST ilist) h) := by
    refine Aux.EVERY_iff.mpr fun t ht => ?_
    obtain ⟨x, hx, rfl⟩ := MEM_term_image_imp _ _ _ ht
    exact term_ok_VSUBST _ x ilist ⟨Aux.EVERY_iff.mp a2.2 x hx, hil⟩
  refine ⟨a1, ⟨term_ok_VSUBST _ c ilist ⟨a2.1, hil⟩, hok⟩,
    ⟨VSUBST_HAS_TYPE c _ ilist ⟨a3.1, hil'⟩, Aux.EVERY_iff.mpr fun t ht => ?_⟩,
    hypset_ok_term_image _ _ a4, fun i hi v hv => ?_⟩
  · obtain ⟨x, hx, rfl⟩ := MEM_term_image_imp _ _ _ ht
    exact VSUBST_HAS_TYPE x _ ilist ⟨Aux.EVERY_iff.mp a3.2 x hx, hil'⟩
  · obtain ⟨hv1, hv2⟩ := hv
    have hs := Aux.structure a1 hi hv1
    have hval : is_valuation0 mem (tysof (sigof thy)) i.1
        (v.1, Aux.upd mem (tmsof (sigof thy)) i v ilist) := by
      refine ⟨hv1.1, fun x ty hty => ?_⟩
      change mem (Aux.upd mem (tmsof (sigof thy)) i v ilist (x, ty)) (typesem i.1 v.1 ty)
      rw [Aux.upd_val mem _ i v ilist hil2]
      rcases REV_ASSOCD_MEM ilist (Var x ty) (Var x ty) with hm | hm
      · obtain ⟨x', ty', e, ht, ho⟩ := hil _ _ hm
        cases e
        have := Aux.termsem_mem hst hs ho
        rw [WELLTYPED_LEMMA _ _ ht] at this
        exact this
      · rw [hm]
        have : term_ok (sigof thy) (Var x ty) := hty
        exact Aux.termsem_mem hst hs this
    refine (termsem_VSUBST mem c ilist ⟨term_ok_welltyped _ _ a2.1, hil'⟩ _ i v).trans ?_
    refine a5 i hi (v.1, Aux.upd mem (tmsof (sigof thy)) i v ilist) ⟨hval, ?_⟩
    refine Aux.EVERY_iff.mpr fun t ht => ?_
    have wt := term_ok_welltyped _ _ (Aux.EVERY_iff.mp a2.2 t ht)
    refine (termsem_VSUBST mem t ilist ⟨wt, hil'⟩ _ i v).symm.trans ?_
    exact Aux.hyp_true hok hv2 (VSUBST_WELLTYPED t BoolTy ilist ⟨wt, hil'⟩)
      (Aux.MEM_term_image _ t h ht)

/- HOL4:
Theorem INST_TYPE_correct:
   is_set_theory ^mem ⇒
    ∀thy h c.
      EVERY (type_ok (tysof thy)) (MAP FST tyin) ∧
      (thy, h) |= c
    ⇒ (thy, term_image (INST tyin) h) |= INST tyin c
-/
theorem INST_TYPE_correct [Nonempty U] (mem : U → U → Prop) (tyin : List (type × type)) :
    is_set_theory mem →
      ∀ (thy : thy) (h : List term) (c : term),
        EVERY (type_ok (thy_tysof thy)) (tyin.map Prod.fst) ∧
        entails0 mem (thy, h) c →
        entails0 mem (thy, term_image (INST tyin) h) (INST tyin c) := by
  rintro hst thy h c ⟨htyin, ⟨a1, a2, a3, a4, a5⟩⟩
  have hok : EVERY (term_ok (sigof thy)) (term_image (INST tyin) h) := by
    refine Aux.EVERY_iff.mpr fun t ht => ?_
    obtain ⟨x, hx, rfl⟩ := MEM_term_image_imp _ _ _ ht
    exact term_ok_INST _ tyin x ⟨Aux.EVERY_iff.mp a2.2 x hx, htyin⟩
  refine ⟨a1, ⟨term_ok_INST _ tyin c ⟨a2.1, htyin⟩, hok⟩,
    ⟨INST_HAS_TYPE c _ tyin _ ⟨a3.1, (TYPE_SUBST_Bool tyin).symm⟩,
      Aux.EVERY_iff.mpr fun t ht => ?_⟩,
    hypset_ok_term_image _ _ a4, fun i hi v hv => ?_⟩
  · obtain ⟨x, hx, rfl⟩ := MEM_term_image_imp _ _ _ ht
    exact INST_HAS_TYPE x _ tyin _ ⟨Aux.EVERY_iff.mp a3.2 x hx, (TYPE_SUBST_Bool tyin).symm⟩
  · obtain ⟨hv1, hv2⟩ := hv
    have hval : is_valuation0 mem (tysof (sigof thy)) i.1 (Aux.ival i tyin v) := by
      refine ⟨fun x => ?_, fun x ty hty => ?_⟩
      · refine typesem_inhabited mem hst (tysof (sigof thy)) i.1 v.1 _ ⟨hv1.1, hi.1.1, ?_⟩
        refine type_ok_TYPE_SUBST _ _ _ ⟨?_, htyin⟩
        rw [type_ok]
        trivial
      · have := hv1.2 x (TYPE_SUBST tyin ty) (type_ok_TYPE_SUBST _ _ _ ⟨hty, htyin⟩)
        rw [typesem_TYPE_SUBST] at this
        exact this
    refine (termsem_INST mem (sigof thy) c tyin _ ⟨a2.1, rfl⟩ i v).trans ?_
    refine a5 i hi (Aux.ival i tyin v) ⟨hval, Aux.EVERY_iff.mpr fun t ht => ?_⟩
    have ot := Aux.EVERY_iff.mp a2.2 t ht
    refine (termsem_INST mem (sigof thy) t tyin _ ⟨ot, rfl⟩ i v).symm.trans ?_
    exact Aux.hyp_true hok hv2 (INST_WELLTYPED t tyin (term_ok_welltyped _ _ ot))
      (Aux.MEM_term_image _ t h ht)

/- HOL4:
Theorem MK_COMB_correct:
   is_set_theory ^mem ⇒
    ∀thy h1 h2 l1 r1 l2 r2.
      (thy,h1) |= l1 === r1 ∧ (thy,h2) |= l2 === r2 ∧
      welltyped (Comb l1 l2)
      ⇒ (thy,term_union h1 h2) |= Comb l1 l2 === Comb r1 r2
-/
theorem MK_COMB_correct [Nonempty U] (mem : U → U → Prop) :
    is_set_theory mem →
      ∀ (thy : thy) (h1 h2 : List term) (l1 r1 l2 r2 : term),
        entails0 mem (thy, h1) (equation l1 r1) ∧ entails0 mem (thy, h2) (equation l2 r2) ∧
        welltyped (Comb l1 l2) →
        entails0 mem (thy, term_union h1 h2) (equation (Comb l1 l2) (Comb r1 r2)) := by
  rintro hst thy h1 h2 l1 r1 l2 r2 ⟨ha, hb, hw⟩
  have hstd := ha.1.2.2
  obtain ⟨o1, o2, e1⟩ := (term_ok_equation _ l1 r1 hstd).mp ha.2.1.1
  obtain ⟨o3, o4, e2⟩ := (term_ok_equation _ l2 r2 hstd).mp hb.2.1.1
  obtain ⟨_, _, rty, e3⟩ := Aux.welltyped_Comb hw
  have hw' : welltyped (Comb r1 r2) :=
    (WELLTYPED_CLAUSES.2.2.1 r1 r2).mpr ⟨term_ok_welltyped _ _ o2, term_ok_welltyped _ _ o4, rty, by
      rw [e1, e2, e3]⟩
  have hok : term_ok (sigof thy) (equation (Comb l1 l2) (Comb r1 r2)) := by
    refine (term_ok_equation _ _ _ hstd).mpr ⟨⟨o1, o3, hw⟩, ⟨o2, o4, hw'⟩, ?_⟩
    simp only [typeof, e1]
  refine binary_inference_rule mem hst thy h1 h2 (equation l1 r1) (equation l2 r2) _
    ⟨Aux.welltyped_equation (term_ok_welltyped _ _ hok), hok, ?_, ha, hb⟩
  rintro i v ⟨hs, t1, t2⟩
  refine (Aux.equation_true hst hs hok).mpr ?_
  have c1 := (Aux.equation_true hst hs ha.2.1.1).mp t1
  have c2 := (Aux.equation_true hst hs hb.2.1.1).mp t2
  rw [Aux.termsem_Comb, Aux.termsem_Comb, c1, c2]

/- HOL4:
Theorem REFL_correct:
   is_set_theory ^mem ⇒
    ∀thy t.
      theory_ok thy ∧ term_ok (sigof thy) t ⇒
      (thy,[]) |= t === t
-/
theorem REFL_correct [Nonempty U] (mem : U → U → Prop) :
    is_set_theory mem →
      ∀ (thy : thy) (t : term),
        theory_ok thy ∧ term_ok (sigof thy) t →
        entails0 mem (thy, []) (equation t t) := by
  rintro hst thy t ⟨h1, h2⟩
  have hok : term_ok (sigof thy) (equation t t) :=
    (term_ok_equation _ _ _ h1.2.2).mpr ⟨h2, h2, rfl⟩
  exact ⟨h1, ⟨hok, trivial⟩, ⟨Aux.welltyped_equation (term_ok_welltyped _ _ hok), trivial⟩,
    hypset_ok_nil,
    fun i hi v hv => (Aux.equation_true hst (Aux.structure h1 hi hv.1) hok).mpr rfl⟩

/- HOL4:
Theorem proves_sound:
   is_set_theory ^mem ⇒ ∀thyh c. thyh |- c ⇒ thyh |= c
-/
theorem proves_sound [Nonempty U] (mem : U → U → Prop) :
    is_set_theory mem →
      ∀ (thyh : thy × List term) (c : term), proves thyh c → entails0 mem thyh c := by
  intro hst thyh c h
  induction h with
  | ABS h1 h2 _ ih => exact ABS_correct mem hst _ _ _ _ _ _ ⟨h1, h2, ih⟩
  | ASSUME h1 h2 h3 => exact ASSUME_correct mem _ _ ⟨h1, h2, h3⟩
  | BETA h1 h2 h3 => exact BETA_correct mem hst _ _ _ _ ⟨h1, h2, h3⟩
  | DEDUCT_ANTISYM _ _ ih1 ih2 => exact DEDUCT_ANTISYM_correct mem hst _ _ _ _ _ ⟨ih1, ih2⟩
  | EQ_MP _ _ h3 ih1 ih2 => exact EQ_MP_correct mem hst _ _ _ _ _ _ ⟨ih1, ih2, h3⟩
  | INST h1 _ ih => exact INST_correct mem _ hst _ _ _ ⟨h1, ih⟩
  | INST_TYPE h1 _ ih => exact INST_TYPE_correct mem _ hst _ _ _ ⟨h1, ih⟩
  | MK_COMB _ _ h3 ih1 ih2 => exact MK_COMB_correct mem hst _ _ _ _ _ _ _ ⟨ih1, ih2, h3⟩
  | REFL h1 h2 => exact REFL_correct mem hst _ _ ⟨h1, h2⟩
  | axioms h1 h2 =>
    obtain ⟨h3, h4⟩ := h1.2.1 _ h2
    exact ⟨h1, ⟨h3, trivial⟩, ⟨h4, trivial⟩, hypset_ok_nil, fun i hi => hi.2.2 _ h2⟩

end

end Candle
