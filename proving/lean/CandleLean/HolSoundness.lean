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

/-! Auxiliary lemmas (namespace `Candle.Aux`). -/

theorem Aux.structure_of [Nonempty U] {mem : U → U → Prop} {thy : thy} {i : interpretation U}
    {v : valuation U} (ht : theory_ok thy) (hm : models0 mem i thy)
    (hv : is_valuation0 mem (thy_tysof thy) (tyaof i) v) : is_structure0 mem (sigof thy) i v :=
  ⟨ht.2.2, hm.2.1, hm.1, hv⟩

/-- Elimination of `entails0`, with the components in a convenient form. -/
theorem Aux.entails_elim [Nonempty U] {mem : U → U → Prop} {thy : thy} {h : List term} {c : term}
    (he : entails0 mem (thy, h) c) :
    theory_ok thy ∧ term_ok (sigof thy) c ∧ (∀ t, t ∈ h → term_ok (sigof thy) t) ∧
    has_type c BoolTy ∧ (∀ t, t ∈ h → has_type t BoolTy) ∧ hypset_ok h ∧
    ∀ (i : interpretation U) (v : valuation U), models0 mem i thy →
      is_valuation0 mem (thy_tysof thy) (tyaof i) v →
      (∀ t, t ∈ h → termsem0 mem (thy_tmsof thy) i v t = true_ mem) →
      termsem0 mem (thy_tmsof thy) i v c = true_ mem := by
  obtain ⟨h1, ⟨h2, h3⟩, ⟨h4, h5⟩, h6, h7⟩ := he
  refine ⟨h1, h2, (Aux.EVERY_iff _ _).mp h3, h4, (Aux.EVERY_iff _ _).mp h5, h6, ?_⟩
  intro i v hm hv hh
  exact h7 i hm v ⟨hv, (Aux.EVERY_iff _ _).mpr hh⟩

/-- Introduction of `entails0`. -/
theorem Aux.entails_intro [Nonempty U] {mem : U → U → Prop} {thy : thy} {h : List term} {c : term}
    (h1 : theory_ok thy) (h2 : term_ok (sigof thy) c) (h3 : ∀ t, t ∈ h → term_ok (sigof thy) t)
    (h4 : has_type c BoolTy) (h5 : ∀ t, t ∈ h → has_type t BoolTy) (h6 : hypset_ok h)
    (h7 : ∀ (i : interpretation U) (v : valuation U), models0 mem i thy →
      is_valuation0 mem (thy_tysof thy) (tyaof i) v →
      (∀ t, t ∈ h → termsem0 mem (thy_tmsof thy) i v t = true_ mem) →
      termsem0 mem (thy_tmsof thy) i v c = true_ mem) : entails0 mem (thy, h) c := by
  refine ⟨h1, ⟨h2, (Aux.EVERY_iff _ _).mpr h3⟩, ⟨h4, (Aux.EVERY_iff _ _).mpr h5⟩, h6, ?_⟩
  intro i hm v hv
  exact h7 i v hm hv.1 ((Aux.EVERY_iff _ _).mp hv.2)

theorem Aux.sem_union {mem : U → U → Prop} {Γ : tmsig} {i : interpretation U} {v : valuation U}
    {sig : sig} {h1 h2 : List term} {b : U} (k1 : hypset_ok h1) (k2 : hypset_ok h2)
    (t1 : ∀ t, t ∈ h1 → term_ok sig t) (t2 : ∀ t, t ∈ h2 → term_ok sig t)
    (hs : ∀ t, t ∈ term_union h1 h2 → termsem0 mem Γ i v t = b) (t : term) (ht : t ∈ h1 ∨ t ∈ h2) :
    termsem0 mem Γ i v t = b := by
  obtain ⟨y, hy, ha⟩ := MEM_term_union h1 h2 t ⟨k1, k2, ht⟩
  have w : ∀ s, s ∈ h1 ∨ s ∈ h2 → welltyped s := by
    rintro s (h | h)
    · exact term_ok_welltyped _ _ (t1 s h)
    · exact term_ok_welltyped _ _ (t2 s h)
  rw [termsem_aconv mem Γ i v t y ⟨ha, w t ht, w y (MEM_term_union_imp _ _ _ hy)⟩]
  exact hs y hy

/-- The semantics of an equation is true iff both sides have the same semantics. -/
theorem Aux.sem_equation [Nonempty U] {mem : U → U → Prop} (hm : is_set_theory mem) {sig : sig}
    {i : interpretation U} {v : valuation U} {s t : term} (hs : is_structure0 mem sig i v)
    (hok : term_ok sig (equation s t)) :
    termsem0 mem (tmsof sig) i v (equation s t) = true_ mem ↔
      termsem0 mem (tmsof sig) i v s = termsem0 mem (tmsof sig) i v t := by
  rw [termsem_equation mem hm sig i v s t _ ⟨hs, hok, rfl⟩, boolean_eq_true mem hm]

theorem Aux.sem_typesem [Nonempty U] {mem : U → U → Prop} (hm : is_set_theory mem) {sig : sig}
    {i : interpretation U} {v : valuation U} {t : term} (hs : is_structure0 mem sig i v)
    (hok : term_ok sig t) :
    mem (termsem0 mem (tmsof sig) i v t) (typesem i.1 v.1 (typeof t)) :=
  termsem_typesem mem hm sig i t v i.1 v.1 _ ⟨rfl, rfl, hs.2.2.2, hs.2.2.1,
    is_std_interpretation_is_type mem i hs.2.1, hok, rfl⟩

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
  rintro hm thy h1 h2 p1 p2 q ⟨hq, hok, hs, e1, e2⟩
  obtain ⟨a1, _, a3, _, a5, a6, a7⟩ := Aux.entails_elim e1
  obtain ⟨_, _, b3, _, b5, b6, b7⟩ := Aux.entails_elim e2
  refine Aux.entails_intro a1 hok ?_ hq ?_ (hypset_ok_term_union _ _ ⟨a6, b6⟩) ?_
  · intro t ht
    rcases MEM_term_union_imp _ _ _ ht with h | h
    · exact a3 t h
    · exact b3 t h
  · intro t ht
    rcases MEM_term_union_imp _ _ _ ht with h | h
    · exact a5 t h
    · exact b5 t h
  · intro i v hmod hv hh
    have hu := Aux.sem_union a6 b6 a3 b3 hh
    exact hs i v ⟨Aux.structure_of a1 hmod hv, a7 i v hmod hv (fun t ht => hu t (Or.inl ht)),
      b7 i v hmod hv (fun t ht => hu t (Or.inr ht))⟩

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
  rintro hm thy x ty h l r ⟨hn, hty, e⟩
  obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := Aux.entails_elim e
  have hsig := theory_ok_sig thy a1
  obtain ⟨k1, k2, k3⟩ := (term_ok_equation _ l r hsig).mp a2
  obtain ⟨w1, w2, _⟩ := (EQUATION_HAS_TYPE_BOOL l r).mp a4
  have hok : term_ok (sigof thy) (equation (Abs (Var x ty) l) (Abs (Var x ty) r)) := by
    refine (term_ok_equation _ _ _ hsig).mpr ⟨⟨x, ty, rfl, hty, k1⟩, ⟨x, ty, rfl, hty, k2⟩, ?_⟩
    simp only [typeof, k3]
  have hbool : has_type (equation (Abs (Var x ty) l) (Abs (Var x ty) r)) BoolTy := by
    refine (EQUATION_HAS_TYPE_BOOL _ _).mpr ⟨Aux.welltyped_Abs.mpr ⟨x, ty, rfl, w1⟩,
      Aux.welltyped_Abs.mpr ⟨x, ty, rfl, w2⟩, ?_⟩
    simp only [typeof, k3]
  refine Aux.entails_intro a1 hok a3 hbool a5 a6 ?_
  intro i v hmod hv hh
  refine (Aux.sem_equation hm (Aux.structure_of a1 hmod hv) hok).mpr ?_
  rw [Aux.termsem_Abs, Aux.termsem_Abs]
  apply abstract_eq mem hm
  intro m hmm
  have hv' : is_valuation0 mem (thy_tysof thy) (tyaof i) (v.1, UPDATE (x, ty) m v.2) :=
    Aux.is_valuation_update hv hmm
  have hst := Aux.structure_of a1 hmod hv'
  refine ⟨Aux.sem_typesem hm hst k1, Aux.sem_typesem hm hst k2, ?_⟩
  refine (Aux.sem_equation hm hst a2).mp (a7 i _ hmod hv' ?_)
  intro t ht
  rw [← hh t ht]
  refine termsem_frees mem _ i t _ _ ⟨term_ok_welltyped _ _ (a3 t ht), rfl, fun y t' hf => ?_⟩
  refine Aux.UPDATE_ne _ _ (fun e => hn ?_)
  cases e
  exact (Aux.EXISTS_iff _ _).mpr ⟨t, ht, hf⟩

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
  refine Aux.entails_intro h1 h3 ?_ h2 ?_ (hypset_ok_sing p) ?_
  · intro t ht; rw [List.mem_singleton.mp ht]; exact h3
  · intro t ht; rw [List.mem_singleton.mp ht]; exact h2
  · intro i v _ _ hh; exact hh p List.mem_cons_self

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
  rintro hm thy x ty t ⟨h1, h2, h3⟩
  have hsig := theory_ok_sig thy h1
  have wt := term_ok_welltyped _ _ h3
  have hty : has_type (Comb (Abs (Var x ty) t) (Var x ty)) (typeof t) :=
    has_type.Comb (has_type.Abs ((WELLTYPED t).mp wt)) has_type.Var
  have hokc : term_ok (sigof thy) (Comb (Abs (Var x ty) t) (Var x ty)) :=
    ⟨⟨x, ty, rfl, h2, h3⟩, h2, _, hty⟩
  have hok : term_ok (sigof thy) (equation (Comb (Abs (Var x ty) t) (Var x ty)) t) :=
    (term_ok_equation _ _ _ hsig).mpr ⟨hokc, h3, rfl⟩
  have hbool : has_type (equation (Comb (Abs (Var x ty) t) (Var x ty)) t) BoolTy :=
    (EQUATION_HAS_TYPE_BOOL _ _).mpr ⟨⟨_, hty⟩, wt, rfl⟩
  refine Aux.entails_intro h1 hok (by simp) hbool (by simp) hypset_ok_nil ?_
  intro i v hmod hv _
  refine (Aux.sem_equation hm (Aux.structure_of h1 hmod hv) hok).mpr ?_
  rw [Aux.termsem_Comb, Aux.termsem_Abs, Aux.termsem_Var]
  have hmx : mem (v.2 (x, ty)) (typesem i.1 v.1 ty) := hv.2 x ty h2
  have hst := Aux.structure_of h1 hmod (Aux.is_valuation_update (x := x) hv hmx)
  rw [apply_abstract mem hm
    (fun m => termsem0 mem (tmsof (sigof thy)) i (v.1, UPDATE (x, ty) m v.2) t) _ _ _
    ⟨hmx, Aux.sem_typesem hm hst h3⟩]
  refine termsem_frees mem _ i t _ _ ⟨wt, rfl, fun y t' _ => ?_⟩
  show UPDATE (x, ty) (v.2 (x, ty)) v.2 (y, t') = v.2 (y, t')
  by_cases e : (x, ty) = (y, t')
  · rw [← e, Aux.UPDATE_eq]
  · rw [Aux.UPDATE_ne _ _ e]

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
  rintro hm thy h1 p1 h2 p2 ⟨e1, e2⟩
  obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := Aux.entails_elim e1
  obtain ⟨_, b2, b3, b4, b5, b6, b7⟩ := Aux.entails_elim e2
  have hsig := theory_ok_sig thy a1
  have t1 := WELLTYPED_LEMMA _ _ a4
  have t2 := WELLTYPED_LEMMA _ _ b4
  have w1 := term_ok_welltyped _ _ a2
  have w2 := term_ok_welltyped _ _ b2
  have hok : term_ok (sigof thy) (equation p1 p2) :=
    (term_ok_equation _ _ _ hsig).mpr ⟨a2, b2, by rw [t1, t2]⟩
  have hbool : has_type (equation p1 p2) BoolTy :=
    (EQUATION_HAS_TYPE_BOOL _ _).mpr ⟨w1, w2, by rw [t1, t2]⟩
  have r1 : ∀ t, t ∈ term_remove p2 h1 → t ∈ h1 := fun t ht => (MEM_term_remove_imp _ _ _ ht).1
  have r2 : ∀ t, t ∈ term_remove p1 h2 → t ∈ h2 := fun t ht => (MEM_term_remove_imp _ _ _ ht).1
  have k1 := hypset_ok_term_remove h1 a6 p2
  have k2 := hypset_ok_term_remove h2 b6 p1
  refine Aux.entails_intro a1 hok ?_ hbool ?_ (hypset_ok_term_union _ _ ⟨k1, k2⟩) ?_
  · intro t ht
    rcases MEM_term_union_imp _ _ _ ht with h | h
    · exact a3 t (r1 t h)
    · exact b3 t (r2 t h)
  · intro t ht
    rcases MEM_term_union_imp _ _ _ ht with h | h
    · exact a5 t (r1 t h)
    · exact b5 t (r2 t h)
  · intro i v hmod hv hh
    have hst := Aux.structure_of a1 hmod hv
    have hu := Aux.sem_union k1 k2 (fun t ht => a3 t (r1 t ht)) (fun t ht => b3 t (r2 t ht)) hh
    refine (Aux.sem_equation hm hst hok).mpr ?_
    have i1 : termsem0 mem (thy_tmsof thy) i v p2 = true_ mem →
        termsem0 mem (thy_tmsof thy) i v p1 = true_ mem := by
      intro hp
      refine a7 i v hmod hv (fun t ht => ?_)
      by_cases ha : ACONV p2 t
      · rw [← termsem_aconv mem _ i v p2 t ⟨ha, w2, term_ok_welltyped _ _ (a3 t ht)⟩]
        exact hp
      · exact hu t (Or.inl (MEM_term_remove h1 p2 t ⟨ht, ha, a6⟩))
    have i2 : termsem0 mem (thy_tmsof thy) i v p1 = true_ mem →
        termsem0 mem (thy_tmsof thy) i v p2 = true_ mem := by
      intro hp
      refine b7 i v hmod hv (fun t ht => ?_)
      by_cases ha : ACONV p1 t
      · rw [← termsem_aconv mem _ i v p1 t ⟨ha, w1, term_ok_welltyped _ _ (b3 t ht)⟩]
        exact hp
      · exact hu t (Or.inr (MEM_term_remove h2 p1 t ⟨ht, ha, b6⟩))
    have hta := is_std_interpretation_is_type mem i hst.2.1
    have m1 := Aux.sem_typesem hm hst a2
    have m2 := Aux.sem_typesem hm hst b2
    rw [t1, typesem_Bool mem _ _ hta, mem_boolset mem hm] at m1
    rw [t2, typesem_Bool mem _ _ hta, mem_boolset mem hm] at m2
    rcases m1 with m1 | m1
    · rw [m1]; exact (i2 m1).symm
    · rcases m2 with m2 | m2
      · rw [m2]; exact i1 m2
      · rw [m1, m2]

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
  rintro hm thy h1 h2 p q p' ⟨e1, e2, ha⟩
  obtain ⟨a1, a2, _, a4, _, _, _⟩ := Aux.entails_elim e1
  obtain ⟨_, b2, _, b4, _, _, _⟩ := Aux.entails_elim e2
  have hsig := theory_ok_sig thy a1
  obtain ⟨_, k2, k3⟩ := (term_ok_equation _ p q hsig).mp a2
  obtain ⟨w1, w2, _⟩ := (EQUATION_HAS_TYPE_BOOL p q).mp a4
  have w3 := term_ok_welltyped _ _ b2
  have hq : has_type q BoolTy := by
    have := (WELLTYPED q).mp w2
    rw [k3, ACONV_TYPE p p' ha ⟨w1, w3⟩, WELLTYPED_LEMMA _ _ b4] at this
    exact this
  refine binary_inference_rule mem hm thy h1 h2 (equation p q) p' q ⟨hq, k2, ?_, e1, e2⟩
  rintro i v ⟨hst, s1, s2⟩
  have s3 := (Aux.sem_equation hm hst a2).mp s1
  show termsem0 mem (tmsof (sigof thy)) i v q = _
  rw [← s3, termsem_aconv mem _ i v p p' ⟨ha, w1, w3⟩]
  exact s2

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
  rintro hm thy h c ⟨hi, e⟩
  obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := Aux.entails_elim e
  have hi2 : ∀ s s', (s', s) ∈ ilist → ∃ x ty, s = Var x ty ∧ has_type s' ty := by
    intro s s' hmem
    obtain ⟨x, ty, e1, e2, _⟩ := hi s s' hmem
    exact ⟨x, ty, e1, e2⟩
  have hi3 : ∀ s s', (s', s) ∈ ilist → ∃ x ty, s = Var x ty := by
    intro s s' hmem
    obtain ⟨x, ty, e1, _⟩ := hi s s' hmem
    exact ⟨x, ty, e1⟩
  refine Aux.entails_intro a1 (term_ok_VSUBST _ c ilist ⟨a2, hi⟩) ?_
    (VSUBST_HAS_TYPE c _ ilist ⟨a4, hi2⟩) ?_ (hypset_ok_term_image h _ a6) ?_
  · intro t ht
    obtain ⟨s, hs, rfl⟩ := MEM_term_image_imp _ _ _ ht
    exact term_ok_VSUBST _ s ilist ⟨a3 s hs, hi⟩
  · intro t ht
    obtain ⟨s, hs, rfl⟩ := MEM_term_image_imp _ _ _ ht
    exact VSUBST_HAS_TYPE s _ ilist ⟨a5 s hs, hi2⟩
  · intro i v hmod hv hh
    have hst := Aux.structure_of a1 hmod hv
    rw [termsem_VSUBST mem c ilist ⟨term_ok_welltyped _ _ a2, hi2⟩]
    refine a7 i _ hmod ⟨hv.1, fun x ty hty => ?_⟩ (fun t ht => ?_)
    · show mem (UPDATE_LIST v.2 _ (x, ty)) (typesem i.1 v.1 ty)
      rw [Aux.UPDATE_LIST_ilist mem _ i v x ty ilist hi3]
      rcases REV_ASSOCD_MEM ilist (Var x ty) (Var x ty) with hmem | hmem
      · obtain ⟨y, t, e1, e2, e3⟩ := hi _ _ hmem
        obtain ⟨rfl, rfl⟩ := term.Var.inj e1
        have := Aux.sem_typesem hm hst e3
        rw [WELLTYPED_LEMMA _ _ e2] at this
        exact this
      · rw [hmem, Aux.termsem_Var]
        exact hv.2 x ty hty
    · rw [← termsem_VSUBST mem t ilist ⟨term_ok_welltyped _ _ (a3 t ht), hi2⟩]
      obtain ⟨y, hy, ha⟩ := MEM_term_image h (VSUBST ilist) t ⟨ht, a6⟩
      obtain ⟨s, hs, rfl⟩ := MEM_term_image_imp _ _ _ hy
      rw [termsem_aconv mem _ i v _ _ ⟨ha,
        VSUBST_WELLTYPED t (Tyvar default) ilist ⟨term_ok_welltyped _ _ (a3 t ht), hi2⟩,
        VSUBST_WELLTYPED s (Tyvar default) ilist ⟨term_ok_welltyped _ _ (a3 s hs), hi2⟩⟩]
      exact hh _ hy

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
  rintro hm thy h c ⟨hi, e⟩
  obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := Aux.entails_elim e
  have hbool : ∀ t, has_type t BoolTy → has_type (INST tyin t) BoolTy := fun t ht =>
    INST_HAS_TYPE t BoolTy tyin BoolTy ⟨ht, (TYPE_SUBST_Bool tyin).symm⟩
  refine Aux.entails_intro a1 (term_ok_INST _ tyin c ⟨a2, hi⟩) ?_ (hbool c a4) ?_
    (hypset_ok_term_image h _ a6) ?_
  · intro t ht
    obtain ⟨s, hs, rfl⟩ := MEM_term_image_imp _ _ _ ht
    exact term_ok_INST _ tyin s ⟨a3 s hs, hi⟩
  · intro t ht
    obtain ⟨s, hs, rfl⟩ := MEM_term_image_imp _ _ _ ht
    exact hbool s (a5 s hs)
  · intro i v hmod hv hh
    rw [termsem_INST mem (sigof thy) c tyin _ ⟨a2, rfl⟩ i v]
    refine a7 i _ hmod ⟨fun x => ?_, fun x ty hty => ?_⟩ (fun t ht => ?_)
    · refine typesem_inhabited mem hm (thy_tysof thy) i.1 v.1 _ ⟨hv.1, hmod.1.1, ?_⟩
      apply type_ok_TYPE_SUBST
      exact ⟨by rw [type_ok]; trivial, hi⟩
    · show mem (v.2 (x, TYPE_SUBST tyin ty)) (typesem i.1 _ ty)
      rw [← typesem_TYPE_SUBST]
      exact hv.2 x _ (type_ok_TYPE_SUBST _ tyin ty ⟨hty, hi⟩)
    · rw [← termsem_INST mem (sigof thy) t tyin _ ⟨a3 t ht, rfl⟩ i v]
      obtain ⟨y, hy, ha⟩ := MEM_term_image h (INST tyin) t ⟨ht, a6⟩
      obtain ⟨s, hs, rfl⟩ := MEM_term_image_imp _ _ _ hy
      rw [termsem_aconv mem _ i v _ _ ⟨ha,
        INST_WELLTYPED t tyin (term_ok_welltyped _ _ (a3 t ht)),
        INST_WELLTYPED s tyin (term_ok_welltyped _ _ (a3 s hs))⟩]
      exact hh _ hy

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
  rintro hm thy h1 h2 l1 r1 l2 r2 ⟨e1, e2, hw⟩
  obtain ⟨a1, a2, _, a4, _, _, _⟩ := Aux.entails_elim e1
  obtain ⟨_, b2, _, b4, _, _, _⟩ := Aux.entails_elim e2
  have hsig := theory_ok_sig thy a1
  obtain ⟨k1, k2, k3⟩ := (term_ok_equation _ _ _ hsig).mp a2
  obtain ⟨j1, j2, j3⟩ := (term_ok_equation _ _ _ hsig).mp b2
  obtain ⟨w1, w2, rty, hr⟩ := Aux.welltyped_Comb.mp hw
  have hw2 : welltyped (Comb r1 r2) :=
    Aux.welltyped_Comb.mpr ⟨term_ok_welltyped _ _ k2, term_ok_welltyped _ _ j2, rty, by rw [k3, j3, hr]⟩
  have ht : typeof (Comb r1 r2) = typeof (Comb l1 l2) := by simp only [typeof, k3]
  have hok : term_ok (sigof thy) (equation (Comb l1 l2) (Comb r1 r2)) :=
    (term_ok_equation _ _ _ hsig).mpr ⟨⟨k1, j1, hw⟩, ⟨k2, j2, hw2⟩, ht⟩
  refine binary_inference_rule mem hm thy h1 h2 (equation l1 r1) (equation l2 r2) _
    ⟨(EQUATION_HAS_TYPE_BOOL _ _).mpr ⟨hw, hw2, ht.symm⟩, hok, ?_, e1, e2⟩
  rintro i v ⟨hst, s1, s2⟩
  refine (Aux.sem_equation hm hst hok).mpr ?_
  rw [Aux.termsem_Comb, Aux.termsem_Comb, (Aux.sem_equation hm hst a2).mp s1,
    (Aux.sem_equation hm hst b2).mp s2]

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
  rintro hm thy t ⟨h1, h2⟩
  have hsig := theory_ok_sig thy h1
  have wt := term_ok_welltyped _ _ h2
  have hok : term_ok (sigof thy) (equation t t) := (term_ok_equation _ _ _ hsig).mpr ⟨h2, h2, rfl⟩
  refine Aux.entails_intro h1 hok (by simp) ((EQUATION_HAS_TYPE_BOOL _ _).mpr ⟨wt, wt, rfl⟩)
    (by simp) hypset_ok_nil ?_
  intro i v hmod hv _
  exact (Aux.sem_equation hm (Aux.structure_of h1 hmod hv) hok).mpr rfl

/- HOL4:
Theorem proves_sound:
   is_set_theory ^mem ⇒ ∀thyh c. thyh |- c ⇒ thyh |= c
-/
theorem proves_sound [Nonempty U] (mem : U → U → Prop) :
    is_set_theory mem →
      ∀ (thyh : thy × List term) (c : term), proves thyh c → entails0 mem thyh c := by
  intro hm thyh c h
  induction h with
  | ABS h1 h2 _ ih => exact ABS_correct mem hm _ _ _ _ _ _ ⟨h1, h2, ih⟩
  | ASSUME h1 h2 h3 => exact ASSUME_correct mem _ _ ⟨h1, h2, h3⟩
  | BETA h1 h2 h3 => exact BETA_correct mem hm _ _ _ _ ⟨h1, h2, h3⟩
  | DEDUCT_ANTISYM _ _ ih1 ih2 => exact DEDUCT_ANTISYM_correct mem hm _ _ _ _ _ ⟨ih1, ih2⟩
  | EQ_MP _ _ ha ih1 ih2 => exact EQ_MP_correct mem hm _ _ _ _ _ _ ⟨ih1, ih2, ha⟩
  | INST hi _ ih => exact INST_correct mem _ hm _ _ _ ⟨hi, ih⟩
  | INST_TYPE hi _ ih => exact INST_TYPE_correct mem _ hm _ _ _ ⟨hi, ih⟩
  | MK_COMB _ _ hw ih1 ih2 => exact MK_COMB_correct mem hm _ _ _ _ _ _ _ ⟨ih1, ih2, hw⟩
  | REFL h1 h2 => exact REFL_correct mem hm _ _ ⟨h1, h2⟩
  | «axioms» h1 h2 =>
    refine Aux.entails_intro h1 (h1.2.1 _ h2).1 (by simp) (h1.2.1 _ h2).2 (by simp) hypset_ok_nil ?_
    intro i v hmod hv _
    exact hmod.2.2 _ h2 v ⟨hv, trivial⟩

end

end Candle
