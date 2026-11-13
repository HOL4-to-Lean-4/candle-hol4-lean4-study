(*
  Some lemmas about the semantics.
*)
Theory holSemanticsExtra
Ancestors
  holSyntaxLib holSyntax holSyntaxExtra holSemantics setSpec
Libs
  preamble

val _ = temp_delsimps ["NORMEQ_CONV"]
val _ = diminish_srw_ss ["ABBREV"]

val _ = Parse.hide "mem";

val mem = ``mem:'U->'U->bool``

Theorem is_std_interpretation_is_type:
   is_std_interpretation i ⇒ is_std_type_assignment (FST i)
Proof
  Cases_on`i` >> simp[is_std_interpretation_def]
QED

(* typesem *)

Theorem typesem_inhabited:
   is_set_theory ^mem ⇒
    ∀tyenv δ τ ty.
    is_type_valuation τ ∧
    is_type_assignment tyenv δ ∧
    type_ok tyenv ty
    ⇒
    inhabited (typesem δ τ ty)
Proof
  strip_tac >> gen_tac >> ho_match_mp_tac typesem_ind >>
  simp[typesem_def,is_type_valuation_def,type_ok_def] >>
  rw[is_type_assignment_def,FLOOKUP_DEF] >>
  fs[FEVERY_ALL_FLOOKUP,FLOOKUP_DEF] >>
  first_x_assum(qspec_then`name`mp_tac) >> simp[] >>
  disch_then match_mp_tac >>
  simp[EVERY_MAP] >> fs[EVERY_MEM] >> metis_tac[]
QED

Theorem typesem_Fun:
   ∀δ τ dom rng.
    is_std_type_assignment δ ⇒
    typesem δ τ (Fun dom rng) =
    Funspace (typesem δ τ dom) (typesem δ τ rng)
Proof
  rw[is_std_type_assignment_def,typesem_def]
QED

Theorem typesem_Bool:
   ∀δ τ.
    is_std_type_assignment δ ⇒
    typesem δ τ Bool = boolset
Proof
  rw[is_std_type_assignment_def,typesem_def]
QED

Theorem typesem_TYPE_SUBST:
   ∀tyin ty δ τ.
      typesem δ τ (TYPE_SUBST tyin ty) =
      typesem δ (λx. typesem δ τ (TYPE_SUBST tyin (Tyvar x))) ty
Proof
  ho_match_mp_tac TYPE_SUBST_ind >> simp[typesem_def] >>
  rw[] >> rpt AP_TERM_TAC >>
  simp[MAP_MAP_o,MAP_EQ_f]
QED

Theorem typesem_tyvars:
   ∀δ τ ty τ'.
    (∀x. MEM x (tyvars ty) ⇒ τ' x = τ x) ⇒
    typesem δ τ' ty = typesem δ τ ty
Proof
  ho_match_mp_tac typesem_ind >>
  simp[tyvars_def,MEM_FOLDR_LIST_UNION,typesem_def] >>
  rw[] >> rpt AP_TERM_TAC >> rw[MAP_EQ_f] >>
  metis_tac[]
QED

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
Proof
  strip_tac >> ntac 2 Cases >> Induct
  >- (
    Cases_on`v`>>
    simp[termsem_def,is_valuation_def,is_term_valuation_def,term_ok_def] )
  >- (
    Cases_on`v`>>
    simp[termsem_def,term_ok_def] >> rw[] >>
    qmatch_abbrev_tac`instance sig ii name ty τ <: X` >>
    qspecl_then[`sig`,`ii`,`name`,`ty`]mp_tac instance_def >>
    rw[Abbr`ty`,Abbr`ii`,Abbr`sig`] >>
    simp[Once typesem_TYPE_SUBST,Abbr`X`,combinTheory.o_DEF] >>
    qmatch_abbrev_tac`X <: typesem δ τi ty0` >>
    fs[is_interpretation_def,is_term_assignment_def,FEVERY_ALL_FLOOKUP] >>
    first_x_assum (qspecl_then[`name`,`ty0`]mp_tac) >>
    simp[] >> disch_then(qspec_then`λx. if MEM x (tyvars ty0) then τi x else boolset`mp_tac) >>
    simp[Abbr`X`,Abbr`τi`] >>
    impl_tac >- (
      fs[is_type_valuation_def] >>
      reverse(rw[])>-metis_tac[mem_boolset]>>
      match_mp_tac (UNDISCH typesem_inhabited) >>
      imp_res_tac type_ok_TYPE_SUBST_imp >>
      fs[is_valuation_def] >> metis_tac[] ) >>
    qmatch_abbrev_tac`a <: b ⇒ a' <: b'` >>
    `a' = a` by (
      unabbrev_all_tac >> rpt AP_TERM_TAC >> simp[MAP_EQ_f] >>
      simp[MEM_MAP,PULL_EXISTS,mlstringTheory.implode_explode]) >>
    `b' = b` by (
      unabbrev_all_tac >>
      match_mp_tac typesem_tyvars >> rw[] ) >>
    rw[] )
  >- (
    simp[termsem_def,term_ok_def] >>
    rw[] >> imp_res_tac typesem_Fun >> fs[] >>
    match_mp_tac (UNDISCH apply_in_rng) >>
    metis_tac[]) >>
  simp[termsem_def,term_ok_def] >>
  rw[] >> imp_res_tac typesem_Fun >> rw[] >>
  simp[termsem_def] >>
  match_mp_tac (UNDISCH abstract_in_funspace) >>
  fs[] >> rw[] >>
  Q.PAT_ABBREV_TAC`vv = (X:'U valuation)` >>
  first_x_assum (qspec_then`vv`mp_tac) >>
  simp[Abbr`vv`] >> disch_then match_mp_tac >>
  Cases_on`v`>> fs[is_valuation_def,is_term_valuation_def] >>
  rw[combinTheory.APPLY_UPDATE_THM] >> rw[]
QED

val Equalsem =
  is_std_interpretation_def
  |> SPEC_ALL |> concl |> rhs
  |> strip_conj |> last
  |> strip_comb |> snd |> last

Theorem termsem_Equal:
   is_set_theory ^mem ⇒
    ∀Γ i v ty.
      is_structure Γ i v ∧ type_ok (tysof Γ) ty ⇒
      termsem (tmsof Γ) i v (Equal ty) = ^Equalsem [typesem (FST i) (FST v) ty]
Proof
  rw[termsem_def,LET_THM] >> fs[is_structure_def] >>
  qspecl_then[`tmsof Γ`,`i`,`«=»`]mp_tac instance_def >> fs[is_std_sig_def]>>
  disch_then(qspec_then`[(ty,Tyvar «A»)]`mp_tac)>>
  simp[REV_ASSOCD] >> disch_then kall_tac >>
  Q.PAT_ABBREV_TAC`aa = tyvars X` >>
  `aa = [«A»]` by simp[tyvars_def,Abbr`aa`,LIST_UNION_def,LIST_INSERT_def] >>
  Q.PAT_ABBREV_TAC`tt = typesem (tyaof i) Y o TYPE_SUBST Z o Tyvar` >>
  `is_type_valuation tt` by (
    simp[Abbr`tt`,is_type_valuation_def] >>
    rw[REV_ASSOCD,typesem_def] >- (
      match_mp_tac (UNDISCH typesem_inhabited) >>
      fs[is_valuation_def,is_interpretation_def] >>
      metis_tac[] ) >>
    fs[is_valuation_def,is_type_valuation_def] ) >>
  qunabbrev_tac`aa` >>
  fs[is_std_interpretation_def,interprets_def] >>
  `MAP implode (STRING_SORT ["A"]) = [«A»]` by
    simp[STRING_SORT_def,INORDER_INSERT_def] >>
  simp[] >> simp[Abbr`tt`,REV_ASSOCD]
QED

(* equations *)

Theorem termsem_equation:
   is_set_theory ^mem ⇒
    ∀sig i v s t tmenv.
    is_structure sig i v ∧
    term_ok sig (s === t) ∧
    tmenv = tmsof sig
    ⇒ termsem tmenv i v (s === t) = Boolean (termsem tmenv i v s = termsem tmenv i v t)
Proof
  rw[] >>
  `is_std_sig sig ∧ is_std_interpretation i` by fs[is_structure_def] >>
  fs[term_ok_equation] >>
  imp_res_tac term_ok_type_ok >>
  simp[equation_def,termsem_def,termsem_Equal] >>
  imp_res_tac is_std_interpretation_is_type >>
  qho_match_abbrev_tac`Abstract a b f ' x ' y = z` >>
  `Abstract a b f ' x = f x` by (
    match_mp_tac (UNDISCH apply_abstract) >>
    unabbrev_all_tac >> simp[] >>
    conj_tac >- metis_tac[is_structure_def,termsem_typesem] >>
    match_mp_tac (UNDISCH abstract_in_funspace) >>
    simp[boolean_in_boolset] ) >>
  simp[Abbr`f`,Abbr`b`] >>
  qho_match_abbrev_tac`Abstract a b f ' y = z` >>
  `Abstract a b f ' y = f y `  by (
    match_mp_tac (UNDISCH apply_abstract) >>
    unabbrev_all_tac >> simp[] >>
    metis_tac[termsem_typesem,boolean_in_boolset,is_structure_def] ) >>
  unabbrev_all_tac >> simp[]
QED

(* aconv *)

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
Proof
  ho_match_mp_tac RACONV_strongind >>
  rpt conj_tac >> simp[termsem_def] >>
  TRY (metis_tac[]) >>
  rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  qmatch_assum_abbrev_tac`RACONV env1 p1` >>
  qspecl_then[`env1`,`p1`]mp_tac RACONV_TYPE >>
  simp[Abbr`env1`,Abbr`p1`] >> strip_tac >>
  rw[termsem_def] >> fs[] >> rw[] >>
  rw[FUN_EQ_THM] >> rpt AP_TERM_TAC >>
  rw[FUN_EQ_THM] >>
  first_x_assum (match_mp_tac o MP_CANON) >>
  simp[ALPHAVARS_def,combinTheory.APPLY_UPDATE_THM] >>
  rw[] >> fs[]
QED

Theorem termsem_aconv:
   ∀Γ i v t1 t2. ACONV t1 t2 ∧ welltyped t1 ∧ welltyped t2 ⇒ termsem Γ i v t1 = termsem Γ i v t2
Proof
  rw[ACONV_def] >>
  imp_res_tac termsem_raconv >>
  rfs[ALPHAVARS_def] >>
  metis_tac[ACONV_def]
QED

(* semantics only depends on valuation of free variables *)

Theorem termsem_frees:
   ∀Γ i t v1 v2.
      welltyped t ∧ FST v1 = FST v2 ∧
      (∀x ty. VFREE_IN (Var x ty) t ⇒ SND v1 (x,ty) = SND v2 (x,ty))
      ⇒ termsem Γ i v1 t = termsem Γ i v2 t
Proof
  ntac 2 gen_tac >> Induct >>
  simp[termsem_def] >- metis_tac[] >>
  rw[] >> rw[termsem_def] >> rpt AP_TERM_TAC >>
  rw[FUN_EQ_THM] >>
  first_x_assum match_mp_tac >>
  rw[combinTheory.APPLY_UPDATE_THM,FUN_EQ_THM] >>
  first_x_assum match_mp_tac >> fs[]
QED

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
Proof
  Induct >> simp[termsem_def] >- (
    simp[REV_ASSOCD_ALOOKUP,APPLY_UPDATE_LIST_ALOOKUP,rich_listTheory.MAP_REVERSE] >>
    rw[] >> BasicProvers.CASE_TAC >> rw[termsem_def] >- (
      imp_res_tac ALOOKUP_FAILS >>
      BasicProvers.CASE_TAC >>
      imp_res_tac ALOOKUP_MEM >>
      fs[MEM_MAP,EXISTS_PROD] >>
      res_tac >> fs[] >> metis_tac[] ) >>
    rw[GSYM MAP_MAP_o] >>
    qmatch_assum_abbrev_tac`ALOOKUP ls (Var s ty) = SOME x` >>
    Q.ISPECL_THEN[`ls`,`termsem Γ i v`,`s`,`ty`]mp_tac ALOOKUP_MAP_dest_var >>
    impl_tac >- (simp[EVERY_MAP,EVERY_MEM,FORALL_PROD,Abbr`ls`] >> metis_tac[]) >>
    rw[]) >>
  rw[] >>
  Q.PAT_ABBREV_TAC`il = FILTER X ilist` >>
  qmatch_assum_rename_tac`welltyped tm` >>
  `simple_subst il tm has_type typeof tm` by (
    match_mp_tac (MP_CANON simple_subst_has_type) >>
    imp_res_tac WELLTYPED >>
    fs[Abbr`il`,EVERY_MEM,EVERY_FILTER,FORALL_PROD] >>
    rw[] >> res_tac >> rw[] ) >>
  imp_res_tac WELLTYPED_LEMMA >> rw[] >>
  simp[termsem_def] >>
  rpt AP_TERM_TAC >> simp[FUN_EQ_THM] >> rw[] >>
  qmatch_abbrev_tac `termsem Γ i vv xx = yy` >>
  first_x_assum(qspec_then`il`mp_tac) >>
  impl_tac >- (
    simp[Abbr`il`] >> fs[IN_DISJOINT,MEM_FILTER,MEM_MAP,EXISTS_PROD] >>
    metis_tac[] ) >>
  disch_then(qspecl_then[`Γ`,`i`,`vv`]mp_tac) >>
  rw[Abbr`vv`,Abbr`yy`] >>
  rpt AP_THM_TAC >> rpt AP_TERM_TAC >>
  simp[FUN_EQ_THM,APPLY_UPDATE_LIST_ALOOKUP,rich_listTheory.MAP_REVERSE] >>
  Cases >> rename1 `ALOOKUP _ (z,tyr)` >>
  simp[GSYM MAP_MAP_o] >>
  BasicProvers.CASE_TAC >>
  qmatch_assum_abbrev_tac`ALOOKUP (MAP (dest_var ## f) ls) (z,tyr) = X` >>
  qunabbrev_tac`X` >>
  Q.ISPECL_THEN[`ls`,`f`,`z`,`tyr`]mp_tac ALOOKUP_MAP_dest_var >>
  (impl_tac >- (simp[EVERY_MAP,EVERY_MEM,FORALL_PROD,Abbr`ls`,Abbr`il`,MEM_FILTER] >> metis_tac[])) >>
  qmatch_assum_abbrev_tac`Abbrev(il = FILTER P ilist)` >>
  qmatch_assum_abbrev_tac`Abbrev(ls = MAP sw il)` >>
  `ls = FILTER (P o sw) (MAP sw ilist)` by (
    simp[Abbr`ls`,Abbr`il`] >>
    simp[rich_listTheory.FILTER_MAP] >>
    simp[Abbr`P`,Abbr`sw`,combinTheory.o_DEF,UNCURRY,LAMBDA_PROD] ) >>
  qunabbrev_tac`ls` >>
  simp[ALOOKUP_FILTER,Abbr`P`,Abbr`sw`,combinTheory.o_DEF,LAMBDA_PROD] >- (
    simp[IF_NONE_EQUALS_OPTION] >>
    rw[combinTheory.APPLY_UPDATE_THM,APPLY_UPDATE_LIST_ALOOKUP] >>
    qmatch_assum_abbrev_tac`P ⇒ ALOOKUP ls vv = NONE` >>
    Q.ISPECL_THEN[`ls`,`termsem Γ i v`,`z`,`tyr`]mp_tac ALOOKUP_MAP_dest_var >>
    impl_tac >- (simp[EVERY_MAP,EVERY_MEM,FORALL_PROD,Abbr`ls`] >> metis_tac[]) >>
    rw[] >> fs[Abbr`P`] ) >>
  simp[combinTheory.APPLY_UPDATE_THM,APPLY_UPDATE_LIST_ALOOKUP] >>
  rw[Abbr`f`] >>
  qmatch_assum_abbrev_tac`ALOOKUP ls vv = SOME zz` >>
  Q.ISPECL_THEN[`ls`,`termsem Γ i v`,`z`,`tyr`]mp_tac ALOOKUP_MAP_dest_var >>
  (impl_tac >- (simp[EVERY_MAP,EVERY_MEM,FORALL_PROD,Abbr`ls`] >> metis_tac[])) >>
  rw[] >> fs[Abbr`zz`] >>
  match_mp_tac termsem_frees >>
  rw[combinTheory.APPLY_UPDATE_THM] >>
  imp_res_tac ALOOKUP_MEM >>
  fs[Abbr`ls`,MEM_MAP,FORALL_PROD,EXISTS_PROD] >>
  metis_tac[welltyped_def]
QED

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
Proof
  rw[] >>
  Q.ISPECL_THEN[`{y | ∃ty u. VFREE_IN (Var y ty) u ∧ MEM u (MAP FST ilist)}`,`tm`]mp_tac fresh_term_def >>
  simp[] >>
  Q.PAT_ABBREV_TAC`fm = fresh_term X tm` >> strip_tac >>
  `ACONV (VSUBST ilist tm) (VSUBST ilist fm)` by (
    match_mp_tac ACONV_VSUBST >> metis_tac[] ) >>
  `welltyped (VSUBST ilist tm)` by metis_tac[VSUBST_WELLTYPED] >>
  `welltyped (VSUBST ilist fm)` by metis_tac[VSUBST_WELLTYPED] >>
  `termsem Γ i v (VSUBST ilist tm) = termsem Γ i v (VSUBST ilist fm)` by
    metis_tac[termsem_aconv] >>
  `VSUBST ilist fm = simple_subst ilist fm` by
    metis_tac[VSUBST_simple_subst] >>
  rw[] >>
  metis_tac[termsem_simple_subst,termsem_aconv]
QED

(* semantics of instantiation *)

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
Proof
  Cases >> Induct >> simp[termsem_def,term_ok_def] >- (
    rw[] >> rw[TYPE_SUBST_compose] >>
    qmatch_abbrev_tac`instance sig int name (TYPE_SUBST i2 ty0) t1 =
                      instance sig int name (TYPE_SUBST i1 ty0) t2` >>
    qspecl_then[`sig`,`int`,`name`]mp_tac instance_def >> simp[Abbr`sig`,Abbr`t2`] >>
    disch_then kall_tac >> rpt AP_TERM_TAC >> rw[FUN_EQ_THM,MAP_EQ_f] >> rw[] >>
    rw[Once REV_ASSOCD_ALOOKUP,Abbr`i2`,ALOOKUP_APPEND,MAP_MAP_o,swap_ff] >>
    rw[ff_def,GSYM MAP_MAP_o,ALOOKUP_MAP] >>
    rw[REV_ASSOCD_ALOOKUP] >> BasicProvers.CASE_TAC >> fs[typesem_def] >>
    rw[Once typesem_TYPE_SUBST,REV_ASSOCD_ALOOKUP] )
  >- (
    rw[] >>
    fs[ALL_DISTINCT_APPEND,IN_DISJOINT] >>
    metis_tac[] ) >>
  rw[] >> rw[] >> rw[termsem_def] >>
  qmatch_abbrev_tac`Abstract d1 r1 f1 = Abstract d2 r2 f2` >>
  `d2 = d1` by (
    unabbrev_all_tac >>
    simp[Once typesem_TYPE_SUBST] ) >>
  qmatch_assum_rename_tac`welltyped tm` >>
  `r2 = r1` by (
    unabbrev_all_tac >>
    qspecl_then[`tm`,`tyin`]mp_tac simple_inst_has_type >> rw[] >>
    imp_res_tac WELLTYPED_LEMMA >> rw[] >>
    simp[Once typesem_TYPE_SUBST] ) >>
  rw[] >> rpt AP_TERM_TAC >>
  unabbrev_all_tac >> rw[FUN_EQ_THM] >>
  first_x_assum(qspec_then`tyin`mp_tac) >> simp[] >>
  impl_tac >- ( fs[IN_DISJOINT] >> metis_tac[] ) >>
  rw[] >>
  match_mp_tac termsem_frees >>
  rw[] >>
  rw[combinTheory.APPLY_UPDATE_THM] >>
  metis_tac[]
QED

Theorem termsem_INST:
   ∀Γ tm tyin tmenv.
      term_ok Γ tm ∧ tmenv = tmsof Γ ⇒
      ∀i v.
        termsem tmenv i v (INST tyin tm) =
        termsem tmenv i
          ((λx. typesem (FST i) (FST v) (TYPE_SUBST tyin (Tyvar x))),
           (λ(x,ty). SND v (x, TYPE_SUBST tyin ty)))
          tm
Proof
  rw[] >> imp_res_tac term_ok_welltyped >>
  Q.ISPECL_THEN[`{x | ∃ty. VFREE_IN (Var x ty) tm}`,`tm`]mp_tac fresh_term_def >>
  simp[] >>
  Q.PAT_ABBREV_TAC`fm = fresh_term X tm` >> strip_tac >>
  `ACONV (INST tyin tm) (INST tyin fm)` by (
    match_mp_tac ACONV_INST >> metis_tac[] ) >>
  `welltyped (INST tyin tm)` by metis_tac[INST_WELLTYPED] >>
  `welltyped (INST tyin fm)` by metis_tac[INST_WELLTYPED] >>
  `termsem tmenv i v (INST tyin tm) = termsem tmenv i v (INST tyin fm)` by
    metis_tac[termsem_aconv] >>
  `{x | ∃ty. VFREE_IN (Var x ty) tm} = {x | ∃ty. VFREE_IN (Var x ty) fm}` by (
    simp[EXTENSION] >> metis_tac[VFREE_IN_ACONV] ) >>
  `INST tyin fm = simple_inst tyin fm` by
    metis_tac[INST_simple_inst] >>
  rw[] >>
  metis_tac[SIMP_RULE(srw_ss())[]termsem_simple_inst,termsem_aconv,term_ok_aconv]
QED

(* extending the context doesn't change the semantics *)

val is_type_valuation_exists = Q.prove(
  `is_set_theory ^mem ⇒ is_type_valuation (K boolset)`,
  simp[is_type_valuation_def] >> metis_tac[boolean_in_boolset]) |> UNDISCH

val rwt = MATCH_MP (PROVE[]``P x ⇒ ((∀x. P x ⇒ Q) ⇔ Q)``) is_type_valuation_exists