(*
   Miscellaneous definitions and minor lemmas used throughout the
   development.
*)

(* Misc. lemmas (without any compiler constants) *)
Theory misc
Ancestors
  alignment alist arithmetic blast[qualified] bitstring bag byte
  combin container list pred_set finite_map rich_list llist option
  pair sorting relation toto comparison bit sptree words set_sep
  indexedLists string machine_ieee integer_word address[qualified]
  path[qualified] res_quan[qualified] lprefix_lub[qualified]
Libs
  boolSimps mp_then dep_rewrite wordsLib BasicProvers
  ASCIInumbersLib bagLib[qualified] blastLib[qualified]

val _ = ParseExtras.tight_equality()

(* Total version of THE *)
Definition the_def:
  the _ (SOME x) = x ∧
  the x NONE =  x
End

val _ = remove_ovl_mapping "max" {Name="max", Thy="realax"}
val _ = remove_ovl_mapping "min" {Name="min", Thy="realax"}
val _ = remove_ovl_mapping "pos" {Name="pos", Thy="real"}
val _ = remove_ovl_mapping "abs" {Name="abs", Thy="realax"}
val _ = remove_ovl_mapping "inf" {Name="inf", Thy="real"}

(* this is copied in preamble.sml, but needed here to avoid cyclic dep *)
val rveq = rpt BasicProvers.VAR_EQ_TAC
val match_exists_tac = part_match_exists_tac (hd o strip_conj)
val asm_exists_tac = first_assum(match_exists_tac o concl)
(* -- *)

(* TODO: move/categorize *)

val _ = numLib.temp_prefer_num();

(* theorem behind impl_tac *)
Theorem DROP_NIL:
  ∀n xs. DROP n xs = [] ⇔ LENGTH xs ≤ n
Proof
  Induct \\ Cases_on ‘xs’ \\ fs [DROP_def]
QED

Theorem revdroprev:
   ∀l n.
     n ≤ LENGTH l ⇒ (REVERSE (DROP n (REVERSE l)) = TAKE (LENGTH l - n) l)
Proof
  fs [GSYM BUTLASTN_def,BUTLASTN_TAKE]
QED

Theorem revtakerev:
   ∀n l. n ≤ LENGTH l ⇒ REVERSE (TAKE n (REVERSE l)) = DROP (LENGTH l - n) l
Proof
  Induct >> simp[DROP_LENGTH_NIL] >>
  qx_gen_tac `l` >>
  `l = [] ∨ ∃f e. l = SNOC e f` by metis_tac[SNOC_CASES] >> simp[] >>
  simp[DROP_APPEND1]
QED

Theorem SORTED_inv_image_LESS_PLUS:
   SORTED (inv_image $< (arithmetic$+ k)) = SORTED $<
Proof
  simp[FUN_EQ_THM]
  \\ Induct
  \\ Q.ISPEC_THEN`$+ k`(fn th => simp[MATCH_MP SORTED_EQ th])
      (MATCH_MP transitive_inv_image transitive_LESS)
  \\ simp[MATCH_MP SORTED_EQ transitive_LESS]
QED

Definition read_bytearray_def:
  (read_bytearray a 0 get_byte = SOME []) /\
  (read_bytearray a (SUC n) get_byte =
     case get_byte a of
     | NONE => NONE
     | SOME b => case read_bytearray (a+1w) n get_byte of
                 | NONE => NONE
                 | SOME bs => SOME (b::bs))
End

(* HOL to have OPT_MMAP f l1 = SOME l2 ==> (LENGTH l2 = LENGTH l1) *)
Theorem read_bytearray_LENGTH:
   !n a f x.
      (read_bytearray a n f = SOME x) ==> (LENGTH x = n)
Proof
  Induct \\ fs [read_bytearray_def] \\ REPEAT STRIP_TAC
  \\ BasicProvers.EVERY_CASE_TAC \\ fs [] \\ rw [] \\ res_tac
QED

Theorem SUM_SET_IN_LT:
   !s x y. FINITE s /\ x IN s /\ y < x ==> y < SUM_SET s
Proof
  metis_tac[SUM_SET_IN_LE,LESS_LESS_EQ_TRANS]
QED

(* only used in proof of tlookup_bij_iff *)
Theorem CARD_IMAGE_ID_BIJ:
   ∀s. FINITE s ⇒ (∀x. x ∈ s ⇒ f x ∈ s) ∧ CARD (IMAGE f s) = CARD s ⇒ BIJ f s s
Proof
  rw[]
  \\ `SURJ f s s` suffices_by metis_tac[FINITE_SURJ_BIJ]
  \\ rw[IMAGE_SURJ]
  \\ `IMAGE f s ⊆ s` by metis_tac[SUBSET_DEF,IN_IMAGE]
  \\ metis_tac[SUBSET_EQ_CARD,IMAGE_FINITE]
QED

(* never used *)
Theorem DISJOINT_IMAGE_SUC:
   DISJOINT (IMAGE SUC x) (IMAGE SUC y) <=> DISJOINT x y
Proof
  fs [IN_DISJOINT] \\ metis_tac [DECIDE ``(SUC n = SUC m) <=> (m = n)``]
QED

(* disgusting and used only in clos_callProof *)
Overload LLOOKUP = “λl n. oEL n l”

Datatype:
  app_list = List ('a list) | Append app_list app_list | Nil
End

Definition append_aux_def:
  (append_aux Nil aux = aux) /\
  (append_aux (List xs) aux = xs ++ aux) /\
  (append_aux (Append l1 l2) aux = append_aux l1 (append_aux l2 aux))
End

Definition append_def:
  append l = append_aux l []
End

Theorem append_aux_thm:
   !l xs. append_aux l xs = append_aux l [] ++ xs
Proof
  Induct \\ metis_tac [APPEND,APPEND_ASSOC,append_aux_def]
QED

Theorem append_thm[simp]:
   append (Append l1 l2) = append l1 ++ append l2 /\
    append (List xs) = xs /\
    append Nil = []
Proof
  fs [append_def,append_aux_def]
  \\ once_rewrite_tac [append_aux_thm] \\ fs []
QED

Definition SmartAppend_def[simp]:
  (SmartAppend Nil l2 = l2) ∧
  (SmartAppend l1 Nil = l1) ∧
  (SmartAppend l1 l2 = Append l1 l2)
End

Theorem SmartAppend_thm:
   ∀l1 l2.
    SmartAppend l1 l2 =
      if l1 = Nil then l2 else
      if l2 = Nil then l1 else Append l1 l2
Proof
  Cases \\ Cases \\ rw[]
QED

Theorem append_SmartAppend[simp]:
   append (SmartAppend l1 l2) = append l1 ++ append l2
Proof
  rw[append_def,SmartAppend_thm,append_aux_def]
  \\ rw[Once append_aux_thm]
QED

(* instant derivation from LIST_EQ_REWRITE *)
Theorem MAP_REVERSE_STEP:
   ∀x f. x ≠ [] ⇒ MAP f (REVERSE x) = f (LAST x) :: MAP f (REVERSE (FRONT x))
Proof
  recInduct SNOC_INDUCT
  \\ rw [FRONT_APPEND]
QED

(* used three times, once with MIN_DEF alongside, which turns it into
   LENGTH_TAKE_EQ
*)
Theorem LENGTH_TAKE_EQ_MIN:
   !n xs. LENGTH (TAKE n xs) = MIN n (LENGTH xs)
Proof
  simp[LENGTH_TAKE_EQ] \\ full_simp_tac(srw_ss())[MIN_DEF] \\ decide_tac
QED

(* should be switched in orientation; looks like an attempt to get congruence
   rule *)
Theorem LIST_REL_MEM:
   !xs ys P. LIST_REL P xs ys <=>
              LIST_REL (\x y. MEM x xs /\ MEM y ys ==> P x y) xs ys
Proof
  full_simp_tac(srw_ss())[LIST_REL_EL_EQN] \\ METIS_TAC [MEM_EL]
QED

(* only used in theorem immediately below *)
Theorem LIST_REL_GENLIST_I:
   !xs. LIST_REL P (GENLIST I (LENGTH xs)) xs =
         !n. n < LENGTH xs ==> P n (EL n xs)
Proof
  simp[LIST_REL_EL_EQN]
QED

Theorem LIST_REL_FRONT_LAST:
   l1 <> [] /\ l2 <> [] ==>
    (LIST_REL A l1 l2 <=>
     LIST_REL A (FRONT l1) (FRONT l2) /\ A (LAST l1) (LAST l2))
Proof
  map_every
    (fn q => Q.ISPEC_THEN q FULL_STRUCT_CASES_TAC SNOC_CASES >>
             fs[LIST_REL_SNOC])
    [`l1`,`l2`]
QED

Definition fromList2_def:
  fromList2 l = SND (FOLDL (\(i,t) a. (i + 2,insert i a t)) (0,LN) l)
End

Theorem EVEN_fromList2_lemma[local]:
  !l n t.
      EVEN n /\ (!x. x IN domain t ==> EVEN x) ==>
      !x. x IN domain (SND (FOLDL (\(i,t) a. (i + 2,insert i a t)) (n,t) l)) ==> EVEN x
Proof
  Induct \\ full_simp_tac(srw_ss())[FOLDL] \\ REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[PULL_FORALL]
  \\ FIRST_X_ASSUM (MP_TAC o Q.SPECL [`n+2`,`insert n h t`,`x`])
  \\ full_simp_tac(srw_ss())[] \\ SRW_TAC [] [] \\ POP_ASSUM MATCH_MP_TAC
  \\ REPEAT STRIP_TAC \\ full_simp_tac(srw_ss())[] \\ full_simp_tac(srw_ss())[EVEN_EXISTS]
  \\ Q.EXISTS_TAC `SUC m` \\ DECIDE_TAC
QED

Theorem BIJ_FLOOKUP_MAP_KEYS:
   BIJ bij UNIV UNIV ==>
    FLOOKUP (MAP_KEYS (LINV bij UNIV) f) n = FLOOKUP f (bij n)
Proof
  fs [FLOOKUP_DEF,MAP_KEYS_def,BIJ_DEF] \\ strip_tac
  \\ match_mp_tac (METIS_PROVE []
      ``x=x'/\(x /\ x' ==> y=y') ==> (if x then y else z) = (if x' then y' else z)``)
  \\ fs [] \\ rw []
  THEN1 (eq_tac \\ rw [] \\ metis_tac [BIJ_LINV_INV,BIJ_DEF,IN_UNIV,LINV_DEF])
  \\ `BIJ (LINV bij UNIV) UNIV UNIV` by metis_tac [BIJ_LINV_BIJ,BIJ_DEF]
  \\ `INJ (LINV bij UNIV) (FDOM f) UNIV` by fs [INJ_DEF,IN_UNIV,BIJ_DEF]
  \\ fs [MAP_KEYS_def] \\ metis_tac [BIJ_LINV_INV,BIJ_DEF,IN_UNIV,LINV_DEF]
QED

Theorem EVERY_ZIP:
   !l f. EVERY (\(x,y). f x) l = EVERY f (MAP FST l)
Proof
  Induct_on `l` >>
  srw_tac[][] >>
  Cases_on `h` >>
  full_simp_tac(srw_ss())[] >>
  metis_tac []
QED

Theorem every_zip_split:
   !l1 l2 P Q.
    LENGTH l1 = LENGTH l2 ⇒
    (EVERY (\(x,y). P x ∧ Q y) (ZIP (l1, l2)) ⇔ EVERY P l1 ∧ EVERY Q l2)
Proof
 Induct_on `l1`
 >> simp []
 >> Cases_on `l2`
 >> rw []
 >> metis_tac []
QED

Theorem every_shim:
 !l P. EVERY (\(x,y). P y) l = EVERY P (MAP SND l)
Proof
Induct_on `l` >>
rw [] >>
PairCases_on `h` >>
rw []
QED

Theorem every_shim2:
 !l P Q. EVERY (\(x,y). P x ∧ Q y) l = (EVERY (\x. P (FST x)) l ∧ EVERY (\x. Q (SND x)) l)
Proof
Induct_on `l` >>
rw [] >>
PairCases_on `h` >>
rw [] >>
metis_tac []
QED

Theorem ZIP_MAP_FST_SND_EQ:
   ∀ls. ZIP (MAP FST ls,MAP SND ls) = ls
Proof
  Induct>>full_simp_tac(srw_ss())[]
QED

Theorem MAP_FST_I_PAIR_MAP[simp]:
   !xs. MAP FST (MAP (I ## f) xs) = MAP FST xs
Proof
  Induct \\ fs [FORALL_PROD]
QED

Theorem EVERY_FST_SND:
   EVERY (λ(a,b). P a ∧ Q b) ls ⇔ EVERY P (MAP FST ls) ∧ EVERY Q (MAP SND ls)
Proof
  rw[EVERY_MEM,MEM_MAP,UNCURRY,EXISTS_PROD,FORALL_PROD,PULL_EXISTS]
  \\ metis_tac[]
QED

Definition tlookup_def:
  tlookup m k = case lookup k m of NONE => k | SOME k => k
End

Theorem tlookup_bij_suff:
   set (toList names) = domain names ⇒
   BIJ (tlookup names) UNIV UNIV
Proof
  strip_tac
  \\ match_mp_tac BIJ_support
  \\ qexists_tac`domain names`
  \\ reverse conj_tac
  >- (
    simp[]
    \\ rw[tlookup_def]
    \\ CASE_TAC \\ fs[domain_lookup])
  \\ `set (toList names) = IMAGE (tlookup names) (domain names)`
  by (
    pop_assum kall_tac
    \\ simp[EXTENSION,tlookup_def,MEM_toList,domain_lookup]
    \\ rw[EQ_IMP_THM] \\ fs[]
    >- (qexists_tac`k` \\ fs[])
    \\ metis_tac[] )
  \\ match_mp_tac (MP_CANON CARD_IMAGE_ID_BIJ)
  \\ fs[] \\ rw[] \\ fs[EXTENSION]
  \\ metis_tac[]
QED

Theorem tlookup_bij_iff:
   BIJ (tlookup names) UNIV UNIV ⇔
   set (toList names) = domain names
Proof
  rw[EQ_IMP_THM,tlookup_bij_suff]
  \\ fs[BIJ_IFF_INV]
  \\ rw[EXTENSION,domain_lookup,MEM_toList]
  \\ rw[EQ_IMP_THM]
  >- (
    Cases_on`k=x` >- metis_tac[]
    \\ spose_not_then strip_assume_tac
    \\ `tlookup names x = x`
    by (
      simp[tlookup_def]
      \\ CASE_TAC \\ fs[] )
    \\ `tlookup names k = x`
    by ( simp[tlookup_def] )
    \\ metis_tac[] )
  \\ Cases_on`x=v` >- metis_tac[]
  \\ spose_not_then strip_assume_tac
  \\ `tlookup names x = v`
  by ( simp[tlookup_def] )
  \\ `∀k. tlookup names k ≠ x`
  by (
    rw[tlookup_def]
    \\ CASE_TAC \\ fs[]
    \\ CCONTR_TAC \\ fs[]
    \\ metis_tac[])
  \\ metis_tac[]
QED

(* should be composition of oEL and as-yet-undefined "THE default" *)
(*TODO upstream*)
Theorem MAX_LIST_APPEND[simp]:
   MAX_LIST (xs++ys) = MAX (MAX_LIST xs) (MAX_LIST ys)
Proof
  Induct_on `xs` >> simp[AC MAX_COMM MAX_ASSOC]
QED

(*Or should it be MAX x (MAX_LIST xs)*)
Theorem MAX_LIST_SNOC[simp]:
   MAX_LIST (SNOC x xs) = MAX (MAX_LIST xs) x
Proof
  simp[SNOC_APPEND]
QED

Definition max3_def[simp]:
  max3 (x:num) y z = if x > y then (if z > x then z else x)
                     else (if z > y then z else y)
End

Theorem ALOOKUP_SNOC:
   ∀ls p k. ALOOKUP (SNOC p ls) k =
      case ALOOKUP ls k of SOME v => SOME v |
        NONE => if k = FST p then SOME (SND p) else NONE
Proof
  Induct >> simp[] >>
  Cases >> simp[] >> srw_tac[][]
QED

Theorem ALOOKUP_GENLIST:
   ∀f n k. ALOOKUP (GENLIST (λi. (i,f i)) n) k = if k < n then SOME (f k) else NONE
Proof
  gen_tac >> Induct >> simp[GENLIST] >> srw_tac[][] >> full_simp_tac(srw_ss())[ALOOKUP_SNOC] >>
  srw_tac[][] >> fsrw_tac[ARITH_ss][]
QED

Theorem MEM_ALOOKUP:
   !xs x v.
      ALL_DISTINCT (MAP FST xs) ==>
      (MEM (x,v) xs <=> ALOOKUP xs x = SOME v)
Proof
  Induct \\ fs [FORALL_PROD] \\ rw []
  \\ res_tac \\ eq_tac \\ rw [] \\ rfs []
  \\ imp_res_tac ALOOKUP_MEM
  \\ fs [MEM_MAP,FORALL_PROD] \\ rfs []
QED

(* TODO - candidate for move to HOL, but in simpler form without accumulator *)
(* only used in inferProg *)
Type num_set = ``:unit spt``
Type num_map = ``:'a spt``

Theorem toAList_domain:
    ∀x. MEM x (MAP FST (toAList t)) ⇔ x ∈ domain t
Proof
  full_simp_tac(srw_ss())[EXISTS_PROD,MEM_MAP,MEM_toAList,domain_lookup]
QED

Theorem domain_nat_set_from_list[simp]:
   ∀ls ns. domain (FOLDL (λs n. insert n () s) ns ls) = domain ns ∪ set ls
Proof
  Induct >> simp[sptreeTheory.domain_insert] >>
  srw_tac[][EXTENSION] >> metis_tac[]
QED

(* only used below in proof of theorem that is in turn used just twice *)
Definition UPDATE_LIST_def:
  UPDATE_LIST = FOLDL (combin$C (UNCURRY UPDATE))
End
val _ = Parse.add_infix("=++",500,Parse.LEFT)

Overload "=++" = ``UPDATE_LIST``

Theorem UPDATE_LIST_THM:
   ∀f. (f =++ [] = f) ∧ ∀h t. (f =++ (h::t) = (FST h =+ SND h) f =++ t)
Proof
  srw_tac[][UPDATE_LIST_def,pairTheory.UNCURRY]
QED

Theorem APPLY_UPDATE_LIST_ALOOKUP:
   ∀ls f x. (f =++ ls) x = case ALOOKUP (REVERSE ls) x of NONE => f x | SOME y => y
Proof
  Induct >> simp[UPDATE_LIST_THM,ALOOKUP_APPEND] >>
  Cases >> simp[combinTheory.APPLY_UPDATE_THM] >>
  srw_tac[][] >> BasicProvers.CASE_TAC
QED

(* should be using indexedLists$findi, or INDEX_OF *)
Definition find_index_def:
  (find_index _ [] _ = NONE) ∧
  (find_index y (x::xs) n = if x = y then SOME n else find_index y xs (n+1))
End

val ALOOKUP_find_index_SOME = Q.prove(
  `∀env. (ALOOKUP env k = SOME v) ⇒
      ∀m. ∃i. (find_index k (MAP FST env) m = SOME (m+i)) ∧
          (v = EL i (MAP SND env))`,
  Induct >> simp[] >> Cases >>
  srw_tac[][find_index_def] >> full_simp_tac(srw_ss())[] >>
  first_x_assum(qspec_then`m+1`mp_tac)>>srw_tac[][]>>srw_tac[][]>>
  qexists_tac`SUC i`>>simp[])
|> SPEC_ALL |> UNDISCH_ALL |> Q.SPEC`0` |> DISCH_ALL |> SIMP_RULE (srw_ss())[]

Theorem find_index_ALL_DISTINCT_EL[simp]:
 ∀ls n m. ALL_DISTINCT ls ∧ n < LENGTH ls ⇒ (find_index (EL n ls) ls m = SOME (m + n))
Proof
Induct >- srw_tac[][] >>
gen_tac >> Cases >>
srw_tac[ARITH_ss][find_index_def] >>
metis_tac[MEM_EL]
QED

Theorem find_index_shift_0:
   ∀ls x k. find_index x ls k = OPTION_MAP (λx. x + k) (find_index x ls 0)
Proof
  Induct >> simp_tac(srw_ss())[find_index_def] >>
  rpt gen_tac >>
  Cases_on`h=x` >- (
    BasicProvers.VAR_EQ_TAC >>
    simp_tac(srw_ss())[] ) >>
  pop_assum mp_tac >>
  simp_tac(srw_ss())[] >>
  strip_tac >>
  first_assum(qspecl_then[`x`,`k+1`]mp_tac) >>
  first_x_assum(qspecl_then[`x`,`1`]mp_tac) >>
  srw_tac[][] >>
  Cases_on`find_index x ls 0`>>srw_tac[][] >>
  simp[]
QED

Theorem EVERY2_RC_same[simp]:
   EVERY2 (RC R) l l
Proof
  srw_tac[DNF_ss][EVERY2_EVERY,EVERY_MEM,MEM_ZIP,relationTheory.RC_DEF]
QED

(* used twice, and only in source_to_flatProof *)
Theorem FST_triple:
 (λ(n,ns,b). n) = FST
Proof
srw_tac[][FUN_EQ_THM,pairTheory.UNCURRY]
QED

Theorem FST_pair:
 (λ(n,v). n) = FST
Proof
srw_tac[][FUN_EQ_THM,pairTheory.UNCURRY]
QED

(* never used *)
Theorem SND_pair:
 (λ(n,v). v) = SND
Proof
srw_tac[][FUN_EQ_THM,pairTheory.UNCURRY]
QED

(* Specialisations to identity function *)

Theorem I_PERMUTES[simp]:
   I PERMUTES s
Proof
rw[BIJ_DEF, INJ_DEF, SURJ_DEF]
QED

Theorem MAP_EQ_ID:
 !f ls. (MAP f ls = ls) = (!x. MEM x ls ==> (f x = x))
Proof
PROVE_TAC[MAP_EQ_f,MAP_ID,combinTheory.I_THM]
QED

(* Specialisations to FEMPTY *)

Theorem FUN_FMAP_FAPPLY_FEMPTY_FAPPLY[simp]:
 FINITE s ==> (FUN_FMAP ($FAPPLY FEMPTY) s ' x = FEMPTY ' x)
Proof
Cases_on `x IN s` >>
srw_tac[][FUN_FMAP_DEF,NOT_FDOM_FAPPLY_FEMPTY]
QED

(* FUPDATE_LIST stuff *)

Theorem NOT_MEM_FLOOKUP_ZIP:
  ∀ys xs zs. ¬MEM n ys ⇒ FLOOKUP (xs |++ ZIP (ys, zs)) n = FLOOKUP xs n
Proof
  Induct >- simp [ZIP_def, FUPDATE_LIST_THM]
  >> Cases_on ‘zs’
  >> simp [ZIP_def, FUPDATE_LIST_THM, FLOOKUP_SIMP]
QED

(* Misc. *)

Theorem LESS_1[simp]:
 x < 1 ⇔ (x = 0:num)
Proof
DECIDE_TAC
QED

  (* --------- SO additions --------- *)

Theorem map_fst:
 !l f. MAP FST (MAP (\(x,y). (x, f y)) l) = MAP FST l
Proof
Induct_on `l` >>
srw_tac[][] >>
PairCases_on `h` >>
full_simp_tac(srw_ss())[]
QED

(* list misc *)

Theorem LENGTH_EQ_FILTER_FILTER:
   !xs. EVERY (\x. (P x \/ Q x) /\ ~(P x /\ Q x)) xs ==>
         (LENGTH xs = LENGTH (FILTER P xs) + LENGTH (FILTER Q xs))
Proof
  Induct \\ SIMP_TAC std_ss [LENGTH,FILTER,EVERY_DEF] \\ STRIP_TAC
  \\ Cases_on `P h` \\ FULL_SIMP_TAC std_ss [LENGTH,ADD_CLAUSES]
QED

(* move into HOL? *)

Theorem num_to_hex_string_length_1:
   ∀x. x < 16 ⇒ (LENGTH (num_to_hex_string x) = 1)
Proof
  REWRITE_TAC[GSYM rich_listTheory.MEM_COUNT_LIST]
  \\ gen_tac
  \\ CONV_TAC(LAND_CONV EVAL)
  \\ strip_tac \\ var_eq_tac
  \\ EVAL_TAC
QED

(* TODO - candidate for move to HOL *)
Theorem num_to_hex_string_length_2:
   ∀x. 16 ≤ x ∧ x < 256 ⇒ (LENGTH (num_to_hex_string x) = 2)
Proof
  REWRITE_TAC[GSYM rich_listTheory.MEM_COUNT_LIST]
  \\ gen_tac
  \\ CONV_TAC(LAND_CONV (RAND_CONV EVAL))
  \\ strip_tac \\ var_eq_tac \\ pop_assum mp_tac
  \\ EVAL_TAC
QED

Theorem num_from_hex_string_num_to_hex_string[simp]:
   num_from_hex_string (num_to_hex_string n) = n
Proof
  ASCIInumbersTheory.num_hex_string
  |> SIMP_RULE std_ss [combinTheory.o_DEF,FUN_EQ_THM]
  |> MATCH_ACCEPT_TAC
QED

Theorem MAPi_ID[simp]:
   MAPi (\x y. y) = I
Proof
  fs [FUN_EQ_THM] \\ Induct \\ fs [o_DEF]
QED

Theorem MAPi_MAP:
  ∀l f g. MAPi f (MAP g l) = MAPi (λi a. f i (g a)) l
Proof
  Induct >> rw []
  >> have ‘(λi a. f (SUC i) (g a)) = ((λi a. f i (g a)) ∘ SUC)’
  >- simp [FUN_EQ_THM]
  >> simp []
QED

(* TODO - candidate for move to HOL - though
     enumerate i0 l = MAPi (λx i. (i + i0, x)) l
*)
Definition enumerate_def:
  (enumerate n [] = []) ∧
  (enumerate n (x::xs) = (n,x)::enumerate (n+1n) xs)
End

(* TODO - candidate for move to HOL *)
Theorem LENGTH_enumerate:
    ∀xs k. LENGTH (enumerate k xs) = LENGTH xs
Proof
  Induct>>fs[enumerate_def]
QED

Theorem EL_enumerate:
    ∀xs n k.
  n < LENGTH xs ⇒
  EL n (enumerate k xs) = (n+k,EL n xs)
Proof
  Induct>>fs[enumerate_def]>>rw[]>>
  Cases_on`n`>>fs[]
QED

Theorem MAP_enumerate_MAPi:
    ∀f xs.
  MAP f (enumerate 0 xs) = MAPi (λn e. f (n,e)) xs
Proof
  rw[]>>match_mp_tac LIST_EQ>>fs[LENGTH_MAP,EL_MAP,EL_MAPi,LENGTH_enumerate,EL_enumerate]
QED

Theorem MAPi_enumerate_MAP:
    ∀f xs.
  MAPi f xs = MAP (λi,e. f i e) (enumerate 0 xs)
Proof
  rw[]>>match_mp_tac LIST_EQ>>fs[LENGTH_MAP,EL_MAP,EL_MAPi,LENGTH_enumerate,EL_enumerate]
QED

Theorem MEM_enumerate:
    ∀xs i e.
  i < LENGTH xs ⇒
  (MEM (i,e) (enumerate 0 xs) ⇔ EL i xs = e)
Proof
  fs[MEM_EL]>>rw[]>>eq_tac>>rw[LENGTH_enumerate]>>
  imp_res_tac EL_enumerate>>fs[]>>
  qexists_tac`i`>>fs[]
QED

Theorem MAP_FST_enumerate:
  MAP FST (enumerate k ls) = GENLIST ($+ k) (LENGTH ls)
Proof
  rw[LIST_EQ_REWRITE,LENGTH_enumerate]>>
  simp[EL_MAP,LENGTH_enumerate,EL_enumerate]
QED

Theorem ALOOKUP_enumerate:
  ∀ls k x.
  ALOOKUP (enumerate k ls) x =
  if k ≤ x ∧ x < LENGTH ls + k then SOME (EL (x-k) ls) else NONE
Proof
  Induct>>rw[enumerate_def]>>
  `x-k = SUC(x-(k+1))` by DECIDE_TAC>>
  simp[]
QED

Theorem SUM_MAP_LENGTH_REPLICATE:
   ∀n ls. SUM (MAP LENGTH (REPLICATE n ls)) = n * LENGTH ls
Proof
  Induct >> simp[REPLICATE,MULT]
QED

Theorem SUM_MAP_COUNT_LIST:
   !n k. SUM (MAP ($+ k) (COUNT_LIST n)) = (n * (2 * k + n - 1)) DIV 2
Proof
  Induct \\ rw [COUNT_LIST_def]
  \\ `!xs. MAP SUC xs = MAP ($+ 1) xs` by (Induct \\ rw [])
  \\ pop_assum (qspec_then `COUNT_LIST n` SUBST1_TAC)
  \\ pop_assum (qspec_then `k + 1` mp_tac)
  \\ simp [MAP_MAP_o, o_DEF]
  \\ `$+ (k + 1) = \x. k + (x + 1)` by fs [FUN_EQ_THM]
  \\ pop_assum SUBST1_TAC \\ rw [ADD1]
  \\ fs [LEFT_ADD_DISTRIB, RIGHT_ADD_DISTRIB]
  \\ metis_tac [ADD_DIV_ADD_DIV, MULT_COMM, DECIDE ``0n < 2``]
QED

Theorem SUM_MOD:
    k > 0 ⇒
  (SUM ls MOD k = (SUM (MAP (λn. n MOD k) ls)) MOD k)
Proof
  Induct_on`ls`>>rw[]>>
  DEP_ONCE_REWRITE_TAC[GSYM MOD_PLUS]>>fs[]
QED

Theorem MOD_SUB_LEMMA:
   n MOD k = 0 /\ m MOD k = 0 /\ 0 < k ==> (n - m) MOD k = 0
Proof
  Cases_on `m <= n` \\ fs []
  \\ imp_res_tac LESS_EQ_EXISTS \\ rw []
  \\ qpat_x_assum `(m + _) MOD k = 0` mp_tac
  \\ once_rewrite_tac[GSYM MOD_PLUS]
  \\ fs[]
QED

Theorem FLAT_REPLICATE_NIL:
   !n. FLAT (REPLICATE n []) = []
Proof
  Induct \\ fs [REPLICATE]
QED

Theorem MEM_REPLICATE_EQ:
   !n x y. MEM x (REPLICATE n y) <=> x = y /\ n <> 0
Proof
  Induct \\ fs [REPLICATE] \\ rw [] \\ eq_tac \\ rw []
QED

(* n.b. used in hol-reflection *)

Theorem FDOM_FLOOKUP:
   x ∈ FDOM f ⇔ ∃v. FLOOKUP f x = SOME v
Proof
  rw[FLOOKUP_DEF]
QED

Theorem FLAT_MAP_SING:
   ∀ls. FLAT (MAP (λx. [f x]) ls) = MAP f ls
Proof
  Induct \\ simp[]
QED

Theorem FLAT_MAP_NIL:
   FLAT (MAP (λx. []) ls) = []
Proof
  rw[FLAT_EQ_NIL,EVERY_MAP]
QED

Theorem PERM_MAP_BIJ:
   ∀f l1 l2.
    BIJ f UNIV UNIV ⇒
    (PERM l1 l2 ⇔ PERM (MAP f l1) (MAP f l2))
Proof
  rw[BIJ_IFF_INV] >>
  EQ_TAC >- rw[sortingTheory.PERM_MAP] >>
  `∀l. MEM l [l1;l2] ⇒ l = MAP g (MAP f l)` by (
    rw[MAP_MAP_o,combinTheory.o_DEF] ) >>
  fs[] >>
  metis_tac[sortingTheory.PERM_MAP]
QED

Theorem lookup_fromList2:
   !l n. lookup n (fromList2 l) =
          if EVEN n then lookup (n DIV 2) (fromList l) else NONE
Proof
  recInduct SNOC_INDUCT \\ srw_tac[][]
  THEN1 (EVAL_TAC \\ full_simp_tac(srw_ss())[lookup_def])
  THEN1 (EVAL_TAC \\ full_simp_tac(srw_ss())[lookup_def])
  \\ full_simp_tac(srw_ss())[fromList2_def,FOLDL_SNOC]
  \\ CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV)
  \\ full_simp_tac(srw_ss())[GSYM fromList2_def,FOLDL_SNOC]
  \\ full_simp_tac(srw_ss())[lookup_insert,lookup_fromList,DIV_LT_X]
  \\ `!k. FST (FOLDL (λ(i,t) a. (i + 2,insert i a t)) (k,LN) l) =
        k + LENGTH l * 2` by
   (qspec_tac (`LN`,`t`) \\ qspec_tac (`l`,`l`) \\ Induct \\ full_simp_tac(srw_ss())[FOLDL]
    \\ full_simp_tac(srw_ss())[MULT_CLAUSES, AC ADD_COMM ADD_ASSOC])
  \\ full_simp_tac(srw_ss())[] \\ srw_tac[][]
  \\ full_simp_tac(srw_ss())[GSYM DIV_LT_X,EL_SNOC]
  \\ full_simp_tac(srw_ss())[MULT_DIV,SNOC_APPEND,EL_LENGTH_APPEND,EVEN_MOD2,MOD_EQ_0]
  \\ TRY decide_tac
  \\ full_simp_tac(srw_ss())[DIV_LT_X]
  \\ `n = LENGTH l * 2 + 1` by decide_tac
  \\ full_simp_tac(srw_ss())[MOD_TIMES]
QED

Theorem domain_fromList2:
   ∀q. domain(fromList2 q) = set(GENLIST (λx. 2n*x) (LENGTH q))
Proof
  rw[EXTENSION,domain_lookup,lookup_fromList2,MEM_GENLIST,
     lookup_fromList,EVEN_EXISTS, PULL_EXISTS, SF CONJ_ss] \\
  metis_tac[]
QED

Theorem EXP2_EVEN:
   ∀n. EVEN (2 ** n) ⇔ n ≠ 0
Proof
  Induct >> simp[EXP,EVEN_DOUBLE]
QED

Theorem ALL_DISTINCT_FLAT:
   ∀l. ALL_DISTINCT (FLAT l) ⇔
        (∀l0. MEM l0 l ⇒ ALL_DISTINCT l0) ∧
        (∀i j. i < j ∧ j < LENGTH l ⇒
               ∀e. MEM e (EL i l) ⇒ ¬MEM e (EL j l))
Proof
  Induct >> dsimp[ALL_DISTINCT_APPEND, LT_SUC, MEM_FLAT] >>
  metis_tac[MEM_EL]
QED

Theorem o_PAIR_MAP:
   FST o (f ## g) = f o FST ∧
   SND o (f ## g) = g o SND
Proof
  simp[FUN_EQ_THM]
QED

Theorem MOD_MINUS:
   0 < p /\ 0 < k ==> (p * k - n MOD (p * k)) MOD k = (k - n MOD k) MOD k
Proof
  strip_tac
  \\ mp_tac (wordsTheory.MOD_COMPLEMENT |> Q.SPECL [`k`,`p`,`n MOD (p * k)`])
  \\ impl_tac THEN1 (fs [MOD_LESS,ZERO_LESS_MULT])
  \\ fs [MOD_MULT_MOD]
QED

Theorem EL_CONS_IF:
  EL n (x :: xs) = (if n = 0 then x else EL (PRE n) xs)
Proof    Cases_on `n` \\ fs []
QED

Theorem DROP_EMPTY:
   !ls n. (DROP n ls = []) ==> (n >= LENGTH ls)
Proof
    Induct \\ rw[DROP]
    \\ Cases_on `n > LENGTH ls` \\ fs[]
    \\ `n < LENGTH (h::ls)` by fs[]
    \\ fs[DROP_EL_CONS]
QED

Theorem OPT_MMAP_SOME[simp]:
   OPT_MMAP SOME ls = SOME ls
Proof
  Induct_on`ls` \\ rw[OPT_MMAP_def]
QED

Theorem DISJOINT_set_simp:
   DISJOINT (set []) s /\
    (DISJOINT (set (x::xs)) s <=> ~(x IN s) /\ DISJOINT (set xs) s)
Proof
  fs [DISJOINT_DEF,EXTENSION] \\ metis_tac []
QED

Theorem LUPDATE_commutes:
   ∀m n e1 e2 l.
    m ≠ n ⇒
    LUPDATE e1 m (LUPDATE e2 n l) = LUPDATE e2 n (LUPDATE e1 m l)
Proof
  Induct_on `l` >> simp[LUPDATE_def] >>
  Cases_on `m` >> simp[LUPDATE_def] >> rpt strip_tac >>
  rename[`LUPDATE _ nn (_ :: _)`] >>
  Cases_on `nn` >> fs[LUPDATE_def]
QED

Theorem LUPDATE_APPEND:
   !xs n ys x.
      LUPDATE x n (xs ++ ys) =
      if n < LENGTH xs then LUPDATE x n xs ++ ys
                       else xs ++ LUPDATE x (n - LENGTH xs) ys
Proof
  Induct \\ fs [] \\ Cases_on `n` \\ fs [LUPDATE_def] \\ rw [] \\ fs []
QED

Theorem FILTER_EL_EQ:
   ∀l1 l2. LENGTH l1 = LENGTH l2 ∧
   (∀n. n < LENGTH l1 ∧ (P (EL n l1) ∨ P (EL n l2)) ⇒ (EL n l1 = EL n l2))
   ⇒
   FILTER P l1 = FILTER P l2
Proof
  Induct \\ rw[] \\ Cases_on`l2` \\ fs[]
  \\ first_assum(qspec_then`0`mp_tac)
  \\ simp_tac (srw_ss())[] \\ simp[]
  \\ rw[] \\ fs[]
  \\ first_x_assum match_mp_tac \\ rw[]
  \\ first_x_assum(qspec_then`SUC n`mp_tac) \\ rw[]
QED

Theorem FST_EL_AFUPDKEY:
   ∀n. n < LENGTH ls ⇒ FST (EL n (AFUPDKEY k f ls)) = FST (EL n ls)
Proof
  Induct_on`ls` \\ simp[]
  \\ Cases \\ rw[AFUPDKEY_def]
  \\ Cases_on`n` \\ fs[]
QED

Theorem EL_AFUPDKEY_unchanged:
   ∀n. n < LENGTH ls ∧ FST (EL n ls) ≠ k ⇒ EL n (AFUPDKEY k f ls) = EL n ls
Proof
  Induct_on`ls` \\ simp[]
  \\ Cases \\ simp[AFUPDKEY_def]
  \\ Cases \\ simp[]
  \\ IF_CASES_TAC \\ rveq \\ rw[]
QED

Theorem HD_LUPDATE:
   0 < LENGTH l ⇒ HD (LUPDATE x p l) = if p = 0 then x else HD l
Proof
  Cases_on `l` >> rw[LUPDATE_def] >> Cases_on `p` >> fs[LUPDATE_def]
QED

Theorem DROP_LUPDATE:
   !n x m l. n ≤ m ⇒ DROP n (LUPDATE x m l) = LUPDATE x (m - n) (DROP n l)
Proof
  rw [LIST_EQ_REWRITE, EL_DROP, EL_LUPDATE] >>
  rw [] >>
  fs []
QED

Theorem w2n_lt_256 =
  w2n_lt |> INST_TYPE [``:'a``|->``:8``]
         |> SIMP_RULE std_ss [EVAL ``dimword (:8)``]

Theorem CHR_w2n_n2w_ORD:
   (CHR o w2n o (n2w:num->word8) o ORD) = I
Proof
  rw[o_DEF, ORD_BOUND, CHR_ORD, FUN_EQ_THM]
QED

Theorem n2w_ORD_CHR_w2n:
   ((n2w:num->word8) o ORD o CHR o w2n) = I
Proof
  rw[w2n_lt_256, o_DEF, ORD_BOUND, ORD_CHR, FUN_EQ_THM]
QED

Theorem CHR_w2n_n2w_ORD_simp[simp]:
   !c. CHR(w2n((n2w:num->word8)(ORD c))) = c
Proof
  metis_tac[CHR_w2n_n2w_ORD,o_THM,I_THM]
QED

Theorem n2w_ORD_CHR_w2n_simp[simp]:
   !w. n2w(ORD(CHR(w2n w))) = (w:word8)
Proof
  metis_tac[n2w_ORD_CHR_w2n,o_THM,I_THM]
QED

Theorem MAP_K_REPLICATE:
   MAP (K x) ls = REPLICATE (LENGTH ls) x
Proof
  Induct_on`ls` \\ rw[REPLICATE]
QED

Theorem TL_DROP_SUC:
   ∀x ls. x < LENGTH ls ⇒ TL (DROP x ls) = DROP (SUC x) ls
Proof
  Induct \\ rw[] \\ Cases_on`ls` \\ fs[]
QED

Theorem DROP_EQ_CONS_IMP_DROP_SUC:
   !xs n y ys. DROP n xs = y::ys ==> DROP (SUC n) xs = ys
Proof
  Induct \\ full_simp_tac(srw_ss())[DROP_def] \\ srw_tac[][]
  \\ res_tac \\ full_simp_tac(srw_ss())[ADD1]
  \\ `n - 1 + 1 = n` by decide_tac \\ full_simp_tac(srw_ss())[]
QED

Theorem DROP_IMP_EL:
   !xs n h t. DROP n xs = h::t ==> (EL n xs = h)
Proof
  Induct \\ fs [DROP_def] \\ Cases_on `n` \\ fs []
QED

Theorem LENGTH_FIELDS:
   ∀ls. LENGTH (FIELDS P ls) = LENGTH (FILTER P ls) + 1
Proof
  gen_tac
  \\ completeInduct_on`LENGTH ls`
  \\ Cases
  \\ rw[FIELDS_def]
  \\ pairarg_tac \\ fs[]
  \\ rw[] \\ fs[] \\ rw[ADD1]
  \\ fs[NULL_EQ]
  \\ imp_res_tac SPLITP_NIL_FST_IMP
  \\ imp_res_tac SPLITP_NIL_SND_EVERY
  \\ imp_res_tac SPLITP_IMP
  \\ fs[NULL_EQ]
  \\ fs[SPLITP] \\ rfs[] \\ rw[]
  >- (`FILTER P t = []` by (simp[FILTER_EQ_NIL] \\ fs[EVERY_MEM])
      \\ simp[])
  \\ first_x_assum(qspec_then`LENGTH t`mp_tac) \\ simp[]
  \\ disch_then(qspec_then`t`mp_tac)
  \\ Cases_on`t` \\ rw[FIELDS_def]
  \\ fs[SPLITP] \\ rfs[]
  \\ rfs[NULL_EQ]
QED

Theorem FIELDS_NEQ_NIL[simp]:
   FIELDS P ls ≠ []
Proof
  disch_then(assume_tac o Q.AP_TERM`LENGTH`)
  \\ fs[LENGTH_FIELDS]
QED

Theorem FIELDS_next:
   ∀ls l1 l2.
   FIELDS P ls = l1::l2 ⇒
   LENGTH l1 < LENGTH ls ⇒
   FIELDS P (DROP (SUC (LENGTH l1)) ls) = l2 ∧
   (∃c. l1 ++ [c] ≼ ls ∧ P c)
Proof
  gen_tac
  \\ completeInduct_on`LENGTH ls`
  \\ ntac 4 strip_tac
  \\ Cases_on`ls`
  \\ rw[FIELDS_def]
  \\ pairarg_tac \\ fs[]
  \\ every_case_tac \\ fs[NULL_EQ] \\ rw[] \\ fs[]
  \\ imp_res_tac SPLITP_NIL_FST_IMP \\ fs[]
  \\ imp_res_tac SPLITP_IMP \\ fs[]
  \\ imp_res_tac SPLITP_NIL_SND_EVERY \\ fs[]
  \\ rfs[PULL_FORALL,NULL_EQ]
  \\ fs[SPLITP]
  \\ every_case_tac \\ fs[]
  \\ rw[]
  \\ fs[SPLITP]
  \\ Cases_on`SPLITP P t` \\ fs[]
  \\ Cases_on`SPLITP P q` \\ fs[]
  \\ rw[]
  \\ `FIELDS P t = q::FIELDS P (TL r)`
  by (
    Cases_on`t` \\ fs[]
    \\ rw[FIELDS_def,NULL_EQ] )
  \\ first_x_assum(qspecl_then[`t`,`q`,`FIELDS P (TL r)`]mp_tac)
  \\ simp[]
QED

Theorem FIELDS_full:
   ∀P ls l1 l2.
   FIELDS P ls = l1::l2 ∧ LENGTH ls ≤ LENGTH l1 ⇒
   l1 = ls ∧ l2 = []
Proof
  ntac 2 gen_tac
  \\ completeInduct_on`LENGTH ls`
  \\ ntac 4 strip_tac
  \\ Cases_on`ls`
  \\ simp_tac(srw_ss()++LET_ss)[FIELDS_def]
  \\ pairarg_tac \\ pop_assum mp_tac \\ simp_tac(srw_ss())[]
  \\ strip_tac
  \\ IF_CASES_TAC
  >-
   (simp_tac(srw_ss())[]
    \\ Cases_on ‘l1 = ""’ \\simp[])
  \\ IF_CASES_TAC
  >- (
    simp_tac(srw_ss())[]
    \\ strip_tac \\ rveq
    \\ fs[NULL_EQ]
    \\ imp_res_tac SPLITP_NIL_SND_EVERY )
  \\ simp_tac(srw_ss())[]
  \\ strip_tac \\ rveq
  \\ qspec_then`h::t`mp_tac(GSYM SPLITP_LENGTH)
  \\ last_x_assum kall_tac
  \\ simp[]
  \\ strip_tac \\ fs[]
  \\ `LENGTH r = 0` by decide_tac
  \\ fs[LENGTH_NIL]
QED

Theorem FLAT_MAP_TOKENS_FIELDS:
   ∀P' ls P.
    (∀x. P' x ⇒ P x) ⇒
     FLAT (MAP (TOKENS P) (FIELDS P' ls)) =
     TOKENS P ls
Proof
  Induct_on`FIELDS P' ls` \\ rw[] \\
  qpat_x_assum`_ = FIELDS _ _`(assume_tac o SYM) \\
  imp_res_tac FIELDS_next \\
  Cases_on`LENGTH ls ≤ LENGTH h` >- (
    imp_res_tac FIELDS_full \\ fs[] ) \\
  fs[] \\ rw[] \\
  fs[IS_PREFIX_APPEND,DROP_APPEND,DROP_LENGTH_TOO_LONG,ADD1] \\
  `h ++ [c] ++ l  = h ++ (c::l)` by simp[] \\ pop_assum SUBST_ALL_TAC \\
  asm_simp_tac std_ss [TOKENS_APPEND]
QED

Definition splitlines_def:
  splitlines ls =
  let lines = FIELDS ((=) #"\n") ls in
  (* discard trailing newline *)
  if NULL (LAST lines) then FRONT lines else lines
End

Theorem splitlines_nil[simp] = EVAL“splitlines ""”

Theorem splitlines_eq_nil[simp]:
   splitlines ls = [] ⇔ (ls = [])
Proof
  rw[EQ_IMP_THM]
  \\ fs[splitlines_def]
  \\ every_case_tac \\ fs[]
  \\ Cases_on`FIELDS ($= #"\n") ls` \\ fs[]
  \\ fs[LAST_DEF] \\ rfs[NULL_EQ]
  \\ Cases_on`LENGTH "" < LENGTH ls`
  >- ( imp_res_tac FIELDS_next \\ fs[] )
  \\ fs[LENGTH_NIL]
QED

Theorem splitlines_CONS_FST_SPLITP:
   splitlines ls = ln::lns ⇒ FST (SPLITP ($= #"\n") ls) = ln
Proof
  rw[splitlines_def]
  \\ Cases_on`ls` \\ fs[FIELDS_def]
  \\ TRY pairarg_tac \\ fs[] \\ rw[] \\ fs[]
  \\ every_case_tac \\ fs[] \\ rw[] \\ fs[NULL_EQ, FIELDS_def]
  \\ qmatch_assum_abbrev_tac`FRONT (x::y) = _`
  \\ Cases_on`y` \\ fs[]
QED

Theorem irreflexive_inv_image:
   !R f. irreflexive R ==> irreflexive (inv_image R f)
Proof
  SIMP_TAC std_ss [irreflexive_def,inv_image_def]
QED

Theorem trichotomous_inv_image:
   !R f. trichotomous R /\ (INJ f UNIV UNIV) ==> trichotomous (inv_image R f)
Proof
  SIMP_TAC std_ss [trichotomous,inv_image_def,INJ_DEF,IN_UNIV] THEN
  METIS_TAC[]
QED

Theorem plus_0_I[simp]:
   $+ 0n = I
Proof
rw[FUN_EQ_THM]
QED

(* used once *)
Theorem SUM_COUNT_LIST =
  SUM_MAP_COUNT_LIST |> Q.SPECL [`n`,`0`] |> SIMP_RULE (srw_ss()) []

Theorem OPTION_MAP_I[simp]:
   OPTION_MAP I x = x
Proof
  Cases_on`x` \\ rw[]
QED

(* should be made an iff in conclusion *)
Theorem the_OPTION_MAP:
     !f d opt.
    f d = d ==>
    the d (OPTION_MAP f opt) = f (the d opt)
Proof
    rw [] >> Cases_on `opt` >> rw [the_def]
QED

Theorem TAKE_FLAT_REPLICATE_LEQ:
   ∀j k ls len.
    len = LENGTH ls ∧ k ≤ j ⇒
    TAKE (k * len) (FLAT (REPLICATE j ls)) = FLAT (REPLICATE k ls)
Proof
  Induct \\ simp[REPLICATE]
  \\ Cases \\ simp[REPLICATE]
  \\ simp[TAKE_APPEND2] \\ rw[] \\ fs[]
  \\ simp[MULT_SUC]
QED

Theorem ADD_MOD_EQ_LEMMA:
   k MOD d = 0 /\ n < d ==> (k + n) MOD d = n
Proof
  rw [] \\ `0 < d` by decide_tac
  \\ fs [MOD_EQ_0_DIVISOR]
  \\ pop_assum kall_tac
  \\ drule MOD_MULT
  \\ fs []
QED

(* should be set l1 ⊆ set l2 *)
Theorem TAKE_DROP_SUBLIST:
   ll ≼ (DROP n ls) ∧ n < LENGTH ls ∧ (nlll = n + LENGTH ll) ⇒
   (TAKE n ls ++ ll ++ DROP nlll ls = ls)
Proof
  rw[IS_PREFIX_APPEND, LIST_EQ_REWRITE, LENGTH_TAKE_EQ, EL_APPEND_EQN, EL_DROP]
  \\ rw[] \\ fs[EL_TAKE]
  \\ fs[NOT_LESS, LESS_EQ_EXISTS]
QED

(* computes the next position for which P holds *)
Theorem ALL_DISTINCT_alist_to_fmap_REVERSE:
   ALL_DISTINCT (MAP FST ls) ⇒ alist_to_fmap (REVERSE ls) = alist_to_fmap ls
Proof
  Induct_on`ls` \\ simp[FORALL_PROD] \\ rw[] \\ rw[FUNION_FUPDATE_2]
QED

Theorem SUM_MAP_K:
   ∀f ls c. (∀x. f x = c) ⇒ SUM (MAP f ls) = LENGTH ls * c
Proof
  rw[] \\ Induct_on`ls` \\ rw[MULT_SUC]
QED

Theorem TOKENS_unchanged:
  EVERY ($~ o P) ls ==> TOKENS P ls = if NULL ls then [] else [ls]
Proof
  Induct_on`ls` \\ rw[TOKENS_def] \\ fs[]
  \\ pairarg_tac \\ fs[NULL_EQ]
  \\ imp_res_tac SPLITP_JOIN
  \\ Cases_on`r=[]` \\ fs[]
  >- ( imp_res_tac SPLITP_NIL_FST_IMP \\ rveq \\ fs[TOKENS_NIL] )
  \\ rw[]
  >- (
    imp_res_tac SPLITP_NIL_FST_IMP
    \\ imp_res_tac SPLITP_IMP
    \\ rfs[] \\ rveq \\ fs[] )
  \\ imp_res_tac SPLITP_IMP
  \\ rfs[NULL_EQ]
  \\ fs[EVERY_MEM]
  \\ `MEM (HD r) (l ++ r)` by (Cases_on`r` \\ fs[])
  \\ Cases_on`MEM (HD r) l` \\ fs[] >- metis_tac[]
  \\ `MEM (HD r) (h::ls)` by metis_tac[MEM_APPEND]
  \\ fs[] \\ rw[] \\ metis_tac[]
QED

(* insert a string (l1) at specified index (n) in a list (l2) *)
Definition insert_atI_def:
  insert_atI l1 n l2 =
    TAKE n l2 ++ l1 ++ DROP (n + LENGTH l1) l2
End

Theorem insert_atI_NIL:
   ∀n l.insert_atI [] n l = l
Proof
  simp[insert_atI_def]
QED

Theorem insert_atI_CONS:
   ∀n l h t.
     n + LENGTH t < LENGTH l ==>
     insert_atI (h::t) n l = LUPDATE h n (insert_atI t (n + 1) l)
Proof
  simp[insert_atI_def] >> Induct_on `n`
  >- (Cases_on `l` >> simp[ADD1, LUPDATE_def]) >>
  Cases_on `l` >> simp[ADD1] >> fs[ADD1] >>
  simp[GSYM ADD1, LUPDATE_def]
QED

Theorem LENGTH_insert_atI:
   p + LENGTH l1 <= LENGTH l2 ⇒ LENGTH (insert_atI l1 p l2) = LENGTH l2
Proof
  simp[insert_atI_def]
QED

Theorem insert_atI_end:
   insert_atI l1 (LENGTH l2) l2 = l2 ++ l1
Proof
  simp[insert_atI_def,DROP_LENGTH_TOO_LONG]
QED

Theorem insert_atI_insert_atI:
   pos2 = pos1 + LENGTH c1 ==>
    insert_atI c2 pos2 (insert_atI c1 pos1 l) = insert_atI (c1 ++ c2) pos1 l
Proof
    rw[insert_atI_def,TAKE_SUM,TAKE_APPEND,LENGTH_TAKE_EQ,LENGTH_DROP,
       GSYM DROP_DROP_T,DROP_LENGTH_TOO_LONG,DROP_LENGTH_NIL_rwt]
    >> fs[DROP_LENGTH_NIL_rwt,LENGTH_TAKE,DROP_APPEND1,TAKE_APPEND,TAKE_TAKE,
       DROP_DROP_T,DROP_APPEND2,TAKE_LENGTH_TOO_LONG,TAKE_SUM,LENGTH_DROP]
QED

Theorem IN_EVEN =
  SIMP_CONV std_ss [IN_DEF] ``x ∈ EVEN``

Definition is_subseq_def:
  (is_subseq ls [] ⇔ T) ∧
  (is_subseq [] (x::xs) ⇔ F) ∧
  (is_subseq (y::ys) (x::xs) ⇔
   (x = y ∧ is_subseq ys xs) ∨
   (is_subseq ys (x::xs)))
End

(* TODO - candidate for move to HOL *)
val is_subseq_ind = theorem"is_subseq_ind";

(* TODO - candidate for move to HOL *)
Theorem is_subseq_refl[simp]:
   ∀ls. is_subseq ls ls
Proof
Induct \\ rw[is_subseq_def]
QED

(* TODO - candidate for move to HOL *)
Theorem is_subseq_nil[simp]:
   is_subseq [] ls ⇔ ls = []
Proof
  Cases_on`ls` \\ rw[is_subseq_def]
QED

(* TODO - candidate for move to HOL *)
Definition make_even_def:
  make_even n = if EVEN n then n else n+1
End

Theorem EVEN_make_even[simp]:
   EVEN (make_even x)
Proof
  rw[make_even_def, EVEN_ADD]
QED

Theorem v2w_32_F[simp]:
   (v2w [F] : word32) = 0w
Proof
EVAL_TAC
QED

Theorem v2w_32_T[simp]:
   (v2w [T] : word32) = 1w
Proof
EVAL_TAC
QED

Theorem MULT_DIV_MULT:
  ∀m l k. 0 < m ∧ 0 < l ⇒ (m * k) DIV (m * l) = k DIV l
Proof
  metis_tac [DIV_DIV_DIV_MULT, MULT_COMM, MULT_DIV]
QED

Definition steps_def:
  (steps f x [] = []) ∧
  (steps f x (j::js) =
   let y = f x j in
   let tr = steps f y js in
     ((j,y)::tr))
End

Definition steps_rel_def:
  (steps_rel R x [] ⇔ T) ∧
  (steps_rel R x ((j,y)::tr) ⇔
    R x j y ∧
    steps_rel R y tr)
End

val steps_rel_ind = theorem"steps_rel_ind";

Theorem LAST_MAP_SND_steps_FOLDL:
   ∀f x ls. LAST (x::(MAP SND (steps f x ls))) = FOLDL f x ls
Proof
  Induct_on`ls` \\ rw[steps_def]
QED

Definition all_words_def:
  (all_words base 0 = ∅) /\
  (all_words base (SUC n) = base INSERT (all_words (base + 1w) n))
End

Theorem IN_all_words:
   x ∈ all_words base n ⇔ (∃i. i < n ∧ x = base + n2w i)
Proof
  qid_spec_tac`base`
  \\ Induct_on`n`
  \\ rw[all_words_def, ADD1]
  \\ rw[EQ_IMP_THM]
  >- ( qexists_tac`0` \\ simp[] )
  >- ( qexists_tac`i + 1` \\ simp[GSYM word_add_n2w] )
  \\ Cases_on`i` \\ fs[ADD1]
  \\ disj2_tac
  \\ simp[GSYM word_add_n2w]
  \\ asm_exists_tac \\ simp[]
QED

Definition eq_shape_def:
  eq_shape LN LN = T /\
  eq_shape (LS _) (LS _) = T /\
  eq_shape (BN t1 t2) (BN u1 u2) = (eq_shape t1 u1 /\ eq_shape t2 u2) /\
  eq_shape (BS t1 _ t2) (BS u1 _ u2) = (eq_shape t1 u1 /\ eq_shape t2 u2) /\
  eq_shape _ _ = F
End

Theorem eq_shape_map:
   !t1 t2 f. eq_shape (map f t1) t2 <=> eq_shape t1 t2
Proof
  Induct \\ Cases_on `t2` \\ fs [eq_shape_def,map_def]
QED

Theorem eq_shape_IMP_domain:
   !t1 t2. eq_shape t1 t2 ==> domain t1 = domain t2
Proof
  ho_match_mp_tac (fetch "-" "eq_shape_ind")
  \\ rw [] \\ fs [eq_shape_def]
QED

Definition copy_shape_def:
  copy_shape LN LN = LN /\
  copy_shape LN (LS y) = LN /\
  copy_shape LN (BN t1 t2) = BN (copy_shape LN t1) (copy_shape LN t2) /\
  copy_shape LN (BS t1 y t2) = LN /\
  copy_shape (LS x) LN = LS x /\
  copy_shape (LS x) (LS y) = LS x /\
  copy_shape (LS x) (BN t1 t2) = LS x /\
  copy_shape (LS x) (BS t1 y t2) = BS (copy_shape LN t1) x (copy_shape LN t2) /\
  copy_shape (BN u1 u2) LN = (if domain (BN u1 u2) = {} then LN else BN u1 u2) /\
  copy_shape (BN u1 u2) (LS y) = BN u1 u2 /\
  copy_shape (BN u1 u2) (BN t1 t2) = BN (copy_shape u1 t1) (copy_shape u2 t2) /\
  copy_shape (BN u1 u2) (BS t1 y t2) = BN u1 u2 /\
  copy_shape (BS u1 x u2) LN = BS u1 x u2 /\
  copy_shape (BS u1 x u2) (LS y) =
     (if domain (BN u1 u2) = {} then LS x else BS u1 x u2) /\
  copy_shape (BS u1 x u2) (BN t1 t2) = BS u1 x u2 /\
  copy_shape (BS u1 x u2) (BS t1 y t2) = BS (copy_shape u1 t1) x (copy_shape u2 t2)
End

Theorem eq_shape_copy_shape[local]:
    !s. domain s = {} ==> eq_shape (copy_shape LN s) s
Proof
  Induct \\ fs [copy_shape_def,eq_shape_def]
QED

Theorem num_lemma[local]:
    (!n. 0 <> 2 * n + 2 /\ 0 <> 2 * n + 1:num) /\
    (!n m. 2 * n + 2 = 2 * m + 2 <=> (m = n)) /\
    (!n m. 2 * n + 1 = 2 * m + 1 <=> (m = n)) /\
    (!n m. 2 * n + 2 <> 2 * m + 1n)
Proof
  rw [] \\ fs [] \\ Cases_on `m = n` \\ fs []
QED

Theorem lookup_copy_shape_LN[local]:
    !s n. lookup n (copy_shape LN s) = NONE
Proof
  Induct \\ fs [copy_shape_def,lookup_def] \\ rw [] \\ fs []
QED

Theorem domain_EMPTY_lookup[local]:
    domain t = EMPTY ==> !x. lookup x t = NONE
Proof
  fs [domain_lookup,EXTENSION] \\ rw []
  \\ pop_assum (qspec_then `x` mp_tac)
  \\ Cases_on `lookup x t` \\ fs []
QED

Theorem lookup_copy_shape:
   !t1 t2 n. lookup n (copy_shape t1 t2) = lookup n t1
Proof
  Induct \\ Cases_on `t2` \\ fs [copy_shape_def,lookup_def] \\ rw []
  \\ fs [lookup_def,lookup_copy_shape_LN,domain_EMPTY_lookup]
QED

(* / TODO *)

(* BEGIN TODO: move to sptreeTheory *)

Theorem fromList2_value:
     ∀ e l t n . MEM e l ⇔  ∃ n . lookup n (fromList2 l) = SOME e
Proof
    rw[lookup_fromList2] >> rw[lookup_fromList] >> fs[MEM_EL] >>
    EQ_TAC >> rw[]
    >- (qexists_tac `n * 2` >> fs[] >> once_rewrite_tac [MULT_COMM] >>
        rw[EVEN_DOUBLE, MULT_DIV])
    >- (qexists_tac `n DIV 2` >> fs[])
QED

(* The range is the set of values taken on by an sptree.
  Not sure if these are worth moving. *)
Theorem TWOxDIV2:
   2 * x DIV 2 = x
Proof
  ONCE_REWRITE_TAC[MULT_COMM]
  \\ simp[MULT_DIV]
QED

Definition good_dimindex_def:
  good_dimindex (:'a) ⇔ dimindex (:'a) = 32 ∨ dimindex (:'a) = 64
End

Theorem good_dimindex_get_byte_set_byte:
  good_dimindex (:'a) ==>
    (get_byte a (set_byte (a:'a word) b w be) be = b)
Proof
  strip_tac \\
  match_mp_tac get_byte_set_byte \\
  fs[good_dimindex_def]
QED

Theorem byte_index_LESS_IMP[local]:
  (dimindex (:'a) = 32 \/ dimindex (:'a) = 64) /\
    byte_index (a:'a word) be < byte_index (a':'a word) be /\ i < 8 ==>
    byte_index a be + i < byte_index a' be /\
    byte_index a be <= i + byte_index a' be /\
    byte_index a be + 8 <= i + byte_index a' be /\
    i + byte_index a' be < byte_index a be + dimindex (:α)
Proof
  fs [byte_index_def,LET_DEF] \\ Cases_on `be` \\ fs []
  \\ rpt strip_tac \\ rfs [] \\ fs []
  \\ `w2n a MOD 4 < 4` by (match_mp_tac MOD_LESS \\ decide_tac)
  \\ `w2n a' MOD 4 < 4` by (match_mp_tac MOD_LESS \\ decide_tac)
  \\ `w2n a MOD 8 < 8` by (match_mp_tac MOD_LESS \\ decide_tac)
  \\ `w2n a' MOD 8 < 8` by (match_mp_tac MOD_LESS \\ decide_tac)
  \\ decide_tac
QED

Theorem NOT_w2w_bit[local]:
  8 <= i /\ i < dimindex (:'b) ==> ~((w2w:word8->'b word) w ' i)
Proof
  rpt strip_tac \\ rfs [w2w] \\ decide_tac
QED

val LESS4 = DECIDE ``n < 4 <=> (n = 0) \/ (n = 1) \/ (n = 2) \/ (n = 3:num)``
val LESS8 = DECIDE ``n < 8 <=> (n = 0) \/ (n = 1) \/ (n = 2) \/ (n = 3:num) \/
                               (n = 4) \/ (n = 5) \/ (n = 6) \/ (n = 7)``

Theorem DIV_EQ_DIV_IMP[local]:
  0 < d /\ n <> n' /\ (n DIV d * d = n' DIV d * d) ==> n MOD d <> n' MOD d
Proof
  rpt strip_tac \\ Q.PAT_X_ASSUM `n <> n'` mp_tac \\ fs []
  \\ MP_TAC (Q.SPEC `d` DIVISION) \\ fs []
  \\ rpt strip_tac \\ pop_assum (fn th => once_rewrite_tac [th])
  \\ fs []
QED

Theorem get_byte_set_byte_diff:
   good_dimindex (:'a) /\ a <> a' /\ (byte_align a = byte_align a') ==>
    (get_byte a (set_byte (a':'a word) b w be) be = get_byte a w be)
Proof
  fs [get_byte_def,set_byte_def,LET_DEF] \\ rpt strip_tac
  \\ `byte_index a be <> byte_index a' be` by
   (fs [good_dimindex_def]
    THENL
     [`w2n a MOD 4 < 4 /\ w2n a' MOD 4 < 4` by fs []
      \\ `w2n a MOD 4 <> w2n a' MOD 4` by
       (fs [alignmentTheory.byte_align_def,byte_index_def] \\ rfs [LET_DEF]
        \\ Cases_on `a` \\ Cases_on `a'` \\ fs [w2n_n2w] \\ rw []
        \\ rfs [alignmentTheory.align_w2n]
        \\ `(n DIV 4 * 4 + n MOD 4) < dimword (:'a) /\
            (n' DIV 4 * 4 + n' MOD 4) < dimword (:'a)` by
          (METIS_TAC [DIVISION,DECIDE ``0<4:num``])
        \\ `(n DIV 4 * 4) < dimword (:'a) /\
            (n' DIV 4 * 4) < dimword (:'a)` by decide_tac
        \\ match_mp_tac DIV_EQ_DIV_IMP \\ fs []),
      `w2n a MOD 8 < 8 /\ w2n a' MOD 8 < 8` by fs []
      \\ `w2n a MOD 8 <> w2n a' MOD 8` by
       (fs [alignmentTheory.byte_align_def,byte_index_def] \\ rfs [LET_DEF]
        \\ Cases_on `a` \\ Cases_on `a'` \\ fs [w2n_n2w] \\ rw []
        \\ rfs [alignmentTheory.align_w2n]
        \\ `(n DIV 8 * 8 + n MOD 8) < dimword (:'a) /\
            (n' DIV 8 * 8 + n' MOD 8) < dimword (:'a)` by
          (METIS_TAC [DIVISION,DECIDE ``0<8:num``])
        \\ `(n DIV 8 * 8) < dimword (:'a) /\
            (n' DIV 8 * 8) < dimword (:'a)` by decide_tac
        \\ match_mp_tac DIV_EQ_DIV_IMP \\ fs [])]
    \\ full_simp_tac bool_ss [LESS4,LESS8] \\ fs [] \\ rfs []
    \\ fs [byte_index_def,LET_DEF] \\ rw [])
  \\ fs [fcpTheory.CART_EQ,w2w,good_dimindex_def] \\ rpt strip_tac
  \\ `i' < dimindex (:'a)` by decide_tac
  \\ fs [word_or_def,fcpTheory.FCP_BETA,word_lsr_def,word_lsl_def]
  \\ `i' + byte_index a be < dimindex (:'a)` by
   (fs [byte_index_def,LET_DEF] \\ rw []
    \\ `w2n a MOD 4 < 4` by (match_mp_tac MOD_LESS \\ decide_tac)
    \\ `w2n a MOD 8 < 8` by (match_mp_tac MOD_LESS \\ decide_tac)
    \\ decide_tac)
  \\ fs [word_or_def,fcpTheory.FCP_BETA,word_lsr_def,word_lsl_def,
         word_slice_alt_def,w2w] \\ rfs []
  \\ fs [DECIDE ``m <> n <=> m < n \/ n < m:num``]
  \\ Cases_on `w ' (i' + byte_index a be)` \\ fs []
  \\ imp_res_tac byte_index_LESS_IMP
  \\ fs [w2w] \\ TRY (match_mp_tac NOT_w2w_bit)
  \\ fs [] \\ decide_tac
QED

(* helpful theorems for _size *)
Definition fmap_update_def[simp]:
  fmap_update f k v = f |+ (k,v)
End

(* TODO: move to HOL? *)
Theorem ALOOKUP_MAP_3:
  ALOOKUP (MAP (λ(x,y,z). (x, f x y, z)) al) x =
  OPTION_MAP (f x ## I) (ALOOKUP al x)
Proof
  fs [GSYM ALOOKUP_MAP_2, LAMBDA_PROD]
QED

Theorem ALOOKUP_MAP_names:
  ALOOKUP (MAP (λname. (name,values name)) names) lookup_name =
    if MEM lookup_name names then SOME (values lookup_name) else NONE
Proof
  Induct_on ‘names’
  >> simp [ALOOKUP_def]
  >> qx_gen_tac ‘name’
  >> Cases_on ‘name = lookup_name’
  >> simp []
QED

Theorem ALOOKUP_MAP_const:
  ALOOKUP (MAP (λname. (name,value)) names) lookup_name =
    if MEM lookup_name names then SOME value else NONE
Proof
  Induct_on ‘names’
  >> simp [ALOOKUP_def]
  >> qx_gen_tac ‘name’
  >> Cases_on ‘name = lookup_name’
  >> simp []
QED

Theorem LIST_REL_MAP_FST:
  LIST_REL (λ(x,v) (y,w). x = y ∧ R v w) bindings bindings' ⇒
  MAP FST bindings = MAP FST bindings'
Proof
  rw [MAP_EQ_LIST_REL]
  >- metis_tac [LIST_REL_LENGTH]
  >> irule LIST_REL_mono
  >> simp [Once CONJ_COMM]
  >> asm_exists_tac
  >> rw []
  >> qmatch_goalsub_rename_tac ‘FST source_binding = FST target_binding’
  >> PairCases_on ‘source_binding’
  >> PairCases_on ‘target_binding’
  >> gvs []
QED
