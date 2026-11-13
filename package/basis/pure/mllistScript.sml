(*
  Pure functions for the List module.
*)
Theory mllist
Libs
  preamble
Ancestors
  indexedLists[qualified] toto[qualified]
  sorting mergesort

Theorem merge_tail_MEM:
  !negate R xs ys acc. MEM x (merge_tail negate R xs ys acc) = ((MEM x xs) \/ (MEM x ys) \/ (MEM x acc))
Proof
  ho_match_mp_tac merge_tail_ind
  \\ rpt strip_tac
  \\ fs[merge_tail_def]
  >- (simp[REV_REVERSE_LEM] \\ metis_tac[])
  >- (simp[REV_REVERSE_LEM] \\ metis_tac[])
  >- (
      rw[]
      \\ fs[]
      \\ metis_tac[]
    )
QED

Theorem mergesortN_tail_MEM:
  !negate R length lst. (MEM x (mergesortN_tail negate R length lst) <=> MEM x (TAKE length lst))
Proof
  ho_match_mp_tac mergesortN_tail_ind
  \\ reverse (rw[])
  >- (
      reverse (rw[Once $ mergesortN_tail_def])
      >- (
        gvs[]
        \\ simp[merge_tail_MEM]
        \\ rename1 ‘DIV2 length’
        \\ `DIV2 length ≤ length` by (
            fs[DIV2_def]
            \\ qspecl_then [`length`, `2`] assume_tac DIV_LESS
            \\ `0 < length /\ 1 < 2 ` by fs[]
            \\ fs[arithmeticTheory.LT_IMP_LE]
          )
        \\ simp[TAKE_DROP_SWAP]
        \\ metis_tac[MEM_APPEND, TAKE_TAKE_T, TAKE_DROP]
      )
      \\ EVERY_CASE_TAC
      \\ rw[mergesortN_tail_def, sort2_tail_def, sort3_tail_def]
      \\ metis_tac[]
    )
    \\ rw[mergesortN_tail_def, sort2_tail_def, sort3_tail_def]
    \\ metis_tac[]
QED

Theorem mergesort_tail_MEM:
  ∀R l. MEM x (mergesort$mergesort_tail R l) ⇔ MEM x l
Proof
  simp[mergesort_tail_def, mergesortN_tail_MEM]
QED

Theorem merge_tail_PERM:
  !negate R xs ys acc. PERM (xs++ys++acc) (merge_tail negate R xs ys acc)
Proof
  ho_match_mp_tac merge_tail_ind
  \\ fs[merge_tail_def]
  \\ reverse (rpt strip_tac)
  >- (
      rw[]
      >- (
        gvs[]
        \\ `PERM (x::(xs ++ y::ys ++ acc)) (xs ++ y::ys ++ x::acc)` by (
            rename1 `PERM (x::(mid ++ acc)) (mid ++ x::acc)`
            \\ match_mp_tac CONS_PERM
            \\ rw[]
          )
        \\ qspecl_then [ `(x::(xs ⧺ y::ys ⧺ acc))`,
                         `(xs ++ y::ys ++ x::acc)`,
                         `(merge_tail negate R xs (y::ys) (x::acc))`
            ] assume_tac PERM_TRANS
        \\ fs[]
      )
      >- (
          `PERM (x::(xs ++ y::ys ++ acc)) (x::(xs ++ ys ++ y::acc))` by simp[PERM_TO_APPEND_SIMPS]
          \\ qspecl_then [ `(x::(xs ++ y::ys ++ acc))`,
                           `(x::(xs ++ ys ++ y::acc))`,
                           `(merge_tail (R x y) R (x::xs) ys (y::acc))`
              ] assume_tac PERM_TRANS
          \\ fs[]
        )
    )
    \\ simp[REV_REVERSE_LEM]
    \\ pure_rewrite_tac [GSYM APPEND_ASSOC, GSYM CONS_APPEND]
    \\ match_mp_tac CONS_PERM
    \\ simp[PERM_APPEND_IFF]
QED

Theorem sort2_tail_PERM:
  !neg R x y. PERM [x;y] (sort2_tail neg R x y)
Proof
  rw[sort2_tail_def]
  \\ `[y;x] = (REVERSE [x;y])` by rw[]
  \\ pop_assum (fn x => pure_rewrite_tac [x] \\ simp[PERM_REVERSE])
QED

Theorem sort3_tail_PERM:
  !neg R x y z. PERM [x;y;z] (sort3_tail neg R x y z)
Proof
  reverse (rw[sort3_tail_def])
  >- (
      `[z;y;x] = REVERSE [x;y;z]` by rw[]
      \\ pop_assum (fn x => pure_rewrite_tac [x] \\ simp[PERM_REVERSE])
    )
  >- (
      `[x;y;z] = REVERSE [z;y;x]` by rw[]
      \\ pop_assum (fn x => pure_rewrite_tac [x] \\ simp[PERM_REVERSE_EQ])
      \\ `PERM ([z;y] ++ [x]) ([y;z] ++ [x])` suffices_by rw[]
      \\ `PERM [z;y] [y;z]` suffices_by simp[PERM_APPEND_IFF]
      \\ `[y;z] = REVERSE [z;y]` by rw[]
      \\ pop_assum (fn x => pure_rewrite_tac [x] \\ simp[PERM_REVERSE])
    )
  >- (
      `PERM ([x;y] ++ [z]) ([y;x] ++ [z])` suffices_by rw[]
      \\ `PERM [x;y] [y;x]` suffices_by simp[PERM_APPEND_IFF]
      \\ `[y;x] = REVERSE [x;y]` by rw[]
      \\ pop_assum (fn x => pure_rewrite_tac [x] \\ simp[PERM_REVERSE])
    )
  >- (
      `[z;x;y] = REVERSE [y;x;z]` by rw[]
      \\ pop_assum (fn x => pure_rewrite_tac [x] \\ simp[PERM_REVERSE_EQ])
      \\ `PERM ([x;y] ++ [z]) ([y;x] ++ [z])` suffices_by rw[]
      \\ `PERM [x;y] [y;x]` suffices_by simp[PERM_APPEND_IFF]
      \\ `[y;x] = REVERSE [x;y]` by rw[]
      \\ pop_assum (fn x => pure_rewrite_tac [x] \\ simp[PERM_REVERSE])
    )
  >- (
      `[z;y] = REVERSE [y;z]` by rw[]
      \\ pop_assum (fn x => pure_rewrite_tac [x] \\ simp[PERM_REVERSE_EQ])
    )
QED

Theorem mergesortN_tail_PERM:
  !neg R len l. PERM (TAKE len l) (mergesortN_tail neg R len l)
Proof
  ho_match_mp_tac mergesortN_tail_ind
  \\ reverse(rw[])
  \\ fs[]
  >- (
      rw[Once $ mergesortN_tail_def]
      >- (Cases_on `l` \\ fs[])
      >- (
          Cases_on `l`
          \\ fs[]
          \\ Cases_on `t`
          \\ fs[]
          \\ simp[sort2_tail_PERM]
        )
      >- (
          Cases_on `l`
              \\ fs[]
              \\ Cases_on `t`
              \\ fs[]
              \\ Cases_on `t'`
              \\ fs[]
              \\ simp[sort2_tail_PERM, sort3_tail_PERM]
        )
      >- (
          fs[]
          \\ irule PERM_TRANS
          \\ irule_at (Pos last) merge_tail_PERM
          \\ rw[]
          \\ irule PERM_FUN_SPLIT
          \\ irule_at (Pos last) (iffRL PERM_SYM)
          \\ first_x_assum (irule_at Any)
          \\ irule PERM_TRANS
          \\ irule_at (Pos last) PERM_APPEND
          \\ irule PERM_FUN_SPLIT
          \\ irule_at (Pos last) (iffRL PERM_SYM)
          \\ first_x_assum (irule_at Any)
          \\ simp[TAKE_DROP_SWAP]
          \\ `DIV2 len < len` by (simp[DIV2_def])
          \\ `DIV2 len + (len - (DIV2 len)) = len` by (
                simp[DIV2_def, SUB_LEFT_ADD]
                \\ rw[]
                \\ gvs[DIV2_def]
             )
          \\ fs[]
          \\ irule PERM_TRANS
          \\ irule_at (Pos last) PERM_APPEND
          \\ `TAKE len l = (TAKE (DIV2 len) l ⧺ DROP (DIV2 len) (TAKE len l))` suffices_by metis_tac[PERM_REFL]
          \\ simp[LIST_EQ_REWRITE]
          \\ conj_tac
          >- (
              Cases_on `len <= (LENGTH l)`
              \\ fs[]
              >- (
                  Cases_on `DIV2 len <= LENGTH l`
                  \\ `!n l. n > LENGTH l ==> (LENGTH (TAKE n l) = LENGTH l)` by (
                      rw[]
                      \\ `TAKE n l' = l'` by fs[]
                      \\ pop_assum (fn x => pure_rewrite_tac [x])
                      \\ REFL_TAC
                    )
                  \\ fs[]
                )
            )
          >- (
              rw[EL_APPEND]
              >- (
                  Cases_on `(DIV2 len) <= (LENGTH l)`
                  \\ fs[EL_TAKE]
                  >- (
                      `!n l. n > LENGTH l ==> (TAKE n l = l)` by rw[]
                      \\ `DIV2 len > LENGTH l` by fs[]
                      \\ simp[EL_TAKE]
                    )
                )
              >- (
                  Cases_on `DIV2 len <= LENGTH l`
                  \\ fs[]
                  >- (simp[EL_DROP])
                  >- (
                      (* False case. *)
                      `LENGTH (TAKE (DIV2 len) l) = (LENGTH l)` by (
                        `TAKE (DIV2 len) l = l` by fs[]
                        \\ pop_assum (fn x => rw [x])
                        )
                      \\ `x >= LENGTH l` by fs[]
                      \\ `x < LENGTH l` by (
                           `l = TAKE len l` by fs[]
                            \\ pop_assum (fn x => pure_rewrite_tac [Once $ x])
                            \\ rfs[]
                        )
                      \\ fs[]
                    )
                )
            )
        )
    )
  \\ rw[mergesortN_tail_def]
  \\ simp[sort2_tail_PERM, sort3_tail_PERM]
QED
(* ^^^^^ TO BE PORTED TO HOL ^^^^^ *)

Definition sort_def:
  sort = mergesort$mergesort_tail
End

Theorem sort_MEM[simp]:
  !R L. MEM x (sort R L) ⇔ MEM x L
Proof
  simp[sort_def, mergesort_tail_MEM]
QED

Theorem sort_PERM:
  !R L. sorting$PERM L (sort R L)
Proof
  simp[sort_def, mergesort_tail_def]
  \\ rpt strip_tac
  \\ `L = TAKE (LENGTH L) L` by rw[]
  \\ pop_assum (fn x => pure_rewrite_tac [Once $ x])
  \\ rw[mergesortN_tail_PERM]
QED

Theorem sort_LENGTH[simp]:
  !R l. LENGTH (sort R l) = LENGTH l
Proof
  simp[sort_def, PERM_LENGTH, sort_PERM]
QED

Theorem sort_set[simp]:
  set (sort R ls) = set ls
Proof
  rw[EXTENSION]
QED

Definition mapi_def:
  (mapi f (n: num) [] = []) /\
  (mapi f n (h::t) = (let y = f n h in (y::(mapi f (n + 1) t))))
End

Theorem MAPI_thm_gen[local]:
  ∀f l x. MAPi (\a. f (a + x)) l = mapi f x l
Proof
  Induct_on `l` \\ rw [MAPi_def, mapi_def] \\
  rw [o_DEF, ADD1] \\
  fs [] \\
  pop_assum (fn th => rw[GSYM th] ) \\
  rw[AC ADD_ASSOC ADD_COMM] \\
  match_mp_tac MAPi_CONG \\ rw[]
QED

Theorem MAPI_thm:
   !f l. MAPi f l = mapi f 0 l
Proof
  rw [(MAPI_thm_gen |> Q.SPECL[`f`,`l`,`0`]
  |> SIMP_RULE (srw_ss()++ETA_ss) [])]
QED

Theorem index_find_thm:
   !x y. OPTION_MAP SND (INDEX_FIND x f l) = OPTION_MAP SND (INDEX_FIND y f l)
Proof
  Induct_on`l` \\ rw[INDEX_FIND_def]
QED

Definition partition_aux_def:
  (partition_aux f [] pos neg =
    (REVERSE pos, REVERSE neg)) /\
    (partition_aux f (h::t) pos neg = if f h then partition_aux f t (h::pos) neg
      else partition_aux f t pos (h::neg))
End

Definition partition_def:
  partition (f : 'a -> bool) l = partition_aux f l [] []
End

Theorem partition_aux_thm[local]:
  ∀f l l1 l2.
    partition_aux f l l1 l2 =
    (REVERSE l1++(FILTER f l), REVERSE l2++(FILTER ($~ o f) l))
Proof
  Induct_on `l` \\
  rw [partition_aux_def] \\
  rw [partition_aux_def]
QED

Theorem partition_pos_thm:
   !f l. FST (partition f l) = FILTER f l
Proof
  rw [partition_def, FILTER, partition_aux_thm]
QED

Theorem partition_neg_thm:
   !f l. SND (partition f l) = FILTER ($~ o f) l
Proof
  rw [partition_def, FILTER, partition_aux_thm]
QED

Definition foldl_def:
  (foldl f e [] = e) /\
  (foldl f e (h::t) = foldl f (f h e) t)
End

Definition foldli_aux_def:
  (foldli_aux f e n [] = e) /\
  (foldli_aux f e n (h::t) = foldli_aux f (f n h e) (SUC n) t)
End

Theorem foldli_aux_thm[local]:
  ∀l f e n.  foldli_aux f e n l = FOLDRi (\n'. f (LENGTH l + n - (SUC n'))) e (REVERSE l)
Proof
  Induct_on `l` \\
  rw [foldli_aux_def] \\
  rw [FOLDRi_APPEND] \\
  rw [ADD1]
QED

Theorem foldl_intro:
  ∀xs x f. FOLDL f x xs = foldl (λx acc. f acc x) x xs
Proof
  Induct \\ fs [foldl_def]
QED

Definition collate_def:
  (collate f [] [] = EQUAL) /\
  (collate f [] (h::t) = LESS) /\
  (collate f (h::t) [] = GREATER) /\
  (collate f (h1::t1) (h2::t2) =
    if f h1 h2 = EQUAL
      then collate f t1 t2
    else f h1 h2)
End

Theorem collate_equal_thm:
   !l. (!x. MEM x l ==> (f x x = EQUAL)) ==> (collate f l l = EQUAL)
Proof
  Induct_on `l` \\ rw [collate_def] \\ rw [collate_def]
QED

Theorem collate_short_thm:
   !f l1 l2. (!x. f x x = EQUAL) ∧ (l1 ≠ l2) /\ (l1 ≼ l2) ==>
        (collate f l1 l2 = LESS)
Proof
  ho_match_mp_tac collate_ind
  \\ rw[collate_def] \\ fs[]
QED

Theorem collate_long_thm:
   !f l1 l2. (!x. f x x = EQUAL) ∧ (l1 ≠ l2) /\ (l2 ≼ l1) ==>
        (collate f l1 l2 = GREATER)
Proof
  ho_match_mp_tac collate_ind
  \\ rw[collate_def] \\ fs[]
QED

Definition LENGTH_AUX_def:
  (LENGTH_AUX [] n = (n:num)) /\
  (LENGTH_AUX (x::xs) n = LENGTH_AUX xs (n+1))
End

Theorem LENGTH_AUX_THM = Q.prove(`
  !xs n. LENGTH_AUX xs n = LENGTH xs + n`,
  Induct THEN ASM_SIMP_TAC std_ss [LENGTH_AUX_def,LENGTH,ADD1,AC ADD_COMM ADD_ASSOC])
  |> Q.SPECL [`xs`,`0`] |> GSYM |> SIMP_RULE std_ss [];

Definition map_rev'_def:
  map_rev' f [] acc = acc ∧
  map_rev' f (x :: xs) acc = map_rev' f xs (f x :: acc)
End

Theorem map_rev'_lemma[local]:
  ∀acc. map_rev' f xs acc = (map_rev' f xs []) ⧺ acc
Proof
  Induct_on ‘xs’
  >- rw[map_rev'_def]
  \\ rpt strip_tac
  \\ rewrite_tac[map_rev'_def]
  \\ first_assum $ once_rewrite_tac o single
  \\ rw[]
QED

Definition filter_rev'_def:
  filter_rev' P [] acc = acc ∧
  filter_rev' P (h::t) acc = if P h then filter_rev' P t (h::acc) else filter_rev' P t acc
End

Theorem filter_rev'_lemma[local]:
  ∀acc. filter_rev' P xs acc = (filter_rev' P xs []) ⧺ acc
Proof
  Induct_on ‘xs’
  >- rw[filter_rev'_def]
  \\ rpt strip_tac
  \\ rewrite_tac[filter_rev'_def]
  \\ Cases_on ‘P h’
  >- (last_x_assum $ once_rewrite_tac o single
      \\ rw[])
  \\ metis_tac[]
QED

Definition flat_rev'_def:
  flat_rev' [] acc = acc ∧
  flat_rev' (x::xs) acc = flat_rev' xs (REV x acc)
End

Theorem flat_rev'_lemma[local]:
  ∀acc. flat_rev' l acc = (flat_rev' l []) ⧺ acc
Proof
  Induct_on ‘l’
  >- rw[flat_rev'_def]
  \\ rpt strip_tac
  \\ rewrite_tac[flat_rev'_def]
  \\ first_assum $ once_rewrite_tac o single
  \\ rw[REV_REVERSE_LEM]
QED
