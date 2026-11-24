# Fidelity scoring: sonnet_lessons

Project: E:/ts_ws/runs/sonnet_lessons_v2/merged (Lean 4.28.0). Witnesses: witnesses.lean (checked with lake env lean, no errors). Logs: log_defs.tsv (553 lines), log_stmts.tsv (267 lines).

## Counts
V-P 0 found. V-C1 19 constants. V-C2 1 (prelude ARB). unsure 0.

## V-C1 (Lean fixes a value that the saved HOL4 theorem leaves open)
Test: Lean proves an equation of mapped constants (and ARB); HOL4 saves only the clauses cited, so two models of the saved defining theorem disagree. No saved theorem fixing the value was found for any item.

- HD: Prelude/List.lean:53. Witness vc1_HD_nil. HOL4 listScript.sml:138 (only HD (h::t) = h). EL inherits.
- CHR: Prelude/Num.lean:35. Witnesses vc1_CHR_300_eq_ARB, vc1_CHR_300_eq_CHR_301. HOL4 stringScript.sml:29 char_BIJ.
- int_div: Prelude/Num.lean:81. vc1_int_div_zero. HOL4 integerScript.sml:1989 (new_specification, j<>0 only).
- int_mod: Prelude/Num.lean:85. vc1_int_mod_zero_eq_ARB. HOL4 integerScript.sml:2074.
- FAPPLY: Prelude/FMap.lean:38. vc1_FAPPLY_outside. HOL4 finite_mapScript.sml:180; only saved fact is NOT_FDOM_FAPPLY_FEMPTY (:563), which does not equate FAPPLY FEMPTY 0 and FAPPLY FEMPTY 1.
- CARD: Prelude/Basic.lean:70. vc1_CARD_UNIV (CARD UNIV = 0 on Nat). HOL4 pred_setScript.sml:3428 CARD_DEF (new_specification, FINITE only).
- MAP3: Misc.lean:60. vc1_MAP3_mismatch. HOL4 miscScript.sml:74.
- locnrow, locn_rowupdate, locncol, locn_colupdate: Location.lean:31/41/51/61. vc1_locnrow_UNKNOWN, vc1_locn_rowupdate_EOF, vc1_locncol_EOF, vc1_locn_colupdate_UNKNOWN. HOL4 locationScript.sml:6, 11, 16, 20.
- dest_Refv: SemanticPrimitivesProps.lean:88. vc1_dest_Refv_W8array. HOL4 semanticPrimitivesPropsScript.sml:165.
- FV_dec (Dmod, Dlocal, Denv): SemanticPrimitivesProps.lean:180. vc1_FV_dec_Dmod, _Dlocal, _Denv. HOL4 semanticPrimitivesPropsScript.sml:220.
- the_Litv_IntLit, _Word8, _Word64, _Float64, _Char: SemanticPrimitives.lean:1155-1187. vc1_the_Litv_IntLit_Conv, vc1_the_Litv_Char_Conv (others same shape). HOL4 semanticPrimitivesScript.sml:718-734.
- type_def_to_ctMap (unequal list lengths): TypeSysProps.lean:78. vc1_type_def_to_ctMap_mismatch. HOL4 typeSysPropsScript.sml:1502.
- Shared ARB across constants: vc1_shared_ARB_Nat_HD_locnrow, vc1_shared_ARB_Nat_FAPPLY_locncol.

Refutation: searched HOL4 for saved theorems fixing each value; none. For the TFL-defined constants (HD, MAP3, locn*, dest_Refv, FV_dec, the_Litv_*, type_def_to_ctMap) the finding relies on the plan's rule that the TFL primitive definition is not a saved theorem; CHR, int_div, int_mod, FAPPLY, CARD do not depend on it.

## V-C2
- ARB (Prelude/Basic.lean:18, Classical.choice): Lean proves Classical.epsilon (fun _ => False) = ARB (vc2_eps_false_eq_ARB); consumer closest_such over an empty set equals ARB (vc2_closest_such_empty). HOL4 ARB is new_constant with no equation (boolScript.sml:245), so two HOL4 models disagree.

## V-P
None. Checked among others: ORD/CHR below 256, PERMUTES (overload of BIJ f s s, pred_setScript.sml:6275), IS_PREFIX orientation, word shifts, Num of negatives, LLENGTH, float round/closest_such.

## Notes (not violations)
[Nonempty] hypotheses; finite maps as subtype; weakS_poly/weakCT_poly; monomorphic type_def_to_ctMap theorems; Type 0 restriction in some statements; EVERY_LIST_REL generalised; renamed theorems (concrete_v_list_eq, type_subst_thm); mlstring_gt/ge instead of > and >=. do_app_cases (40 operator cases) and type_op_cases compared in full and equivalent.

## Unsure
None.

## Coverage
Statements: all 267 compared with statements_pretty.txt, 0 unread (statements only; provability not checked, all are sorry). Definitions: 315 TARGETS definition/datatype/inductive rows plus prelude constants, 0 unread; but for the large modules (SemanticPrimitives, TypeSystem, TypeSoundInvariants, Namespace, Ffi, FpSem, Evaluate, TypeSysProps, Weakening) the comparison was a single side-by-side reading pass and the log reasons are generic. No numeric or evaluation tests of ok definitions against HOL4 values. RealX float model checked by reading only. V-C2 search beyond ARB/epsilon-over-empty-predicate was not exhaustive.

## Wrong comments
None found in the parts read; comments were not audited line by line.
