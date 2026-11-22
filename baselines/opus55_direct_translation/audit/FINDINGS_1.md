# Audit 1: Prelude, misc, mllist, mlstring (Opus 5.5 translation)

The auditor could not write this file itself (the harness refused subagent file writes and asked for
the findings as text). The orchestrator saved its final report here verbatim.

## Fidelity audit 1 (Prelude, misc, mllist, mlstring): no defects, no suspects, 9 notes

**Scope.** I checked every definition in the 7 Prelude modules against the HOL4 library sources (bool, combin, pair, arithmetic, relation, ternaryComparisons, toto, pred_set, list, rich_list, indexedLists, sorting, mergesort, string, numposrep, ASCIInumbers, finite_map, alist, words, bitstring, fcp, sptree). I also checked every definition and all 76 target statements in Misc (44), Mllist (11) and Mlstring (21). All 76 targets are present under their HOL4 names.

**How I checked.** I compared each declaration with the HOL4 script text, not only the comment: clause order, argument order, implicit quantification, precedence and types. I confirmed points in Lean in `/home/claude/work/audit/ws1/scratch/A1.lean`, `A2.lean` and `A3.lean`; all of these compile:
- `ch '\n'`, `ch '0'`, `ch 'A'`, `ch 'a'` and `ch 'F'` have the right codes.
- `splitlines (str "") = []` and `splitlines [ch '\n'] = [[]]`.
- `v2w [True] = n2w 1` and `v2w [False] = n2w 0` at `word32`.
- I proved `concat_nil`, `substring_0`, `CHR_w2n_n2w_ORD_simp`, `n2w_ORD_CHR_w2n_simp`, `EVEN_make_even`, `is_subseq_nil` and `SmartAppend_thm`, plus the key step of `sort2_tail_PERM`.
- I inspected the elaborated forms of `append_thm`, `mlstring_common_char_prefix`, `CHR_w2n_n2w_ORD`, `MAPi_ID`, `plus_0_I`, `APPLY_UPDATE_LIST_ALOOKUP` and `domain_nat_set_from_list`.

**Notes** (same meaning; none changes any of the 278 targets):
- **N1, word width is a bare `Nat`** (Prelude/Words.lean:20-36). `word n := BitVec n` and `dimindex n := n`, so width 0 is allowed, while HOL4 always has `dimindex ≥ 1` (fcpScript.sml:64). No impact: every word target uses width 8 or 32, and no other module uses words. Any future statement over all widths should assume `0 < n`.
- **N2, `ch` reduces the code mod 256** (Prelude/String.lean:159). It is only correct for ASCII. Every use in scope (`'\n'`, `'0' '9' 'a' 'f' 'A' 'F'`) was checked by `rfl`.
- **N3, unspecified HOL4 values are fixed Lean values.** This covers `ARB`, `HD []`, `LAST []`, `CHR n` for n ≥ 256, `FAPPLY` outside the domain, and `SEG` and `FUN_FMAP` (chosen by ε from their specs). This matches HOL4. In particular, `FAPPLY` outside the domain is one value for every map and key, as HOL4's `OUTL (INR one)` is. `FUN_FMAP_FAPPLY_FEMPTY_FAPPLY` depends on this, and it holds the same way in both systems.
- **N4, `[Nonempty]` instances** on `find_index_ALL_DISTINCT_EL` (Misc.lean:177) and `FUN_FMAP_FAPPLY_FEMPTY_FAPPLY` (Misc.lean:213). Harmless, because every HOL4 type is nonempty.
- **N5, `append_thm` (Misc.lean:58) has three independent type variables.** This is exactly what HOL4 type inference gives (miscScript.sml:141). A version with one shared `α` would be equivalent, so a type-signature difference of that kind here changes nothing.
- **N6, `mlstring_common_char_prefix` (Mlstring.lean:220) copies the HOL4 quirks.** The HOL4 text has a duplicate binder `t2` and leaves `t1` and `c2` free (mlstringScript.sml:207). The Lean statement keeps both, and only the binder order differs. Precedence also matches (`^` is at 480, left associative).
- **N7, HOL4 `bool` is Lean `Prop`.** This applies to `neg`/`negate` in the sorting functions, to `bitstring = List Prop`, and to relations. It is equivalent under `propext` and classical logic; proofs will need `by_cases`.
- **N8, well-founded definitions use Lean termination measures.** This covers `merge_tail`, `mergesortN_tail` (last clause written `n+4`), `FIELDS`, `n2l`, `compare_aux` and sptree `lookup`/`insert`. The equations are the HOL4 clauses, and the order of overlapping patterns matches HOL4's first-match rule. I checked this for `merge_tail`, `mergesortN_tail`, `SmartAppend`, `string_lt`, `is_subseq`, `LIST_REL` and `ZIP`. HOL4 `ZIP` is a specification, but its equations fix every value, so the direct definition is equivalent.
- **N9, `MEM` is written `x ∈ l` (Lean `List.Mem`) and `set` is `LIST_TO_SET`.** They are equivalent; proofs will need a bridge lemma between the two forms.

**Also found faithful**, by name:
- **Prelude:** `UPDATE`, `LEX`, `RTC` (inductive), `TotOrd`, `TO_of_LinearOrder`, `GSPEC`, `FINITE` (impredicative), `PERMUTES`, `TL []`/`FRONT []` = `[]`, `SEG`, `PERM`, `SORTED`, `sort2_tail`/`sort3_tail`, the fmap encoding and its operations, `alist_to_fmap` (first entry wins), `string_lt`, `HEX` (HOL4 itself gives `CHR 0` for n ≥ 16, so this is not ARB), `UNHEX`, `n2w`/`w2n`/`FCP`/`v2w`, and the sptree functions.
- **Misc, Mllist, Mlstring:** every definition and every target. The derived statements match what the HOL4 ML code produces: `w2n_lt_256` is `∀w:word8. w2n w < 256`, and `splitlines_nil` is `splitlines "" = []`. `strcat_assoc` has the right-hand side `(s1^s2)^s3`. No statement uses `BEq` or `==`; the derived `DecidableEq` instances decide real equality.

**Uncertainty:** I proved only about 10 of the 76 targets, or their key steps. For the rest, faithfulness rests on comparing the text and the elaborated statements, not on proofs.

The baseline holds up in this scope: the only differences are modelling choices, and none can make a target false or trivially true.
