# FINDINGS_1: fidelity audit of Prelude/*, Misc, Mllist, Mlstring

Scope: `CandleLean/Prelude/{Basic,PredSet,List,String,FiniteMap,Words,Mergesort}.lean`, `CandleLean/Misc.lean`, `CandleLean/Mllist.lean`, `CandleLean/Mlstring.lean`. That is all definitions plus the 76 target theorems of misc, mllist and mlstring. I compared each one with the HOL4 script text (`misc/miscScript.sml`, `basis/pure/mllistScript.sml`, `basis/pure/mlstringScript.sml`) and with the HOL4 library sources under `ws/hol4/HOL4-src/`.

**Result: no defects, no suspects.** Every definition and target statement in scope means the same as its HOL4 original. The entries below are notes: modelling choices worth recording, or traps from the brief that I checked on purpose.

Lean checks, run in `/home/claude/work/audit/ws1/scratch/T1.lean` and `T2.lean` (all passed unless stated):
- `splitlines str!"" = []` (the EVAL value behind `splitlines_nil`)
- `splitlines str!"a\n" = [str!"a"]`
- `v2w [True] : word32 = n2w 1` and `v2w [False] : word32 = n2w 0`
- `concat [] = ml!""`
- `mlstring_lt ml!"a" ml!"b"` and `mlstring_lt ml!"" ml!"b"`
- `strcat (strcat «a» «b») «c» = «abc»`
- `strcat_assoc` and `concat_sing`: full proofs
- `substring_0`: the goal left is true, but my final `rfl` failed because it needed `omega`
- `num_from_hex_string (num_to_hex_string 26) = 26`
- `{a, b} = INSERT a (INSERT b ∅)` by `rfl`
- `7/0 = 0 ∧ 7%0 = 7`

## Notes

**N1. Unspecified values come from choice: HD, LAST, SEG, CHR, OUTL, FUN_FMAP.**
- Lean: Prelude/List.lean:23, :125, :215; String.lean:60; Basic.lean:100; FiniteMap.lean:71.
- HOL4: listScript.sml:138 (HD), :2124 (LAST_DEF); rich_listScript.sml:277-285 (SEG, `new_specification`); sumScript.sml:286 (OUTL, `new_recursive_definition`); finite_mapScript.sml:1585 (FUN_FMAP_DEF, `new_specification`); the string char bijections.
- Each Lean constant is `select` of a function satisfying the HOL clauses.
- HOL4 also leaves these values unspecified rather than `ARB`. `Defn.sml:1180-1200` (`non_wfrec_defn`) sends constructor-pattern `Definition`s such as HD and LAST through `Prim_rec`, which does no ARB completion.
- Impact: none. Fix: none.

**N2. `num` DIV, MOD and subtraction match Lean.**
- Lean: Prelude/Basic.lean:108-124, plus users `n2l`, `l2n`, `sptree.insert`, `DIV2`, `mergesortN_tail`, `PAD_LEFT`, `UNHEX`, `compare_aux`.
- HOL4: arithmeticScript.sml:2335-2339 gives `DIV m 0 = 0` and `MOD m 0 = m`, the same as Lean. Truncated subtraction is the same. `UNHEX`'s `10 + n - ORD #"a"` associates the same way in both, and its guard keeps it in range.
- Impact: none.

**N3. HOL `bool` used as data is `Prop`: `negate`/`neg` in mergesort, `bitstring`.**
- Lean: Prelude/Mergesort.lean:83-163, Words.lean:37-65.
- HOL4: mergesortScript.sml:101-159, bitstringScript.sml:51-98.
- `R x y ≠ neg` on `Prop` is XOR, by propext. `testbit` is equality on `List Prop`. `v2w_32_T` and `v2w_32_F` were confirmed in Lean.
- Impact: none. Proofs will need `by_cases` instead of `Bool` reasoning.

**N4. Clause order in `mergesortN_tail` and `merge_tail`.**
- Lean: Prelude/Mergesort.lean:111-158. HOL4: mergesortScript.sml:127-155.
- The HOL general clause applies exactly for `n ≥ 4`, because `n = 0..3` are fully covered first. This matches the Lean `n + 4` pattern.
- The overlapping `merge_tail` clauses take the first match in both.
- Lean uses well-founded recursion, so proofs need the equation lemmas.
- Impact: none.

**N5. `char`, `string`, `mlstring` and `strlit`.**
- Lean: String.lean:15-86, Mlstring.lean:15-29. HOL4: stringScript.sml (`string_lt_def` at 615), mlstringScript.sml:19-25.
- `char` equality is equality of `val`, by proof irrelevance. `char_lt` is `ORD a < ORD b`. The `string_lt` clause order matches.
- `strlit` is an abbrev of `implode`, matching the HOL overload.
- No statement uses `BEq` or `==` (checked by grep). The derived `DecidableEq` is never used in place of HOL equality.
- Impact: none.

**N6. `word N` is `BitVec N`; `v2w` goes through `FCP_value`.**
- Lean: Words.lean:16-65. HOL4: wordsScript.sml:978 (`w2n_lt`), bitstringScript.sml:97.
- `n2w`, `w2n` and `v2w` agree with HOL at widths 8 and 32.
- One difference outside scope: HOL's `dimindex` is always at least 1, while Lean allows `word 0`. Nothing in scope uses a non-literal width.
- `w2n_lt_256` correctly expands the ML pipeline (`INST_TYPE`, then `SIMP_RULE` with `EVAL dimword(:8)`) to `∀ w : word8, w2n w < 256`.
- Impact: none.

**N7. `fmap` is a structure over `α → Sum β Unit` with the HOL `is_fmap` inductive.**
- Lean: FiniteMap.lean:19-79. HOL4: finite_mapScript.sml:69-90, 1079, 1310, 1447, 1585; alistScript.sml:21.
- `fmap` equality is extensional, as in HOL.
- `FAPPLY` off the domain is `OUTL (INR ())`, one value per type, as in HOL. This is what makes `FUN_FMAP_FAPPLY_FEMPTY_FAPPLY` true at `x ∉ s`.
- `FUN_FMAP` has the same Skolem shape as the HOL `new_specification`.
- Impact: none.

**N8. Sets are `α → Prop`; `LIST_TO_SET`/`MEM` use Lean list membership.**
- Lean: PredSet.lean, List.lean:53-63. HOL4: pred_setScript.sml (FINITE_DEF 2909, IMAGE_DEF 1808, PERMUTES 6275).
- `FINITE` is the HOL closure definition, so infinite sets are allowed. `PERMUTES` is `BIJ f s s`, which is the overload in scope.
- Impact: none.

**N9. Extra type variables and `[Nonempty _]` binders.**
- Example: Misc.lean:147, `append_thm` with types α, β, γ.
- HOL type inference gives the three independent conjuncts independent type variables, so this is faithful. `Nonempty` always holds for HOL types.
- No statement in scope is narrower or wider in type than its HOL original.
- Impact: none.

**N10. `mlstring_common_char_prefix`: free variables and a duplicate binder.**
- HOL4: mlstringScript.sml:207 has `∀c1 s1 s2 t2 t2.` with `t1` and `c2` free (a typo in the source).
- Lean makes `t1` and `c2` parameters and keeps `(t2 t2 : mlstring)`, where the inner binder shadows the outer one as in HOL.
- The meaning is the same. Impact: none.

**N11. `^` on mlstring is `strcat`, left associative.**
- HOL4: mlstringScript.sml:165-166 sets `add_infix("^",480,LEFT)`; the statement is at line 181.
- HOL4 core gives `^` no other fixity. The only `"^"` in arithmeticScript is an OpenTheory name.
- So `s1 ^ s2 ^ s3` is `(s1 ^ s2) ^ s3`, and the Lean `strcat_assoc` is non-trivial. It was proved in scratch.
- `toString` is only the overload `chr_to_str` (line 249).
- Impact: none.

## Summary table

| id | Lean | HOL4 | declarations | class | target impact |
|---|---|---|---|---|---|
| N1 | List.lean:23,125,215; String:60; Basic:100; FiniteMap:71 | listScript 138,2124; rich_list 277; sum 286; finite_map 1585 | HD, LAST, SEG, CHR, OUTL, FUN_FMAP | note | none |
| N2 | Basic.lean:108-124 and users | arithmetic 2335-2339 | DIV, MOD, `-` | note | none |
| N3 | Mergesort.lean, Words.lean | mergesort 101-159; bitstring 51-98 | bool data as `Prop` | note | none (proof style only) |
| N4 | Mergesort.lean:111-158 | mergesort 127-155 | merge_tail, mergesortN_tail | note | none |
| N5 | String.lean, Mlstring.lean:15-29 | stringScript; mlstring 19-25 | char, string, mlstring, strlit | note | none |
| N6 | Words.lean | words 978; bitstring 97 | word, n2w, w2n, v2w | note | none |
| N7 | FiniteMap.lean | finite_map 69-1585 | fmap and its operations | note | none |
| N8 | PredSet.lean, List.lean:53-63 | pred_set | Set, FINITE, PERMUTES, set, MEM | note | none |
| N9 | Misc.lean:147 and others | misc `append_thm` | type variables | note | none |
| N10 | Mlstring `mlstring_common_char_prefix` | mlstring 207 | free and duplicate variables | note | none |
| N11 | Mlstring `strcat_assoc` and others | mlstring 165, 181 | `^` fixity | note | none |

## Checked and found faithful

- **Prelude/Basic:** select, select_spec, ARB, EXISTS_UNIQUE, K, S, I, C, UPDATE, FST, SND, UNCURRY, PAIR_MAP (including the precedence of `##`), LEX, OPTION_MAP, OPTION_BIND, ISL, OUTL, SUC, MAX, EVEN, DIV2, transitive, reflexive, irreflexive, trichotomous, RC, RTC, inv_image, StrongOrder, StrongLinearOrder, ordering, invert_comparison, flip_ord, TotOrd, TO_of_LinearOrder.
- **Prelude/PredSet:** Set, membership, setOf, GSPEC, EMPTY, UNIV, SUBSET, UNION, INTER, DIFF, INSERT, set literals, DISJOINT, IMAGE, INJ, SURJ, BIJ, PERMUTES, FINITE, INFINITE.
- **Prelude/List:** NULL, HD, TL, APPEND, FLAT, LENGTH, MAP, LIST_TO_SET, set, MEM, FILTER, FOLDR, FOLDL, EVERY, EXISTS, EL, LIST_REL, EVERY2, ZIP, REVERSE, REV, LAST, FRONT (`FRONT []` is defined in HOL4 too), TAKE, DROP, ALL_DISTINCT, isPREFIX, SNOC, GENLIST, PAD_LEFT, LLEX, OPT_MMAP, MAX_LIST, SEG, SPLITP, MAPi, PERM, SORTED, ALOOKUP.
- **Prelude/String:** char, string, the literal macros, ORD, CHR, char_lt, string_lt, FIELDS, l2n, n2l, s2n, n2s, HEX, UNHEX, num_from_hex_string, num_to_hex_string.
- **Prelude/FiniteMap:** is_fmap, fmap, FEMPTY, FUPDATE, FAPPLY, FDOM, FLOOKUP, FEVERY, FRANGE, FUN_FMAP, alist_to_fmap, spt, num_set, num_map, sptree.insert, sptree.domain.
- **Prelude/Words:** word, word8, word32, dimword, n2w, w2n, bitstring, zero_extend, fixwidth, shiftr, field, testbit, FCP_value, v2w.
- **Prelude/Mergesort:** sort2_tail, sort3_tail, merge_tail, mergesortN_tail, mergesort_tail.
- **Misc definitions:** app_list, append_aux, append, SmartAppend (first-match clause order), max3, UPDATE_LIST (argument order), find_index, splitlines, is_subseq, make_even, fmap_update.
- **Misc targets (43):** all of them, including:
  - precedence and fixity in UPDATE_LIST_THM, FUN_FMAP_FAPPLY_FEMPTY_FAPPLY and FIELDS_next;
  - bool `=` written as `↔` in MAP_EQ_ID;
  - the ML-generated statements w2n_lt_256 and splitlines_nil.
- **Mllist:** sort and all 11 targets.
- **Mlstring definitions:** mlstring, strlit, strlen, strsub, substring, concat, explode_aux, explode, strcat, chr_to_str, compare_aux, compare, mlstring_lt, app_list_ann, char_to_word8, word8_to_char.
- **Mlstring targets (25):** all of them.

## Limits of this audit

- I checked whether targets are true only by matching each one against its HOL4 text and by the small Lean experiments above. I did not prove the targets in general.
- I compared the prelude against the HOL4 sources in `ws/hol4/HOL4-src/`, assuming that is the HOL4 version the package builds against.