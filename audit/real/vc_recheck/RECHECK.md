# V-C recheck (27 November 2026)

Plan v3.4, section 3, asks that every counterexample behind a V-C label respect the saved HOL4 theorems and their dependencies, and that the label stay `unsure` where this is not verified. This file checks the 42 HOL4 counterexamples behind the 63 V-C (declaration, translation) pairs of the key.

## Result

| Verdict | Entries | Pairs |
|---|---|---|
| V-C | 36 | 56 |
| holds in HOL4 | 6 | 7 |
| unsure | 0 | 0 |

- **V-C** (56 pairs): the counterexample is a model of the HOL4 theory, so every saved theorem holds in it, and the Lean equation fails in it.
- **holds in HOL4** (7 pairs): HOL4's kernel definition fixes the value to ARB, and the Lean equation states exactly that. It is true in every model of the HOL4 theory, so it is not a V-C error. These leave the key (`key.json`, field `recheck`); the tables are recomputed (`../TABLES.md`; key as run: `../TABLES_pre_recheck.md`).

## Method

1. How each constant is introduced was read from the HOL4 and CakeML sources and from HOL4's definition code (`Defn.prim_mk_defn`, src/tfl/src/Defn.sml:1281). A one-argument pattern definition over a datatype goes through `Prim_rec.new_recursive_definition`, a `new_specification`: the missing cases are left open (loose). A multi-argument or nested pattern definition goes through TFL, which fills missing patterns with `ARB` (Pmatch.sml) in the kernel definition `f = WFREC R (\f a. case a of ... => ARB ...)`; this kernel definition is not among the saved theorems.
2. Loose (L): the counterexample replaces the constant c by c' = (\x. if P x then g x else c x), with g arbitrary (for SEG a different closed form, since its specification ties the open values together). HOL4 proves, for every g, that c' satisfies c's specification. Constants defined later from c are reinterpreted by their own definitions (a constant definition fixes them; a later specification is met by some witness, because its existence theorem holds in the new model). Then the new interpretation is a model of the HOL4 theory, so every saved theorem holds in it (soundness of HOL with loose specifications; Candle proves this for its own kernel). The Lean equation e fixes c inside P, so it fails for a suitable g.
3. ARB (A): ARB has no axiom, so varying ARB at one type gives a model too, but the TFL constant changes with it: c args = ARB holds in every model. HOL4 proves c args = ARB on P from the kernel definition. The theories here do not save that definition, so it was proved on a copy defined by the same `Define` from the saved equations (`arb_value_*.sml`); the copy's kernel definition is printed in the logs.
4. Supplement: `vcheck.py` also rewrote every saved theorem that mentions c (with the ancestors; HD also changes EL) and tried fixed tactics with a 15 s limit (column "theorems re-proved"). A failure there is not a refutation: most failures are definitions of other constants built on c, which the model reinterprets, or tactic limits. This check alone would leave most entries `unsure`.

## Entries

| Key declaration | Family | Translations | P (region varied) | How HOL4 introduces it | Evidence | Theorems re-proved (supplement) | Verdict |
|---|---|---|---|---|---|---|---|
| ARB | candle | candle_sonnet | `T` | new_constant, no axiom (boolScript.sml:245) | no axiom mentions ARB; the type `itself`, defined from ARB (boolScript.sml:4481), is reinterpreted with it | 31 of 80 | V-C |
| CARD | ts | ts_sonnet | `s = UNIV /\ INFINITE s` | new_specification, guarded by FINITE (pred_setScript.sml:3428) | `CARD_DEF` with the replacement: rw (vcheck.py) | 107 of 141 | V-C |
| CHR | candle | candle_opus, candle_sonnet | `n = 256` | type bijection: joint specification char_BIJ with ORD (stringScript.sml:25-29) | `CHR_256` proved (spec_manual.sml) | 51 of 81 | V-C |
| CHR | ts | ts_opus | `n = 256 \/ n = 257` | type bijection: joint specification char_BIJ with ORD (stringScript.sml:25-29) | `CHR_256_257` proved (spec_manual.sml) | 26 of 42 | V-C |
| CHR | ts | ts_opus_nolessons | `n = 256` | type bijection: joint specification char_BIJ with ORD (stringScript.sml:25-29) | `CHR_256` proved (spec_manual.sml) | 26 of 42 | V-C |
| CHR | ts | ts_sonnet | `n = 300 \/ n = 301` | type bijection: joint specification char_BIJ with ORD (stringScript.sml:25-29) | `CHR_300_301` proved (spec_manual.sml) | 26 of 42 | V-C |
| CLASH | candle | candle_opus, candle_opus_nolessons, candle_sonnet | `?s. r = Result s` | primitive recursion, one clause (holSyntaxLibScript.sml:92) | `CLASH_def` with the replacement: rw (vcheck.py) | 1 of 3 | V-C |
| FAPPLY | candle | candle_opus | `?y. s = INR y` | new_recursive_definition OUTL (INL x) = x (sumScript.sml:286); FAPPLY f x = OUTL (fmap_REP f x) is an abbreviation (finite_mapScript.sml:180) and changes with OUTL | `OUTL` with the replacement: rw (vcheck.py) | 5 of 66 | V-C |
| FAPPLY | ts | ts_opus, ts_opus_nolessons, ts_sonnet | `?y. s = INR y` | new_recursive_definition OUTL (INL x) = x (sumScript.sml:286); FAPPLY f x = OUTL (fmap_REP f x) is an abbreviation (finite_mapScript.sml:180) and changes with OUTL | `OUTL` with the replacement: rw (vcheck.py) | 5 of 60 | V-C |
| FUN_FMAP | candle | candle_sonnet | `INFINITE s` | new_specification, guarded by FINITE (finite_mapScript.sml:1585) | `FUN_FMAP_DEF` with the replacement: rw_metis (vcheck.py) | 11 of 13 | V-C |
| FV_dec | ts | ts_opus | `?n. d = Denv n` | primitive recursion, no clause for Denv, Dmod, Dlocal (semanticPrimitivesPropsScript.sml:220) | `FV_dec_def` with the replacement: rw (vcheck.py) | 1 of 1 | V-C |
| FV_dec | ts | ts_opus_nolessons | `(?m. d = Dmod m []) \/ d = Dlocal [] []` | primitive recursion, no clause for Denv, Dmod, Dlocal (semanticPrimitivesPropsScript.sml:220) | `FV_dec_def` with the replacement: rw (vcheck.py) | 1 of 1 | V-C |
| FV_dec | ts | ts_sonnet | `d = Denv (strlit "") \/ d = Dmod (strlit "") [] \/ d = Dlocal [] []` | primitive recursion, no clause for Denv, Dmod, Dlocal (semanticPrimitivesPropsScript.sml:220) | `FV_dec_def` with the replacement: rw (vcheck.py) | 1 of 1 | V-C |
| HD | candle | candle_opus, candle_opus_nolessons, candle_sonnet | `l = []` | primitive recursion HD (h::t) = h (listScript.sml:138) | `HD_spec` proved (spec_manual.sml) | 33 of 262 | V-C |
| HD | ts | ts_opus, ts_opus_nolessons, ts_sonnet | `l = []` | primitive recursion HD (h::t) = h (listScript.sml:138) | `HD_spec` proved (spec_manual.sml) | 30 of 261 | V-C |
| LAST | candle | candle_opus, candle_opus_nolessons, candle_sonnet | `l = []` | primitive recursion on h::t (listScript.sml:2124) | `LAST_DEF` with the replacement: rw_metis (vcheck.py) | 47 of 54 | V-C |
| MAP3 | ts | ts_opus | `(l1 = [] /\ ~(l2 = []) /\ l3 = []) \/ (~(l1 = []) /\ l2 = [] /\ l3 = [])` | TFL definition; pattern completion gives ARB on unequal shapes (miscScript.sml:74) | `MAP3_a` proved (arb_value_ts.sml), `MAP3_b` proved (arb_value_ts.sml) | 0 of 1 | holds in HOL4 |
| MAP3 | ts | ts_opus_nolessons | `l1 = [] /\ ~(l2 = []) /\ l3 = []` | TFL definition; pattern completion gives ARB on unequal shapes (miscScript.sml:74) | `MAP3_a` proved (arb_value_ts.sml) | 0 of 1 | holds in HOL4 |
| MAP3 | ts | ts_sonnet | `~(l1 = []) /\ l2 = [] /\ l3 = []` | TFL definition; pattern completion gives ARB on unequal shapes (miscScript.sml:74) | `MAP3_b` proved (arb_value_ts.sml) | 0 of 1 | holds in HOL4 |
| RESULT | candle | candle_opus, candle_opus_nolessons, candle_sonnet | `?s. r = Clash s` | primitive recursion, one clause (holSyntaxLibScript.sml:88) | `RESULT_def` with the replacement: rw (vcheck.py) | 2 of 5 | V-C |
| SEG | candle | candle_sonnet | `m = 1 /\ k = 0 /\ l = []` | new_specification (rich_listScript.sml:285); SEG (SUC m) k [] is open | `SEG_spec` proved (spec_manual.sml), `SEG_witness_fails` proved (spec_manual.sml); SEG' m k l = TAKE m (DROP k l) ++ REPLICATE (m - (LENGTH l - k)) a | 24 of 36 | V-C |
| THE | ts | ts_opus, ts_opus_nolessons | `x = NONE` | new_recursive_definition THE (SOME x) = x (optionScript.sml:176) | `THE_DEF` with the replacement: rw (vcheck.py) | 15 of 48 | V-C |
| dest_Refv | ts | ts_opus, ts_sonnet | `r = W8array []` | primitive recursion, one clause (semanticPrimitivesPropsScript.sml:165) | `dest_Refv_def` with the replacement: rw (vcheck.py) | 1 of 1 | V-C |
| dest_Refv | ts | ts_opus_nolessons | `r = Varray []` | primitive recursion, one clause (semanticPrimitivesPropsScript.sml:165) | `dest_Refv_def` with the replacement: rw (vcheck.py) | 1 of 1 | V-C |
| dest_var | candle | candle_opus, candle_opus_nolessons | `?a ty. tm = Const a ty` | primitive recursion, one clause (holSyntaxScript.sml:57) | `dest_var_def` with the replacement: rw (vcheck.py) | 1 of 15 | V-C |
| int_div | ts | ts_opus | `j = 0 /\ (i = 5 \/ i = 1 \/ i = 2)` | new_specification, guarded by j <> 0 (integerScript.sml:1989) | `int_div` with the replacement: metis (vcheck.py) | 31 of 39 | V-C |
| int_div | ts | ts_opus_nolessons | `j = 0` | new_specification, guarded by j <> 0 (integerScript.sml:1989) | `int_div` with the replacement: metis (vcheck.py) | 29 of 39 | V-C |
| int_div | ts | ts_sonnet | `j = 0 /\ (i = 1 \/ i = 2)` | new_specification, guarded by j <> 0 (integerScript.sml:1989) | `int_div` with the replacement: metis (vcheck.py) | 31 of 39 | V-C |
| int_mod | ts | ts_opus | `j = 0 /\ (i = 1 \/ i = 2)` | new_specification, guarded by j <> 0 (integerScript.sml:2074) | `int_mod` with the replacement: rw_metis (vcheck.py) | 29 of 35 | V-C |
| int_mod | ts | ts_opus_nolessons | `j = 0` | new_specification, guarded by j <> 0 (integerScript.sml:2074) | `int_mod` with the replacement: rw_metis (vcheck.py) | 27 of 35 | V-C |
| int_mod | ts | ts_sonnet | `j = 0 /\ i = 7` | new_specification, guarded by j <> 0 (integerScript.sml:2074) | `int_mod` with the replacement: rw_metis (vcheck.py) | 29 of 35 | V-C |
| locnrow | ts | ts_opus, ts_sonnet | `l = UNKNOWNpt` | primitive recursion on POSN (locationScript.sml:6) | `locnrow_def` with the replacement: rw_metis (vcheck.py) | 1 of 1 | V-C |
| locnrow | ts | ts_opus_nolessons | `l = EOFpt` | primitive recursion on POSN (locationScript.sml:6) | `locnrow_def` with the replacement: rw_metis (vcheck.py) | 1 of 1 | V-C |
| locncol | ts | ts_opus, ts_sonnet | `l = EOFpt` | primitive recursion on POSN (locationScript.sml:16) | `locncol_def` with the replacement: rw_metis (vcheck.py) | 1 of 1 | V-C |
| locncol | ts | ts_opus_nolessons | `l = UNKNOWNpt` | primitive recursion on POSN (locationScript.sml:16) | `locncol_def` with the replacement: rw_metis (vcheck.py) | 1 of 1 | V-C |
| locn_rowupdate | ts | ts_opus | `l = UNKNOWNpt` | primitive recursion on POSN (locationScript.sml:11) | `locn_rowupdate_def` with the replacement: rw_metis (vcheck.py) | 1 of 1 | V-C |
| locn_rowupdate | ts | ts_opus_nolessons, ts_sonnet | `l = EOFpt` | primitive recursion on POSN (locationScript.sml:11) | `locn_rowupdate_def` with the replacement: rw_metis (vcheck.py) | 1 of 1 | V-C |
| locn_colupdate | ts | ts_opus, ts_opus_nolessons | `l = EOFpt` | primitive recursion on POSN (locationScript.sml:20) | `locn_colupdate_def` with the replacement: rw_metis (vcheck.py) | 1 of 1 | V-C |
| locn_colupdate | ts | ts_sonnet | `l = UNKNOWNpt` | primitive recursion on POSN (locationScript.sml:20) | `locn_colupdate_def` with the replacement: rw_metis (vcheck.py) | 1 of 1 | V-C |
| termsem0 | candle | candle_opus | `?a b. t = Abs a b /\ (!x ty. ~(a = Var x ty))` | TFL definition; pattern completion gives ARB for Abs of a non-variable (holSemanticsScript.sml:134) | `termsem` proved (arb_value_candle.sml) | 3 of 13 | holds in HOL4 |
| type_def_to_ctMap | ts | ts_opus, ts_opus_nolessons | `tds = [] /\ (?i. ids = [i])` | TFL definition; pattern completion gives ARB for tds = [], ids non-empty (typeSysPropsScript.sml:1502) | `tdc` proved (arb_value_ts.sml) | not run (argument type did not parse) | holds in HOL4 |
| type_def_to_ctMap | ts | ts_sonnet | `next_stamp = 0 /\ tds = [] /\ (?i. ids = [i])` | TFL definition; pattern completion gives ARB for tds = [], ids non-empty (typeSysPropsScript.sml:1502) | `tdc` proved (arb_value_ts.sml) | not run (argument type did not parse) | holds in HOL4 |

## Limitations

- The argument rests on soundness of HOL4 with loose specifications, not on a proof of each saved theorem in the new model. The type-soundness theories here come from a fast build (`--fast`), whose proofs are not re-run; their theorems are proved in CakeML's full build.
- For the TFL constants the kernel definition was reproduced on a copy, not read from the theory. ARB-valued equations relating two open points (for example two list shapes of MAP3) also hold in HOL4, for the same reason.
- The readers of the blinded check answered "yes" on the rows of the dropped pairs: they judged against the saved theorems, which do not state the ARB cases (`../check/CHECK_RESULTS_recheck.md`).
- Varying ARB reinterprets the type `itself` with it (its carrier is {ARB}); this is a model change, not a theorem checked in HOL4.
