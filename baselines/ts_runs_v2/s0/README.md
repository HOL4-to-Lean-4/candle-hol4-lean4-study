# S0 scan for the Lean type-soundness translations (port of the Candle S0 tool)

Model-free statement scan. Each of the 267 theorem statements of a Lean project is translated into one canonical form and compared with the HOL4 kernel export (`candle_study/tools/hol4_query/out_ts/statements.jsonl`). The original tool (`candle_study/tools/s0_scan/`) was not edited.

## Layout
- `scan.py`, `DumpLean.lean`, `run.sh PROJECT OUT MAP`, `runscan.sh RUN SUB MAP`: generalised copy of the tool. `S0_ROOT` (default `CmlTS`) replaces the hard-coded `Candle` prefix; the dump file uses an `@@ROOT@@` placeholder filled in by `run.sh`.
- `build_map.py`: writes the v0 maps from HOL4 constant names, the run's CONVENTIONS.md tables and Lean name existence. It is run before any disagreement was looked at.
- `map_<run>.v0.tsv`: the frozen pre-fitting maps (do not edit; they define "before").
- `fit_maps.py`, `fit_edits_extra.py`: apply the fitted edits on top of v0 and write `map_<run>.tsv`.
- `results/<run>/report.json`, `results/<run>/summary.txt`: final scans. `out/<run>/v0/`: the before scans (rescanning with `map_<run>.v0.tsv` and the current `scan.py` reproduces 77/74/84 exactly).
- `mutate.py`, `mutations_main.json`, `mutations_blind.json`, `results/selftest_*`, `scratch/`: self-test.

## Generalisations of the original tool
- Namespace and module prefix are parameters: `NS` row (constant prefix, e.g. `CmlTS.`) and `NAME` rows (explicit theorem renames) are used by `lean_name_for`. The sonnet run has no prefix.
- Map filter syntax `Name#Inst` (a row applies only when an instance argument is `Inst`) is used for Int/Nat instance differences.
- Rules in the map (RULE rows, `@name`): record updates (`f_fupd (K e) s` equals `Struct.mk` over projections), `X_CASE` and Lean matchers as `('case', discrs, alts)`, `decide p` = `p`, `b = true` = `b`, `K` reduction, `{x}` = `INSERT x EMPTY`, `MEM x l` = `LMEM`, Int numerals, `ZIP (a,b)` pair argument in the opus runs.
- Instances check: only EXTRA classes in Lean are flagged (a theorem may need fewer instances than HOL4 types have). The original compared both directions.
- Extras (Lean theorems without a HOL4 counterpart) are counted only if they are sorry theorems.
- The four clashing names are mapped by explicit `NAME` rows: `concrete_v_list`, `tveLookup_freevars`, `type_subst`, `EVERY_LIST_REL`.

## Results (267 of 267 matched, 0 missing, 0 extras in all runs; definition audit flags nothing)

| run | flags before fitting (v0) | flags after | fitted rows | map rows by status after |
|---|---|---|---|---|
| opus_lessons | 77 (28.8%) | 9 (3.4%) | 7 | convention 419, lean-core 28, fitted 7 |
| opus_nolessons | 74 (27.7%) | 7 (2.6%) | 5 | convention 419, lean-core 28, fitted 5 |
| sonnet_lessons | 84 (31.5%) | 23 (8.6%) | 9 | convention 415, lookup 3, lean-core 28, fitted 9 |

Caveat for reading the drop from 77/74/84: the v0 maps are built from CONVENTIONS.md and library names only; the fitted rows below were added after seeing disagreements. They are meaning-preserving normalisations (each was inspected on affected statements), but the "after" number is a fitted number. The self-test below runs with the fitted rules active.

### Fitted rows and rules (all marked `fitted` in the map)
- RULE PAIRN (all runs): a tuple pattern with n > 2 components is one matcher alternative; parameters are right-nested FST/SND projections.
- RULE ETAQ (all runs): kernel `$! P` / `$? P` (eta-contracted quantifier) is expanded to a binder on the HOL4 side.
- RULE RECMK (all runs): a HOL4 record literal is an update of ARB that sets every field; a Lean `Struct.mk` without a common root is the same literal; a literal made of projections of one record is that record.
- RULE TDEF (all runs): `Texn`, `Tref t`, `Tfn a b`, `Tlist t`, ... unfolded to `Tapp [...] T*_num` on both sides (definitions of typeSystem).
- TYPE `namespace$namespace` -> `[CmlTS.]Namespace` (all runs; v0 missed the CONVENTIONS rename; it caused 57 unmapped flags).
- NAME `typeSound$EVERY_LIST_REL_local` -> `EVERY_LIST_REL` and NAME `typeSound$EVERY_LIST_REL` -> `EVERY_LIST_REL_2` (opus_lessons) / `EVERY_LIST_REL'` (sonnet). v0 had the two copies the wrong way round (the `[local]` copy in the export is the generic one at line 50). opus_nolessons needed no fix (`EVERY_LIST_REL_lem`).
- CONST `weakening$weakS` -> `weakS_poly`, `weakening$weakCT` -> `weakCT_poly` (sonnet only; polymorphic versions).

## Remaining flags and diagnosis

Labels: real = a real difference between the Lean and the HOL4 statement; limit = tool limit (same meaning, different encoding the scan does not normalise); undecided = needs a manual or S1 look.

| theorem | runs | diagnosis |
|---|---|---|
| op_type_sound | all 3 | limit. Lean has one nested `match` with wildcard (`Rerr (Rabort (Rffi_error _)) => True`, `Rerr (Rabort _) => False`); HOL4 has nested `result_CASE`/`error_result_CASE`/`abort_CASE` with explicit `Rtype_error => F`, `Rtimeout_error => F`, `Rffi_error v => T`. Same meaning, checked against the source. |
| exp_type_sound | all 3 | limit (same nested-case/wildcard shape; case count 6 vs 2). Checked by shape, not line by line. |
| decs_type_sound, decs_type_sound_no_check | all 3 | limit (same shape; case count 3 vs 1). Checked by shape. |
| is_clock_io_mono_do_app_simple | all 3 | limit. Lean `some ((refs, ffi), r)` is a nested pair pattern inside an option alternative; HOL4 shows FST/SND. Source text of both is the same function. |
| do_app_cases | all 3 | undecided. Constant counts are lower in Lean in the same way in all runs (`>=` 20 vs 16, LENGTH 23 vs 18, `num:0` 26 vs 21; HOL4 has 85 disjunctions, Lean 74/63/63). A shared deficit may be an encoding effect or a shared omission; a manual diff of the disjunct list is needed. The opus_lessons and sonnet runs add Bool/Sum/ffi_result encoding differences on top. |
| type_op_cases | opus_lessons, sonnet | undecided. After TDEF, `Tapp` 83 vs 82, `Tlist_num` 7 vs 5, `t_of` 6 vs 5 in Lean. Not flagged in opus_nolessons. Needs a manual look. |
| type_env_conv_thm | all 3 | real (documented, small). Lean adds `[Nonempty ε]` for an unused existential variable of polymorphic type; the Lean comment says so. In sonnet it also has monomorphic binder types. |
| check_ctor_tenv_ok | opus_lessons, sonnet | real (specialisation). HOL4 `tis : α list` and polymorphic namespace parameters; Lean fixes `type_ident`, `modN`, `typeN`. The Lean statement is an instance of the HOL4 one. |
| 14 binder-types theorems (type_tenv_ctor_weakening, type_tenv_val_weakening_lemma, tenv_abbrev_ok_lookup, tenv_ctor_ok_merge, tenv_ctor_ok_lookup, mem_type_def_to_ctMap, type_def_to_ctMap_mem, nsLookup_add_tenvE1/2/3, add_tenvE_bvl, store_type_extension_weakS/refl/trans) | sonnet only | real (specialisation). The Lean statement uses monomorphic abbreviations (`Namespace`, `FMap` with fixed arguments) where HOL4 has type variables. Lean is weaker than HOL4 in generality; unlikely to matter for the closure, but it is a difference. |

Totals: opus_lessons 9 = 5 limit (op_type_sound, exp_type_sound, decs x2, is_clock...), 2 undecided, 2 real. opus_nolessons 7 = 5 limit, 1 undecided, 1 real. sonnet_lessons 23 = 5 limit, 2 undecided, 16 real (14 monomorphic + check_ctor_tenv_ok + type_env_conv_thm).

## Self-test (opus_lessons, scratch copies under `scratch/`, original project untouched)
The mutations were chosen by me (the porter), not by the tool author, on theorems that are clean in the unmutated scan; the Candle tool used 12 author-chosen mutations. Each mutation changes the Lean statement text only; the project was rebuilt with `lake build` and re-dumped; the final map (fitted rules active) was used. Bug and benign mutations went into one copy (`scratch/opus_lessons_main`, different theorem per mutation), blind-spot mutations into a second copy (`scratch/opus_lessons_blind`) so they cannot mask each other.

| id | change | caught |
|---|---|---|
| M01 | `i < m + n` to `i ≤ m + n` (find_index_LESS_LENGTH) | yes (constants, structure) |
| M02 | dropped a conjunct (ALOOKUP_find_index_SOME) | yes (connectives, constants) |
| M03 | swapped operands of `≤` (IS_PREFIX_THM) | yes (structure) |
| M04 | swapped arguments of `++` (map_some_eq_append) | yes (structure) |
| M05 | `≥` to `>` (DROP_EMPTY) | yes (constants) |
| M06 | `∧` to `∨` in a hypothesis (MAP_EQ_MAP_IMP) | yes (connectives, hypotheses) |
| M07 | numeral 1 to 2 (LESS_1) | yes (literals) |
| M08 | `∃` to `∀` (FDOM_FLOOKUP) | yes (binders) |
| M09 | reversed hypothesis direction (nsSub_mono) | yes (structure) |
| M10 | `↔` to `→` (explode_11) | yes (connectives, hypotheses) |
| M11 | swapped two environments in the conclusion (weak_tenvE_bind) | yes (structure) |
| M12 | variable replaced by numeral 0 (weak_tenvE_bind_var_list) | yes (literals) |
| M13 | swapped the two states of a relation (do_app_io_events_mono) | yes (structure) |
| M14 | added false hypothesis `1 = 2 →` (weakS_refl) | yes (hypotheses, literals) |
| B01 | definition body of find_index changed (`n+1` to `n+2`) | no (blind spot: definition bodies are not compared) |
| B02 | universe of unused type variables `Type` to `Type 1` (weak_tenvE_bind_tvar2) | no (blind spot: universe levels) |
| B03 | unused polymorphic binder `α` to `Nat` (weak_tenvE_bind_var_list) | yes (binder-types); not a blind spot in this run |
| N01 | benign: swapped two adjacent same-type universal binders (map_some_eq) | not flagged (correct) |
| N02 | benign: swapped the two sides of an equality (tlookup_bij_iff) | flagged (false positive: Eq is not symmetrised) |

Result: 14 of 14 statement bugs caught; of the 3 blind-spot probes 2 missed (by design) and 1 caught; of 2 benign rewrites 1 false positive. No other theorem changed status (no collateral flags). All mutated theorems are short statements outside the 9 theorems that already carry a flag; a mutation inside one of those would be hidden by the existing flag (S0 reports a flag, not which part is wrong). Mutations touched 5 modules (Misc, Weakening, EvaluateProps, Mlstring, NamespaceProps).

## Not covered
- Definition bodies (only axiom/opaque/sorry in reachable definitions is audited): B01.
- Implicit type annotations that do not change the term shape, universe levels: B02.
- Nested pattern matching and wildcard alternatives (the limit flags above).
- Proofs (all 267 are `sorry` by construction; S0 reads statements only).
- Shared errors: if all Lean runs and a map row make the same mistake, S0 sees agreement with the map, not with HOL4. The shared `do_app_cases` deficit is an example of what needs a manual look.
- Missing instance hypotheses (Lean needs fewer classes than HOL4): by design not flagged.
- `do_app_cases` and `type_op_cases` have not been re-derived by hand.
