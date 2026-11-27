# Audit on real translation errors (24 and 25 Nov 2026)

Author's check (26 Nov): `check/CHECK_RESULTS.md`. Draft. Tables by script, with S0 (scripts alone) next to the arms, per translation, without the provisional errors, and with paired module-level tests: `TABLES.md` (`report.py`). Main result of the paper (author, 25 Nov); the author's check is `check/` (read `check/README.md`, not this file, before answering).

V-C recheck (27 Nov): `vc_recheck/RECHECK.md`. With the saved theorems as reference (author), 62 of 63 V-C pairs are confirmed and `termsem0` (candle_opus) stays unsure, unresolved; the key is now 104 errors (S1 100, S8 64; `TABLES.md`). The numbers below are the key as run (105), as in `TABLES_pre_recheck.md`.

63 modules from 8 translations: 51 with 105 known errors, 12 with none known ("controls"). Each auditor saw one comment-stripped module with the HOL4 sources, read-only, same brief.
Errors were known before the run from the conservativity tests, the statement and type-variable scans and study 1 (`key.json`, `build_units.py`). A finding counts if it names the declaration (and the class, where a declaration has two errors); matched by script (`final.py`), not by a human scorer.
One correction to the key after the run: the integer-division error of study 1 was keyed under `do_app`; it sits in `do_arith`, which `do_app` calls. All three auditors reported it there.

## Known errors found

| Arm | All (105) | Open value fixed, V-C (63) | Type too specific, definitions (25) | Type too specific, statements (15) | Study 1 (2) | Cost |
|---|---|---|---|---|---|---|
| S1 Astra | 101 | 63 | 21 | 15 | 2 | subscription quota |
| S3 Opus, run a | 63 | 53 | 3 | 5 | 2 | $54.72 |
| S3 Opus, run b | 59 | 53 | 3 | 1 | 2 | $55.34 |
| S8 Opus a or b | 64 | 53 | 4 | 5 | 2 | $110.06 |
| S4 Astra, accepted by Neon | 101 | 63 | 21 | 15 | 2 | subscription quota |
| S6 Opus a, accepted by Opus | 62 | 53 | 3 | 4 | 2 | $54.72 + $22.59 |

- 37 errors were found by Astra and by neither Opus run; none the other way round. Four were missed by all: `build_ctor_tenv` (ts_opus, ts_sonnet) and `interprets0` (candle_opus, candle_fable). The type-variable script finds all four.
- Union of the two Opus runs: 64, one more than run a alone.
- S0 alone finds 40 of 105 (all from its own flags) and no open value; S0 or S1 finds 105, S0 or the Opus union 95. Without the 15 provisional errors: S1 86, Opus union 59 of 90. Details in `TABLES.md`.
- The 25 + 15 "type too specific" errors came from scripts, so the scripts find them by construction. The 15 statement cases are provisional until the human scoring of the CSV.
- 47 of the 105 errors are in one translation (ts_sonnet), which weighs heavily in the totals. `final.py` prints the counts per translation.

## Findings outside the key

| | S1 Astra | S3a | S3b |
|---|---|---|---|
| New true errors, confirmed (11 in all) | 11 | 4 | 4 |
| Consequence of a known error | 1 | 0 | 0 |
| Equation that needs a Hilbert-choice term (tier 2 in plan v3.3; 6 in all) | 6 | 1 | 2 |
| Disputed (word width 0, infinite index types) | 5 | 0 | 0 |
| False (parameter order of `store_ffi`) | 1 | 0 | 0 |
| Study-1 modules, not adjudicated one by one | 47 | 26 | 25 |

New true errors: Candle Sonnet `PERMUTES` (demands more than HOL4; checked in Lean and HOL4), `instance_`, `termsem`, `FAPPLY`; Candle Fable `termsem0`; TS Sonnet `thunk_op'`, `tenv_val_ok_nsEmpty`, `tenv_ctor_ok_nsEmpty`,
`tenv_abbrev_ok_nsEmpty`, `type_env_conv_thm`, `fix_clock_do_eval_res`. The five Candle ones have Lean checks in `proofs/`; the six TS ones were confirmed by comparing the HOL4 types with the Lean ones.
Fable, for which the earlier test of named constants found no V-C, has one. Of the 11, `type_env_conv_thm` was flagged by the statement scan and `thunk_op'` by a type-variable clash dismissed before; 5 only repeat the type of a keyed constant. So at most 5 are neither flagged nor repeats (`TABLES.md`). The key was incomplete: 116 errors are known (105 and 11) if the 15 provisional ones stand.

Controls (12): Astra flagged 4, each Opus run 1. Adjudicated: one (candle_sonnet HolSemantics, `instance_`, `termsem`) has true errors, two are tier 2, one (word width 0) is disputed. No control got a plainly false finding.

## Review
Neon accepted 173 of 174 Astra findings. The one it rejected (`select (fun _ => False) = ARB`, ts_opus, tier 2) is true: `proofs/New_ts_opus.lean`. It accepted the false `store_ffi` finding. Opus rejected 1 of 95, a provisional known statement error.
Review removed no false finding in this run.

## Deviations and limits
- The first 9 Neon reviews ran without the sentence telling it to use only file tools; the others have it. Queues were stuck or out of quota for long periods.
- Astra used a JavaScript tool built into Codex (30 calls) to read and match files; a scan found no path outside the unit folder and no network call. One Opus call used Bash.
- Transcript scan: the only accesses outside the unit folder are tool-result files of the same session; the other hits are text that looks like a path.
- The key and the adjudication were made by Claude, not by the owner. One run of Astra, so no variance estimate for it.
- Tokens: Astra 13.6M input (8.9M cached) and 166k output; Neon 53 reviews, 7.8M tokens; Opus $132.65 list price in all.
