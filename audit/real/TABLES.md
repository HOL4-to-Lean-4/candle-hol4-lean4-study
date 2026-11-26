# Tables of the audit on real errors

Written by `report.py`. Known errors only; a hit means the finding names the declaration (reasons are not checked here).

Key after the V-C recheck of 27 November (`vc_recheck/RECHECK.md`): 98 errors. 7 open-value errors left the key because the Lean equation holds in every model of the HOL4 theory (TFL fills missing patterns with ARB). The key as run (105) is in `TABLES_pre_recheck.md` (`AUDIT_KEY=pre_recheck python report.py`).

## Known errors found

| Arm | All (98) | Open value fixed (56) | Type too specific, definitions (25) | Type too specific, statements, provisional (15) | Study 1 (2) | Without provisional (83) |
|---|---|---|---|---|---|---|
| S0 scripts | 40 | 0 | 25 | 15 | 0 | 25 |
| S1 Astra | 94 | 56 | 21 | 15 | 2 | 79 |
| S3a Opus | 63 | 53 | 3 | 5 | 2 | 58 |
| S3b Opus | 59 | 53 | 3 | 1 | 2 | 58 |
| S8 Opus a or b | 64 | 53 | 4 | 5 | 2 | 59 |
| S4 Astra+Neon | 94 | 56 | 21 | 15 | 2 | 79 |
| S6 Opus+Opus | 62 | 53 | 3 | 4 | 2 | 58 |
| S0 or S1 | 98 | 56 | 25 | 15 | 2 | 83 |
| S0 or S8 | 95 | 53 | 25 | 15 | 2 | 80 |

The S0 column is not an independent result: the 40 "type too specific" errors entered the key *because* these scripts flagged them. S0 cannot see open values. The open-value errors were known from named-constant tests written by hand or by models (Lean witnesses), not from S0. Study 1 errors were known from failed proofs.

## Per translation (known errors found)

| Translation | Known | S0 | S1 Astra | S3a Opus | S3b Opus | S8 Opus a or b | S4 Astra+Neon | S6 Opus+Opus |
|---|---|---|---|---|---|---|---|---|
| candle_opus | 8 | 1 | 7 | 6 | 6 | 6 | 7 | 6 |
| candle_opus_nolessons | 5 | 0 | 5 | 5 | 5 | 5 | 5 | 5 |
| candle_sonnet | 9 | 1 | 9 | 9 | 9 | 9 | 9 | 9 |
| candle_fable | 1 | 1 | 0 | 0 | 0 | 0 | 0 | 0 |
| ts_opus | 16 | 4 | 15 | 12 | 12 | 12 | 15 | 12 |
| ts_opus_nolessons | 12 | 0 | 12 | 10 | 10 | 10 | 12 | 10 |
| ts_sonnet | 45 | 33 | 44 | 19 | 15 | 20 | 44 | 18 |
| study1 | 2 | 0 | 2 | 2 | 2 | 2 | 2 | 2 |

## S0 flags and false alarms

| Translation | Constants compared | Constants flagged | of these known or new errors | Statements flagged | of these known or new errors |
|---|---|---|---|---|---|
| candle_opus | 156 | 1 | 1 | not run per translation | |
| candle_opus_nolessons | 144 | 0 | 0 | not run per translation | |
| candle_sonnet | 172 | 1 | 1 | not run per translation | |
| candle_fable | 153 | 1 | 1 | not run per translation | |
| ts_opus | 483 | 4 | 3 | 9 | 1 |
| ts_opus_nolessons | 481 | 2 | 0 | 7 | 0 |
| ts_sonnet | 483 | 20 | 19 | 23 | 16 |

A flag that is no known or new error is a name match between different things (`thunk_op` is a type in two translations), a word length that is a number in Lean (`shift_lookup`), or a statement with another shape that was not shown to differ in meaning.

## Errors outside the key (10, confirmed by the main session and by the author's check)

| Translation | Declaration | Flagged by S0 | Follows from a known error | S1 | S3a | S3b |
|---|---|---|---|---|---|---|
| candle_sonnet | `PERMUTES` | no | no | yes | yes | yes |
| candle_sonnet | `instance_` | no | no | yes | yes | yes |
| candle_sonnet | `termsem` | no | no | yes | no | no |
| candle_sonnet | `FAPPLY` | no | no | yes | yes | yes |
| ts_sonnet | `thunk_op'` | type variables (name clash with a type, dismissed) | no | yes | no | no |
| ts_sonnet | `tenv_val_ok_nsEmpty` | no | `tenv_val_ok` | yes | no | no |
| ts_sonnet | `tenv_ctor_ok_nsEmpty` | no | `tenv_ctor_ok` | yes | no | no |
| ts_sonnet | `tenv_abbrev_ok_nsEmpty` | no | `tenv_abbrev_ok` | yes | no | no |
| ts_sonnet | `type_env_conv_thm` | statement (binder-types, instances) | `type_ctor` | yes | yes | no |
| ts_sonnet | `fix_clock_do_eval_res` | no | `fix_clock, do_eval_res` | yes | no | no |

8 of the 10 are not flagged by S0. Flagged ones were dismissed or not keyed before the run, so they are not discoveries beyond the scripts. 5 only repeat the type of a constant that is itself a known error; 4 are neither flagged nor repeated. Many of the 15 provisional statement errors are of the repeating kind too (not checked one by one).

## Paired comparison by module


all known errors:

| Comparison | Errors | Modules | Difference in recall | 95% interval (bootstrap over modules) | p (sign flips per module) | Leave one translation out |
|---|---|---|---|---|---|---|
| S1 Astra vs S3a Opus | 98 | 47 | +0.32 | [+0.12, +0.50] | 0.0016 | +0.11 to +0.35 |
| S1 Astra vs S8 Opus a or b | 98 | 47 | +0.31 | [+0.10, +0.50] | 0.0033 | +0.11 to +0.34 |

without provisional:

| Comparison | Errors | Modules | Difference in recall | 95% interval (bootstrap over modules) | p (sign flips per module) | Leave one translation out |
|---|---|---|---|---|---|---|
| S1 Astra vs S3a Opus | 83 | 47 | +0.25 | [+0.10, +0.43] | 0.0041 | +0.11 to +0.28 |
| S1 Astra vs S8 Opus a or b | 83 | 47 | +0.24 | [+0.08, +0.42] | 0.0080 | +0.11 to +0.27 |

open values only:

| Comparison | Errors | Modules | Difference in recall | 95% interval (bootstrap over modules) | p (sign flips per module) | Leave one translation out |
|---|---|---|---|---|---|---|
| S1 Astra vs S3a Opus | 56 | 31 | +0.05 | [+0.00, +0.15] | 0.4978 | +0.02 to +0.07 |
| S1 Astra vs S8 Opus a or b | 56 | 31 | +0.05 | [+0.00, +0.15] | 0.4978 | +0.02 to +0.07 |

type too specific, definitions:

| Comparison | Errors | Modules | Difference in recall | 95% interval (bootstrap over modules) | p (sign flips per module) | Leave one translation out |
|---|---|---|---|---|---|---|
| S1 Astra vs S3a Opus | 25 | 14 | +0.72 | [+0.38, +0.90] | 0.0139 | +0.43 to +0.75 |
| S1 Astra vs S8 Opus a or b | 25 | 14 | +0.68 | [+0.31, +0.88] | 0.0299 | +0.43 to +0.71 |

Astra has one draw and Opus two, so the interval does not include run-to-run variation of Astra. Modules of one translation share a translator, and the same constant fails in several translations, so modules are not independent; with 8 translations no cluster interval at that level is reported. These numbers describe the selected errors, not model families.
