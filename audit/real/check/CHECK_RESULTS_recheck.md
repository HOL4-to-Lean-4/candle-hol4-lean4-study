# Author's check of the audit findings

Written by `analyse.py`. 108 of 108 rows answered; 1706 minutes logged.

## Controls (claim is not true of the shown declaration)

Answered "no" (correct): 8 of 8 (68% to 100%). Answered "unsure": 0.

## Answers by stratum and arm

| Stratum | Arm | Rows | Difference real: yes | no | unsure | Reason (of yes): right | partly | wrong | cannot tell |
|---|---|---|---|---|---|---|---|---|---|
| agreement sample | S1 | 7 | 7 | 0 | 0 | 7 | 0 | 0 | 0 |
| agreement sample | S3a | 3 | 3 | 0 | 0 | 3 | 0 | 0 | 0 |
| agreement sample | S3b | 2 | 2 | 0 | 0 | 2 | 0 | 0 | 0 |
| control | control | 8 | 0 | 8 | 0 | 0 | 0 | 0 | 0 |
| discordant | S1 | 43 | 43 | 0 | 0 | 43 | 0 | 0 | 0 |
| discordant | S3a | 5 | 5 | 0 | 0 | 5 | 0 | 0 | 0 |
| discordant | S3b | 1 | 1 | 0 | 0 | 1 | 0 | 0 | 0 |
| missed by all | key | 4 | 4 | 0 | 0 | 4 | 0 | 0 | 0 |
| outside key: disputed | S1 | 5 | 0 | 0 | 5 | 0 | 0 | 0 | 0 |
| outside key: duplicate root | S1 | 1 | 0 | 0 | 1 | 0 | 0 | 0 | 0 |
| outside key: false | S1 | 1 | 0 | 0 | 1 | 0 | 0 | 0 | 0 |
| outside key: new | S1 | 11 | 11 | 0 | 0 | 11 | 0 | 0 | 0 |
| outside key: new | S3a | 4 | 4 | 0 | 0 | 4 | 0 | 0 | 0 |
| outside key: new | S3b | 4 | 4 | 0 | 0 | 3 | 1 | 0 | 0 |
| outside key: tier 2 | S1 | 6 | 6 | 0 | 0 | 6 | 0 | 0 | 0 |
| outside key: tier 2 | S3a | 1 | 1 | 0 | 0 | 1 | 0 | 0 | 0 |
| outside key: tier 2 | S3b | 2 | 2 | 0 | 0 | 2 | 0 | 0 | 0 |

Agreement sample, difference real and reason right: 12 of 12 (76% to 100%)

Groups (same declaration, several claims) with both "yes" and "no" for q1: none. The claims may differ, so this is listed, not counted.

## Key corrections

Known errors whose every checked claim was answered "no": 0: none.

Known errors in the sheet with no "yes" and not refuted (unsure or unanswered): 0: none.

Provisional statement errors by the 51-row sheet (it decides, because it is scored first and shows more): {'weaker': 15}. Dropped ("same" or "note"): none. The two sheets disagree on: none.

## Recall after the check

A hit in the checked strata counts only if the author found the difference real (q1 yes); "right reason" also needs q3 right. Hits that were not in the sheet (found by all three runs, outside the sample of 12) stay as they were.

| Arm | Known errors found before the check (98) | Kept errors (98): found, difference real | found, reason also right |
|---|---|---|---|
| S1 | 94 | 94 | 94 |
| S3a | 63 | 63 | 63 |
| S3b | 59 | 59 | 59 |
| S8 | 64 | 64 | 64 |

S1 against S8, difference in recall on the kept errors, interval from 10000 resamples of modules:

- difference real: +0.31 [+0.11, +0.49]
- reason also right: +0.31 [+0.11, +0.49]

## Findings outside the key

| Category before the check | Declarations checked | confirmed (q1 yes) | refuted (all no) | open |
|---|---|---|---|---|
| disputed | 5 | 0 | 0 | 5 |
| duplicate root | 1 | 0 | 0 | 1 |
| false | 1 | 0 | 0 | 1 |
| new | 11 | 11 | 0 | 0 |
| tier 2 | 6 | 6 | 0 | 0 |

Study-1 findings outside the key are not in the sheet and are counted neither way.

## V-C recheck (27 November)

This file uses the key after the V-C recheck (`../vc_recheck/RECHECK.md`). 7 known errors and the new error `termsem0` (candle_fable) left the key: the Lean equation holds in every model of the HOL4 theory, because TFL fills the missing patterns with ARB. The readers answered these rows against the saved theorems, which do not state the ARB cases: C016, C041, C048, C054, C067, C071, C077, C078, C091. Answers q1: {'yes': 9}. The fixed analysis with the key as run is `CHECK_RESULTS.md`.
