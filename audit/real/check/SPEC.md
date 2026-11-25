# What is in the check sheet (read after answering)

Written before the first answer. `make_sheet.py` (seed `check-20261126`) draws the rows; `analyse.py` fixes the analysis.

108 rows, 91 declarations:

| Stratum | Rows | Rule |
|---|---|---|
| Discordant known errors | 49 | every finding that names a known error which some but not all of the three runs S1, S3a, S3b found |
| Outside the key | 35 | every finding outside the key except study 1: 19 about new errors, 9 tier 2, 5 disputed, 1 duplicate root, 1 called false |
| Agreement sample | 12 | a random known error among the 58 that all three found, and a random one of its findings |
| Missed by all | 4 | claims written by script from the HOL4 and Lean types |
| Controls | 8 | a true claim about one type-soundness translation, shown with the same declaration of another translation in which the scripts see no type difference |

The 46 other errors found by all three are not checked one by one. Study-1 findings outside the key are not in the sheet.

Controls: the claim is not true of the shown declaration, so the expected answer to q1 is `no`. Fewer than 7 of 8 `no` answers means the check is reported as unreliable. The controls are recognisable to a reader who sees that the claim names types absent from the text; the author had been told in a progress note that there are 8 controls.

The scripted rules are fixed, but the claims and the shown excerpts were not edited by hand, so 4 rows ("missed by all") have a script-written claim that reads alike, and Astra's and Opus's claims differ in style.

SHA-256 of the unpublished key at the time of writing (check_key.csv): caf111841e627b94601e7f2ab93c17e972d45b5ca2f19a42561a876c1f376e73. Sheet: 79a428c7c76c529179554c88f1e2480888c20e9bde099d167064592948e0a5d3.
