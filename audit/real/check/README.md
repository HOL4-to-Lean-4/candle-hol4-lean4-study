# Checking the audit findings

For the author. 108 rows about 91 declarations (rows with the same `group` are about the same declaration, possibly with different claims).
Expect about 5 to 8 minutes per row, so 1.5 to 2 days. Stop and continue when you like.

**Order.** First fill `baselines/ts_runs_v2/scoring/scoring_sheet.csv` (51 rows). Only then start here: some rows here show the same theorems with a claim next to them.
Do not open the other files in `audit/` and `baselines/`, the readiness review, `ledger/costs.csv` or any translation before you finish.

**Copy the sheet first** (`check_sheet_filled.csv`) and fill the copy. Keep the columns and the row numbers. `make_sheet.py` refuses to overwrite a sheet with answers.

## What you see

| Column | Meaning |
|---|---|
| `claim` | What somebody said is wrong. It is a claim, not a fact. Some rows are controls: the claim is not about the shown text. |
| `claimed_class` | V-P: the statement or definition does not mean the same. V-C: Lean can prove an equation that HOL4 leaves open. |
| `hol4_*` | HOL4 source, its line, and the exact HOL4 type from the kernel (`α`, `β` are type variables). Open the file if the excerpt is not enough. |
| `lean_*` | Lean text without comments, and the abbreviations it uses. |
| `check_offered_with_the_claim` | A Lean check that came with the claim. It is copied as it was; whether it runs here was not checked. |

## Answers

- `q1_difference_real`: `yes` if the shown Lean declaration differs from HOL4 in the way the contract counts (`CONTRACT` below), `no` if not, `unsure` if you cannot tell after a fair look.
  Judge the declaration, not the wording. If the claim points at a real difference but for another reason, `q1` is `yes` and `q3` says so.
- `q2_kind`: your own words from the list; `harmless` = a difference that does not matter (extra `[Nonempty]`, other but equivalent form); `needs choice term` = the equation needs Hilbert choice.
- `q3_reason` (only if `q1` is `yes`): `right` = the claim names the actual cause and its consequence holds; `partly` = right place, but some statement in the claim is wrong;
  `wrong` = another difference than the claimed one; `cannot tell`.
- `minutes` and `comment`: free. Minutes are used to report human effort.

You may use HOL4 (WSL) or Lean. A check is stronger than a guess; write which one you ran in `comment`. Do not change an answer after you have seen the results.

**CONTRACT.** V-P: the Lean statement or definition is not the HOL4 one under the type mapping, and the difference changes what it says. A type that is properly more specific than HOL4's counts.
V-C: Lean proves an equation or inequation about mapped constants that HOL4's saved theorems leave open (for example `HD []`). An equation that needs a Hilbert-choice term is `needs choice term`.
Notes only (answer `no`, or `harmless` in q2): another representation with a stated map, extra `[Nonempty]` on a type variable, unused binder types, names, order of arguments.

If the contract does not settle a case, answer `unsure` and say so in `comment`.

## What is in the sheet

The rows were chosen by a fixed rule and some rows are controls. The rule and the counts are in `SPEC.md`; read it after you finish. Do not open `make_sheet.py` or `analyse.py` before.

## Afterwards

```powershell
python audit/real/check/analyse.py audit/real/check/check_sheet_filled.csv baselines/ts_runs_v2/scoring/scoring_sheet_filled.csv
```
It needs `check_key.csv`: it is not in the repository (it names the runs); rebuild it with `make_sheet.py` on the PC that has `E:\auditreal` (`build_units.py`), after moving the filled sheet away.
The second file name is the filled 51-row sheet under any name; its `key.csv` is rebuilt with `make_csv.py`. The analysis was written and tested on made-up answers before the first answer and stays as it is.
The script prints answers per stratum and arm, the control rate, errors to remove from the key, recall before and after, and the difference between the arms with an interval.
