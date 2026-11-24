# Brief: score one Lean 4 translation of the CakeML type-soundness closure against HOL4

Objective: find every declaration of one Lean project that breaks the fidelity contract, with evidence that a script can re-run.
The result decides a published comparison of translators, so a wrong accusation and a missed defect are equally bad.

## Inputs (read only)
- Lean project: `E:/ts_ws/runs/RUN_v2/merged` (Lean 4.28.0, already built; `CONVENTIONS.md` states the translator's choices).
- HOL4 and CakeML sources used by the translator: `E:/ts_ws/runs/RUN_v2/ws1` (its HOL4/CakeML folder) and the full HOL4 tree `E:/ts_ws/hol4src`.
- Targets: `E:/ts_ws/common/TARGETS.tsv` (theorems, definitions, inductives, datatypes with script and line).
- Elaborated HOL4 statements of the 267 theorems (pretty-printed, from the kernel):
  `E:/NUS/mcomp/Dissertation/candle_study/tools/hol4_query/out_ts/statements_pretty.txt`.
- Contract: `E:/NUS/mcomp/Dissertation/candle_study/plan/v3/plan_v3.3.tex`, section "Fidelity contract". Read it first.

## Contract in short
- V-P (preservation): some fact HOL4 proves about mapped constants becomes false or unprovable in Lean.
- V-C (conservativity): Lean proves an equation written only with mapped constants that HOL4 does not prove.
  Tier 1: no choice term in the equation (the image of `ARB` may appear). Tier 2: the equation needs a Hilbert-choice term.
  Only count facts provable from theorems that HOL4 theories save. Check in the HOL4 source whether HOL4 itself proves the value
  (example: look for a saved theorem for the corner case before claiming it is unspecified).
- Comments and names are not defects; record wrong comments separately.

## Work
1. Definitions: compare every definition, inductive and datatype of TARGETS.tsv, and every library constant of the Lean prelude, with the HOL4
   source (defining theorem, argument order, fixity and overloading, types, clause order, corner cases). Keep a log, one line per declaration:
   `name<TAB>file<TAB>verdict(ok|V-P|V-C1|V-C2|unsure)<TAB>reason`. Do not skip declarations silently; mark unread ones `unread`.
2. Statements: compare each of the 267 theorem statements with `statements_pretty.txt` (types, quantifier order may differ harmlessly, hypotheses, conclusions).
   Log them the same way.
3. For every V-P, V-C1 or V-C2 write a Lean file that shows it: a proved equation or a proved negation, or, for V-P, the concrete inputs on which the two sides differ,
   with the HOL4 theorem name and source line that decides the HOL4 side.
   Lean checks: `cd E:/ts_ws/runs/RUN_v2/merged && lake env lean ABSOLUTE_PATH_TO_YOUR_FILE` (the file starts with `import CmlTS`).
4. Try to refute each of your own findings before you report it (is the value saved somewhere in HOL4? is the HOL4 constant really the one you think it is?).

## Rules
- Do not modify the project, do not run `lake build`, do not use the network, git or other people's reports.
  In particular do not read `E:/ts_ws/score/*` of other runs, other runs' folders, or `candle_study/baselines`.
- Write only into `E:/ts_ws/score/RUN/`: `log_defs.tsv`, `log_stmts.tsv`, `witnesses.lean`, `REPORT.md`.
- `REPORT.md`: findings (V-P, V-C1, V-C2 with witness name and HOL4 line), unsure items, coverage (how many of each list were read, honestly), wrong comments.
- Final reply: at most 25 lines with counts, the list of V-P and V-C1 findings, and what you did not cover.
