# Task: prove the sorry theorems of a Lean 4 project

The working directory holds `lean/`, a Lean 4.28.0 Lake project (Batteries only, already built) with 278 theorems whose proof is `sorry`. They are translations of
HOL4 theorems. The HOL4 sources and proofs are deliberately not available in this task; comments quote only HOL4 statements and definitions. Do not look for HOL4 scripts,
HOL4 proofs or earlier Lean proofs of these theorems anywhere. Your task: prove as many of the 278 as you can.

## Frozen parts
Do not change any definition, inductive type, opaque constant, notation, theorem statement, theorem name or import that exists now; only the proofs `by sorry` may be replaced.
You may add new lemmas and helper definitions (only auxiliary, named `Aux.<something>`), in the same files or in new files under `lean/CandleLean/Proofs/` imported where
needed. Opaque constants are only known through their characterising theorems (`..._pkg`-based): do not try to unfold them, and do not weaken them.
After the run a script compares every frozen statement and definition with the original; a change invalidates the run. Files elsewhere, git and the network are off limits.

## Rules
- No `sorry`, `admit`, `axiom`, `native_decide`, `unsafe`, `implemented_by` or `partial` in anything you add.
- Never prove a theorem by editing it, its hypotheses, or a definition it uses.
- If you think a statement is false, do not change it. Prove its negation in `lean/CandleLean/Proofs/Refuted.lean` as `theorem Refuted.<name>` (a full proof, no sorry) and
  leave the original `sorry`. A failed attempt is not a refutation.
- Proving a theorem may use other `sorry` theorems of the project only if you record it (column `uses_sorry`); prefer the dependency order of the files so that this is not needed.

## Method
Work through the files in import order. Prefer `lake env lean` on one file over `lake build`; build everything at the end. Save work often: after each group of proved theorems, build,
then append to `lean/PROGRESS.tsv` (tab-separated: UTC time from `date -u +%FT%TZ`, theorem name, `proved` / `unproved` / `refuted`, note). If you run out of budget, stop with a project that builds.
Tools: Read, Write, Edit, Glob, Grep and Bash (`lake build ...`, `lake env lean ...`, `cd lean`, `ls`, `date -u ...` only; no pipes or redirections). One Lean process at a time.

## Finish
When nothing more can be proved, build the whole project, then reply with: number proved, names of unproved theorems with one line each on why, refuted theorems, and any statement you
suspect is wrong without a proof. End your final message with the line `RUN COMPLETE`.
