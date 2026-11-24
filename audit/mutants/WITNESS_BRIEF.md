# Brief: witnesses for seeded mutants

Objective: for each mutant in your batch decide, with a Lean proof, whether it really differs from the base. A mutant without a proved difference is dropped, so never
weaken the standard to keep one. A wrong witness would put an equivalent "mutant" into the ground truth of a published experiment.

## Inputs (read only)
- Base project `E:/ts_ws/audit_base/lean` (Lean 4.28.0, built, 278 `sorry` theorems). Check a file with
  `cd E:/ts_ws/audit_base/lean && lake env lean ABSOLUTE_PATH` (the file starts with `import CandleLean`). Do not edit or build the base.
- `E:/NUS/mcomp/Dissertation/candle_study/audit/mutants/pool.jsonl`: fields `id`, `declaration`, `operator`, `label`, `old_decl`, `new_decl`, `file`, `line`, `diff`.
- `SPEC.md` in the same folder (section Witness) and the batch list in your task.
- For the U1 (V-C) mutants: the contract in `candle_study/plan/v3/plan_v3.3.tex`, section "Fidelity contract".

## What a witness is
- Definition, prelude, relation: in `namespace Mut` restate the mutated declaration (its text must be exactly `new_decl`; dependants only if the proof needs them), then prove
  `theorem witness : ∃ …, Mut.f … ≠ Base.f …` (or `¬ ∀ …, (Mut.R … ↔ Base.R …)`) with concrete inputs. Base name = the fully qualified base constant.
- Types or abbreviations (for example `word8`): a theorem that shows a concrete consequence that differs from the base.
- Statement: `theorem witness : ¬ (mutated statement)`, written as the mutated statement's Prop. If it is a weakening, give a proof of the mutated statement
  (no `sorry`) together with a theorem that some instance of the base statement is not implied by it, if you can; otherwise the mutant is `drop`.
- U1: a proved equation between mapped constants on the mutated declarations that the base cannot prove from the saved HOL4 clause, plus one line naming that clause.
- Keep it honest: a proof must not use `sorry`, `axiom`, `native_decide`, `unsafe`, or any `sorry`-backed base theorem. Run `#print axioms witness` at the end;
  allowed: propext, Classical.choice, Quot.sound.

## Output (write only here: `E:/NUS/mcomp/Dissertation/candle_study/audit/mutants/witnesses/`)
- `MUT-xxxx.lean` for each accepted mutant: compiles with no errors, ends with `#print axioms witness`.
- One row per mutant of your batch in `batch_N.tsv`: `id<TAB>verdict<TAB>reason`, verdict one of `witness`, `equivalent` (with a proof in `MUT-xxxx_equiv.lean` if cheap, otherwise an argument),
  `undecided`. Append after each mutant, so an interruption loses nothing.
- At most 20 minutes of work per mutant; then `undecided`.
- Do not read other batches' files or the audit briefs. No network, no git, no lake build.

Final reply: at most 12 lines: counts per verdict, the ids of `undecided`, and anything odd about the mutants (for example a mutant whose label V-P looks wrong).
