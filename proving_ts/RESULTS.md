# Proving round on the Opus type-soundness translation (24 Nov 2026)

Draft. Base: the Opus 5.5 "with lessons" translation (`E:/ts_ws/runs/opus_lessons_v2/merged`) after a repair of three definitions and one statement whose types were less general than HOL4's
(`repair.py`: `build_ctor_tenv`, `ctMap_has_exns`, `ctMap_has_bools`, `check_ctor_tenv_ok`). The repaired base was frozen (`frozen_base.tsv`, `PINS.txt`) before the prover started.
Same rules as the Candle round (`../proving/`): one isolated `claude -p` session, Claude Opus 5.5, high effort, HOL4 scripts with proofs available, no network, no subagents.

**Result: 267 of 267 proved, none refuted.** 51.7 minutes of active time in two parts (the usage limit stopped the first at 230; it was resumed after the reset), 370,892 output tokens, $18.35 at list price.

**Protocol deviation.** As in the Candle round, the plan's rule that the prover never sees HOL4 proofs was broken (the brief was copied from that round). Reads of `miscScript.sml`, `namespacePropsScript.sml`,
`evaluatePropsScript.sml`, `weakeningScript.sml` and `typeSoundScript.sml` returned 127 `QED` proof ends. The proofs are valid Lean proofs of the frozen statements. The run is not evidence about proving without the HOL4 proofs.

## Checks (main session)
- Clean rebuild succeeds with no `sorry` warning. `KernelCheck.lean`: 0 constants use `sorry`, 0 declared axioms; axioms propext, Classical.choice, Quot.sound only. `Ax267.lean`: the 267 target names are theorems with only those axioms.
- `leanchecker` replayed all modules, return code 0 (it reuses Lean's own kernel).
- All pins match, so the brief, settings and base are the frozen ones. No frozen constant is missing except auxiliary matchers; no definition or opaque constant changed.
- The stored type of two theorems has another hash (`op_type_sound`, `decs_type_sound_no_check`): the elaborator now uses a matcher made by an earlier lemma. I restated both from the original text and proved them with the final theorems (`Restate.lean`).
- Text: 269 lines removed from the frozen sources. 267 hold `sorry`; the other 2 are the last line of `with_same_clock` and `pat_bindings_accum`, where `:= by` became `:= rfl` and `:= ⟨...⟩` (statement text unchanged).
- The prover added about 7,800 lines: `CmlTS.Aux.*` lemmas, four helper files, imports, `set_option` lines (heartbeats, linters). No `axiom`, `native_decide`, `unsafe`, `implemented_by`, `extern`.
- Transcript scan: one rule break, a scratch file `s1.lean` written and run in the session's own temp folder outside the workspace (reported by the prover). No other outside access; one denied command.
- `do_app_cases` and `type_op_cases`, undecided by the statement scan, are proved: they are true of the Lean definitions. This does not show that they are HOL4's statements (disjunction counts differ).

## What it does not show
As for Candle: that the Lean statements mean what HOL4's say, or that definitions are right. One run, no variance estimate.
