# Proving round on the repaired Opus translation of Candle (24 Nov 2026)

Draft. One run, Claude Opus 5.5 at high effort, one isolated `claude -p` session, no subagents, no network, HOL4 package (with HOL4 proofs) available.
Brief, settings, driver and hash pins are in this folder; the proved project is in `lean/`.

**Result: 278 of 278 statements proved**, none refuted, in 32.7 minutes (378 turns, 262,289 output tokens, $11.35 list price).

## Checks (run by the main session, not by the prover)
- `lake build` succeeds; `KernelCheck.lean`: 0 constants use `sorry`; axioms propext, Classical.choice, Quot.sound only.
- The 278 target names are all theorems with only those axioms (`Ax278.lean`: OK 278).
- `leanchecker` replayed all 19 modules with the kernel, return code 0. It reuses Lean's own kernel, so it is not an independent kernel.
- Freeze: 278 lines were removed from the base sources, every one of them containing `sorry`; nothing else was removed. `Frozen.lean` dumps the type of every
  non-internal constant (and the value of every definition and opaque): 1 of the 593 theorem types has another hash, `APPLY_UPDATE_LIST_ALOOKUP`. Its source text is identical; the elaborator now shares the
  matcher `Aux.ALOOKUP_append.match_1` (an added lemma created it first). The other differences are proof-internal auxiliaries (`match_*`, `splitter`).
- The run added about 600 `Aux.*` theorems and four helper definitions, and one import (`HolSemanticsExtra` imports `HolSyntaxExtra2`).
- Transcript scan: no path outside the workspace, no file or process access in the Lean files it wrote (tools: 311 Edit, 29 Read, 26 Bash, 8 Grep, 2 Glob, 1 Write; 0 denials).

## What it does and does not show
- All 278 Lean statements are provable, so none is false in Lean, and no definition blocked a proof.
- It does not show that the statements mean what HOL4 says: a statement that is too weak, or a definition that is wrong in a way that keeps it provable, would pass.
- The prover is the same model family as the translator, and the HOL4 proofs were available to it. This is the intended setting, but it is not evidence about proving without them.
- One run, so there is no variance estimate.
