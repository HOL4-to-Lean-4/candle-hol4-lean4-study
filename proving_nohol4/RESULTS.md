# Proving reruns without HOL4 proofs (25 Nov 2026)

Draft. Reruns of `../proving/` (Candle) and `../proving_ts/` (type soundness), which had broken the plan's rule that the prover never sees HOL4 proofs. Same bases, one isolated `claude -p` session each,
Claude Opus 5.5, high effort, no network, no subagents, 12 h cap, no token cap.

| | With HOL4 proofs (24 Nov) | Without (25 Nov) |
|---|---|---|
| Candle, 278 statements | 278 proved, 32.7 min, 262,289 output tokens, $11.35 | 278 proved, 31.2 min, 246,023 output tokens, $10.94 |
| Type soundness, 267 statements | 267 proved, 51.7 min, 370,892 output tokens, $18.35 | 267 proved, 76.7 min, 431,025 output tokens, $22.04 |

None refuted in any run. One run per cell, so no variance estimate. The two reruns ran at the same time on one PC, so wall times are not exact.

## What was removed
- `hol4/` is not in the workspace. The brief says the sources are deliberately unavailable.
- HOL4 proof text in Lean comments: 60 lines (33 Candle, 27 type soundness): termination tactics, two tactic proofs, derivations by conversions (`strip_proofs.py`, checked by `prooftext.py`). Comments still quote HOL4 statements and definitions.
- Reading is limited to the workspace and the Lean toolchain (`settings.json`); a probe confirmed refusals for HOL4 sources, the old proofs, the study folder and WSL. Workspaces: `E:/prove2/<candle|ts>/ws`.
- Differences from the plan: v3.2 asks for three runs per round, the v3.3 draft for one; v3.3 asks for an output-token cap, none was set (author: no limit). Workspaces also hold `CONVENTIONS.md` (part of the translation) and Batteries.

## Checks (main session)
- The base is the first round's by `Frozen.lean` (type and value hashes), `sorry` count 278 and 267. Pins unchanged.
- Clean rebuild: no `sorry`. `Ax278.lean`, `Ax267.lean`: all targets use only propext, Classical.choice, Quot.sound. `KernelCheck.lean`: 0 constants use `sorry`. `leanchecker` replay: return code 0 (type soundness: without `Proofs/Scratch.lean`, an unimported comment-only file).
- Definitions and opaque constants: none changed, no new axiom or opaque. Type soundness: every theorem type hash identical. Candle: `termsem_INST` and `termsem_simple_inst` have another hash (they now use a shared matcher);
  both restated from the original text and proved (`Restate.lean`).
- Text: 278 (Candle) and 287 (type soundness) lines removed from the base. All are `sorry` lines, except 20 last lines of statements in type soundness whose `:= by` became a term proof; statement text unchanged.
- Transcripts (`scan2.py`): no access outside the workspace, no file read by a Lean program, and none of the HOL4 proof lines (25 characters or more) occurs in any tool result. Four commands were refused (one `mkdir` in Candle; `wc -l` and two `grep` in type soundness).
  Two or three harmless read-only shell commands outside the allowed list ran in type soundness (reported by the prover).
- Candle: 4,695 lines added in the source, type soundness 7,763. Only lemmas and helpers named `Aux.*`, imports, one `set_option maxHeartbeats`.

## Limits
CakeML is public; the model may know the HOL4 proofs from training. The comparison with the first round is one run against one run.
