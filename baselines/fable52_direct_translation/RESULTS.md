# Baseline: direct HOL4-to-Lean 4 translation by Claude Fable 5.2 (no workflow)

Run on 21 Nov 2026 (UTC). Translation only: definitions and theorem statements, every proof
`sorry`. No proving was attempted.

**Result.** The translation compiles (Lean 4.28.0, core + Batteries). All 278 kernel-closure
theorems of `holSoundness.proves_sound` are stated, and only they use `sorry`. Three audits of the
result against the HOL4 sources found **no semantic defect and no suspect**, only modelling notes.

## Setup

- Input: the reduced HOL4 package in `package/` of this repository (CakeML `48ee98a7`), 10
  theories, plus the HOL4 system sources `vendor/HOL/src` (pinned HOL4 `9783a499`) for library
  constants. Target list `run/TARGETS.tsv`: 278 theorems, 114 definitions, 3 inductive relations,
  6 datatypes (the `kernel_closure` entries of `manifest/manifest.json`), as a minimum; the
  translator also had to translate whatever else those need.
- Translator: Claude Fable 5.2 (`claude-fable-5-2`, high effort), as Claude Code subagents in a
  cloud container (4 cores, 15 GB). No human or other model took part in the translation. No
  agent was resumed or given a second instruction.
- Lean 4.28.0 with Batteries `v4.28.0` only. Mathlib was not used (the cloud container cannot
  download it; study 1 also avoided it).
- Two stages, so that names stay consistent:
  1. **Stage 1** (one agent, brief `run/BRIEF_stage1.md`): all datatypes, definitions, inductive
     relations and HOL4 library constants, plus `lean/CONVENTIONS.md` (naming and type mapping).
  2. **Stage 2** (four agents in parallel, brief `run/BRIEF_stage2.md`, each in its own copy of
     the stage 1 project): the 278 statements. A: misc, mllist, mlstring (76). B: setSpec,
     holSyntaxLib, holSyntax, holSemanticsExtra, holSoundness (79). C: holSyntaxExtra, first half
     (61). D: holSyntaxExtra, second half (62), in the extra module `HolSyntaxExtra2.lean`.
     Stage 2 agents could not change stage 1 definitions; they could add missing ones (none did).
- Clean room: the agents saw only the HOL4 sources, the target list and the Lean project. They
  did not get the earlier type-soundness Lean translations, the paper, or the workflow skills and
  docs. The briefs forbid web, git, other paths and subagents. A scan of every tool call in the
  five transcripts (`run/scan_transcripts.py`) found no access outside the agent's workspace and
  the Lean toolchain, and no web or git call. Two agents (stage 1, C) wrote their own temporary
  helper files to the session scratchpad under `/tmp/claude*`, which the brief listed as
  off-limits; both reported it, and the files held only their own scripts and workspace
  extracts. The model's training data (cutoff June 2026) can include the public CakeML sources.

## Numbers

| Stage | Agent | Start (UTC) | End (UTC) | Duration | API responses | Tool calls | Output tokens |
|---|---|---|---|---|---|---|---|
| 1 | definitions | 18:16:54 | 18:49:31 | 32.6 min | 82 | 82 | 207,121 |
| 2 | A | 18:50:03 | 18:55:05 | 5.0 min | 25 | 29 | 34,090 |
| 2 | B | 18:50:03 | 18:56:45 | 6.7 min | 28 | 31 | 46,558 |
| 2 | C | 18:50:03 | 18:56:19 | 6.3 min | 28 | 31 | 43,040 |
| 2 | D | 18:50:04 | 18:54:36 | 4.5 min | 19 | 22 | 32,772 |
| Total | | 18:16:54 | 18:56:45 | **39.9 min wall** | 182 | 195 | 363,581 |

Tokens, summed from the API usage fields of the five transcripts (`run/token_usage.txt`):
output 363,581; cache read 28,475,575; cache write 1,036,349; uncached input 364.

API-equivalent cost at Fable 5.2 list prices ($8 input, $40 output, $0.20 cache read per MTok,
cache write at the 5-minute rate $10 per MTok): **about $30.60** (stage 1 $15.49, stage 2 $15.11).
If Claude Code wrote the cache at the 1-hour rate ($16 per MTok), the total is about $36.80. The
run used the Claude subscription, so nothing was billed per token. The orchestrating session's
own tokens (setup, merge, audit coordination) are not included.

Output: 17 Lean modules, 6,646 lines (`lean/`): 7 prelude modules for HOL4 library constants
(`Prelude/Basic`, `PredSet`, `List`, `String`, `FiniteMap`, `Words`, `Mergesort`) and one module
per theory, all in namespace `Candle`. Stage 1 wrote 4,018 lines in 33 minutes; stage 2 added
the 278 statements in 7 minutes.

## Mechanical checks

- `lake build` after deleting the build directory: succeeds, 278 `declaration uses sorry`
  warnings, no errors (`run/build_final.log`).
- A Lean kernel check over the environment: all 278 targets exist as theorems in namespace
  `Candle` (two renamed because the names clash with definitions: `RACONV` → `RACONV_thm`,
  `REV_ASSOCD` → `REV_ASSOCD_thm`), each depends on `sorryAx`; the other 907 `Candle` constants
  do not, and use only `propext`, `Classical.choice`, `Quot.sound`.
- No `axiom`, `partial`, `unsafe`, `implemented_by`, `extern`, `native_decide`, `opaque`; no
  `decreasing_by sorry`. All termination proofs are real.
- Each stage 2 agent left the stage 1 text of its files byte-identical.

## Fidelity audit

Three Claude Opus 5.5 auditors (not Fable), one per scope, compared every definition and target
statement with the HOL4 scripts and HOL4 library sources, and tested suspected differences in
Lean (`audit/BRIEF_audit_*.md`, findings in `audit/FINDINGS_{1,2,3}.md`). The brief named the
defect classes found in the study-1 translation: int division and modulus, 8-bit `char`, derived
`BEq`, finite maps, words, choice and `ARB`, clause order, overloads, ML-generated statements.

**Defects: 0. Suspects: 0. Notes: 27.** The main modelling choices:

- **Characters and strings.** `char` is a structure `{val : Nat, val < 256}`, not Lean's Unicode
  `Char`; `string` is `List char`. (Study 1's translation used Lean `Char`.)
- **Numbers.** Only `num` occurs; HOL4 `DIV`/`MOD` by 0 and truncated subtraction agree with Lean
  `Nat`. No `int` in the closure, so the study-1 floored/Euclidean defect cannot arise.
- **Equality.** No statement uses `BEq` or `==`; HOL `bool` is `Prop` throughout, also as data
  (bitstrings are `List Prop`, mergesort's `neg` flag is a `Prop`).
- **Finite maps** are a structure over `α → Sum β Unit` with HOL4's own `is_fmap` predicate, so
  `FAPPLY` outside the domain is HOL4's single unspecified value. **Sets** are `α → Prop`, with
  HOL4's impredicative `FINITE`. **Words** are `BitVec N`.
- **Unspecified values.** `HD`, `LAST`, `SEG`, `CHR`, `OUTL`, `dest_var`, `RESULT`, `CLASH`, and
  the `new_specification` constants `FUN_FMAP`, `VARIANT_PRIMES`, `fresh`, `instance'` are
  `Classical.epsilon` of their HOL4 specification; HOL4 also leaves these values unspecified
  rather than `ARB`. `termsem` on `Abs` of a non-variable is `ARB`, as HOL4's pattern completion
  gives.
- **Inductive relations.** `type_lt` and `term_lt` are the intersection of all relations closed
  under the rules, because Lean's `inductive` rejects the nested `LEX`/`LLEX` occurrence. Same
  meaning as HOL4 `Inductive`, but no Lean recursor: proofs need hand-made case lemmas.
- **Recursion.** Several functions use well-founded recursion with other measures than HOL4
  (`orda`, `term_union`, `INST_CORE`, `type_ok`, `typesem`, mergesort); equations and first-match
  order of overlapping clauses are the same. Proofs need the equation lemmas, not `rfl`.
- **Statements.** Free HOL4 variables are explicit theorem arguments; every type variable gets
  `{α : Type} [Nonempty α]`; HOL4's independent type variables in separate conjuncts are kept
  independent; `=` on booleans is `↔`. Statements HOL4 builds with ML (`SIMP_CONV`, `CONJUNCTS`,
  `EVAL`) were worked out by hand: `subtype_Tyvar`, `subterm_Var`, `subterm_Const`,
  `type_lt_thm`, `term_lt_thm`, `w2n_lt_256`, `splitlines_nil`, `Equalsem`, `VARIANT_PRIMES_def`.

**Open uncertainty.** `pair_inj` in setSpec: `(a,b) = (c,d)` type-checks both as HOL pairs and as
the set-theory `pair`. The translation uses the set-theory reading (HOL4 prefers the latest
overload, and later theorems need it); the HOL4 proof alone does not decide it. Running HOL4 on
the term would settle it.

**Limits.** The auditors are Claude models, like the translator, so they may share its blind
spots; an audit by another model family (or the H/M adjudicators) may find more. Truth of the 278
statements was checked only by reading and small Lean experiments (a few statements were proved
in scratch files: `strcat_assoc`, `concat_sing`, `arities_match_nil`, `swap_ff`, ...). A proving
run is the real test: a statement that is false as translated will show up there.

## Files

- `lean/`: the translation (Lake project; `lake build` from here).
- `run/`: briefs, target list and assignments, the agents' `PROGRESS` logs and final reports,
  token usage, build log, transcript scan script.
- `audit/`: audit briefs and findings.
- `transcripts/`: the gzipped Claude Code transcripts of the five translators and three auditors.
