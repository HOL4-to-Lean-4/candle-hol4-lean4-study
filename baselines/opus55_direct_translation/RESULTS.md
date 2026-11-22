# Baseline: direct HOL4-to-Lean 4 translation by Claude Opus 5.5 (no workflow)

Run on 22 Nov 2026 (UTC). A repeat of the Fable 5.2 baseline (`../fable52_direct_translation/`)
with Claude Opus 5.5 as the translator. Everything else was kept the same: source, briefs, stages,
assignments, Lean version, checks and audit briefs. Translation only: definitions and theorem
statements, every proof `sorry`.

**Result.** The translation compiles (Lean 4.28.0, core + Batteries). All 278 kernel-closure
theorems of `holSoundness.proves_sound` are stated, and only they use `sorry`. Three audits found
**no semantic defect and no suspect**, 22 notes. A side-by-side comparison with the Fable 5.2
translation found **no difference in meaning** in any statement or definition. Where the two differ
in form, Fable follows the HOL4 text more literally in 8 places and Opus in 2. Opus took 45 minutes
and about $19 (Fable: 40 minutes, about $31).

## Setup

- Input: identical to the Fable run. The reduced HOL4 package in `package/` (CakeML `48ee98a7`),
  10 theories, plus `vendor/HOL/src` (HOL4 `9783a499`). Target list `run/TARGETS.tsv` (copied from
  the Fable run): 278 theorems, 114 definitions, 3 inductive relations, 6 datatypes.
- Translator: Claude Opus 5.5 (`claude-opus-5-5`, high effort), as Claude Code subagents in a cloud
  container (4 cores, 15 GB). No human or other model took part in the translation. No agent was
  resumed or given a second instruction.
- Lean 4.28.0 with Batteries `v4.28.0` only.
- Two stages, with the Fable briefs unchanged (`run/BRIEF_stage1.md`, `run/BRIEF_stage2.md`) and
  the Fable assignments (`run/ASSIGNMENT_{A,B,C,D}.tsv`):
  1. **Stage 1** (one agent): all datatypes, definitions, inductive relations and HOL4 library
     constants, plus `lean/CONVENTIONS.md`.
  2. **Stage 2** (four agents in parallel, each in its own copy): the 278 statements. A: misc,
     mllist, mlstring (76). B: setSpec, holSyntaxLib, holSyntax, holSemanticsExtra, holSoundness (79).
     C: holSyntaxExtra, first half (61). D: holSyntaxExtra, second half (62), in
     `HolSyntaxExtra2.lean`. The orchestrator created the empty `HolSyntaxExtra2.lean` skeleton
     and its import before stage 2, as in the Fable run.
- Translators saw the full HOL4 scripts, including proofs (project rule of 22 Nov 2026).

## Clean room

The briefs forbid web, git, other paths and subagents. A scan of every tool call in the five
translator transcripts (`run/scan_transcripts.py`) found no access outside each agent's workspace
and the Lean toolchain, and no web or git call. As in the Fable run, the agents kept their own
helper files in the session scratchpad under `/tmp/claude*`, which the brief listed as off-limits;
each reported it, and the files held only their own scripts and extracts. The stage 1 agent also
read the output file of one of its own background builds (also under `/tmp/claude*`) and stopped it.

**Context leak, reported plainly.** The harness attached two of Juntong's project-chat messages to
the start of every subagent's context in this session (translators, auditors and the comparison
agent; visible as `queued_command` attachments in each transcript). They said that the Fable 5.2
baseline was "almost perfect, just one minor Type-Signature Discrepancy (Non-Semantic)", and that
an outside-Claude check had been "done with gemini neon". They contain no Lean or HOL4 content and
do not name the declaration. No translator mentioned them in its output. The auditors did: two of
them refer to "the minor type-signature discrepancy already known". The translators may have paid
more attention to type signatures because of it; the result does not show that (Opus has one more
type-signature deviation from HOL4 than Fable, see below). The model's training data (cutoff June
2026) can include the public CakeML sources.

## Numbers

| Stage | Agent | Start (UTC) | End (UTC) | Duration | API responses | Tool calls | Output tokens |
|---|---|---|---|---|---|---|---|
| 1 | definitions | 06:58:02 | 07:35:21 | 37.3 min | 129 | 132 | 207,004 |
| 2 | A | 07:36:50 | 07:43:02 | 6.2 min | 29 | 30 | 38,275 |
| 2 | B | 07:36:50 | 07:42:23 | 5.5 min | 25 | 26 | 38,131 |
| 2 | C | 07:36:51 | 07:41:27 | 4.6 min | 22 | 23 | 30,029 |
| 2 | D | 07:36:50 | 07:41:28 | 4.6 min | 20 | 21 | 30,227 |
| Total | | 06:58:02 | 07:43:02 | **45.0 min wall** | 225 | 232 | 343,666 |

Tokens, from the API usage fields of the five transcripts (`run/token_usage.txt`): output 343,666;
cache read 35,292,080; cache write 944,773 (all at the 5-minute rate); uncached input 452.

API-equivalent cost at Opus 5.5 list prices ($4 input, $20 output, $0.20 cache read, $5 cache write
5-minute, per MTok): **about $18.66** (stage 1 $11.31, stage 2 $7.35). At the 1-hour cache-write
rate ($8) it would be about $21.49. The run used the Claude subscription, so nothing was billed per
token. The orchestrating session's own tokens are not included. Audit: $8.82 (3 auditors). Fable
comparison: $4.96.

Output: 18 Lean modules, 6,518 lines (`lean/`): 7 prelude modules (`Prelude/Basic`, `PredSet`,
`List`, `String`, `FiniteMap`, `Words`, `Sptree`) plus the aggregator `Prelude.lean`, and one module
per theory (holSyntaxExtra in two), all in namespace `Candle`.

### Opus 5.5 vs Fable 5.2

| | Fable 5.2 | Opus 5.5 |
|---|---|---|
| Wall time | 39.9 min | 45.0 min |
| Stage 1 / stage 2 | 32.6 / 6.7 min | 37.3 / 6.2 min |
| Output tokens | 363,581 | 343,666 |
| Cache read | 28.5 M | 35.3 M |
| API-equivalent cost | $30.60 | $18.66 |
| Lean lines | 6,646 | 6,518 |
| Targets stated / sorry only in targets | 278 / yes | 278 / yes |
| `decreasing_by sorry`, forbidden keywords | none | none |
| Audit defects / suspects / notes | 0 / 0 / 27 | 0 / 0 / 22 |
| Type-signature deviations from HOL4 in targets | 1 | 3 |

## Mechanical checks

- `lake build` after deleting the build directory: succeeds, 278 `declaration uses sorry`
  warnings, no errors (`run/build_final.log`).
- Kernel check (`run/KernelCheck.lean`, output `run/kernel_check.txt`): of the 902 `Candle`
  constants, exactly 278 depend on `sorryAx`, and they are the 278 targets (two renamed, as in the
  Fable run: `RACONV` → `RACONV_thm`, `REV_ASSOCD` → `REV_ASSOCD_thm`). The rest use only
  `propext`, `Classical.choice`, `Quot.sound`.
- No `axiom`, `partial`, `unsafe`, `implemented_by`, `extern`, `native_decide`, `opaque`; no
  `decreasing_by sorry`.
- Each stage 2 agent only added lines to its files (diff against stage 1 has no removed lines).
- Agent C's report and `PROGRESS` log say 60 theorems; all 61 assigned are in the file.

## Fidelity audit

The same three audit briefs as for Fable (`audit/BRIEF_audit_*.md`), with three Claude Opus 5.5
auditors. The harness did not let the auditors write files, so the orchestrator saved their reports
verbatim as `audit/FINDINGS_{1,2,3}.md`.

**Defects: 0. Suspects: 0. Notes: 22** (audit 1: 9, audit 2: 10, audit 3: 3). The main modelling
choices:

- **Characters and strings.** `char` is a structure with a number below 256; `string` is
  `List char`; `mlstring` has the single constructor `implode`. Like Fable, Opus chose 8-bit `char`
  without being told.
- **Numbers.** Only `num`; no `int` in the closure.
- **Equality.** No `BEq` or `==`; HOL `bool` is `Prop` throughout.
- **Finite maps** are `α → Option β` with finite support (Fable kept HOL4's own `α → β ⊕ Unit`
  with `is_fmap`). **Sets** are `α → Prop` with impredicative `FINITE`. **Words** are `BitVec n`
  (width 0 allowed, unused).
- **Unspecified values.** `HD []`, `LAST []`, `dest_var` of a non-variable, `RESULT`/`CLASH` on the
  wrong constructor are one fixed `ARB`. The auditors called this HOL4's pattern completion, but these HOL4 definitions go through `Prim_rec` (`Defn.sml` `non_wfrec_defn`), which leaves the missing cases unspecified, so Fable's choice is the literal one; `SEG`, `FUN_FMAP`,
  `VARIANT_PRIMES`, `fresh`, `instance` are `Classical.epsilon` of their specifications, with the
  HOL4 defining theorems proved.
- **Inductive relations.** `type_lt`, `term_lt` are the least relation closed under the rules
  (Lean rejects them as inductives); the others are Lean inductives.
- **Statements.** `[Nonempty]` only where a constant needs it (Fable put it on every type
  variable). The ML-generated statements were worked out by hand, with the same results as Fable.
- `pair_inj` uses the set-theory pair, as in Fable.

## Comparison with the Fable 5.2 translation

`audit/COMPARISON_fable52.md` goes through each of Fable's 27 audit notes and each of Opus's 22, and
diffs the elaborated type signatures, statements, definition equations and inductive rules of the
two projects with Lean metaprograms.

- **No difference in meaning** in any statement or definition. 245 of 278 statements are
  identical after normalising names; the other 33 differ only in form.
- Fable's 27 notes: same in Opus 17, equivalent but different form 3, Fable closer to the HOL4
  text 6, Opus closer 1. Opus's other notes: same 4, equivalent 5, Opus closer 1.
- Where Fable is closer: HOL4's unspecified values (`HD []`, `dest_var`, `RESULT`, `CLASH`) are
  `select` of the specification in Fable but a fixed `ARB` in Opus, so `HD [] = ARB` is provable in
  Opus only (no target is affected); Fable keeps HOL4's finite-map representation; and two
  type signatures (below). Where Opus is closer: `type_ok` uses `EVERY` as in HOL4, and boolean
  `=` is kept as `=`.

**Type signatures** (the Gemini finding). HOL4 gives an unused bound variable its own type
variable. Across the 278 targets:

| target | HOL4 | Fable | Opus |
|---|---|---|---|
| `VSUBST_WELLTYPED` (outer `ty` unused, shadowed by `∃x ty`) | `ty : 'a` | `ty : α` (matches) | `ty : type` (deviates) |
| `REV_ASSOCD` (two conjuncts) | 4 independent type variables | 4 (matches) | 2 shared by both conjuncts (deviates) |
| `mlstring_common_char_prefix` (duplicate binder `t2 t2`) | outer `t2 : 'a` | `mlstring` (deviates) | `mlstring` (deviates) |

All three are equivalent to the HOL4 statements (checked in Lean for `VSUBST_WELLTYPED`).
`mlstring_common_char_prefix` is the only type-signature deviation from HOL4 in Fable's targets, so
it is a likely match for Gemini's finding, which did not name the declaration. Opus has it too, plus
the other two.

## Files

- `lean/`: the translation (Lake project; `lake build` from here).
- `run/`: briefs, target list, assignments, the agents' `PROGRESS` logs and final reports, token
  usage, build log, kernel check script and output, transcript scan script.
- `audit/`: audit briefs, findings, and the Fable comparison.
- `transcripts/`: gzipped Claude Code transcripts of the five translators, three auditors and the
  comparison agent.

## HOL4 check of the open points (added 22 Nov 2026)

HOL4 (`vendor/HOL`) and the package were built in the cloud (`scripts/build.sh native`, all 10
theories OK). `run/hol4_check.sml` prints the HOL4 theorems with types; output in
`run/hol4_check.txt`.

- **`pair_inj`** is stated over `'U` with `is_set_theory mem`, so `,` is the set-theory pair. Both
  translations are right.
- **Unspecified values.** `dest_var_def`, `HD`, `LAST_DEF`, `RESULT_def` and `CLASH_def` have only
  the constructor cases, and no other theorem in the closure mentions the missing cases. HOL4 does
  not fix `dest_var (Const x ty)`, `HD []` and so on, which confirms the correction above.
- **Type signatures.** `REV_ASSOCD` has 4 type variables (α β in the first conjunct, γ δ in the
  second). In `VSUBST_WELLTYPED` the outer `ty` has type `α`. Both match the table above.
- **`mlstring_common_char_prefix`** is `∀(c1:char) (s1 s2:string) (t2:α) (t2:mlstring). implode
  (STRING c1 s1) ^ t1 = implode (STRING c2 s2) ^ t2 ⇔ …`. The outer `t2 : α` is unused, and `t1`
  and `c2` are free in the HOL4 theorem (the binder list repeats `t2` where `t1` and `c2` were
  meant). Both translations bind `t1` and `c2` as parameters and type the outer `t2` as `mlstring`.
- **ML-built statements.** `subtype_Tyvar`, `subterm_Var`, `subterm_Const`, `type_lt_thm` and
  `term_lt_thm` (holSyntaxExtra), `w2n_lt_256` and `splitlines_nil` (misc) print as both
  translations state them, up to binder names.
