# Ablation: Opus 5.5 direct translation with study-1 lessons removed from the briefs

Run on 22 Nov 2026 (UTC). A repeat of the Opus 5.5 baseline (`../opus55_direct_translation/`)
in which only the briefs changed: every list of study-1 edge cases was removed (plan v3.2,
"Baselines and ablations"). Source, stages, assignments, model, Lean version and checks are
unchanged. Translation only: every proof `sorry`.

**Result.** The translation compiles, all 278 targets are stated, and only they use `sorry`.
A side-by-side comparison with the Opus baseline found **no difference in meaning** in any of
the 278 statements or in any definition they use. Without the lessons, Opus still chose an 8-bit
`char`, HOL4's own finite-map representation, `opaque` `ARB` and Hilbert choice for
under-specified constants. The run took 40 minutes and about $15 (baseline: 45 minutes, about $19).
On Candle, the study-1 lessons in the briefs made no measurable difference.

## What changed in the briefs

`run/BRIEF_stage1.md` and `run/BRIEF_stage2.md` against the baseline briefs:

- Stage 1, rule 1: removed "including edge cases (division and modulus, subtraction on naturals,
  characters and strings, order and duplicates in lists, partial functions and `ARB`, Hilbert
  choice, sets that may be infinite, finite maps)".
- Stage 1, `CONVENTIONS.md` item: "how HOL4 types map (num, int, char, string, mlstring, sets,
  finite maps, options, pairs, words if any, ...)" became "how HOL4 types map to Lean types".
- Stage 1, final report: removed "(sets, finite maps, chars/strings, div/mod, choice, `ARB`,
  termination)".
- Stage 2, rule 1: "with the same types (watch implicit HOL4 type variables, numeral types, `num`
  subtraction, overloaded operators, sets and finite maps, and free variables, which HOL4
  quantifies universally)" became "with the same types".

No audit brief was used: the check is a comparison with the audited, HOL4-checked Opus baseline.

## Numbers

| Stage | Start (UTC) | End (UTC) | Duration | API responses | Output tokens |
|---|---|---|---|---|---|
| 1 (definitions) | 14:05:11 | 14:39:01 | 33.8 min | 111 | 187,353 |
| 2 (A, B, C, D in parallel) | 14:39:20 | 14:45:02 | 5.7 min | 64 | 95,691 |
| Total | 14:05:11 | 14:45:02 | **39.9 min wall** | 175 | 283,044 |

Tokens (`run/token_usage.txt`): output 283,044; cache read 29,190,658; cache write 767,904 (all
5-minute); uncached input 350. API-equivalent cost at Opus 5.5 list prices: **about $15.34**
(stage 1 $10.35, stage 2 $4.99). Comparison agent: $3.67. Output: 19 Lean modules (9 prelude),
5,858 lines.

| | Opus baseline | Opus no lessons |
|---|---|---|
| Wall time | 45.0 min | 39.9 min |
| Output tokens | 343,666 | 283,044 |
| API-equivalent cost | $18.66 | $15.34 |
| Targets stated / `sorry` only in targets | 278 / yes | 278 / yes |
| Statements differing in meaning from the baseline | | 0 of 278 |

## Mechanical checks

- `lake build` from a clean build directory: succeeds, 278 `declaration uses sorry` warnings
  (`run/build_final.log`).
- Kernel check (`run/KernelCheck.lean`, output `run/kernel_check.txt`): of 1,201 constants in
  `CandleLean.*` modules, exactly 278 depend on `sorryAx`, and they are the 278 targets (renamed
  `RACONV_thm`, `REV_ASSOCD_thm` as before). The rest use only `propext`, `Classical.choice`,
  `Quot.sound`.
- No `axiom`, `partial`, `unsafe`, `implemented_by`, `extern`, `native_decide`,
  `decreasing_by sorry`; the only `opaque` is `ARB`, which HOL4 also leaves undefined.
- Each stage 2 agent only added lines to its assigned files. Agent B added `open Classical` to
  `HolSoundness.lean`, as `CONVENTIONS.md` asks. Agent A's report says 75 theorems; all 76
  assigned are in the files.

## Clean room and context

The transcript scan (`run/scan_transcripts.py`) shows no access outside each workspace and the Lean
toolchain, and no web or git use; agents C and D kept scratch files in the session scratchpad, and
stage 1 briefly used `/tmp/x`. The stage 1 agent got no extra context. The four stage 2 agents
received four of Juntong's project-chat messages as `queued_command` attachments (about a new
repository for the whole migration, its name, the migration order, and creating it). They contain
no HOL4, Lean or study-1 content.

## Comparison with the Opus baseline

`audit/COMPARISON_opus55_baseline.md` (one Opus 5.5 agent; elaborated statements and definition
bodies of both projects dumped by Lean metaprograms, normalised and diffed, differences reviewed by
hand and against the HOL4 sources and `../opus55_direct_translation/run/hol4_check.txt`).

- 0 of 278 statements and 0 definitions differ in meaning. 231 statements are identical after
  normalisation, 47 differ in form only.
- The no-lessons run is closer to the HOL4 text in several encodings: set comprehensions as
  `GSPEC`, finite maps as HOL4's `α → β ⊕ Unit` with `is_fmap` (as Fable did), `ARB` as an
  `opaque` constant, `CHR` through Hilbert choice, and boolean `=` kept as `=`. The baseline is
  closer for pair-pattern lambdas, the inlined `Equalsem` and the independent type variables of
  `append_thm`, and it avoids unnecessary `[Nonempty U]` hypotheses.
- Shared with the baseline: `HD []`, `LAST []`, `RESULT`/`CLASH` on the wrong constructor and
  `dest_var` of a non-variable are `ARB`, where HOL4 leaves them unspecified; and the unused
  bound variables of `VSUBST_WELLTYPED` and `mlstring_common_char_prefix` get a concrete type.

## Files

- `lean/`: the translation (Lake project).
- `run/`: briefs, assignments, target list, `PROGRESS` logs, agent reports, build log, kernel check,
  token usage, scan and usage scripts.
- `audit/COMPARISON_opus55_baseline.md`: the comparison report.
- `transcripts/`: gzipped transcripts of the five translators and the comparison agent.
