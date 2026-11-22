# Baseline: direct HOL4-to-Lean 4 translation by Claude Sonnet 5.5

Run on 22 Nov 2026 (UTC). A repeat of the Opus 5.5 baseline (`../opus55_direct_translation/`)
with Claude Sonnet 5.5 (`claude-sonnet-5-5`) as the translator, as planned in plan v3.2
("Baselines and ablations", cheaper translator). Briefs, stages, assignments, Lean version and
checks are the same as the Opus baseline (the briefs include study-1's edge-case lists).
Translation only: every proof `sorry`.

**Result.** The translation compiles after one name fix at merge time, all 278 targets are stated,
and only they use `sorry`. A side-by-side comparison with the Opus baseline found **no difference
in meaning** in any of the 278 statements. Sonnet fixes a few values that HOL4 leaves unspecified
(for example `RESULT (Clash t) = t`, `CHR n = CHR 0` for n ≥ 256); each is a valid choice and no
target is affected. Sonnet took about 26 minutes of agent time and **about $7.21**, against $18.66
for Opus and $30.60 for Fable.

## Numbers

| Stage | Start (UTC) | End (UTC) | Duration | API responses | Output tokens | Cost |
|---|---|---|---|---|---|---|
| 1 (definitions) | 15:01:20 | 15:22:56 | 21.6 min | 79 | 181,232 | $4.45 |
| 2 (A, B, C, D in parallel) | 16:35:53 | 16:39:58 | 4.1 min | 53 | 94,617 | $2.76 |
| Total | | | **25.7 min** | 132 | 275,849 | **$7.21** |

Stage 2 started 73 minutes after stage 1 ended because the cloud container restarted in between;
the gap is not counted. Tokens (`run/token_usage.txt`): output 275,849; cache read 21,011,580;
cache write 939,757 (all 5-minute); uncached input 264. Prices for Sonnet 5.5 per MTok: $2 input,
$10 output, $0.10 cache read, $2.50 cache write (5 minutes). Comparison agent (Opus 5.5): $5.88.
Output: 20 Lean modules (5 prelude), 5,403 lines.

| | Fable 5.2 | Opus 5.5 | Opus 5.5, no lessons | Sonnet 5.5 |
|---|---|---|---|---|
| Agent time | 39.9 min | 45.0 min | 39.9 min | 25.7 min |
| Output tokens | 363,581 | 343,666 | 283,044 | 275,849 |
| API-equivalent cost | $30.60 | $18.66 | $15.34 | $7.21 |
| Builds after merge | yes | yes | yes | after one name fix |
| Statements differing in meaning from the Opus baseline | 0 | | 0 | 0 |

## Mechanical checks

- **Merge.** Each stage 2 agent built its own copy successfully. The merged project first failed
  with 4 errors: agent C stated the HOL4 theorem `RACONV` under that name in namespace
  `Candle.HolSyntaxExtra`, and in the merged project it shadowed the relation `RACONV` that agent
  D's statements in the same namespace refer to. The orchestrator qualified the 4 uses in
  `HolSyntaxExtra2.lean` as `HolSyntax.RACONV` (`run/merge_fix.diff`); no statement changed meaning.
  The split of holSyntaxExtra across two agents is an orchestration choice, so this counts as a
  merge problem of the method, not a translation defect.
- `lake build` from a clean build directory: succeeds, 278 `declaration uses sorry` warnings
  (`run/build_final.log`).
- Kernel check (`run/KernelCheck.lean`, `run/kernel_check.txt`): of 1,320 constants in
  `CandleLean.*` modules, exactly 278 depend on `sorryAx`, and they are the 278 targets
  (`REV_ASSOCD` renamed `REV_ASSOCD_thm`; the theorem `RACONV` keeps its name in its namespace).
  The rest use only `propext`, `Classical.choice`, `Quot.sound`.
- No `axiom`, `partial`, `unsafe`, `opaque`, `implemented_by`, `extern`, `native_decide`,
  `decreasing_by sorry`. Each stage 2 agent only added lines.

## Clean room and context

The transcript scan shows no access outside each workspace and the Lean toolchain, and no web or
git use. Stage 1, C and D kept scratch files under `/tmp/claude-0/` (outside the session
scratchpad's name pattern but inside the forbidden `/tmp/claude*` prefix); they held only the
agents' own extracts. No agent received any `queued_command` attachment in this run.

## Comparison with the Opus baseline

`audit/COMPARISON_opus55_baseline.md` (one Opus 5.5 agent, metaprogram dumps, normalised diff,
manual review against the HOL4 sources).

- 0 of 278 statements differ in meaning. 227 are identical after normalisation, 51 differ in form.
- Sonnet's own choices for values HOL4 leaves open: `ARB` is `default` under `[Inhabited _]`;
  `CHR n = CHR 0` for n ≥ 256; `RESULT (Clash t) = t` and `CLASH (Result t) = t`; `FUN_FMAP` on an
  infinite set is `FEMPTY`; `SEG` out of range is `[]`; `instance_` has a default branch. Each is a
  model of the HOL4 specification, and every target that uses these constants keeps them in range
  by hypothesis. (`TL [] = []`, truncating `ZIP` and division by 0 are specified in HOL4 itself, and
  Sonnet matches them.)
- Sonnet's `type_lt` is a mutual inductive with `type_llex`; the comparison agent proved in Lean
  that it equals the least relation closed under HOL4's rules.
- Form: Sonnet adds `[Inhabited U]` to nine lemmas that do not need it, drops or concretises some
  unused HOL4 binders (`mlstring_common_char_prefix`, `REV_ASSOCD_FILTER`, `dbVFREE_IN_bind`), and
  puts type variables in one universe. Baseline is closer to the HOL4 text there; Sonnet is closer
  for boolean `=` and the `Equalsem` constant.

**Correction to the comparison report.** The agent wrote that HOL4's pattern completion makes
`RESULT (Clash t)` one fixed `ARB`, so that Sonnet's `RESULT (Clash t) = t` contradicts HOL4.
This is wrong. In the built HOL4 theory the only definition of `RESULT` is
`∀t. RESULT (Result t) = t` (and of `CLASH`, `∀t. CLASH (Clash t) = t`); `simp` and `metis` cannot
prove `RESULT (Clash a) = RESULT (Clash b)` from it (`run/hol4_check_RESULT.sml`). The value is
unspecified, as for `dest_var` and `HD` (see the HOL4 check in the Opus RESULTS.md), so Sonnet's
choice is as valid as Opus's `ARB`. This is the third Claude auditor to make this claim.

## Files

- `lean/`: the translation, with the merge fix applied.
- `run/`: briefs, assignments, target list, `PROGRESS` logs, agent reports, build log, kernel check,
  token usage, merge fix, HOL4 query for `RESULT`.
- `audit/COMPARISON_opus55_baseline.md`: the comparison report (uncorrected; see above).
- `transcripts/`: gzipped transcripts of the five translators and the comparison agent.
