# Continue this work on another PC

Status: 26 November 2026. Read this file first, then `plan/v3/plan_v3.4.pdf` (draft, see "Open" below).

**Scoring done (26 November).** The author and volunteer readers from a university mathematics department (all familiar with Lean and HOL4; not named; one reader per row; readers saw only the four check files; the 51-row sheet filled together) filled both sheets: `baselines/ts_runs_v2/scoring/scoring_sheet_filled.csv` and `audit/real/check/check_sheet_filled.csv`. The fixed analysis ran once: `audit/real/check/CHECK_RESULTS.md`. The minutes in the check sheet are each reader's estimate, not timed (column `minutes_basis`: "Estimate"; first written as "Planning estimate", corrected at the author's request on 27 November). No model drafted answers (author, 27 November). Wording: "volunteer readers", not "colleagues"; no seniority; acknowledgements thank them as a group (author, 27 November). No second-reader agreement check (author: too time-consuming; stated as a limitation).

## Set up

In a Linux cloud session: `sh scripts/setup_cloud.sh`, then see `CLOUD.md` (what works there and what still needs the PC, checked 27 November).

On a Windows PC:

1. Install Git, Python 3.10 or newer, elan (Lean 4.28.0 is fetched by each project's `lean-toolchain`), and, for HOL4, WSL or Docker.
2. Clone to `E:\NUS\mcomp\Dissertation\candle_study`. The scripts use fixed `E:/` paths. Without an `E:` drive, first map a folder: `subst E: C:\work` (run it again after each restart).
   ```powershell
   git clone https://github.com/HOL4-to-Lean-4/candle-hol4-lean4-study.git E:\NUS\mcomp\Dissertation\candle_study
   ```
3. Recreate the work folders (`E:\ts_ws`; about 80 MB, or 200 MB with study 1):
   ```powershell
   python E:\NUS\mcomp\Dissertation\candle_study\scripts\setup_pc.py --study1
   ```
4. Build any Lean project with `lake build` in its folder, for example `proving_nohol4/candle/lean`. Lake fetches Batteries.
5. Only for HOL4 queries: in WSL, clone to `~/candle_build/repo` and run `sh scripts/build.sh native` (about 16 minutes). `tools/hol4_query/README.md` says more.
6. Only for new model runs: install and sign in to the `claude`, `codex` and `agy` CLIs on that PC. Do not copy credentials between PCs. Versions used: Claude Code 2.1.325, Codex CLI 0.169.0, agy 1.5.16.
   `run.py`, `drive.sh` and `launch.sh` contain `D:\Git\bin\bash.exe`; change it to where Git is on the new PC.
7. Only to rebuild the audit units: `python audit/real/build_units.py` writes `E:\auditreal` (63 units, about 2 GB) and rewrites `audit/real/key.json`; `git diff` should then show no change in it (the one correction to the key is made in `final.py`).
   The pilot's `build_units.py` writes `E:\auditwork`; `pilot/ground.py` and `mk_decoy.py` use it.

## Where things are

| What | Where |
|---|---|
| Plan v3.4 (draft), v3.3 (not adopted) and the critiques | `plan/v3/` |
| Candle translations (Opus, Opus without lessons, Sonnet, Fable) | `baselines/*/lean` |
| Type-soundness translations (three), their briefs and launch scripts | `baselines/ts_runs_v2/*/lean`, `baselines/ts_runs_v2/run` |
| **1. Scoring sheet for the author (51 rows)** | `baselines/ts_runs_v2/scoring/scoring_sheet.csv` |
| **2. Check sheet for the author (108 rows), how to fill it** | `audit/real/check/check_sheet.csv`, `audit/real/check/README.md` |
| Tables of the audit, script alone and per translation (has results) | `audit/real/TABLES.md`, made by `report.py` |
| Repaired Candle base used for proving and for the audit pilot | `audit_base/lean` |
| HOL4 packages | `package/` (Candle), `package_ts/` (type soundness, from `typesound_lean4_sorry/hol4-ultramin` at `165e03b24`) |
| Audit pilot, audit on real errors | `audit/pilot`, `audit/real` |
| Proving runs with HOL4 proofs (broke the plan's rule) | `proving`, `proving_ts` |
| Proving runs without HOL4 proofs (the valid ones) | `proving_nohol4` |
| Costs of the model runs (some scoring agents are missing: `baselines/ts_runs_v2/RESULTS.md`) | `ledger/costs.csv` |

## Done so far

- Candle: four translations, scored against the v3.3 contract (`baselines/rescore_v33`); base repaired.
- Type soundness: three translations, scored (`baselines/ts_runs_v2/RESULTS.md`).
- Audit pilot with planted defects (`audit/pilot/RESULTS.md`). The experiment with planted defects is dropped (author, 25 November).
- Audit on real errors, the main result of the paper (author, 25 November): 63 modules, six arms, tables by script (`audit/real/RESULTS.md`, `TABLES.md`; results inside).
- Check sheet for the author and its analysis script, written before any answer (`audit/real/check`). The analysis was run on made-up answers only.
- Proving without HOL4 proofs: Candle 278 of 278, type soundness 267 of 267 (`proving_nohol4/RESULTS.md`).

## Open

1. The author scores the 51 rows of `scoring_sheet.csv`: fill the last two columns. The statement entries of the key are provisional until then.
   `key.csv` (row to run) is not in the repository; after scoring, rebuild it with `make_csv.py`. It now stops if the sheet has answers. Still copy the filled sheet first (`*_filled.csv`).
   Then the author fills the check sheet (`audit/real/check/README.md`), then `analyse.py`. Order matters. **Done 26 November.**
   The author decided on 25 November to do the check and stated that they had not seen the results printed earlier in the work. Blinding: no file listed under "Blinding" above is opened before both sheets are filled.
2. Plan v3.4 is a draft. `plan/v3/plan.tex` (version 3.2) stays the adopted text until the author adopts v3.4. v3.4 makes the author the checker, which 3.2 said was not done; the paper states it.
3. `interprets0` in the Candle base is still too specific (known, not repaired).
4. Open decisions for the author: a second S1 (Astra) audit run, a second reader on a sample, the workflow loop (see "Open" in plan v3.4).
5. One run per cell, except two Opus audit runs, so there are no variance estimates.
6. Readiness: Astra's answer of 25 November is in `plan/v3/readiness_astra_2026-11-25.md`. Its three points are met in the files; whether they are met in fact depends on the author's check. Astra is asked again after the author has read plan v3.4 and done the scoring.
7. Record error: `audit/pilot/leantv_opus_lessons.tsv` was made from the repaired base, not the unrepaired one that the pilot used; the correct dump is `audit/real/tv/tv_ts_opus_lessons.tsv`.
8. V-C recheck done (27 November): `audit/real/vc_recheck/RECHECK.md` (`make_recheck.py`). Reference: the saved theorems, not unsaved kernel definitions (author, 27 November: "keep saved theorems"). Specified constants: the changed constant's introduction (from the sources) plus a HOL4 proof that it still holds, so the counterexample is a model of the theory. TFL constants (`MAP3`, `type_def_to_ctMap`): a replacement defined by the saved clauses plus an arbitrary catch-all, with every saved theorem that mentions the constant proved for it (`saved_ts.sml`; for `termsem0`, `saved_candle.sml`: satisfies0, models0 and entails0 are redefined from the replacement, and all 25 saved theorems that mention any of the four are proved, mostly through a lemma that the replacement agrees with termsem0 on well-typed terms). Result: all 63 V-C pairs confirmed, and the new `termsem0` (candle_fable) too. The key is unchanged at 105 (S1 101, S3a 63, S3b 59, S8 64; S1-S8 +0.35 [+0.16, +0.53]; open values +0.16 [+0.07, +0.28]). The unsure mechanism stays in the scripts (`key.json` field `recheck`; `score.py` drops such entries unless `AUDIT_KEY=pre_recheck`) but no entry uses it now. Under a kernel reading 7 pairs would hold in HOL4 (`arb_value_*.sml`); this is reported as a dependence on the reference. `vcheck.py` (theorem by theorem, fixed tactics) is a supplement only. Tables: `audit/real/TABLES.md` (key as run: `TABLES_pre_recheck.md`), `audit/real/check/CHECK_RESULTS_recheck.md` (`CHECK_RESULTS.md` is the fixed analysis with the key as run). Astra's readiness review of 27 November: `plan/v3/readiness_astra_2026-11-27.md` (G1 freeze v3.4: not ready, reconcile the reference in section 3, now done with the saved-theorem reading; G2 audit as main evidence: ready with conditions; G3 start writing: ready; G4 recheck: ready with conditions, written for the kernel reading). After it: the ts_sonnet witness `FAPPLY FEMPTY 0 = FAPPLY FEMPTY 1` is struck (follows from saved FAPPLY_DEF; the pair keeps `FAPPLY FEMPTY 5 = locncol EOFpt`); `final.py` keeps the class test where a V-C entry was dropped. Still open: the section 3 test for the 10 new errors and the tier-2 cases; an independent HOL4/Lean reader for disputed witnesses (author's call).
9. Theorem counts: study 1 has 269, this study 267; the two are `lookup_tenv_names` and `tenv_names_bind_var_list`, inside a comment block of `typeSysPropsScript.sml` (plan v3.4, section 4).
10. Write-ups put limitations, deviations and disclosures at the very end (author, 26 November).

## Rules the author set

- Provers never see HOL4 proofs. Check every run brief against the plan before starting, and report any difference first.
- Any Lean proof is accepted if Lean accepts it and the statement is correct; the proof method does not matter.
- `HD []` and similar fixed open values count as conservativity errors (V-C). A type that is properly more specific than HOL4's counts as a preservation error (V-P).
- The author does the human scoring.
- No spending limit on Opus and Sonnet runs; report at each milestone. No 128k token cap.
- Critique and delegated decisions: GPT-6.2 Astra through `codex`, Neon through `agy`. Disputes over tier 2 and conservativity were decided by Astra (`plan/v3/critique_astra_decisions_2026-11-24.md`).
- Model runs get isolated folders, read access to their own workspace only, and no network. Never use `--dangerously-skip-permissions`.
- Commit and push to `main` after each milestone, and update this file (author, 25 November). Scan staged files for emails, tokens and local user paths first.
- No Claude authorship, in this and every other repository of the author: the author is author and committer of each commit, with no `Co-Authored-By` or session lines, no "Generated with" lines in pull requests, and no branch names with `claude`. This applies from 25 November 2026 on; older history stays as it is (author). On a new PC, before the first commit, set `git config user.name` and `user.email` to the values of the latest commit (`git log -1 --format='%an %ae'`), and put `"attribution": {"commit": "", "pr": ""}` in `~/.claude/settings.json`.

## Not in the repository

- Raw model transcripts and proving workspaces (2,367 files, 211 MB, 41 MB packed): they contain account details. They are in a release of the author's private repository `Lee-Juntong/candle-hol4-lean4-raw`, and on the first PC.
  Findings, verdicts and usage extracted from them are here (`runs/<unit>/*.json`, `*.meta`). Restore after `setup_pc.py`, from Git Bash, with the newest date (or download the files from the release page in a browser):
  ```bash
  cd /e/ts_ws && gh release download raw-2026-11-25 -R Lee-Juntong/candle-hol4-lean4-raw && sha256sum -c candle_raw_2026-11-25.tar.gz.sha256 && tar -xzf candle_raw_2026-11-25.tar.gz -C /e
  ```
  `gh` must be signed in to the author's account. The archive does not hold HOL4 sources or `.lake` builds. `bash scripts/backup_raw.sh` uploads a new dated archive; run it at each milestone that adds raw files.
- Study 1's Lean project: `setup_pc.py --study1` fetches it from the public CakeML fork at `0d1173557`.
- Mutant compile caches in `E:\ts_ws\mut_work`: in the raw-file archive.
- The proving controls `E:\ts_ws\prove`, `E:\ts_ws\prove2_ctl`, `E:\prove2`: in the raw-file archive; the main files are also in `proving*/`. To rerun, copy the files back to the paths named in `drive.sh`.
- A first type-soundness run on incomplete HOL4 sources, discarded before scoring: in the raw-file archive, without the HOL4 sources.
