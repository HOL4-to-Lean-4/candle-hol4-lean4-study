# Continue this work on another PC

Status: 25 November 2026. Read this file first, then `plan/v3/plan_v3.3.pdf` (draft, see "Open" below).

## Set up

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
7. Only to rebuild the audit units: `python audit/real/build_units.py` writes `E:\auditreal` (63 units, about 2 GB) and rewrites `audit/real/key.json`; `git diff` should then show only the one correction described in `audit/real/RESULTS.md`.
   Restore the file with `git checkout audit/real/key.json`. The pilot's `build_units.py` writes `E:\auditwork`; `pilot/ground.py` and `mk_decoy.py` use it.

## Where things are

| What | Where |
|---|---|
| Plan v3.3 (draft) and the critiques of it | `plan/v3/` |
| Candle translations (Opus, Opus without lessons, Sonnet, Fable) | `baselines/*/lean` |
| Type-soundness translations (three), their briefs and launch scripts | `baselines/ts_runs_v2/*/lean`, `baselines/ts_runs_v2/run` |
| **Scoring sheet for the author (51 rows)** | `baselines/ts_runs_v2/scoring/scoring_sheet.csv` |
| Repaired Candle base used for proving and for the audit pilot | `audit_base/lean` |
| HOL4 packages | `package/` (Candle), `package_ts/` (type soundness, from `typesound_lean4_sorry/hol4-ultramin` at `165e03b24`) |
| Audit pilot, audit on real errors | `audit/pilot`, `audit/real` |
| Proving runs with HOL4 proofs (broke the plan's rule) | `proving`, `proving_ts` |
| Proving runs without HOL4 proofs (the valid ones) | `proving_nohol4` |
| Costs of every run | `ledger/costs.csv` |

## Done so far

- Candle: four translations, scored against the v3.3 contract (`baselines/rescore_v33`); base repaired.
- Type soundness: three translations, scored (`baselines/ts_runs_v2/RESULTS.md`).
- Audit pilot: every arm found all 6 mutants (`audit/pilot/RESULTS.md`).
- Audit on real errors: 105 known errors in 63 modules. Astra 101, Opus 63 and 59, Opus union 64, Astra reviewed by Neon 101 (`audit/real/RESULTS.md`).
- Proving without HOL4 proofs: Candle 278 of 278, type soundness 267 of 267 (`proving_nohol4/RESULTS.md`).

## Open

1. The author scores `scoring_sheet.csv`: fill the last two columns. The 15 keyed "type too specific (statement)" errors are provisional until then.
   Do not open `audit/real`, the two RESULTS files above or any translation before scoring: they show which run a row is from. `key.csv` (row to run) is not in the repository; after scoring, rebuild it with `make_csv.py`.
   **`make_csv.py` overwrites `scoring_sheet.csv`: copy the filled sheet first.**
2. Plan v3.3 is a draft. `plan/v3/plan.tex` (version 3.2) stays the adopted text until the author adopts v3.3.
3. `interprets0` in the Candle base is still too specific (known, not repaired).
4. 60 equivalent-change decoys have no proof; only needed if the mutant experiment goes on.
5. One run per cell everywhere, so there are no variance estimates.

## Rules the author set

- Provers never see HOL4 proofs. Check every run brief against the plan before starting, and report any difference first.
- Any Lean proof is accepted if Lean accepts it and the statement is correct; the proof method does not matter.
- `HD []` and similar fixed open values count as conservativity errors (V-C). A type that is properly more specific than HOL4's counts as a preservation error (V-P).
- The author does the human scoring.
- No spending limit on Opus and Sonnet runs; report at each milestone. No 128k token cap.
- Critique and delegated decisions: GPT-6.2 Astra through `codex`, Neon through `agy`. Disputes over tier 2 and conservativity were decided by Astra (`plan/v3/critique_astra_decisions_2026-11-24.md`).
- Model runs get isolated folders, read access to their own workspace only, and no network. Never use `--dangerously-skip-permissions`.
- Commit and push to `main` after each milestone, and update this file (author, 25 November). Scan staged files for emails, tokens and local user paths first. The author is the only author of commits.

## Not in the repository

- Raw model transcripts and proving workspaces (2,367 files, 211 MB, 41 MB packed): they contain account details. They are in the author's private Google Drive, folder `candle-hol4-lean4-study`, and on the first PC.
  Findings, verdicts and usage extracted from them are here (`runs/<unit>/*.json`, `*.meta`). Restore after `setup_pc.py`, from Git Bash, with the newest date (or download the archive in a browser):
  ```bash
  cd /e/ts_ws && rclone copy gdrive:candle-hol4-lean4-study . --include "/candle_raw_2026-11-25.*" && sha256sum -c candle_raw_2026-11-25.tar.gz.sha256 && tar -xzf candle_raw_2026-11-25.tar.gz -C /e
  ```
  `rclone config` must have a Drive remote called `gdrive` for the author's account. The archive does not hold HOL4 sources or `.lake` builds. `bash scripts/backup_raw.sh` uploads a new dated archive; run it at each milestone that adds raw files.
- Study 1's Lean project: `setup_pc.py --study1` fetches it from the public CakeML fork at `0d1173557`.
- Mutant compile caches in `E:\ts_ws\mut_work`: in the Drive archive.
- The proving controls `E:\ts_ws\prove`, `E:\ts_ws\prove2_ctl`, `E:\prove2`: in the Drive archive; the main files are also in `proving*/`. To rerun, copy the files back to the paths named in `drive.sh`.
- A first type-soundness run on incomplete HOL4 sources, discarded before scoring: in the Drive archive, without the HOL4 sources.
