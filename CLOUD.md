# Running the work in a cloud session

Checked on 27 November 2026 in Claude Code cloud sessions (Ubuntu 24.04, 4 cores, 15 GB RAM). First check on the built-in environment; Astra and the download hosts rechecked later that day on the user's environment "Default".

## Set up

```sh
sh scripts/setup_cloud.sh          # HOL4 + Candle package, then Lean 4.28.0
```

Each new cloud session starts from a fresh clone, so the setup runs again in each session (or put it in a cloud environment's setup script).

| Step | Result | Time |
|---|---|---|
| Poly/ML v5.9.2 (with GMP) | built from `vendor/polyml` | 2 min |
| HOL4 9783a499 | built from `vendor/HOL` | 16 min |
| HOL examples the package needs | built | 1 min |
| Candle package (`holSoundnessTheory`) | built | 1.5 min |
| `tools/hol4_query/hol4q.py` print / eval / prove | work (Linux mode added: no WSL needed) | 10-20 s per query |
| elan | installed | 1 min |
| Lean 4.28.0 | On "Default": elan installs it directly since `release.lean-lang.org` was allowed (27 Nov, 06:10 UTC; checked with v4.27.0). The script falls back to the GitHub release archive, then to the source tag. Without GitHub release downloads it builds from the v4.28.0 source tag | 17 s (34 min from source) |
| `proving_nohol4/candle/lean` | `lake build` succeeds, 200 jobs, no `sorry` | 1 min |
| `proving_nohol4/ts/lean` | `lake build` succeeds, 47 jobs, no `sorry` | 1 min |

HOL4 total: about 20 minutes. Lean: under 20 seconds on "Default"; about 35 minutes from source where GitHub release downloads are blocked.

## Paths

The scripts find this repository by themselves and keep their work folders outside it. Three environment variables set the places:

| Variable | Meaning | Default |
|---|---|---|
| `STUDY_ROOT` | this repository | the clone the script is in |
| `WORK_ROOT` | folder that holds `ts_ws/`, `auditreal/`, `auditwork/`, `prove2/` | `E:/` on Windows, `~/work` elsewhere |
| `DISS_ROOT` | folder that holds study 1 (`r1check/`) | the folder that holds the clone |

`WORK_ROOT` has the same layout as the first PC's `E:` drive, so the raw-file archive unpacks into it directly. Typical cloud start:

```sh
export WORK_ROOT=~/work
python3 scripts/setup_pc.py --study1      # recreates ts_ws (70 MB) and study 1
python3 audit/real/build_units.py         # 63 audit units in $WORK_ROOT/auditreal (2.1 GB, 10 s)
```

Checked on Linux, 27 November: `build_units.py` gives the same 63 units and the same `key.json` as on the PC (apart from the later `recheck_note` fields and Windows line ends, so `git checkout audit/real/key.json` afterwards); `audit/pilot/build_units.py` gives the same pilot key; `make_sheet.py` and `make_csv.py` give the committed outputs, and `mk_run.py` too apart from one line added by hand to `audit/real/run.py` on 24 November (the note about shell commands). Scripts that read run outputs (`tv_candle.py`, `proving*/cmp.py`, `proving_nohol4/setup.py`) need the raw-file archive unpacked into `WORK_ROOT` first; `verify_witnesses.py` needs Lean on the path. The Git Bash path `D:\Git\bin\bash.exe` is set only on Windows. The prover settings that `proving_nohol4/setup.py` and `mk_ws.py` write deny the model read access to `DISS_ROOT` and the other work folders under the current paths.

## Astra through the SSS gateway

Works on "Default" (27 Nov). `tools/astra_gateway/` has the client: `astra.py` (models, probe, one call without tools) and `codex_astra.sh` (`codex exec` with the audit flags of `audit/real/run.py` S1 and the gateway as Codex's provider; install with `npm install -g @openai/codex`). Both `gpt-6.2-astra` and `gpt-6-astra` resolve and the gateway reports the requested name; each run logs the reported model in its `.meta.json`. The gateway adds about 14,000 to 16,000 input tokens (mostly cached) to every call. Details and the model list are in `tools/astra_gateway/README.md`.

## Notes

- For the audits, `tools/astra_gateway/codex_astra.sh` replaces the S1 call of `audit/real/run.py`.

Aristotle has dropped Lean support (author, 27 November) and is no longer part of the setup.

## What works

- Claude Code with Opus 5.5 and Sonnet 5.5 (`claude -p --model ...`), Claude Code 2.1.332.
- Gemini Neon: the separate cloud thread with `agy` (`tools/neon_cloud/`).
- Astra (`gpt-6.2-astra`) through the SSS gateway, see above.
- Raw files: the private repository `HOL4-to-Lean-4/candle-hol4-lean4-raw` (moved into the organisation 27 Nov) holds each archive as a plain file under `raw-<date>/`. In a session that has the repository: `git clone --depth 1 https://github.com/HOL4-to-Lean-4/candle-hol4-lean4-raw`, then `cd candle-hol4-lean4-raw/raw-2026-11-27 && sha256sum -c *.sha256 && tar -xzf candle_raw_2026-11-27.tar.gz -C "$WORK_ROOT"`. Since 27 November the archive also holds the two withheld scoring keys (`baselines/ts_runs_v2/scoring/key.csv`, `audit/real/check/check_key.csv`, under `NUS/mcomp/Dissertation/candle_study/` in the archive, so in `$WORK_ROOT/NUS/mcomp/Dissertation/candle_study/` after unpacking); copy them into the clone and `analyse.py` and `make_csv.py` run. Everything the work needs is now on GitHub except credentials. Each archive is about 41 MB (GitHub refuses files over 100 MB in git; release assets may be up to 2 GB, and the script keeps larger archives in the release only). `scripts/backup_raw.sh` commits new archives there and also uploads them to a release.
- Python 3.13 scripts that read the repository (for example `audit/real/score.py`).
- Git push to both repositories.
