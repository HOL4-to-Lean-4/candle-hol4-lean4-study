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
| Lean 4.28.0 | On "Default": elan still fails (elan 4.4 downloads from `release.lean-lang.org`, which is not allowed), so the script fetches the GitHub release archive and links it. Without GitHub release downloads it builds from the v4.28.0 source tag | 17 s (34 min from source) |
| `proving_nohol4/candle/lean` | `lake build` succeeds, 200 jobs, no `sorry` | 1 min |
| `proving_nohol4/ts/lean` | `lake build` succeeds, 47 jobs, no `sorry` | 1 min |

HOL4 total: about 20 minutes. Lean: under 20 seconds on "Default"; about 35 minutes from source where GitHub release downloads are blocked.

## Astra through the SSS gateway

Works on "Default" (27 Nov). `tools/astra_gateway/` has the client: `astra.py` (models, probe, one call without tools) and `codex_astra.sh` (`codex exec` with the audit flags of `audit/real/run.py` S1 and the gateway as Codex's provider; install with `npm install -g @openai/codex`). Both `gpt-6.2-astra` and `gpt-6-astra` resolve and the gateway reports the requested name; each run logs the reported model in its `.meta.json`. The gateway adds about 14,000 to 16,000 input tokens (mostly cached) to every call. Details and the model list are in `tools/astra_gateway/README.md`.

## What does not work in the cloud yet

- Lean through elan: elan 4.4 downloads toolchains from `release.lean-lang.org` (singular). Adding that host to "Default" lets `elan toolchain install` work directly; until then `setup_cloud.sh` uses the GitHub release archive, which is as fast.
- Raw files: the private repository `Lee-Juntong/candle-hol4-lean4-raw` is in the personal account, outside the session's GitHub access. Moving it into the HOL4-to-Lean-4 organisation (kept private) and adding it to the project gives access. The archive (41 MB) is under GitHub's 100 MB file limit, so it can be committed as a file and fetched with `git clone`.
- `audit/real/check/analyse.py` and `make_csv.py` need `check_key.csv` and `key.csv`, which are withheld from the repository (on the PC only).
- Scripts that use fixed `E:/` paths (`build_units.py`, `run.py`, `mk_run.py`, `tv_candle.py`, `make_sheet.py`) need a path option before they run on Linux. For the audits, `codex_astra.sh` replaces the S1 call of `audit/real/run.py`.

Aristotle has dropped Lean support (author, 27 November) and is no longer part of the setup.

## What works

- Claude Code with Opus 5.5 and Sonnet 5.5 (`claude -p --model ...`), Claude Code 2.1.332.
- Gemini Neon: the separate cloud thread with `agy` (`tools/neon_cloud/`).
- Astra (`gpt-6.2-astra`) through the SSS gateway, see above.
- Python 3.13 scripts that read the repository (for example `audit/real/score.py`).
- Git push to both repositories.
