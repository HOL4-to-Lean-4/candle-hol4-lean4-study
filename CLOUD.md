# Running the work in a cloud session

Checked on 27 November 2026 in a Claude Code cloud session (Ubuntu 24.04, 4 cores, 15 GB RAM, the project's built-in environment with no settings of its own).

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
| Lean 4.28.0 | **elan cannot download it** (the network blocks `releases.lean-lang.org` and GitHub release downloads); built from the v4.28.0 source tag and linked as the elan toolchain | 34 min |
| `proving_nohol4/candle/lean` | `lake build` succeeds, 200 jobs, no `sorry` | 1 min |
| `proving_nohol4/ts/lean` | `lake build` succeeds, 47 jobs, no `sorry` | 1 min |

HOL4 total: about 20 minutes. Lean from source: about 35 minutes; about 1 minute if the environment allows `releases.lean-lang.org` and `github.com` release downloads.

## What does not work in the cloud yet

The project ran on the built-in cloud environment, which has no settings. The user's own cloud environment "Default" has what most of the missing pieces need.

- Astra (`gpt-6.2-astra`): goes through the SSS gateway. Its settings (`SSS_BASE_URL`, `SSS_GPT_KEY`, host `api.ssstoken.net`) are in the "Default" environment only, so this session could not reach it and the smoke test is still to do. Select "Default" for the project; the next session runs the test.
- Lean and GitHub release downloads: add `releases.lean-lang.org`, `github.com`, `release-assets.githubusercontent.com` and `objects.githubusercontent.com` to the allowed hosts of "Default". Then elan installs Lean 4.28.0 in about a minute.
- Raw files: the private repository `Lee-Juntong/candle-hol4-lean4-raw` is in the personal account, outside the session's GitHub access. Moving it into the HOL4-to-Lean-4 organisation (kept private) and adding it to the project gives access. The archive (41 MB) is under GitHub's 100 MB file limit, so it can be committed as a file and fetched with `git clone`; release downloads need the hosts above.
- `audit/real/check/analyse.py` and `make_csv.py` need `check_key.csv` and `key.csv`, which are withheld from the repository (on the PC only).
- Scripts that use fixed `E:/` paths (`build_units.py`, `run.py`, `mk_run.py`, `tv_candle.py`, `make_sheet.py`) need a path option before they run on Linux.

Aristotle has dropped Lean support (author, 27 November) and is no longer part of the setup.

## What works

- Claude Code with Opus 5.5 and Sonnet 5.5 (`claude -p --model ...`), Claude Code 2.1.332.
- Gemini Neon: the separate cloud thread with `agy` (`tools/neon_cloud/`).
- Python 3.13 scripts that read the repository (for example `audit/real/score.py`).
- Git push to both repositories.
