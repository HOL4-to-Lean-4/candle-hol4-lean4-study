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

- Astra (`gpt-6.2-astra`): no `codex` CLI or OpenAI credential, and `api.openai.com` and `chatgpt.com` are blocked. Astra runs stay on the PC until API access is set up for the cloud.
- Aristotle: `ARISTOTLE_API_KEY` is not set, and `aristotle.harmonic.fun` is blocked.
- Raw files: the private repository `Lee-Juntong/candle-hol4-lean4-raw` is outside the session's GitHub access, and GitHub release downloads are blocked.
- `audit/real/check/analyse.py` and `make_csv.py` need `check_key.csv` and `key.csv`, which are withheld from the repository (on the PC only).
- Scripts that use fixed `E:/` paths (`build_units.py`, `run.py`, `mk_run.py`, `tv_candle.py`, `make_sheet.py`) need a path option before they run on Linux.

## What works

- Claude Code with Opus 5.5 and Sonnet 5.5 (`claude -p --model ...`), Claude Code 2.1.332.
- Gemini Neon: the separate cloud thread with `agy` (`tools/neon_cloud/`).
- Python 3.13 scripts that read the repository (for example `audit/real/score.py`).
- Git push to both repositories.
