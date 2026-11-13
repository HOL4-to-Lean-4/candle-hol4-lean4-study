# Candle study: migrating `proves_sound` from HOL4 to Lean 4

Follow-up study to the CakeML type-soundness translation. The target is CakeML's
Candle theorem `proves_sound` in `candle/standard/semantics/holSoundnessScript.sml`.
This repository is self-contained: it holds the reduced HOL4 package, the pinned
HOL4 and Poly/ML sources, the build recipe, and the cost ledger.

## Pins

| Component | Upstream | Commit | Date |
|---|---|---|---|
| CakeML (source of the package) | https://github.com/CakeML/cakeml (master) | `48ee98a76be82e08a3a5613e34a1b8ec3c24c835` | 2026-11-13T15:47:08+01:00 |
| HOL4 (vendored in `vendor/HOL`) | https://github.com/HOL-Theorem-Prover/HOL (master) | `9783a49979c94c401ff8c0e51b2eefae7ea95ae3` | 2026-10-27T09:48:32+11:00 |
| Poly/ML (vendored in `vendor/polyml`) | https://github.com/polyml/polyml (tag v5.9.2) | `4557554077078decce4ce5f90da00a713cfc32e4` | 2025-08-06T17:24:03+01:00 |
| Lean 4 | not fixed yet | proposed: see below | |

CakeML's `build-instructions.sh` says CakeML master builds on HOL4 master, so HOL4 is
pinned to the last HOL4 master commit before the CakeML pin. CakeML's README still
names Poly/ML 5.7.1; we use the current release, 5.9.2, configured as CakeML
recommends (`--enable-intinf-as-int`).

**Lean (proposed, not fixed).** As of 2026-11-13, Aristotle's public docs
(aristotlelib 3.3.0 on PyPI) say it verifies C and Verilog and does not take
Lean-only projects. The FAQ says Lean support will return. No Lean version is
published. Proposal: pin `leanprover/lean4:v4.28.0`, the version the first study's
Aristotle runs used. Revisit when Aristotle's Lean support returns and states a version.

## Layout

- `package/`: reduced HOL4 package (closure of `proves_sound`) with CakeML's LICENSE.
  How it was reduced: `REDUCTION.md`.
- `manifest/manifest.json`: every definition, datatype, inductive relation and theorem in the closure.
- `manifest/files.tsv`: per-file upstream path, SHA-256 and modification reason.
- `tools/reduce/`: the reduction scripts and their records.
- `vendor/HOL`, `vendor/polyml`: unmodified upstream source trees at the pins.
  Per-file SHA-256 lists are in `vendor/HOL.sha256` and `vendor/polyml.sha256`.
- `docker/Dockerfile`: builds Poly/ML and HOL4 from `vendor/` (no network clone).
- `scripts/build.sh`, `scripts/build.ps1`: rebuild everything from a clean checkout.
- `ledger/`: `costs.csv` and the extractors for Claude Code and Codex transcripts.
- `plan/`: study plan.
- `PROVENANCE.md`: origin, commit, license and hash of everything copied in.

## Rebuild

HOL4 needs Linux (or WSL, or Docker). From the repository root:

```sh
sh scripts/build.sh native    # Linux/WSL: builds Poly/ML, HOL4, then package/ (into _build/)
sh scripts/build.sh docker    # or: build the docker image from vendor/, then the package inside it
```

On Windows with Docker Desktop or WSL:

```powershell
scripts\build.ps1             # Docker
scripts\build.ps1 -Mode wsl   # WSL
```

Start and end times of each stage are written to `logs/` (git-ignored).

To rebuild only the package against an already built HOL4 (Linux, WSL or Docker),
set `HOLDIR` to the built vendor HOL and run:

```sh
cd package/candle/standard/semantics
CAKEMLDIR=<repo>/package $HOLDIR/bin/Holmake holSoundnessTheory
```

`<repo>` is the absolute path of this repository. On 4 cores in the cloud this took
about 1 min 40 s.

## Cost ledger

```sh
python ledger/extract_claude.py ~/.claude/projects/<project>/<session>.jsonl --arm A --phase P --include-subagents
python ledger/extract_codex.py ~/.codex/sessions/YYYY/MM/DD/rollout-*.jsonl --arm A --phase P
```

Each run appends one row per session to `ledger/costs.csv` and skips sessions already
there. Codex rows report uncached input in `input_tokens` and cached input in
`cache_read_tokens`. The USD columns are filled in by hand.

## Licenses

The study's own files (scripts, ledger, docs) are by Lee-Juntong. Vendored and copied
third-party files keep their upstream licenses: HOL4 (BSD-style, `vendor/HOL/COPYRIGHT`),
Poly/ML (LGPL 2.1, `vendor/polyml/COPYING`), CakeML (`package/LICENSE`).
