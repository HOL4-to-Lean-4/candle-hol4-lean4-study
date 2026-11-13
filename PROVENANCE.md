# Provenance

Everything in this repository that came from elsewhere, with its origin and license.

## vendor/HOL: HOL4

- Upstream: https://github.com/HOL-Theorem-Prover/HOL
- Commit: `9783a49979c94c401ff8c0e51b2eefae7ea95ae3` (2026-10-27T09:48:32+11:00), branch master
- How copied: `scripts/vendor_exact.py`, which writes every blob of the commit byte-for-byte
  (no line-ending conversion, no export filters) and stages it with the upstream mode.
  No `.git`, no build outputs, not modified. Git tree of `vendor/HOL` =
  upstream tree `29cad92945bc239c6389d991c6ae6b3ead1f6da3` (identical). The 15 upstream
  symlinks are kept as symlinks in git (on Windows checkouts they appear as small text files).
- License: HOL4 BSD-style license, `vendor/HOL/COPYRIGHT`, with third-party notices in
  `vendor/HOL/copyrights/`. Both kept unchanged.
- File hashes: `vendor/HOL.sha256` (SHA-256 per file, paths relative to `vendor/HOL`).

## vendor/polyml: Poly/ML

- Upstream: https://github.com/polyml/polyml
- Commit: `4557554077078decce4ce5f90da00a713cfc32e4` (tag v5.9.2, 2025-08-06T17:24:03+01:00)
- How copied: `scripts/vendor_exact.py`, as for HOL4. Not modified. Git tree of `vendor/polyml` =
  upstream tree `190217a8d58ef06a6ec327e35c8470313d51b7e5` (identical).
- License: GNU LGPL 2.1, `vendor/polyml/COPYING`, kept unchanged.
- File hashes: `vendor/polyml.sha256`.

## package/: CakeML files

- Upstream: https://github.com/CakeML/cakeml
- Commit: `48ee98a76be82e08a3a5613e34a1b8ec3c24c835` (2026-11-13T15:47:08+01:00), branch master
- License: CakeML LICENSE, copied unchanged into `package/LICENSE`.
- Files: see "Reduced package" below.

## Reduced package

The CakeML files are now in `package/`, reduced to the closure of `holSoundness.proves_sound`.

- Per-file record: `manifest/files.tsv`, one row per file in `package/`, with its upstream
  path, the upstream and package SHA-256, whether it was modified, and the reason
  for each modification.
- How the reduction was done, with counts: `REDUCTION.md`. The scripts and their records
  are in `tools/reduce/`.
- License: CakeML `LICENSE`, copied unchanged to `package/LICENSE`.
