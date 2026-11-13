# Reduced HOL4 package for Candle's `proves_sound`

Upstream: CakeML `48ee98a76be82e08a3a5613e34a1b8ec3c24c835` (2026-11-13), HOL4 `9783a49979c94c401ff8c0e51b2eefae7ea95ae3` (2026-10-27, the commit CakeML's own `holbuild.toml` pins), Poly/ML v5.9.2 `4557554077078decce4ce5f90da00a713cfc32e4` built with `--enable-intinf-as-int`.

Main theorem: `holSoundness.proves_sound`, `is_set_theory mem ⇒ ∀thyh c. thyh |- c ⇒ thyh |= c`.

## Result

| | Upstream (script closure) | Package |
|---|---|---|
| Theory scripts | 10 | 10 |
| Lines in theory scripts | 12,987 | 8,766 |
| Theorems (`Theorem`/`Triviality`) | 1,012 stored | 517 |
| ... of which in the kernel dependency closure | | 278 |
| Definitions (`Definition`) | | 165 |
| Inductive relations | | 8 |
| Datatypes / type abbreviations / overloads | | 6 / 12 / 77 |

The package builds stand-alone in HOL4 (`Holmake holSoundnessTheory` in `candle/standard/semantics`, about 1 min 40 s on 4 cores). `holSoundnessScript.sml` and `holSemanticsScript.sml` are unchanged from upstream.

The 10 theories: `misc`, `mllist`, `mlstring`, `setSpec`, `holSyntaxLib`, `holSyntax`, `holSyntaxExtra`, `holSemantics`, `holSemanticsExtra`, `holSoundness`.

## Method

The first study's reduction (Feb 2026) was done by hand-run scripts that were never committed; only its commit messages describe it (kernel dependency tracking plus cross-file name checks, keeping all `[simp]` theorems, two passes). This package re-implements that method as scripts, in `tools/reduce/`:

1. `deps.sml`: for every stored theorem and definition of the 10 theories, records the theorems its proof used (HOL4 kernel dependency tracking, `Tag.dep_of`), the constants and type operators in its statement, the constants it defines, and its source location.
2. `closure.py`: closure from `proves_sound` plus every `[simp]` theorem or definition (removing them would change simp sets): proof dependencies, plus the definitions of every constant in a kept statement, plus datatype entries. Result `keep.json`.
3. `prune.py`: splits each script into top-level blocks (comments respected) and removes `Theorem`, `Triviality`, `Definition` and `Inductive` blocks that store nothing in the closure. `open`, `Overload`, `val` and other ML blocks stay.
4. `loop.sh`: rebuilds in HOL4; when the build fails because a proof script names a removed theorem or a definition uses a removed constant, it restores that block and repeats. It took several build-and-restore rounds. The names restored are in `records/extra.json`.

Pass 1 also kept every block whose name appears in a kept block's text; it built at 9,480 lines with 574 theorems. Pass 2 (this package) restores only what the build needs.

## Why 517 theorems, and the proposed manifest

HOL4 proof scripts often name lemmas in tactic lists that the final proof does not use, so the package keeps 239 theorems that no kernel dependency of `proves_sound` reaches. The 278 theorems in the kernel closure already include every lemma that the HOL4 proofs of `proves_sound` actually use. Proposal: the canonical manifest for translation and proof measurement is the 278 kernel-closure theorems plus the definitions, datatypes and relations their statements need; the other 239 stay in the HOL4 package only so that it replays. `manifest/manifest.json` marks each declaration with `kernel_closure`.

## Files

- `package/`: the HOL4 sources (no build outputs), with CakeML's `LICENSE`.
- `manifest/manifest.json`: every declaration (kind, name, theory, script, line, `[simp]`, `kernel_closure`).
- `manifest/files.tsv`: each file's upstream path, upstream and package SHA-256, and whether and why it was modified.
- `tools/reduce/`: the scripts above; `records/` holds their inputs and outputs.
