# package/

Reduced HOL4 package for CakeML's `candle/standard/semantics/holSoundnessScript.sml`,
theorem `proves_sound`: the 10 theory scripts reduced to what the HOL4 build of that
theorem needs, with CakeML's `LICENSE`. Method and counts: ../REDUCTION.md. Per-file
upstream path, SHA-256 and modification reason: ../manifest/files.tsv.

Rebuild (Linux, WSL or Docker), with HOLDIR set to the built vendor HOL:

```sh
cd candle/standard/semantics
CAKEMLDIR=<repo>/package $HOLDIR/bin/Holmake holSoundnessTheory
```
