Stage 1 (definitions) is done. `lake build` from `/home/claude/work/ws/lean` ends with "Build completed successfully (18 jobs)". The one warning is an unused variable `h` in `variant`.

**Modules and declaration counts.** Counts are top-level `def`, `abbrev`, `inductive`, `structure`, `instance`, `class`, `theorem` and `lemma` lines, which includes my helper lemmas.
- `Prelude/Basic` 62, `Prelude/List` 42, `Prelude/FMap` 11, `Prelude/String` 33, `Prelude/Sort` 5
- `Misc` 12, `Mllist` 11, `Mlstring` 34, `SetSpec` 25
- `HolSyntaxLib` 11, `HolSyntax` 89, `HolSyntaxExtra` 33
- `HolSemantics` 30, `HolSemanticsExtra` 1 (`Equalsem`)
- `HolSoundness` 0. It has only an empty namespace, because no definitions were needed.
- `CandleLean.lean` imports all of these.

I wrote `lean/CONVENTIONS.md` (name table with module for each name, renames, type mappings, notation, overloads, modelling choices) and `lean/PROGRESS.tsv` (one `done` line per module group, UTC timestamps). `scratch/` is deleted.

**Sorries.** There is no `sorry`, `decreasing_by sorry`, `axiom`, `partial`, `unsafe`, `native_decide`, `implemented_by` or `opaque` anywhere. All termination proofs are real. `PROGRESS.tsv` has no `problem` entries.

**Untranslatable targets.** None found. About 55 sample target statements, covering every theory, type-checked in a scratch file with no errors. I did not type-check all 278 statements.

**Where the Lean meaning differs from HOL4, or I made a modelling choice**
- **bool:** `bool` is `Prop`, with classical decidability from `open Classical`. Every file is `noncomputable section`.
- **Sets:** `'a set` is `HOL.Set a := a → Prop`, with a custom `{x | p}` macro and instances for membership, union and so on. `FINITE s` means "s is contained in some list".
- **Finite maps:** `FMap` is a structure with a `lookup : α → Option β` field and a finite-support proof, plus an ext lemma.
- **Chars and strings:** `char` is a structure with `val < 256`. `CHR n` for n ≥ 256 is `CHR 0`. `string` is `List char`. Literals use `hchar` and `hstr`. `mlstring` is a one-constructor inductive, and `ml` builds literals.
- **div/mod:** Lean's conventions apply (`x / 0 = 0`, `x % 0 = x`). HOL4 leaves these unspecified.
- **Words:** `word8` and `word32` are `BitVec`.
- **ARB:** it becomes `default` via `[Inhabited _]`. This affects `HD []`, `LAST []`, out-of-range `EL`, `FAPPLY` outside the domain, `dest_var` of a non-variable, `termsem` on `Abs` of a non-`Var`, `empty`, `apply` and similar. I added `[Inhabited U]` to the set-theory and semantics definitions that need it.
- **Choice (`@`):** it becomes `Classical.epsilon`, or `Classical.choose` with a `dite` default. This covers `sub`, `power`, `union`, `upair`, `fresh`, `fresh_term` and `LEAST`. `VARIANT_PRIMES` uses `LEAST`.
- **Other unspecified values:**
  - `TL [] = []` and out-of-range `SEG` is `[]`.
  - `RESULT (Clash t) = t` and `CLASH (Result t) = t`.
  - `FUN_FMAP` on an infinite set is `FEMPTY`.
  - `instance_` defaults to `tmaof i name []`.
  - `ZIP` truncates.
- **Nested inductives:** `TYPE_SUBST`, `tyvars`, `type_ok` and `typesem` go through mutual `*_list` helpers. Each has an `_eq` lemma showing it equals the HOL4 `MAP`/`FOLDR`/`EVERY` form.
- **Orderings:**
  - `type_lt` is a mutual inductive with `type_llex` (= `LLEX type_lt`).
  - `LEX` is unfolded in `term_lt`.
- **Termination:**
  - `orda`, `INST_CORE`, `FIELDS` and `n2l` use WF recursion. `INST_CORE` uses the helper `sizeof_VSUBST_helper`.
  - `variant` uses a custom measure (`variant_bound` / `variant_fvlen`).
  - `mergesortN_tail` has overlapping clauses, and the last one applies for n ≥ 4.
- **Renames:**
  - `instance` is `instance_`, and `datatype dbterm` is `DbTerm`.
  - `Bool` is `BoolTy`, and set-theory `true`/`false` are `mtrue`/`mfalse`.
  - `toString` is `chr_to_str`, and mlstring `compare` is `mlstring_compare`.
  - `set` is `HOL.LIST_TO_SET`.
  - `Unit` is `unit`.
  - `X0 ^mem` becomes `X mem`.
- **Overloads:** `tysof`, `tmsof`, `sigof` and `axsof` are the classes `TysOf`, `TmsOf`, `SigOf` and `AxsOf`, with instances for `sig`, `thy` and `List update`. `^` on mlstring is `strcat`. I gave no `<` or `<=` overloads for mlstring; use `mlstring_lt`.
- **Notation:** `##`, `=+`, `=++`, `|+`, `===` and `|-` are scoped.

**Clean-room compliance.** No rule was broken. I read only files under `/home/claude/work/ws/`, the Lean and Batteries sources under `lean/.lake/packages/`, and the Lean toolchain. My temporary files were under `/tmp/claude-0/s/`. I did not read `/home/claude/candle-hol4-lean4-study`, `/mnt/` or `/tmp/claude*`, and I used no web, git, MCP, browser or subagent tools.
