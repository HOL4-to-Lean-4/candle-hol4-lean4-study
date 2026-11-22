All 76 assigned theorems are stated, each with a `/- HOL4: ... -/` comment and `:= by sorry`. `lake build` ends with "Build completed successfully (19 jobs)", with only `sorry` and stage 1 linter warnings.

- **Where they went:** 39 in `CandleLean/Misc.lean`, 11 in `CandleLean/Mllist.lean`, 26 in `CandleLean/Mlstring.lean`. In each file the block sits at the end, before the closing `end`, in HOL4 source order. The Lean names are the HOL4 names.
- **Progress log:** `/home/claude/work/wsA/PROGRESS.tsv` has 76 lines, all `done`.
- **Definitions added:** none.
- **Stage 1 definitions I believe are wrong:** none.

Places where a statement could differ in meaning from HOL4:
- **`[Inhabited α]` on `find_index_ALL_DISTINCT_EL`:** Lean's `EL` needs it. HOL4 types are all non-empty, so this should not change the meaning.
- **`FUN_FMAP_FAPPLY_FEMPTY_FAPPLY`:** it carries `[Inhabited β]` for the same reason, since `FAPPLY` needs it.
- **`mlstring_common_char_prefix`:** HOL4 binds `t2` twice (`∀c1 s1 s2 t2 t2.`), and the outer binder is vacuous with a fresh type variable. I dropped it. The free variables `t1` and `c2` are quantified outermost.
- **`splitlines_nil`:** HOL4 states it as `EVAL “splitlines ""”`. I worked out the result as `splitlines "" = []` and wrote it with `hstr ""`.
- **`w2n_lt_256`:** HOL4 derives it from `w2n_lt` instantiated at `:8`. I wrote the result by hand as `∀ w : word8, w2n w < 256`.
- **`strcat_assoc`:** `^` is left-associative, so `s1 ^ s2 ^ s3` is written `strcat (strcat s1 s2) s3`.
- **`«»` literals:** written as `ml ""`.
- **Booleans as `Prop`:** HOL4 `=` between booleans is `=` on `Prop`, in `MAP_EQ_ID` and `merge_tail_MEM`. `⇔` is `↔`.
- **`v2w_32_F` and `v2w_32_T`:** `0w` and `1w` are written `(n2w 0 : word32)` and `(n2w 1 : word32)`, and `[F]`/`[T]` as `[False]`/`[True]`.
- **Implicit type variables:** these became `{α : Type u}` binders, with `Type _` for the one extra type variable in `MAP_FST_I_PAIR_MAP`. I did not touch the existing `universe u v` line in `Misc.lean`.

Clean room: I followed the rules. I read only files inside `/home/claude/work/wsA/` and did not use the web, git, MCP tools or subagents. I edited only `Misc.lean`, `Mllist.lean` and `Mlstring.lean`, plus `PROGRESS.tsv`. I also left three scratch files in the workspace root (`misc_thms.lean`, `mllist_thms.lean`, `mlstring_thms.lean`). They are not part of the Lean project and can be deleted.
