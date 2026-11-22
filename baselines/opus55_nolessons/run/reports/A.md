All 75 assigned theorems are stated, each with a `sorry` proof, and the final `lake build` succeeds (23 jobs, only `declaration uses 'sorry'` warnings). I could state every assigned theorem.

**Where they are**
- 39 `misc` theorems in `/home/claude/work/wsA/lean/CandleLean/Misc.lean`, added at the end of the file after all stage 1 definitions, in HOL4 source order.
- 11 `mllist` theorems in `/home/claude/work/wsA/lean/CandleLean/Mllist.lean`. I put the seven mergesort theorems (`merge_tail_MEM` … `mergesortN_tail_PERM`) before the stage 1 `sort` definition, where they sit in the HOL4 script. The four `sort_*` theorems come after it. No stage 1 declaration was changed or moved.
- 25 `mlstring` theorems in `/home/claude/work/wsA/lean/CandleLean/Mlstring.lean`, added at the end, in source order.
- Every theorem keeps its HOL4 name at top level and has a `/- HOL4: ... -/` comment above it.
- `/home/claude/work/wsA/PROGRESS.tsv` has one `done` line per theorem, 75 lines.

**Definitions added:** none.

**Stage 1 definitions I believe are wrong:** none found.

**Places where the meaning could differ from HOL4, or where I made a choice**
- **Free variables.** HOL4 variables that are free in a statement became explicit theorem arguments, which is the same as HOL4's implicit universal closure. Examples: `x` in the `*_MEM` theorems, `P` in the `FIELDS` theorems, `f` in `MAP_FST_I_PAIR_MAP`.
- **Boolean equations.** Where HOL4 writes `=` between booleans (`merge_tail_MEM`, `MAP_EQ_ID`), I kept `=` on `Prop`. I used `↔` where HOL4 writes `⇔`. By `propext` the two mean the same.
- **`mlstring_common_char_prefix`.** The HOL4 text is `∀c1 s1 s2 t2 t2. …`, which binds `t2` twice and leaves `c2` and `t1` free. I made `c2` and `t1` theorem arguments, and called the outer, unused `t2` `_t2`. The meaning is the same; the HOL4 statement itself looks like a typo for `∀c1 c2 s1 s2 t1 t2`.
- **`w2n_lt_256`.** HOL4 derives it rather than stating it. I stated the result: `∀ w : word8, w2n w < 256`. This comes from `wordsTheory.w2n_lt` (`!w:'a word. w2n w < dimword(:'a)`) with `'a` set to 8 and `dimword(:8)` evaluated to 256.
- **`splitlines_nil`.** HOL4 defines it as `EVAL “splitlines ""”`. I stated what it evaluates to, `splitlines ([] : string) = []`, worked out by hand: `FIELDS` gives `[""]`, `LAST` is `""`, `NULL` holds, `FRONT [""] = []`.
- **`plus_0_I`.** HOL4 `$+ 0n` is written as `(fun n : Nat => 0 + n)`, as `CONVENTIONS.md` allows. It is the eta-expanded form of the same function.
- **`strcat_assoc`.** HOL4 `^` is left-associative, so `s1 ^ s2 ^ s3` became `strcat (strcat s1 s2) s3`.
- **`[Nonempty _]`.** I added it only where `CONVENTIONS.md` requires it: `find_index_ALL_DISTINCT_EL` (uses `EL`) and `FUN_FMAP_FAPPLY_FEMPTY_FAPPLY` (uses `FAPPLY`/`FUN_FMAP`).
- **Type variables.** I wrote them as `{α : Type}`. This matches HOL4 types.

**Clean room:** I followed the rules. I read only files inside `/home/claude/work/wsA` (package sources, HOL4-src, stage 1 Lean files and `CONVENTIONS.md`). I used no web, git, MCP, browser or device tools and no subagents. I edited only the three assigned Lean files and created `PROGRESS.tsv`.
