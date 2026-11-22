All 61 assigned theorems are stated in `lean/CandleLean/HolSyntaxExtra.lean` (61 of 61), in HOL4 source order after the stage 1 definitions, each with a `/- HOL4: ... -/` comment and `:= by sorry`. The final `lake build` succeeds (19 jobs), and the only warnings are unused-variable ones in stage 1 files and `sorry` warnings.

`PROGRESS.tsv` in the workspace root has one `done` line per theorem. Every theorem keeps its HOL4 name, and none needed a rename.

**Not stated:** none.

**Added definitions:** none.

**Stage 1 definitions I believe are wrong:** none found.

**Where meaning could differ from HOL4:**
- **Free variables.** HOL4 theorems with free variables (for example `RACONV`, `hypset_ok_cons`, `term_image_nil`, `type_cmp_refl`) are stated as Lean theorems with explicit binders, which means universal quantification. I bound every variable explicitly.
- **`subtype_Tyvar`, `subterm_Var`, `subterm_Const`.** HOL4 gives these as `SIMP_CONV` results with no written statement. I derived the statements by hand and wrote them as `x subtype/subterm (Var/Tyvar/Const ..) ↔ x = ...`. The orientation follows `RTC_CASES2`. I did not run HOL4, so these three are my reconstruction, and I recorded that in their `PROGRESS.tsv` notes.
- **`type_lt_thm`, `term_lt_thm`.** I wrote each conjunct with its own `∀` (the `GEN_ALL` in the source). The `_` wildcards became distinct fresh variables.
- **`RACONV` theorem and statements that use `RACONV`.** The name clashes with the stage 1 inductive `RACONV`, so I wrote `HolSyntax.RACONV` explicitly in those statements.
- **`λ(x,y). (y,x)`.** I wrote it as `fun p => (p.2, p.1)`, which is definitionally the same.
- **`UNCURRY $=`.** I wrote it as `UNCURRY (fun a b : term => a = b)`.
- **`bool` equalities.** HOL4's `=` and `⇔` between booleans become `↔`. The exception is `WELLTYPED_CLAUSES` (last clause) and `ACONV_eq_orda`, where the source uses `=` and I kept `=` on `Prop`.
- **`F` and `T`.** They are `False` and `True`.
- **`term_union_thm`.** The `case ... of` is a Lean `match` on `Ordering`.
- **Type variables.** HOL4's implicit type variables are Lean implicit `Type u` variables (`ALOOKUP_MAP_dest_var`, `swap_ff`, `ff_def`).

**Clean-room:** I followed the rules. I read only files inside `/home/claude/work/wsC` (the HOL4 sources and the Lean project). I used no web, git, MCP, browser or other-workspace paths. I wrote scratch text to `/tmp/claude-0/blk.lean` (the session scratch area). I spawned no subagents and edited no files other than `HolSyntaxExtra.lean` and `PROGRESS.tsv`.
