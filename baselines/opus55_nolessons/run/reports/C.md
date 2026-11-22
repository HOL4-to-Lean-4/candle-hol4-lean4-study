I stated all 61 of 61 assigned holSyntaxExtra theorems in `/home/claude/work/wsC/lean/CandleLean/HolSyntaxExtra.lean`, and the final `lake build` succeeds (23 jobs). The only warnings are "declaration uses sorry".

**What was written**
- Each theorem has the HOL4 source text in a `/- HOL4: ... -/` comment directly above it and the proof `:= by sorry`.
- The theorems are in HOL4 source order, placed among stage 1's definitions without changing them:
  - HOL4 lines 18–223 go before `inductive subtype1`.
  - `subtype_Tyvar` goes after the `subtype` abbrev.
  - `subterm_Var`, `subterm_Const` and the theorems from HOL4 lines 277–1067 go after the `subterm` abbrev and before the `dbterm_` datatype. In HOL4 that datatype is at line 1497, after all of these theorems.
- `/home/claude/work/wsC/PROGRESS.tsv` has one `done` line for each theorem.

**Not stated:** none.

**Definitions added:** none.

**Stage 1 definitions I believe are wrong:** none found.

**Places where the Lean statement could differ from HOL4, or where I made a choice**
1. **`RACONV`**: the Lean name is `RACONV_thm`, because `RACONV` is already the inductive relation and Lean rejects the duplicate name. It is logged in PROGRESS.tsv. Its free variables (env, x1, x2, ty1, ty2, l1, r1, l2, r2, v1, t1, v2, t2) are universally quantified at the front, so the meaning is the same.
2. **`subtype_Tyvar`, `subterm_Var`, `subterm_Const`**: in HOL4 these are produced by `SIMP_CONV` with `RTC_CASES2` and the `_cases` theorems, not written out. I worked out the result by hand:
   - `subtype ty (Tyvar x) ↔ ty = Tyvar x`
   - `subterm tm (Var x ty) ↔ tm = Var x ty`
   - `subterm tm (Const x ty) ↔ tm = Const x ty`

   The reasoning: the step case of `RTC_CASES2` needs `subtype1 u (Tyvar x)` or `subterm1 u (Var/Const ..)`, and both are impossible. The only risk is the exact shape that `srw_ss` produces, for example `Tyvar x = ty` instead of `ty = Tyvar x`. That would change the form but not the meaning.
3. **`type_lt_thm`, `term_lt_thm`**: HOL4 applies `GEN_ALL` to each conjunct, so each wildcard `_` became its own universally quantified variable inside that conjunct. The `⇔ T` and `⇔ F` cases are stated as `↔ True` and `↔ False`.
4. **Free variables quantified explicitly with `∀`**: `type_cmp_refl`, `term_cmp_refl`, `hypset_ok_cons`, `EVERY_term_union` and `EVERY_term_remove` (including `P : term → Prop`), and `term_image_nil` (`f`).
5. **Boolean `=` in HOL4**: `ACONV_eq_orda` and the last conjunct of `WELLTYPED_CLAUSES` keep `=` on `Prop`. HOL4 `⇔` is `↔`.
6. **`'a` type variables**: in `ALOOKUP_MAP_dest_var`, `swap_ff` and `ff_def` they are implicit `{β γ : Type}` and similar. This uses `Type` (universe 0) only, which is a slight universe restriction but faithful for HOL4 types.
7. **HOL4 notation**: paired lambdas such as `λ(x,y). (y,x)` became projections, for example `fun p => (p.2, p.1)`. The rest follows CONVENTIONS.md: `##` is `PAIR_MAP`, `$=` is `fun a b => a = b`, `case` is `match`, and `MAP FST`/`MAP SND` are `List.map Prod.fst`/`List.map Prod.snd`.
8. **Shadowed `ty`**: in `VSUBST_HAS_TYPE` and `VSUBST_WELLTYPED` the inner `∃ x ty` shadows the outer `ty`, as in HOL4.

**Clean room:** I followed the rules. I read only files inside `/home/claude/work/wsC`. I used no web, git, MCP or other tools, spawned no subagents, and edited only `CandleLean/HolSyntaxExtra.lean` plus `PROGRESS.tsv`. I wrote temporary snippet files in my session scratchpad (under `/tmp/claude-0/...`) and spliced them in with a script. I never read any other path there.
