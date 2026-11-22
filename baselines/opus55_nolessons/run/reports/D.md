I stated all 62 of my 62 assigned theorems. They are in /home/claude/work/wsD/lean/CandleLean/HolSyntaxExtra2.lean, in HOL4 source order. Each has the `/- HOL4: ... -/` comment with the source statement and the proof `:= by sorry`. The final `lake build` succeeds (23 jobs), and its only warnings are "declaration uses sorry".

- **Could not state:** none.
- **Definitions added:** none. Everything needed was already in stage 1.
- **Stage 1 definitions I believe are wrong:** none found. I did not do a full audit; I only read the definitions these statements use.
- **Names:** all theorems keep their HOL4 names. As CONVENTIONS.md prescribes, they are at the top level with no namespace.
- **Log:** /home/claude/work/wsD/PROGRESS.tsv has one line per theorem, all with status `done`.

**Places where the Lean form differs from the HOL4 text (I believe none changes the meaning):**
1. **Free variables** in `term_ok_equation`, `fresh_union`, `bind_list_aux_clauses`, `arities_match_nil` and `arities_match_Tyvar` are bound by an explicit outer `∀`. This is HOL4's implicit generalisation.
   - In `bind_list_aux_clauses`, the inner `∀ ... ty ...` of the last conjunct shadows the outer free `ty`, exactly as in HOL4.
2. **`dbVFREE_IN_bind`** has HOL4's unused `∀b`, whose type is the unconstrained `'a`. In Lean this is `{α : Type}` with `(b : α)`.
3. **`bind`** is written `bind_`, per CONVENTIONS.md. This affects `bind_not_free`, `bind_dbVSUBST`, `bind_dbVSUBST_cons`, `dbVFREE_IN_bind` and `dbINST_bind`.
4. **Pattern lambdas** such as `λ(x,y). ...` and `λ(s',(s,ty)). ...` are written with projections (`p.1`, `p.2`, `p.2.1`). This is the same function as HOL4's `UNCURRY` form. It affects `term_ok_raconv`, `MAP_db_FILTER_neq`, `REV_ASSOCD_MAP_db`, `VSUBST_dbVSUBST`, `simple_subst_has_type` and `rename_bvars_RACONV`.
5. **HOL4 notation mapped to Lean**, following CONVENTIONS.md:
   - `FST`/`SND` become `.1`/`.2` or `Prod.fst`/`Prod.snd`; `MAP`, `LENGTH`, `TAKE` and `DROP` become the Lean `List` functions; `o` becomes `∘`.
   - `FST sig` becomes `sig.1`, `Bool` becomes `Bool_`, and `has_type` is written as a prefix function.
   - `ZIP` takes a pair, as in HOL4.
6. **Equality on booleans and `⇔`:**
   - The HOL4 `=` between booleans in `arities_match_nil` and `arities_match_Tyvar` is kept as `=` on `Prop`, which is `↔` by `propext`.
   - Every `⇔` is written `↔`.
7. **Set comprehensions** such as `{x | ...}` and `{(x,ty) | ...}` use stage 1's `GSPEC` macros. I checked with `#check` that the element types come out as intended: `mlstring`, `mlstring × type` and `Set string`.

**Clean room:** I followed the rules. I read only files inside /home/claude/work/wsD (the HOL4 package sources and the Lean project). I edited only `CandleLean/HolSyntaxExtra2.lean` and created the root `PROGRESS.tsv`. I also wrote one throwaway `#check` file in my session scratchpad (/tmp/claude-0/-home-claude/a7028057-51a5-5984-b20c-9e2d129a6ff1/scratchpad/chk.lean), which is outside the project. I did not use the web, git, MCP tools or subagents, and I ran one Lean process at a time.
