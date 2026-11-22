62 of 62 assigned theorems written in `/home/claude/work/wsD/lean/CandleLean/HolSyntaxExtra2.lean`, inside `namespace Candle` with `open HOL Classical`, HOL4 source order, each `:= by sorry`, all names as in HOL4. Only other change: `universe u` inside the `noncomputable section` (for `dbVFREE_IN_bind`). `lake build` succeeds (198 jobs), only `declaration uses 'sorry'` warnings.

Could not state: none. Definitions added: none. Stage 1 definitions believed wrong: none (checked `bind`, `db`, `dbVSUBST`, `dbVFREE_IN`, `dbINST`, `dbterm`, `bind_list_aux`, `bv_names`, `simple_subst`, `simple_inst`, `rename_bvars`, `fresh`, `arities_match`, `VSUBST`, `INST_CORE`, `term_ok`, `type_ok`, `theory_ok`, `is_std_sig`).

Possible differences:
- `dbVFREE_IN_bind`: unused HOL4 variable `b : 'a` written `(b : α)` with `{α : Type u}` and no `[Nonempty α]`; for empty `α` trivially true, equivalent overall since `α` is universally quantified.
- Free variables made explicit: `bind_list_aux_clauses` (n x ty), `fresh_union` (s t : Set string), `arities_match_nil` (ls), `arities_match_Tyvar` (v ps ty obs).
- Boolean `=` in `arities_match_nil`/`arities_match_Tyvar` written as `=` on `Prop`, per CONVENTIONS.md.
- `λ(x,y)` written with projections; `{(x,ty) | P}` as `GSPEC (fun p => ((p.1,p.2), P p.1 p.2))` per CONVENTIONS.md.
- Notation per CONVENTIONS.md (FST/SND, o, MEM, set, ∪, ===, has_type, Bool→BoolTy). Explicit brackets where precedence could differ (e.g. `INST_CORE_HAS_TYPE` conclusion `A ∨ (B ∧ C)`). Compiled a copy with `autoImplicit`/`relaxedAutoImplicit` off: no auto-bound variables.

Clean room: followed. Read only `/home/claude/work/wsD/`, wrote only temporary files in the session scratchpad; edited only `HolSyntaxExtra2.lean` and `PROGRESS.tsv`; no web, git, MCP, browser or subagents.
