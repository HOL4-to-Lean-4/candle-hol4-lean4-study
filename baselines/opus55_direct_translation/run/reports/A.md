76 of 76 assigned theorems stated (Misc 39, Mllist 11, Mlstring 26), each `sorry`; `lake build` succeeds (198 jobs), only "declaration uses sorry" warnings. All HOL4 names kept, `namespace Candle`, `/- HOL4: ... -/` comments, HOL4 source order after needed defs; script check: order matches ASSIGNMENT.tsv, no stage 1 line changed. PROGRESS.tsv one `done` line per theorem. Added `universe w` to Misc.lean (append_thm, MAP_FST_I_PAIR_MAP).

Not stated: none. Definitions added: none. Stage 1 definitions believed wrong: none.

Choices:
- append_thm: separate type variables per conjunct (α, β, γ).
- w2n_lt_256 (ML-built): `∀ w : word8, w2n w < 256`.
- splitlines_nil (EVAL): `splitlines (str "") = []`.
- mlstring_common_char_prefix: free `t1`, `c2` quantified outermost; doubled `t2` binder kept (outer vacuous, as in HOL4).
- Free variables explicit, outside HOL4's own ∀ (x in merge_tail_MEM, sort_MEM; P in FIELDS theorems).
- `[Nonempty α]` in find_index_ALL_DISTINCT_EL (EL), `[Nonempty β]` in FUN_FMAP_FAPPLY_FEMPTY_FAPPLY (FAPPLY), per CONVENTIONS.md.
- Boolean `=` as `=` on Prop (MAP_EQ_ID, merge_tail_MEM), `⇔` as `↔`.
- plus_0_I: `$+ 0n` as `(fun n : Nat => 0 + n)`.
- 0w/1w as n2w 0 / n2w 1. word8 types in CHR_w2n_n2w_ORD, n2w_ORD_CHR_w2n fixed by annotations, checked with #check.
- «» as `mls ""`, strlit as implode.
- strcat_assoc RHS `(s1 ^ s2) ^ s3`; UPDATE_LIST_THM RHS `UPDATE_LIST (UPDATE h.1 h.2 f) t`.

Clean room: followed; insertion scripts and #check files in the session scratchpad. No web, git, MCP, subagents.
