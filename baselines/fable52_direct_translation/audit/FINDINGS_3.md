I could not write `/home/claude/work/audit/FINDINGS_3.md`: the Write tool refused, saying subagents must return findings as text. I did not try another way to write it. The findings follow; the caller should save them to that path.

# FINDINGS_3: fidelity audit of theory `holSyntaxExtra`

**Result: no defects and no suspects.** The six notes below record modelling choices that keep the meaning. No target can become false or trivially true through the translation.

All 123 targets are in `CandleLean/HolSyntaxExtra.lean` and `CandleLean/HolSyntaxExtra2.lean` (`RACONV` is named `RACONV_thm`). I checked them, and all the definitions in scope, against `holSyntaxExtraScript.sml`.

**Method.**
- I read every HOL4 statement next to its Lean statement.
- For the statements that ML code generates, I worked out by hand what the ML produces.
- I used `#check` (`ws3/scratch/t1.lean`) to confirm how Lean parses the statements whose binder and connective scope was least clear.
- With small proofs (`ws3/scratch/t2.lean`) I checked the `arities_match` equations, including the overlapping clause, and `arities_match_nil`, `arities_match_Tyvar`, `swap_ff`, `ff_def` and the first conjunct of `bind_list_aux_clauses`. All of these are provable.

## Notes

- **N1** (`HolSyntaxExtra.lean:962` `VSUBST_WELLTYPED`, HOL `:1067`; `HolSyntaxExtra2.lean:298` `dbVFREE_IN_bind`, HOL `:1593`).
  - In HOL4 the outer `ty` (hidden by the inner `∃x ty`) and the unused `b` get the type `'a`.
  - Lean adds `{α : Type} [Nonempty α]` for them. An unused quantifier over a non-empty type changes nothing.
  - Impact: none. Fix: none.
- **N2**: free variables of a HOL4 theorem are explicit Lean parameters. This means the same.
  - Affected: `RACONV_thm`, `subtype_Tyvar`, `subterm_Var`, `subterm_Const`, `type_cmp_refl`, `term_cmp_refl`, `hypset_ok_cons`, `EVERY_term_union`, `EVERY_term_remove`, `term_image_nil`, `term_ok_equation`, `bind_list_aux_clauses`, `fresh_union`, `arities_match_nil`, `arities_match_Tyvar`.
  - In `bind_list_aux_clauses`, `n`, `x`, `ty` are free, and the 4th conjunct rebinds `ty` correctly.
  - Impact: none.
- **N3**: statements that ML generates are faithful.
  - `subtype_Tyvar`, `subterm_Var`, `subterm_Const` (`SIMP_CONV` with `RTC_CASES2` and `*_cases`): the result is `ty = Tyvar x`, `tm = Var x ty`, `tm = Const x ty`.
  - `type_lt_thm`, `term_lt_thm` (`CONJUNCTS |> map GEN_ALL`): HOL4 makes each `_` a distinct fresh variable (`HOL4-src/parse/Parse_support.sml:159-167`). Lean quantifies `_0 _1 …` separately, with the correct types.
  - `mlstring_lt LEX LLEX type_lt` = `LEX mlstring_lt (LLEX type_lt)`, as Lean has it.
  - Impact: none.
- **N4** (`HolSyntax.lean:178`, `:205`; holSyntax scope): `type_lt` and `term_lt` are defined as the intersection of all relations closed under the HOL4 rules.
  - This has the same meaning as HOL4 `Inductive`.
  - It affects proofs only: there are no cases or induction principles. Proving `type_lt_thm` and `term_lt_thm` needs a hand-made monotonicity argument for LLEX and LEX.
- **N5**: `dest_var` and `RESULT` are one-clause, non-recursive definitions with a constructor pattern.
  - HOL4 makes them with `Prim_rec.new_recursive_definition` (`tfl/src/Defn.sml:1180-1199`), so the missing cases are unspecified, not `ARB`. The Lean `select` encoding matches.
  - `fresh` is `select` of `∀s. FINITE s ⇒ fresh s ∉ s`. I worked through the ML derivation and it gives this property. It is not stated as a Lean theorem, so a proof of `fresh_union` must get it from `select_spec`.
  - Every target that reaches the unspecified cases has a `welltyped` or `IS_RESULT` hypothesis.
  - Impact: none.
- **N6** (`HolSyntaxExtra.lean:284`, HOL `:3180`) `arities_match`: the overlapping clauses keep the HOL4 order, and Lean also takes the first match (checked with `simp`). It is defined by well-founded recursion, so proofs must use its equation lemmas: `rfl` does not work. Impact: none.

| id | declaration(s) | class | target impact |
|---|---|---|---|
| N1 | `VSUBST_WELLTYPED`, `dbVFREE_IN_bind` | note | none |
| N2 | 15 statements with free variables as parameters | note | none |
| N3 | `subtype_Tyvar`, `subterm_Var`, `subterm_Const`, `type_lt_thm`, `term_lt_thm` | note | none |
| N4 | `type_lt`, `term_lt` | note | proofs only |
| N5 | `dest_var`, `RESULT`, `fresh` | note | none |
| N6 | `arities_match` | note | none |

## Checked and found faithful

**Definitions:**
- `subtype1`, `subtype`, `subterm1`, `subterm`.
- `dbterm` (as `dbterm_ty`), `bind`, `db`, `dbVSUBST`, `dbVFREE_IN`, `dbINST`.
- `dbterm` (uses `find_index … 0`), `bind_list_aux`, `bv_names`.
- `simple_subst` (filters on `SND p ≠ v`), `simple_inst`.
- `rename_bvars` (the second recursive call uses the names the first one returns; the two `Abs` clauses do not overlap).
- `fresh`, `types_in`, `arities_match`.

**All 123 target statements.** These needed particular care:
- `VFREE_IN_RACONV`: the `⇔` is inside `∀x ty`, with `A ∧ ¬B` on each side (confirmed with `#check`).
- `INST_CORE_HAS_TYPE`: groups as `E1 ∨ (F ∧ G)`.
- `TYPE_SUBST_tyvars`: the sides of `tyin` and `tyin'` match HOL4.
- `term_ok_equation`: the order `typeof t = typeof s` matches HOL4.
- `REV_ASSOCD_MAP_db`: the inner `k` hides the outer `k`, as in HOL4.
- `FINITE_VFREE_IN_2` and `FINITE_MEM_Var`: the set comprehensions are encoded correctly.

**Constants the statements use:**
- Prelude: `PAIR_MAP`, `UNCURRY`, `LEX`, `LLEX`, `RTC`, `transitive`, `StrongOrder`, `StrongLinearOrder`, `trichotomous`, `TotOrd`, `TO_of_LinearOrder`, `flip_ord`, `OPTION_MAP`, `ALOOKUP`, `EVERY`, `MEM`/`set`, `FILTER`, `ZIP`, `ALL_DISTINCT`, `TAKE`, `DROP`, `SORTED`, `DISJOINT`, `FINITE`, `setOf`, `INSERT`, `UNION`, `I`.
  - `ZIP`: this HOL4's `ZIP_def` truncates the longer list, and the Lean one does too.
- Package: `find_index`, `REV_ASSOCD`, `ALPHAVARS`, `IS_RESULT`, `RESULT`.
- holSyntax: `has_type`, `typeof`, `RACONV`, `ACONV`, `ordav`, `orda`, `term_union`, `term_remove`, `term_image`, `VFREE_IN`, `TYPE_SUBST`, `VSUBST`, `sizeof`, `INST_CORE`, `INST`, `tyvars`, `tvars`, `equation`, `type_ok`, `term_ok`, `alpha_lt`, `hypset_ok`, `is_std_sig`, `theory_ok`.
- Name resolution: inside `namespace Candle`, `bind` resolves to `Candle.bind` and `set` to `Candle.set` (confirmed).

**Uncertainty.**
- I checked the holSyntax constants against their HOL4 text, but not clause by clause in depth, because they are another auditor's scope.
- Of the targets, I proved only the small sanity examples listed under Method.