# Audit 3: holSyntaxExtra (Opus 5.5 translation)

The auditor could not write this file itself (the harness refused subagent file writes and asked for
the findings as text). The orchestrator saved its final report here verbatim.

I found no defects and no suspects in the holSyntaxExtra scope, only three notes. None of the notes changes the meaning of any target, and none can make a target false or trivially true.

**What I checked**
- All 123 targets: 62 in `HolSyntaxExtra.lean`, 61 in `HolSyntaxExtra2.lean`. The only extra theorem is `fresh_def`, which is proved, not a target.
- I compared each statement and definition with the actual `holSyntaxExtraScript.sml`, not only the `/- HOL4: -/` comments.
- The target names match `TARGETS.tsv` exactly, except that `RACONV` is named `RACONV_thm` in Lean.
- Experiments are in `/home/claude/work/audit/ws3/scratch/t1.lean`, `t2.lean` and `t3.lean`.

**N1 (note).** `VSUBST_WELLTYPED`, `HolSyntaxExtra.lean:988` vs `holSyntaxExtraScript.sml:1067`.
- HOL4 binds an outer `ty` in `∀tm ty ilist.` that is never used, because the inner `∃x ty` shadows it. Type inference therefore gives it a free type `'a`.
- Lean gives it type `type`. The inner `∃ x ty` is translated correctly.
- No semantic effect, because a `∀` over an unused variable of a nonempty type is equivalent to its body. This is probably the "minor type-signature discrepancy" already known.
- Fix (optional): write `{α : Type u} (ty : α)`, or leave it as it is.

**N2 (note).** `dbVFREE_IN_bind`, `HolSyntaxExtra2.lean:293` vs `holSyntaxExtraScript.sml:1593`.
- The unused variable `b : 'a` is translated faithfully as `{α : Type u} (b : α)`.
- At an empty `α` the Lean statement is vacuous. Because it quantifies over every `α`, it is still equivalent to HOL4: instantiate `α := Unit`.
- Callers must pass a dummy `b`, for example `()`.

**N3 (note).** Encodings that only change how proofs go.
- **`RACONV_thm`:** renamed because `RACONV` is the inductive relation. HOL4's free variables become explicit parameters, which is equivalent.
- **`arities_match`:** the HOL4 patterns overlap, and Lean uses first-match semantics as HOL4 does. The equation lemma `eq_5` carries the side condition "not both heads are `Tyapp`".
  - I proved the targets `arities_match_nil` and `arities_match_Tyvar`.
  - I tested small cases: one `Tyvar`/`Tyapp` pair gives True, two `Tyapp`s with the same name and mismatched arity give False, and different names give True.
- **`rename_bvars`:** the HOL4 `let (names,t) = …` bindings are written with projections. In the `Comb` case the second call correctly uses the updated `names` and the original `t2`. I confirmed this with `simp` on a term with two binders.
- **`fresh`:** it is `Classical.epsilon` of `∀s. FINITE s → f s ∉ s` on `Set string`, where `string = List char` with 8-bit `char`. This is exactly the `new_specification` result.
- **`dest_var`:** on a non-variable it returns one single `ARB` (checked by `rfl`), matching HOL4's pattern completion.

**Found faithful**
- **Definitions and relations:**
  - `subtype1` and `subterm1`, with the `RTC` overloads `subtype` and `subterm`.
  - The datatype `dbterm` (named `dbterm_t` in Lean).
  - `bind`, `db`, `dbVSUBST`, `dbVFREE_IN`, `dbINST`, `dbterm`, `bind_list_aux`, `bv_names`.
  - `simple_subst`: the filter tests the second pair component, which I confirmed by `simp`.
  - `simple_inst`, `rename_bvars`, `fresh`, `types_in`, `arities_match`.
- **Prelude and holSyntax constants the scope uses:**
  - Relations and orders: `LEX`, `LLEX`, `SORTED`, `TotOrd`, `TO_of_LinearOrder`, the relation predicates, `RTC`, `flip_ord`.
  - Pairs and lists: `PAIR_MAP`, `UNCURRY`, `ALOOKUP`, `FILTER`, `EVERY`, `ALL_DISTINCT`, `ZIP`, `LIST_TO_SET`, `find_index`, `REV_ASSOCD`, `ALPHAVARS`.
  - Sets: `GSPEC`, `setOf`, `UNION`, `INSERT`, `DISJOINT`, `FINITE`. I confirmed that the `{(x,ty) | P}` encoding has the intended membership.
  - holSyntax constants: `RESULT`/`IS_RESULT`, `TYPE_SUBST`, `VSUBST`, `INST_CORE`, `INST`, `sizeof`, `typeof`, `has_type`, `RACONV`, `type_lt`/`term_lt`, `orda`/`ordav`, `term_union`/`term_remove`/`term_image`, `VFREE_IN`, `type_ok`/`term_ok`, `hypset_ok`, `is_std_sig`, `theory_ok`.
  - I checked these only as far as this scope uses them. Their full audit belongs to the other auditors.
- **All 123 target statements:**
  - I checked quantifier scope, precedence (`∧` binds tighter than `⇔`, `⇒` is right-associative), shadowing, free-variable generalisation, argument order and how `MEM`/`IN`/`set` resolve. I used `#check` on the tricky ones, for example `INST_CORE_HAS_TYPE`, `VFREE_IN_RACONV`, `WELLTYPED_CLAUSES` and `rename_bvars_ACONV`.
  - I worked out the SIMP_CONV-generated statements by hand: `subtype_Tyvar`, `subterm_Var` and `subterm_Const`.
  - The `CONJUNCTS |> map GEN_ALL` statements (`type_lt_thm`, `term_lt_thm`) match.
- **Other checks:**
  - No `BEq`, `==` or `decide` appears in the scope.
  - `bind` resolves to `Candle.bind` and `sizeof` to `Candle.sizeof`.

**Limits.** I proved only a few small targets: `TYPE_SUBST_Bool`, `subterm_Var`, `arities_match_nil` and `arities_match_Tyvar`. The deeper targets also depend on constants outside this scope, such as `mlstring_lt`/`compare` and `VARIANT`, which are for the mlstring and holSyntax auditors.

**Summary table**

| id | Lean location | HOL4 location | declaration | class | impact on targets |
|---|---|---|---|---|---|
| N1 | `HolSyntaxExtra.lean:988` | `holSyntaxExtraScript.sml:1067` | `VSUBST_WELLTYPED` | note | none (unused bound variable has type `type` instead of `'a`) |
| N2 | `HolSyntaxExtra2.lean:293` | `holSyntaxExtraScript.sml:1593` | `dbVFREE_IN_bind` | note | none (unused `b : α`, vacuous only at empty `α`) |
| N3 | various | various | `RACONV_thm` name, `arities_match` overlap, `rename_bvars` lets, `fresh`, `dest_var` ARB | note | none |

Defects: 0. Suspects: 0. Notes: 3.
