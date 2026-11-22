# Comparing the baseline and nolessons translations of Candle `proves_sound`

## Bottom line

- **Target statements:** none of the 278 differ in meaning.
- **Definitions:** none of the definitions, datatypes or inductive relations the statements use differ in meaning. This covers all 114 + 6 + 3 targets and the HOL4 library constants under them.
- **What does differ:** encodings only. Examples are `GSPEC` against `setOf`, pair-pattern lambdas against projections, `=` against `↔`, universes, extra `[Nonempty U]` binders, `BitVec` against a subtype word, and the representation of finite maps. Neither translation has a constant defined with `sorry`. Neither adds an `axiom`; the only `opaque` is nolessons' `ARB`.

## How it was checked

1. In each project I wrote a scratch metaprogram. It dumped every constant's elaborated type, once with the default printer and once with `pp.explicit`. It also dumped every `def`'s body and checked each body for `sorry` (none found).
2. For nolessons, the dump rewrote `MEM a l` to list membership and `strlit` to `implode`. For baseline, it added `===` notation for `equation`.
3. I normalised the dumps with a script:
   - removed the namespaces `Candle.`, `HOL.` and `sptree.`;
   - applied the rename tables from both `CONVENTIONS.md` files (`BoolTy`/`Bool_`, the `*0` constants, `ctxt_tysof`/`thy_tysof` mapped to `tysof`, `compare`/`compare_`, `dbterm_t`/`dbterm_`, `bind`/`bind_`);
   - mapped `mls ""` to `implode []`;
   - dropped universe names and `[Nonempty _]` binders.
4. Results of the diff:
   - **Default printer:** 231 of 278 statements are textually identical and 47 differ.
   - **`pp.explicit`:** the leftover differences come only from class instance arguments, `word` against `BitVec`, the `implode` spelling and `Nonempty`. No hidden implicit argument or coercion differs.
5. I read all 47 differing statements by hand.
6. I compared every definition used, both by its stripped source and by its dumped body; 119 bodies differ in text and I reviewed each one. This covered:
   - the Prelude (List, Set, String, FiniteMap, Words, Sptree, ASCIInumbers, Mergesort);
   - Misc, Mllist, Mlstring and SetSpec;
   - HolSyntaxLib, HolSyntax, HolSyntaxExtra and HolSemantics.
7. I checked points against the HOL4 sources. These include:
   - `type_lt`/`term_lt` (holSyntaxScript.sml:113-135);
   - `orda`/`ordav` (:145-167);
   - `VARIANT_PRIMES` (:281-290);
   - `instance_def` (holSemanticsScript.sml:112-119);
   - `fresh_def` (holSyntaxExtraScript.sml:2325);
   - `arities_match` (:3180) and `rename_bvars` (:2203);
   - `FAPPLY_DEF` (finite_mapScript.sml:180);
   - `ARB` (boolScript.sml:245), `append_thm` (miscScript.sml:141), and `hol4_check.txt`.
8. All scratch files were deleted at the end.

## Differences in meaning

None. The HOL4 facts the checks rely on:

- **`type_lt_thm`, `term_lt_thm`, `subtype_Tyvar`, `subterm_Var`, `subterm_Const`, `pair_inj`, `splitlines_nil`** (in `hol4_check.txt`): both translations match HOL4's printed statements.
- **`VSUBST_WELLTYPED` and `mlstring_common_char_prefix`:** HOL4 has an unused bound variable of type `α` (`ty:α`, and the first `t2:α`). Both translations give it a concrete type. That is equivalent, and the two translations agree.

## Form-only differences (encodings)

| Area / declarations | baseline | nolessons | HOL4 text | Closer to HOL4 |
|---|---|---|---|---|
| Set comprehension in statements (11): termsem_simple_subst, termsem_simple_inst, VSUBST_simple_subst, INST_CORE_simple_inst, INST_simple_inst, rename_bvars_RACONV, rename_bvars_ACONV, FINITE_VFREE_IN, FINITE_VFREE_IN_list, VFREE_IN_FINITE, VFREE_IN_FINITE_ALT | `setOf P` (= `P`) | `GSPEC (fun x => (x, P x))` | `{x \| P}` = `GSPEC (λx. (x,P))` | nolessons (literal). Equivalence checked in Lean. |
| `{(x,ty) \| …}` (FINITE_VFREE_IN_2, FINITE_MEM_Var) | `GSPEC fun p => ((p.1,p.2), …)` | `GSPEC fun (x,ty) => ((x,ty), …)` | pattern `λ(x,ty).` | nolessons |
| Pair-pattern lambdas (12): termsem_raconv, termsem_VSUBST, termsem_INST, swap_ff, ff_def, RACONV_SYM, ALPHAVARS_TYPE, RACONV_TYPE, ordav_sym, orda_sym, REV_ASSOCD_ALOOKUP, REV_ASSOCD_FILTER | `match p with \| (x,y) => …` | `p.snd`, `p.fst` | `λ(x,y). …` (UNCURRY) | baseline |
| HOL `=` on bool: WELLTYPED_CLAUSES (last conjunct), ACONV_eq_orda | `↔` | `=` on `Prop` | `=` | nolessons (literal); equal by `propext` |
| termsem_Equal | the `Equalsem` lambda written inline | `Equalsem mem [...]` (reducible abbrev) | ML value `^Equalsem` spliced in | baseline (HOL4 term is the inlined lambda) |
| append_thm | separate type variables α, β, γ per conjunct | one α | HOL4 infers independent type variables | baseline. Logically equivalent because each conjunct is universally quantified. |
| Type-variable names, order and universes (ALOOKUP_MAP_dest_var, MEM_FOLDR_LIST_UNION, MAP_FST_I_PAIR_MAP, UPDATE_LIST_THM, APPLY_UPDATE_LIST_ALOOKUP, FUN_FMAP_FAPPLY_FEMPTY_FAPPLY, irreflexive/trichotomous_inv_image) | universe-polymorphic `Type u/v/w` | mostly `Type` | one universe | equivalent |
| Binder order/names (mlstring_common_char_prefix, ALPHAVARS_REFL) | `t2 t2` | `_t2 t2`, reordered | free `t1`, `c2`; unused `t2:α` | equivalent |
| Character literal (PRIMED_NAME_EXISTS, PRIMED_INFINITE, VARIANT, splitlines) | `ch '\''` (code mod 256), `str ""` | `CHR 39`, `[]` | `#"'"`, `""` | nolessons (`CHR n` like HOL4). `ch '\'' = CHR 39` checked with `decide`. |
| `∪` against `UNION` (fresh_union, domain_nat_set_from_list) | `UNION s t` | `s ∪ t` (unfolds to `UNION`) | `∪` | equivalent |
| Words (w2n_lt_256, CHR_w2n_n2w_ORD*, n2w_ORD_CHR_w2n*, v2w_32_T/F) | `BitVec n`, `FCP` via `FCP_bits` | structure `{w2n // w2n < 2^d}`, `FCP` via a sum over `range d` | `bool[d]` (fcp) | both are bijections; same bits |
| `[Nonempty U]` (31 statements: the setSpec ones, typesem_*, termsem_raconv/aconv/frees/VSUBST/INST/simple_*, REV_ASSOCD_FILTER) | omitted where not needed (`sub`, `upair`, `instance_`, `termsem0` use explicit witnesses) | always present | every HOL type is nonempty | baseline (no extra hypothesis); harmless |
| Finite maps | structure `{rep : α → Option β; finite support}`; `FAPPLY` outside the domain is `ARB` | HOL4's `α → β ⊕ Unit` with inductive `is_fmap`; `FAPPLY f x = OUTL (fmap_REP f x)` | `FAPPLY_DEF: f ' x = OUTL (fmap_REP f x)` | nolessons. Baseline proves `FAPPLY FEMPTY 0 = ARB` by `rfl`, which HOL4 cannot prove. No target uses this. |
| `ARB` | `Classical.epsilon (fun _ => False)` | `opaque` | `new_constant` with no definition | nolessons (baseline proves `ARB = ε(λ_.F)`, which no target uses) |
| `CHR n`, n ≥ 256 | `(ARB : Nat → char) n` | `Classical.epsilon` of the bijection specification | `char_BIJ` abstraction (unspecified for n ≥ 256) | nolessons slightly closer; both are unspecified |
| `sigof`/`tysof` overloads | separate constants `thy_tysof`, `ctxt_tysof`, … | type-class methods | type-dependent overloads | equivalent |
| `has_type`, `RACONV`, `proves`, `updates`, `subtype1` constructors | implicit arguments, capitalised names | explicit arguments, lowercase names | — | same rules |

## Counts (278 statements)

- **Identical after normalisation:** 231. The normalisation covers renames, `MEM` against `∈`, `strlit`/`mls ""` against `implode`, universes and `Nonempty` binders.
- **Different in form only:** 47 (11 + 2 + 12 + 2 + 1 + 9 + 2 + 3 + 2 + 3 from the table rows above).
- **Different in meaning:** 0.

## Limits

- **The two can only be compared side by side.** The projects are separate environments, so I could not prove the statements equivalent across them. Equivalence rests on textual diffs, an explicit-mode diff, and manual review of the definitions and of the 47 differing statements. I used a few Lean `example`s for the edge cases (GSPEC against setOf, `ch` against `CHR`, the `FAPPLY`/`ARB` behaviour of baseline, `HD [] = ARB`).
- **Shared choices that go beyond HOL4.** These are not differences between the two, but they are worth knowing:
  - Both define `HD []`, `LAST []`, `RESULT (Clash _)`, `CLASH (Result _)` and `dest_var` of a non-variable as `ARB`. HOL4 specifies only the defining clause.
  - Both write HOL4's unused bound variables, the `ty:α` in VSUBST_WELLTYPED-style statements, at a concrete type.
- **Not compared:** helper and auxiliary lemmas, and constants that only nolessons translates (`sum_sizes`, `make_app_list_ann`, `shrink`, `str_app_list_opt`, `ConstDef`). No target statement uses them.
- **No proofs were attempted.** Unspecified values (ARB, OUTL, epsilon) are compared by how they are specified, not by trying to show something is unprovable in HOL4.

