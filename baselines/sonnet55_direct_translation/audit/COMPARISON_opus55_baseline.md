# Comparison of the sonnet and baseline Candle translations

## Bottom line
- **0 of the 278 target statements differ in meaning** between baseline and sonnet.
- **0 definitions differ in a way that any target can see.** One sonnet definition does not match HOL4: `RESULT (Clash t) = t` and `CLASH (Result t) = t`. HOL4 does not leave these values free. It provably maps every `Clash t` to the same `ARB`. Under every target's hypotheses, `RESULT` and `CLASH` only ever see the expected constructor, so no target changes.
- 227 statements are identical after normalisation. The other 51 differ in form only.
- Three items on your list of over-specified values are not over-specified: HOL4 itself fixes `TL [] = []`, a truncating `ZIP`, and `DIV`/`MOD` by 0.

## Differences in meaning

| Declaration | Baseline | Sonnet | HOL4 | Right | Evidence |
|---|---|---|---|---|---|
| (no target statement) | — | — | — | — | 227 statements have identical elaborated types after normalisation. The other 51 were each checked by hand and differ in form only. |
| `RESULT` / `CLASH` (definition; no target affected) | `RESULT (Clash t) = ARB` (one fixed value, the same for all `t`) | `RESULT (Clash t) = t`, `CLASH (Result t) = t` | Pattern completion fills a missing constructor with `ARB` (HOL4-src/1/Pmatch.sml:154,182). So HOL4 proves `RESULT (Clash a) = RESULT (Clash b)`. | Baseline | Lean: in sonnet, `RESULT (Clash (0:Nat)) ≠ RESULT (Clash 1)` is proved by `simp [RESULT]`. In baseline, `RESULT (Clash a) = RESULT (Clash b)` is proved by `rfl`. Every target that uses `INST`, `INST_CORE` or `RESULT` has a `welltyped`/`term_ok`/`IS_RESULT` hypothesis (holSyntaxExtraScript.sml:1265,1273,1283,1468,1788,1908,2046,2110,2162). Under it, `RESULT` and `CLASH` are only applied to the matching constructor, so the sonnet choice is never reached. |

## Over-specified values in sonnet

| Value | HOL4 status | Target affected? | How |
|---|---|---|---|
| `ARB` = `default` under `[Inhabited _]` | `ARB = @x. F`, unspecified | No | Instances that appear as hypotheses are universally quantified, so this is equivalent. For types with a global instance (`mlstring`, `type`, `term`, `char`), `HD []`, `dest_var` of a non-variable and `FAPPLY` outside the domain become known values. Every target that uses `dest_var`, `EL` or `FAPPLY` keeps them in range by hypothesis (`termsem_VSUBST`, `RACONV_dbterm`, `INST_CORE_simple_inst`, `find_index_ALL_DISTINCT_EL`, `FUN_FMAP_FAPPLY_FEMPTY_FAPPLY`, …). It stays consistent with HOL4 because pattern-completion values and `FAPPLY` outside the domain (`OUTL (INR _)`) are each one constant in HOL4 too. |
| `CHR n = CHR 0` for n ≥ 256 | Unspecified: the abstraction function of `new_type_definition` (string/stringScript.sml:25-29, 40-45) | No | It is a consistent choice. The targets only apply `CHR` to `w2n` of a `word8`, or to `ORD #"0" + n` with n < 16. |
| `TL [] = []` | **Specified** (list/src/listScript.sml:142-145, `TL_DEF`) | No | Not an over-specification. Baseline is the same. |
| `RESULT (Clash t) = t`, `CLASH (Result t) = t` | **Not free**: equals the `ARB` constant (Pmatch.sml:154,182) | No | It contradicts a HOL4-provable equation, but every use in a target is guarded (see above). |
| `ZIP` truncates | **Specified** (listScript.sml:1784-1790, `ZIP_def`) | No | Not an over-specification. `RACONV_TRANS` and `dbterm_RACONV` also have length hypotheses. |
| `FUN_FMAP f P = FEMPTY` for infinite P | Unspecified (`new_specification`, finite_mapScript.sml:1585) | No | The only target, `FUN_FMAP_FAPPLY_FEMPTY_FAPPLY`, assumes `FINITE s` (miscScript.sml:538). |
| `instance_` default `tmaof i name []` | Unspecified outside its spec (`new_specification`, holSemanticsScript.sml:112-130) | No | Sonnet picks a `tyin` by `choose`. The value does not depend on that choice (this is the HOL4 existence proof), so the spec holds. The default branch is a valid choice for a function meeting the spec, so every HOL4 consequence stays true. |
| `DIV`/`MOD` by 0 as in Lean | **Specified**: `DIV m 0 = 0`, `MOD m 0 = m` (num/theories/arithmeticScript.sml:2335-2339) | No | Same as Lean. |
| `SEG (m+1) k [] = []` (extra, not on your list) | Unspecified (`new_specification`, rich_listScript.sml:276-285) | No | Only `substring` uses `SEG`, and only in range (`off + len ≤ LENGTH s`). |

## Other checks
- **`type_lt` (mutual inductive with `type_llex`) is the same relation as HOL4's.** I proved in sonnet that `type_lt a b ↔ ∀R, rulesH R → R a b`, where `rulesH` is the HOL4 rule set with `LEX mlstring_lt (LLEX R)`. I also proved `LLEX type_lt l1 l2 → type_llex l1 l2`. Both compiled with no `sorry`; the only axioms are `propext`, `Classical.choice` and `Quot.sound`. `term_lt` splits `LEX` into two strictly positive constructors, which is equivalent.
- **`[Inhabited _]` hypotheses** add nothing that HOL4 does not already guarantee. Sonnet has them on `apply_abstract`, `apply_in_rng` and seven `termsem_*` lemmas where baseline has none. Elsewhere sonnet's `Inhabited` stands where baseline has `Nonempty`.
- **Finite maps and sets.** `FMap` is a lookup function with finite support. `FDOM`, `FLOOKUP`, `FUPDATE`, `FUNION`, `FRANGE`, `FEVERY` and `alist_to_fmap` (first entry wins) match HOL4. `FINITE` is "contained in some list", which is equivalent to HOL4's inductive `FINITE`. `PERM` is HOL4's `FILTER` definition word for word. `GSPEC` sets and `setOf ∃` sets are the same sets.
- **Precedence, quantifier scope and free variables.** After normalisation the binder structure is identical, except for vacuous binders noted below.
- **ML-built statements** match each other and `hol4_check.txt`: `subtype_Tyvar`, `subterm_Var`, `subterm_Const`, `type_lt_thm`, `term_lt_thm`, `w2n_lt_256`, `splitlines_nil`, `pair_inj`, `VSUBST_WELLTYPED`, `REV_ASSOCD`.
- **Library definitions in sonnet's Prelude and theory files** were read against HOL4 and match: `merge_tail`, `mergesortN_tail`, `FIELDS`, `HEX`, `UNHEX`, `v2w`, `v2n`, sptree `lookup`/`insert`/`domain`, `TotOrd`, `LLEX`, `SPLITP`, `INST_CORE`, `VSUBST`, `rename_bvars`, `dbterm`, `arities_match`, `proves`, `term_ok`, `theory_ok`, `termsem`, `entails`, and others.
- **Sonnet's `VARIANT_PRIMES` uses `LEAST`.** Baseline uses an epsilon over the minimality spec. The least such n is unique, so they agree.

## Notable form-only differences

| Declaration(s) | Difference | Closer to the HOL4 text |
|---|---|---|
| `mlstring_common_char_prefix` | HOL4 has `∀… (t2:α) (t2:mlstring)`, with t1 and c2 free. Baseline has `(t2 t2 : mlstring)`; sonnet has a single `t2`. The shadowed binder is vacuous. | Baseline (keeps the duplicate binder) |
| `REV_ASSOCD_FILTER`, `dbVFREE_IN_bind` | Unused HOL4 binders (`d`, `b : 'a`): baseline keeps them polymorphic; sonnet drops `d` and makes `b : Nat`. | Baseline |
| `append_thm`, `ALOOKUP_MAP_dest_var`, `swap_ff`, `ff_def` | Sonnet puts all type variables in one type or one universe. Each conjunct is closed separately, or HOL4 has a single universe, so the meaning is the same. | Baseline |
| 9 lemmas (`apply_abstract`, `apply_in_rng`, `termsem_*`) | Sonnet adds `[Inhabited U]`. | Baseline (HOL4 has no such hypothesis) |
| `WELLTYPED_CLAUSES`, `ACONV_eq_orda`, `arities_match_nil`, `arities_match_Tyvar` | `=` on `Prop` versus `↔`. | Sonnet (`⇔` is `=` in HOL4) |
| `termsem_Equal` | Sonnet uses a constant `Equalsem`; baseline inlines the lambda. They are equal by unfolding. | Sonnet (mirrors `^Equalsem`) |
| `FINITE_VFREE_IN_2`, `FINITE_MEM_Var` | `GSPEC` versus `setOf (∃ x ty, p = (x,ty) ∧ …)`. | Baseline (`GSPEC`) |
| About 20 lemmas (`RACONV_SYM`, `ordav_sym`, `termsem_VSUBST`, …) | `match p with (x,y)` versus `p.1`/`p.2` and `Prod.fst`. | Baseline (the HOL4 text uses paired lambdas) |
| `RACONV`, `MAPi_ID`, `FIELDS_next`, `plus_0_I`, `PRIMED_*`, `MEM_LIST_*`, `fresh_union`, `EVERY2_RC_same`, `domain_nat_set_from_list` | Binder order, `.succ` versus `+1`, eta form, `List.append` versus `++`, `∪`/`insert` instances versus `UNION`/`INSERT`, `LIST_REL` versus `EVERY2`. | About equal |

## Counts
- Identical after normalisation: **227**
- Form-only differences: **51**
- Meaning differences: **0**

## Limits
- **How statements were normalised.** I elaborated them with a metaprogram and unfolded aliases (`MEM`, `MAP`, `LENGTH`, `TAKE`, `DROP`, `FST`, `SND`, `strlit`, `tysof`/`tmsof`/`sigof`, `Equalsem`). I then renamed by regex (namespaces, `…0` suffixes, `mtrue`/`true_`, `ml`/`mls`, `Inhabited`→`Nonempty`) and diffed the text. The 51 remaining diffs were judged by hand, not proved equivalent in Lean.
- **Definitions were compared by reading the source** against HOL4, with Lean checks only for `type_lt`, `RESULT`/`CLASH` and `CHR`. Sonnet's `FINITE`, `EVEN` and `v2w` are claimed equivalent to HOL4's from standard facts, without a Lean proof.
- I did not re-audit baseline definitions in full. Where both projects share a reading, a mistake common to both would not show up.
- I only checked that recursive definitions have the HOL4 clause shapes, not that their compiled equations match.
- All scratch files were deleted, and neither project's sources were edited.

