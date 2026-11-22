# Opus 5.5 vs Fable 5.2: per-finding comparison

One Claude Opus 5.5 agent compared the two translations after both audits (22 Nov 2026,
07:54-08:28 UTC). It dumped the elaborated binders, statements, definition
equations and inductive rules of both projects with Lean metaprograms, normalised and diffed them,
and tested suspected differences in Lean. Its report follows, lightly trimmed; F = Fable, O = Opus,
paths relative to `lean/CandleLean/`. The orchestrator re-checked the two type-signature rows and
`mlstring_common_char_prefix` against the HOL4 scripts.

**Bottom line.** No target statement or definition differs in meaning between the two
translations. Where they differ in form, Fable is closer to the HOL4 text in 8 places and Opus in 2.

## Fable findings (27 notes) against Opus

"X-closer" means the two are equivalent and X follows the HOL4 text more literally.

| id | declaration | Fable | Opus | verdict |
|---|---|---|---|---|
| F1-N1 | HD, LAST, SEG, CHR, OUTL, FUN_FMAP | `select` of the HOL specification | HD/LAST pattern-match with `[] => ARB`; SEG/FUN_FMAP `epsilon` of the same spec; `CHR n = if n<256 then ⟨n,_⟩ else (ARB:Nat→char) n`; no OUTL | Fable-closer. HOL4 defines HD/LAST by `Prim_rec`, so `HD []` is unspecified; in Opus `HD [] = ARB` is provable. CHR equivalent. No target affected. |
| F1-N2 | DIV, MOD, `-` | Lean `/ % -` | same | same |
| F1-N3 | bool as `Prop` | yes | yes | same |
| F1-N4 | merge_tail, mergesortN_tail | Mergesort:42,69 | List:286,315 | same (identical equations) |
| F1-N5 | char, string, mlstring, strlit | `char{val,isLt}`; `chr!`/`str!`/`ml!` | `char{ord,ord_lt}`; `ch`/`str`/`mls` | differs-equivalent |
| F1-N6 | word, n2w, v2w | BitVec; `v2w` via `FCP_value` | BitVec; `v2w` via `FCP` | same |
| F1-N7 | fmap | `α → β ⊕ Unit` with `is_fmap`; `FAPPLY = OUTL` | `α → Option β` plus finite support; off-domain `FAPPLY` is `ARB` | Fable-closer; both one value per type off the domain |
| F1-N8 | Set, FINITE, PERMUTES, LIST_TO_SET, MEM | `LIST_TO_SET l = (· ∈ l)` | `LIST_TO_SET` recursive | same |
| F1-N9 | type variables, `[Nonempty]`; `append_thm` | 3 type variables; `Nonempty` on every type variable | 3 type variables; `Nonempty` only where needed; `Type u` | differs-equivalent |
| F1-N10 | mlstring_common_char_prefix | `(t2 t2 : mlstring)` (Mlstring:309) | same binders (Mlstring:220) | same; both type the shadowed outer `t2` as `mlstring` where HOL4 infers `'a` |
| F1-N11 | `^` / strcat_assoc | Mlstring:281 | Mlstring:196 | same |
| F2-N1 | type_lt, term_lt | HolSyntax:178,205 | HolSyntax:169,196 | same (identical) |
| F2-N2 | type_ok | `∀ a, MEM a args → …` | `EVERY (type_ok tysig) args` | Opus-closer |
| F2-N3 | termsem0 on Abs of a non-variable | one wildcard `ARB` clause | three explicit `ARB` clauses | same value |
| F2-N4 | dest_var, RESULT, CLASH, VARIANT_PRIMES, instance, HD | all `select` of the spec | dest_var/RESULT/CLASH/HD by `ARB` completion; VARIANT_PRIMES/instance `epsilon` of the same spec | Fable-closer for the `ARB` group, same for the rest |
| F2-N5 | setSpec overloads | set-theory readings | set-theory readings | same |
| F2-N6 | `,`, `'`, `True` in the semantics | HOL pair; `apply`; `true0` | same (`true_`) | same |
| F2-N7 | Equalsem; VARIANT_PRIMES_def | named abbreviation | term inline in `termsem_Equal` | differs-equivalent |
| F2-N8 | REV_ASSOCD_thm, REV_ASSOCD_FILTER | 4 independent type variables; `d : γ` | 2 type variables shared by both conjuncts; `d : γ` | Fable-closer for REV_ASSOCD_thm (HOL4 infers 4); same for REV_ASSOCD_FILTER |
| F2-N9 | free variables become parameters | yes | yes | same |
| F2-N10 | termination measures | WF recursion | WF recursion | same |
| F3-N1 | VSUBST_WELLTYPED; dbVFREE_IN_bind | `(ty : α)`; `b : α` | `(ty : type)`; `b : α` | Fable-closer for VSUBST_WELLTYPED (HOL4 gives `'a`); same for dbVFREE_IN_bind |
| F3-N2 | 15 statements with free variables | parameters | parameters | same |
| F3-N3 | subtype_Tyvar, subterm_Var, subterm_Const, type_lt_thm, term_lt_thm | binder names `_0 _1 …` | `a b …` | same |
| F3-N4 | type_lt / term_lt | | | same |
| F3-N5 | dest_var, RESULT, fresh | `select` of the spec | dest_var/RESULT by `ARB`; `fresh` is `epsilon fresh_spec` | Fable-closer for dest_var/RESULT; same for `fresh` |
| F3-N6 | arities_match | HolSyntaxExtra:284 | HolSyntaxExtra:306 | same (identical) |

Count: same 17, differs-equivalent 3, Fable-closer 6, Opus-closer 1, semantic 0.

## Opus findings not covered above

14 of the 22 Opus notes are the same topics as rows above. The other 8, plus 2 points neither audit
raised:

| id | topic | Fable | Opus | verdict |
|---|---|---|---|---|
| O1-N2 | character literals | `chr!` checks code < 256 at elaboration | `ch c` takes code mod 256 | differs-equivalent (only ASCII used) |
| O1-N8 | WF definitions, ZIP | List:109 | List:117 | same |
| O2-N1 | `[Nonempty U]` on setSpec constants | on every constant | only where needed | differs-equivalent |
| O2-N2 | sub, power, union, upair, apply | `select` with `[Nonempty U]` | `epsilon` with explicit witness | differs-equivalent |
| O2-N5 | TYPE_SUBST Fun clause | | | same |
| O2-N6 | renames | `true0`, `Bool'`, `instance'`, `dbterm_ty`, `tysof_ctxt` | `true_`, `BoolTy`, `instance_`, `dbterm_t`, `ctxt_tysof`, `thy_tysof` | differs-equivalent |
| O2-N10 | ordav `⇔` | | | same |
| O3-N3 | RACONV_thm, rename_bvars lets, arities_match | | | same |
| new | bool `=` in merge_tail_MEM, arities_match_nil, arities_match_Tyvar, MEM_FOLDR_INORDER_INSERT, MAP_EQ_ID | `↔` | Prop `=`, as the HOL text | Opus-closer (textually); equivalent |
| new | binders of inductive rules | explicit | implicit; order differs in DEDUCT_ANTISYM, EQ_MP, MK_COMB | differs-equivalent |

Count: same 4, differs-equivalent 5, Opus-closer 1, semantic 0.

## Type signatures of the 278 targets

The only instance binders in either translation are `[Nonempty _]`; no `DecidableEq`, `BEq` or
`Inhabited`. Fable puts `Nonempty` on every type variable (122 instances on the 102 targets with
type variables). Opus puts it on 26 targets that need it. Every HOL type is non-empty, and no Opus
statement without `Nonempty` changes meaning at an empty type (all ∃ binders over type variables
checked).

Signature differences between the two translations:

| target | Fable | Opus | HOL4 | matches HOL4 |
|---|---|---|---|---|
| VSUBST_WELLTYPED | `{α} [Nonempty α] … (ty : α)` (HolSyntaxExtra:962) | `(ty : type)` (HolSyntaxExtra:988) | holSyntaxExtraScript:1067: the outer `ty` is shadowed by `∃x ty` and unused, so `'a` | Fable (equivalent; proved in Lean) |
| REV_ASSOCD_thm | `{α β γ δ}`, conjuncts independent (HolSyntaxLib:155) | `{α β}` shared by both conjuncts (HolSyntaxLib:180) | holSyntaxLibScript:34: 4 independent type variables | Fable (equivalent) |

Same in both, but different from HOL4: `mlstring_common_char_prefix` (HOL mlstringScript:207,
`∀c1 s1 s2 t2 t2.`): the outer `t2` is unused, so HOL4 gives it type `'a`; both translations type
it `mlstring`. Non-semantic. This is the only binder-type deviation from HOL4 found in the Fable
translation, so it is a candidate for the "minor type-signature discrepancy (non-semantic)" that a
Gemini review reported in Fable's translation (the declaration was not named to us).

## pair_inj

Both use the set-theory pair: `pair mem a b = pair mem c d ↔ a = c ∧ b = d` (Fable SetSpec:389,
Opus SetSpec:354). Both also agree on `upair_inj`, `mem_product` and `apply_abstract`. HOL4 prefers
the newest overload, and later proofs (setSpecScript:348, :359) rewrite with `pair_inj` in a way that
only works for the set-theory pair.

## Differences in meaning

None found. 245 of 278 statements are textually identical after normalisation; the other 33 differ
only in `UNCURRY` vs projections, `match` vs `.1`/`.2`, `∪` vs `UNION`, literal form, set-builder
encoding, binder order or names, and the two type-variable rows above. 327 of 482 shared
definitions have identical unfolding equations; the rest differ only in encoding (`select` vs `ARB`
completion or `epsilon`, the fmap representation, pair matching vs projections, `∀ MEM` vs `EVERY`).
Inductive rules agree up to implicit binders.

One provability difference that affects no target: Opus fixes some HOL-unspecified values to `ARB`
(`HD []`, `LAST []`, `dest_var` of a non-variable, `RESULT (Clash _)`, `CLASH (Result _)`), so
`HD [] = ARB` is provable in Opus but not in Fable or HOL4. This is one model of the HOL4
specification, so every HOL4 theorem stays true.
