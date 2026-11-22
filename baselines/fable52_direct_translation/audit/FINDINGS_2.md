# FINDINGS_2: setSpec, holSyntaxLib, holSyntax, holSemantics, holSemanticsExtra, holSoundness

There are 10 entries, all `note`. Defects: 0. Suspects: 0. No entry changes the meaning of any target, and none makes a target false or trivially true. Fix for each: none.

- **N1: `type_lt` and `term_lt` (`HolSyntax.lean:178`, `:205`; `holSyntaxScript.sml:113`, `:120`).**
  - Lean defines each as the intersection of all relations closed under the rules (`∀R'. rules R' → R' a0 a1`). That is exactly the definition HOL4 `Inductive` makes.
  - The rules match one for one: `LEX mlstring_lt (LLEX type_lt')`, and `term_lt` uses the defined `type_lt` in its Var/Const rules. `LEX` and `LLEX` match the HOL4 library.
  - Lean check: `type_lt (Tyvar a) (Tyapp b [])` holds and `type_lt (Tyapp a []) (Tyvar b)` does not.
  - Effect on proofs: they need case lemmas, not `inductive` recursors.
- **N2: `type_ok` (`HolSyntax.lean:690`; `:426`).** Lean writes `∀ a, MEM a args → …` in place of `EVERY (type_ok tysig) args`. The two are equivalent, and `type_ok_def` (`HolSyntax.lean:711`) proves the HOL4 equations.
- **N3: `termsem0` on `Abs` of a non-variable (`HolSemantics.lean:188`; `holSemanticsScript.sml:134`).** It is `ARB`, which is what HOL4's pattern completion gives. The other clauses match exactly.
- **N4: unspecified constants made with `select`.**
  - These are `dest_var`, `RESULT`, `CLASH`, `VARIANT_PRIMES`, `instance'` and `HD` (used in `is_std_interpretation0` and `Equalsem`).
  - Each is "some function that satisfies the HOL4 specification". I checked each specification term by term, including the quantifier order of `instance'` (`tmsig i name ty ty0 tyin`).
  - Values such as `HD []` or `RESULT (Clash _)` are just as unspecified in HOL4.
- **N5: overloads in setSpec.**
  - Some HOL4 texts would also type-check with another overload:
    - `a + b` as numbers (`upair_inj`);
    - `(a,b)` as a HOL pair (`pair_inj`, `abstract_def`);
    - `∅` and `∪` as `pred_set` constants (`mem_one`, `mem_two`, `mem_binary_union`, `product`).
  - HOL4 prefers the most recent overload, which is the set-theory one, and Lean uses the set-theory constant everywhere. The HOL4 proofs confirm this reading:
    - `upair_inj` is false for numeric `+`.
    - `mem_one` is proved through `one_def`/`mem_unit`.
    - `apply_abstract`'s premise `f x <: t` forces `f : 'U → 'U`.
- **N6: the comma, `'`, `True` and `False` in holSemantics, holSemanticsExtra and holSoundness (setSpec is an ancestor).**
  - Every `(…,…)` is forced to be a HOL pair by the types around it:
    - `tmvof v (x,ty)` and `σ (v,ty)`;
    - `(sig,h,c)` and `(thy,h) |= …`;
    - the valuation pairs;
    - `(s,s')` going into `dest_var ##`;
    - the `ALPHAVARS` argument.
  - `t1 ' t2` in `termsem_def` must be the set-theory `apply`, because the finite-map reading fails the occurs check.
  - `True` and `False` are `true0 mem` and `false0 mem`.
- **N7: text that HOL4 builds with ML code.**
  - **`Equalsem`** (`HolSemanticsExtra.lean:32`; `holSemanticsExtraScript.sml:139`): taking `rhs`, then the last conjunct, then the last argument of `is_std_interpretation_def` gives the `λl. Abstract (HD l) …` term. The Lean `abbrev` is exactly that term, applied to the one-element list.
  - **`VARIANT_PRIMES_def`** (`HolSyntax.lean:395`; `holSyntaxScript.sml:281`): `HO_MATCH_MP LEAST_EXISTS`, then `SIMP_RULE` removing `¬¬`, then `GENL [t,x,ty]` and Skolemisation, give exactly the Lean specification.
- **N8: type variables.**
  - `REV_ASSOCD_thm` gives its two conjuncts independent type variables. HOL4 types the bound variables of the two conjuncts independently too, so the generality is the same.
  - `REV_ASSOCD_FILTER` binds `d` without using it, and Lean gives it its own type `γ`.
  - The `[Nonempty _]` added on every type variable is harmless, because every HOL4 type is non-empty.
- **N9: free variables become theorem arguments.**
  - Examples: `ilist` and `tyin` in `INST_correct`/`INST_TYPE_correct`, `x ty t` in `PRIMED_NAME_EXISTS`, and `mem` in the statements without `is_set_theory`.
  - Statements that lack `is_set_theory` in HOL4 also lack it in Lean, for example `ASSUME_correct`, which is trivially valid in both.
- **N10: termination arguments.** `orda`, `term_union`, `INST_CORE`, `type_ok` and `typesem` use different termination measures from HOL4. The equations are the same, and so is the first-match order of overlapping patterns (`orda`'s `case`, `term_union`'s `(l1,[])` row, `domain`/`codomain`). Proofs need the equation lemmas, not `rfl`.

## Summary table

| id | Lean | HOL4 | declaration | class | changes a target? |
|---|---|---|---|---|---|
| N1 | HolSyntax.lean:178, 205 | holSyntaxScript.sml:113, 120 | `type_lt`, `term_lt` | note | no |
| N2 | HolSyntax.lean:690 | holSyntaxScript.sml:426 | `type_ok` | note | no |
| N3 | HolSemantics.lean:188 | holSemanticsScript.sml:134 | `termsem0` (Abs of non-variable) | note | no |
| N4 | HolSyntax.lean:86, 395; HolSyntaxLib.lean:69, 82; HolSemantics.lean:154 | various | `dest_var`, `VARIANT_PRIMES`, `RESULT`, `CLASH`, `instance'`, `HD` | note | no |
| N5 | SetSpec.lean:163–399 | setSpecScript.sml:174–371 | overloads `+`, `,`, `∅`, `∪` | note | no |
| N6 | HolSemantics*, HolSoundness | holSemantics*, holSoundness | overloads `,`, `'`, `True` | note | no |
| N7 | HolSemanticsExtra.lean:32; HolSyntax.lean:395 | holSemanticsExtraScript.sml:139; holSyntaxScript.sml:281 | `Equalsem`, `VARIANT_PRIMES_def` | note | no |
| N8 | HolSyntaxLib.lean:155, 188 | holSyntaxLibScript.sml:34, 59 | type variables, unused binder | note | no |
| N9 | several | several | free variables as arguments | note | no |
| N10 | HolSyntax.lean:274, 305, 567 | holSyntaxScript.sml:155, 185, 351 | termination measures | note | no |

## Checked and found faithful

- **setSpec:** all 25 definitions and all 28 target statements, including the precedence of `⇔`, `=`, `∧`, `<:`, `suchthat` and `'`.
- **holSyntaxLib:** all definitions and all 18 target statements.
- **holSyntax:** all definitions and all 7 target statements. Points checked:
  - `VSUBST`;
  - `INST_CORE`: `[Var x' ty,Var x ty]` is a one-element list of a pair;
  - `===`: right-associative, and tighter than `|-` and `=`;
  - all 10 `proves` rules;
  - the 5 `updates` rules, where `ctxt : update list` selects the context overloads;
  - `conexts_of_upd` and `consts_of_upd`.
- **holSemantics:** every definition.
- **holSemanticsExtra:** `Equalsem` and all 16 target statements. In `termsem_simple_subst` and `termsem_VSUBST`, the precedence of `=++` (infixl 500), `##` and `o` is settled by parentheses.
- **holSoundness:** all 11 target statements.
- **Constants from other theories that my targets use:** `bv_names`, `simple_subst`, `simple_inst`, `UPDATE_LIST`, and the `mlstring` functions `implode`, `explode`, `strsub`, `strlen`, `compare`, `compare_aux`, `mlstring_lt`.
- **Prelude constants this scope uses,** checked against the HOL4 library sources:
  - `select`, `ARB`, `EXISTS_UNIQUE`, `K`, `C`, `UPDATE`;
  - `FST`, `SND`, `UNCURRY`, `PAIR_MAP`, `LEX`;
  - `OUTL`, `ISL`, `TO_of_LinearOrder`;
  - `Set` and `∈`, `setOf`, `EMPTY`, `UNIV`, `UNION`, `INTER`, `INSERT`, `DISJOINT`, `IMAGE`, `FINITE`;
  - the list functions `NULL`, `HD`, `TL`, `EL`, `MAP`, `LENGTH`, `APPEND`, `FILTER`, `FOLDR`, `FOLDL`, `EVERY`, `EXISTS`, `MEM`, `LIST_TO_SET`, `REVERSE`, `ALL_DISTINCT`, `GENLIST`, `SNOC`, `LLEX`, `PERM`, `SORTED`, `ALOOKUP`;
  - `char`, `ORD`, `CHR`, `char_lt`, `string_lt`;
  - the finite-map functions `is_fmap`, `fmap`, `FEMPTY`, `FUPDATE`, `FAPPLY`, `FDOM`, `FLOOKUP`, `FEVERY`, `FRANGE`, `alist_to_fmap`.
- **Not applicable in this scope:** division and modulus, words, `int`. `mlstring` and `char` derive `DecidableEq`, but it only decides Prop equality, so it changes nothing.

## Uncertainty

N5 relies on HOL4 choosing the most recent overload when two readings type-check. The script's proofs confirm that choice for `upair_inj`, `mem_one` and `abstract`/`apply_abstract`. For `pair_inj` the HOL4 proof alone would not decide it. The set-theory reading is the one that later uses (`apply_abstract`) need, and it is the stronger statement.