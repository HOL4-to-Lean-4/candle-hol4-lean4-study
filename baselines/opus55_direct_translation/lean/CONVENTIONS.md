# Translation conventions (HOL4 Candle → Lean 4)

Stage 2 (theorem translation) must follow these rules so the statements use the definitions
of stage 1 in the way they were meant.

## 1. Files, namespaces, opens

| HOL4 theory | Lean module | Namespace |
|---|---|---|
| HOL4 library constants (bool, combin, pair, relation, arithmetic, list, rich_list, sorting, mergesort, pred_set, finite_map, alist, string, ASCIInumbers, numposrep, words, bitstring, fcp, sptree, ternaryComparisons, toto) | `CandleLean/Prelude/{Basic,PredSet,List,String,FiniteMap,Words,Sptree}.lean` | `HOL` (sptree functions: `HOL.sptree`) |
| misc | `CandleLean/Misc.lean` | `Candle` |
| mllist | `CandleLean/Mllist.lean` | `Candle` |
| mlstring | `CandleLean/Mlstring.lean` | `Candle` |
| setSpec | `CandleLean/SetSpec.lean` | `Candle` |
| holSyntaxLib | `CandleLean/HolSyntaxLib.lean` | `Candle` |
| holSyntax | `CandleLean/HolSyntax.lean` | `Candle` |
| holSyntaxExtra | `CandleLean/HolSyntaxExtra.lean` | `Candle` |
| holSemantics | `CandleLean/HolSemantics.lean` | `Candle` |
| holSemanticsExtra | `CandleLean/HolSemanticsExtra.lean` (no definitions, see §8) | `Candle` |
| holSoundness | `CandleLean/HolSoundness.lean` (no definitions) | `Candle` |

* Every file has `open HOL Classical` inside `namespace Candle`, and all definitions sit in a
  `noncomputable section`. Theorems for theory X go in the module of X (or a file that
  imports it), inside `namespace Candle`, with `open HOL Classical`.
* Universe-polymorphic HOL type variables are written `{α : Type u}`. The set-theory
  universe `'U` is `{U : Type u}`. Wherever a HOL constant needs an arbitrary element of `U`
  (it mentions `ARB`, `HD`, `empty`, `boolset`, `True`, `False`, `FAPPLY`), it takes the
  instance argument `[Nonempty U]`. Theorems about such constants need `[Nonempty U]` in
  their context. This adds no assumption, because every HOL type is nonempty.
* Helper lemmas that are not HOL4 theorems are in the namespace `Aux` (`HOL.Aux.*`,
  `Candle.Aux.*`). Their names never collide with target names. Do not use them as the
  translations of target theorems.
* The constructors of these types are exported, so you can write them without a prefix:
  `type` (`Tyvar Tyapp`), `term` (`Var Const Comb Abs`), `update` (`ConstSpec TypeDefn NewType
  NewConst NewAxiom`), `result` (`Clash Result`), `dbterm_t` (`dbVar dbBound dbConst dbComb
  dbAbs`), `mlstring` (`implode`), `app_list_ann` (`BigList BigAppend Small`), `ordering`
  (`LESS EQUAL GREATER`), `spt` (`LN LS BN BS`).
  **Not exported:** `app_list` (`app_list.List`, `app_list.Append`, `app_list.Nil`), because
  `List`/`Nil` would clash.
* Name clash: inside `namespace Candle`, `compare` resolves to `Candle.compare` (mlstring
  comparison). In `simp [...]`/`rw [...]` lists and outside the namespace, write
  `Candle.compare` explicitly, because `Ord.compare` may be chosen otherwise.

## 2. Type mappings

| HOL4 | Lean |
|---|---|
| `bool` | `Prop` **everywhere**, also inside data (`bitstring = List Prop`, `neg : Prop`, `b` in `boolean b`, comparison results `R x y` used as values) |
| `T`, `F` | `True`, `False` |
| `num` | `Nat` |
| `int` | `Int` (not used by the definitions) |
| `'a list` | `List α` |
| `'a option`, `SOME`, `NONE` | `Option α`, `some`, `none` |
| `'a # 'b`, `(x,y)`, `FST`, `SND` | `α × β`, `(x, y)`, `.1`, `.2` |
| `'a -> bool` used as a set, `'a set` | `HOL.Set α` (`def Set α := α → Prop`) |
| `('a,'b) fmap` | `HOL.fmap α β` (§5) |
| `char` | `HOL.char` (structure `⟨ord, ord_lt : ord < 256⟩`) |
| `string` | `HOL.string := List char` |
| `mlstring` | `Candle.mlstring` (`inductive mlstring | implode : string → mlstring`) |
| `'a word`, `word8`, `word32` | `BitVec n`, `word8 := BitVec 8`, `word32 := BitVec 32` |
| `dimindex(:'a)` | `dimindex n` (`= n`), `dimword n = 2 ^ n` |
| `ordering` | `HOL.ordering` (`LESS | EQUAL | GREATER`) |
| `'a spt`, `num_map`, `num_set` | `HOL.spt α`, `num_map α`, `num_set` |
| `bitstring` | `bitstring := List Prop` |
| holSyntax `tysig`, `tmsig`, `sig`, `thy` | `abbrev tysig := fmap mlstring Nat`, `tmsig := fmap mlstring type`, `sig := tysig × tmsig`, `thy := sig × Set term` |
| holSemantics `'U tyass`, `tmass`, `tyval`, `tmval`, `interpretation`, `valuation` | `tyass U`, `tmass U`, `tyval U`, `tmval U` (`mlstring × type → U`), `interpretation U := tyass U × tmass U`, `valuation U := tyval U × tmval U` |

Arithmetic: HOL4 `DIV`/`MOD` are Lean `/`/`%`. They agree at 0 (`k DIV 0 = 0`, `k MOD 0 = k`).
`-` on `num` is truncated in both systems. `SUC n` is `n + 1`. `PRE n` is `n - 1`. `MAX`/`MIN`
are `HOL.MAX`/`HOL.MIN` (equal to Lean `max`/`min`). `DIV2 n = n / 2`. `EVEN`/`ODD` are
`HOL.EVEN`/`HOL.ODD` (Prop-valued, recursive).

## 3. Literals and syntax

| HOL4 | Lean |
|---|---|
| `«abc»`, `strlit "abc"`, `implode "abc"` | `mls "abc"` (`= implode (str "abc")`) |
| `"abc"` (HOL string) | `str "abc"` (`: List char`) |
| `#"c"` | `ch 'c'` (only for characters with code < 256) |
| `[a;b;c]` | `[a, b, c]` |
| `h::t`, `l1 ++ l2` | `h :: t`, `l1 ++ l2` |
| `x IN s`, `x ∈ s`, `MEM x l` | `x ∈ s` (Set membership instance), `x ∈ l` (Lean list membership) |
| `set l` / `LIST_TO_SET l` | `LIST_TO_SET l` |
| `{x | P x}` | `setOf (fun x => P x)` |
| `{f x | P x}` | `GSPEC (fun x => (f x, P x))` |
| `{(x,ty) | P x ty}` | `GSPEC (fun (p : α × β) => ((p.1, p.2), P p.1 p.2))`, or `setOf (fun p => P p.1 p.2)` (same set) |
| `{}`, `∅` (pred_set), `UNIV` | `EMPTY` (also `∅`), `UNIV` |
| `s ∪ t`, `s ∩ t`, `s DIFF t`, `x INSERT s`, `s ⊆ t` | `UNION s t`, `INTER s t`, `DIFF s t`, `INSERT x s`, `SUBSET s t` (instances `∪ ∩ \ insert ⊆` exist and unfold to these) |
| `FINITE s`, `INFINITE s`, `IMAGE f s`, `DISJOINT s t` | same names |
| `f o g` | `f ∘ g` |
| `I`, `K`, `C`, `UNCURRY` | `HOL.I`, `HOL.K`, `HOL.C`, `HOL.UNCURRY` (or Lean lambdas) |
| `(a =+ b) f` | `UPDATE a b f` |
| `f =++ l` | `UPDATE_LIST f l` |
| `(f ## g) p` | `PAIR_MAP f g p` |
| `R1 LEX R2` | `LEX R1 R2` |
| `@x. P x` | `Classical.epsilon (fun x => P x)` (needs `Nonempty`) |
| `?!x. P x` | `EXISTS_UNIQUE (fun x => P x)` |
| `ARB` | `HOL.ARB` |
| `if b then x else y` | `if b then x else y` (Classical decidability) |
| `case`/pattern matching | `match` |
| `R^*` / `RTC R` | `RTC R` (`HOL.RTC`, inductive: `refl x`, `step x y z`) |
| `RC R` | `RC R` |

## 4. Name table (HOL4 name → Lean name, only names that differ or need explanation)

Library constants:

| HOL4 | Lean | Remark |
|---|---|---|
| `MAP`, `LENGTH`, `APPEND`, `FLAT`, `REVERSE`, `FOLDR`, `FOLDL`, `TAKE`, `DROP`, `CONS`, `NIL` | `List.map`, `List.length`, `++`, `List.flatten`, `List.reverse`, `List.foldr`, `List.foldl`, `List.take`, `List.drop`, `::`, `[]` | Lean core. Argument order is Lean's (`l.map f`, `List.foldr f e l`, `l.take n`, `l.drop n`) |
| `MEM x l` | `x ∈ l` | |
| `HD`, `TL`, `EL`, `NULL`, `LAST`, `FRONT`, `FILTER`, `EVERY`, `EXISTS`, `ALL_DISTINCT`, `SNOC`, `GENLIST`, `REV`, `ZIP`, `SUM`, `PAD_LEFT`, `PAD_RIGHT`, `LIST_REL`, `EVERY2`, `LLEX`, `isPREFIX`, `OPT_MMAP`, `MAPi`, `SPLITP`, `SEG`, `MAX_LIST`, `PERM`, `SORTED` | same names in `HOL` | `ZIP` takes a pair `ZIP (l1, l2)` as in HOL4. `EL n l`, `SEG m k l` use HOL4 argument order |
| `sorting$PERM`, `sorting$SORTED` | `HOL.PERM`, `HOL.SORTED` | |
| `mergesort$sort2_tail`, `sort3_tail`, `merge_tail`, `mergesortN_tail`, `mergesort_tail` | same names | |
| `OPTION_MAP`, `OPTION_BIND` | `Option.map`, `Option.bind` | |
| `FEMPTY`, `FUPDATE`, `f ' x` (`FAPPLY`), `FDOM`, `FLOOKUP`, `FEVERY`, `FRANGE`, `FUN_FMAP`, `ALOOKUP`, `alist_to_fmap` | same names | `f |+ (k,v)` is `FUPDATE f (k, v)` |
| `ORD`, `CHR`, `char_lt`, `char_le`, `string_lt`, `string_le`, `FIELDS` | same names | |
| `l2n`, `n2l`, `s2n`, `n2s`, `HEX`, `UNHEX`, `num_from_hex_string`, `num_to_hex_string` | same names | |
| `n2w`, `w2n`, `FCP`, `v2w`, `zero_extend`, `fixwidth`, `shiftr`, `field`, `testbit` | same names | `n2w k : BitVec n` = `BitVec.ofNat n k`; `w2n` = `.toNat`; `FCP f` takes a `Nat → Prop` |
| `sptree$lookup`, `insert`, `domain` | `HOL.sptree.lookup`, `HOL.sptree.insert`, `HOL.sptree.domain` | Use the full name: `insert`/`domain` clash with other names |
| `transitive`, `reflexive`, `irreflexive`, `symmetric`, `antisymmetric`, `trichotomous`, `StrongOrder`, `StrongLinearOrder`, `Order`, `LinearOrder`, `inv_image`, `RTC`, `RC` | same names | |
| `invert_comparison`, `cpn`, `comp`, `TotOrd`, `TO_of_LinearOrder` | same names | |

CakeML/Candle constants:

| HOL4 | Lean | Remark |
|---|---|---|
| `Bool` (overload) | `BoolTy` | Lean's `Bool` cannot be shadowed safely |
| `Fun s t`, `Equal ty`, `is_instance` | `Fun s t`, `Equal ty`, `is_instance ty0 ty` | reducible defs that unfold to the overloaded terms |
| `instance` | `instance_` | `instance` is a Lean keyword |
| `true`, `false` (setSpec), `True`, `False` (overloads `true ^mem`) | `true_ mem`, `false_ mem` | |
| holSyntaxExtra type `dbterm` | `dbterm_t` (the function `db` is `db`, `dbterm` (the function) is `dbterm`) | type and function had the same name |
| `tysof sig`, `tmsof sig` (on `sig`) | `tysof s`, `tmsof s` | `= s.1`, `s.2` |
| `sigof thy`, `axsof thy` (on `thy`) | `sigof t`, `axsof t` | `= t.1`, `t.2` |
| `tysof thy`, `tmsof thy` (overload `tysof o sigof`) | `thy_tysof t`, `thy_tmsof t` | equal to `tysof (sigof t)` / `tmsof (sigof t)` by `rfl` |
| `tysof ctxt`, `tmsof ctxt`, `sigof ctxt`, `axsof ctxt`, `thyof ctxt` (on `update list`) | `ctxt_tysof ctxt`, `ctxt_tmsof ctxt`, `ctxt_sigof ctxt`, `ctxt_axsof ctxt`, `thyof ctxt` | `type_list`, `const_list`, `axexts`, `conexts`, `axioms_of_upd`, `axiom_list` keep their names |
| `s === t` | `equation s t` | |
| `tm has_type ty` | `has_type tm ty` | |
| `(thy,h) |- c` | `proves (thy, h) c` | |
| `upd updates ctxt` | `updates upd ctxt` | |
| `ty1 subtype ty2` | `subtype ty1 ty2` (`= RTC subtype1`) | |
| `subterm` | `subterm` (`= RTC subterm1`) | |
| `x <: y` | `mem x y` | |
| `x ' y` (setSpec) | `apply mem x y` | |
| `x suchthat P` | `sub mem x P` | |
| `Pow x`, `x + y` (upair), `∅` (setSpec), `Unit x`, `One`, `Two`, `boolset`, `(x,y)` (pair, in set contexts), `x ∪ y` (binary_union), `x × y` (`CROSS`, product), `Relspace`, `Funspace`, `Boolean b`, `Abstract`, `Holds` | `power mem x`, `upair mem x y`, `empty mem`, `unit mem x`, `one mem`, `two mem`, `boolset mem` (`= two mem`), `pair mem x y`, `binary_union mem x y`, `product mem x y`, `relspace mem x y`, `funspace mem x y`, `boolean mem b`, `abstract mem dom rng f` | Every `^mem` overload is the `0`-free constant applied to `mem` first |
| `is_type_assignment`, `is_type_valuation`, `is_term_assignment`, `is_term_valuation`, `is_valuation`, `termsem`, `is_interpretation`, `is_std_type_assignment`, `is_std_interpretation`, `interprets`, `models`, `satisfies`, `|=`, `is_structure` | `is_type_assignment0 mem`, `is_type_valuation0 mem`, `is_term_assignment0 mem`, `is_term_valuation0 mem`, `is_valuation0 mem`, `termsem0 mem`, `is_interpretation0 mem`, `is_std_type_assignment0 mem`, `is_std_interpretation0 mem`, `interprets0 mem`, `models0 mem`, `satisfies0 mem`, `entails0 mem`, `is_structure0 mem` | overloads expanded |
| `i satisfies (sig,h,c)` | `satisfies0 mem i (sig, h, c)` | one triple argument |
| `(thy,h) |= c` | `entails0 mem (thy, h) c` | one pair argument |
| `i models thy` | `models0 mem i thy` | |
| `γ interprets name on vs as f` | `interprets0 mem γ name vs f` | |
| `inhabited s` | `inhabited mem s` (`= ∃ x, mem x s`) | |
| `tyaof`, `tmaof`, `tyvof`, `tmvof` | same names (`= .1`, `.2`) | |
| `Equalsem` (holSemanticsExtra overload) | no constant; see §8 | |
| `s1 ^ s2` (mlstring) | `strcat s1 s2` | |
| `toString c` | `chr_to_str c` | |
| `s1 < s2` on mlstrings | `mlstring_lt s1 s2` | `mlstring_le/gt/ge` are not translated (not needed) |
| `flip_ord` | `flip_ord` (`= invert_comparison`, reducible) | |
| `mlstring$compare` | `Candle.compare` | |
| `strlit` | `strlit` (reducible, `= implode`) | prefer `implode` in statements |
| `mllist$sort` | `Candle.sort` (`= mergesort_tail`) | |
| `misc$append` (app_list) | `Candle.append` | |
| `LLOOKUP` (misc overload) | not translated (not used by targets) | |

Every other CakeML constant has the same name in `Candle`.

## 5. Encodings and edge cases

* **Unspecified values.** `ARB` is `Classical.epsilon (fun _ => False)`. HOL4 leaves these
  values unspecified, and Lean uses the same fixed but unknown elements:
  `HD []`, `LAST []`, `EL n l` for `n ≥ LENGTH l` (via `HD []`/`TL []`), `CHR n` for `n ≥ 256`
  (`ARB n`), `FAPPLY f x` for `x ∉ FDOM f` (one `ARB`, the same for all such `x`, as in
  HOL4's `FAPPLY` = `OUTL` of a fixed `INR`), `RESULT (Clash _)`, `CLASH (Result _)`, the
  missing cases that TFL fills with `ARB` (for example `termsem0 ... (Abs (Const ..) ..)`).
  Do not prove any property of these values that HOL4 cannot prove.
* **`new_specification` constants** (`SEG`, `FUN_FMAP`, `VARIANT_PRIMES`, `fresh`,
  `instance_`) are `Classical.epsilon` of their specification `*_spec`. Their HOL4
  defining theorems are proved under the HOL4 names: `HOL.SEG_def`, `HOL.FUN_FMAP_DEF`,
  `Candle.VARIANT_PRIMES_def`, `Candle.fresh_def`, `Candle.instance_def` (each one states
  `<name>_spec <name>`, so use `(X_def) ...` to get the clauses).
* **Hilbert-choice definitions** (`sub`, `power`, `union`, `upair`, `apply`) use
  `Classical.epsilon` with an explicit inhabitant, so they need no `Nonempty`.
* **Inductive relations** are Lean `inductive` predicates with HOL4 rule names as
  constructors. Implicit arguments are the free variables of the rule:
  `has_type.{Var,Const,Comb,Abs}`, `RACONV.{Var,Const,Comb,Abs}` (`RACONV env (t1, t2)`,
  pair argument as in HOL4), `proves.{ABS,ASSUME,BETA,DEDUCT_ANTISYM,EQ_MP,INST,INST_TYPE,
  MK_COMB,REFL,axioms}`, `updates.{new_axiom,new_constant,new_specification,new_type,
  new_type_definition}`, `subtype1.rule`, `subterm1.{comb_left,comb_right,abs_body,abs_var}`,
  `RTC.{refl,step}`. The `_cases`/`_ind`/`_rules` theorems are Lean's `.casesOn`/`.rec`/
  constructors. Use the `cases`/`induction` tactics.
* **`type_lt` and `term_lt`** are not strictly positive (they use `LLEX`/`LEX`). They are
  defined as the least relation closed under the rules (impredicative `∀ R, rules R → R a b`),
  which is exactly what HOL4's `Inductive` constructs. You must prove their rules/induction
  principle by unfolding.
* **Recursive functions** are Lean structural or well-founded recursion. Their equation
  lemmas (`f.eq_1`, `f.eq_def`, `simp [f]`, `unfold f`) have the HOL4 clause shapes. For
  nested recursion through lists (`TYPE_SUBST`, `type_ok`, `tyvars`, `typesem`, ...), the
  equations use `List.map`/`EVERY`/`List.foldr` over the original list (no `attach`).
* **Pattern order.** Where HOL4 clauses overlap, the Lean `match` lists them in the HOL4
  order. A wildcard case is written out where TFL makes a fallback.
* **fmap**: `structure fmap α β where rep : α → Option β; finite_support : ∃ l, ∀ a, rep a ≠
  none → a ∈ l`. Two fmaps with the same `rep` are equal (proof irrelevance). `FDOM f =
  {x | f.rep x ≠ none}`; `FLOOKUP f x = if x ∈ FDOM f then some (f ' x) else none` (it equals
  `f.rep x`); `FUPDATE f (k, v)` overwrites `k`; `alist_to_fmap` = `FOLDR (λ(k,v) f. f |+ (k,v))
  FEMPTY` (first entry wins).
* **char**: a natural number `< 256`. `CHR n` for `n < 256` is that character. `ch 'c'`
  reduces the Unicode code point modulo 256, so use it only for ASCII.
* **Strings.** `HOL.string` is `List char` (so `STRCAT`, `STRLEN` etc. are `++`, `length`).
  `explode (implode s) = s`. `strlen`, `strsub`, `substring`, `concat`, `strcat` follow
  mlstringScript exactly (via `explode`).
* **Words**: `word n` is `BitVec n`. `v2w` uses HOL4's `FCP (λi. testbit i v)`. Bit `i`
  is set iff `testbit i v` (the most significant bit comes first in the list).
* **Sets** are predicates: `HOL.Set α := α → Prop`. `x ∈ s` is `s x` (`Aux.mem_def`). Use
  `funext`/`propext` for set extensionality. `FINITE` is the HOL4 impredicative definition
  (the least family closed under `EMPTY` and `INSERT`).
* **Booleans in data.** `bool`-valued fields and results are `Prop`. HOL4 `b1 = b2` on
  booleans is `b1 = b2 : Prop` (equivalent to `↔` by `propext`). `R x y ≠ neg` in sorting
  functions is a Prop disequality.
* **`is_subseq`** (misc) follows the HOL4 definition exactly: `is_subseq ys xs` holds when
  `xs` is a subsequence of `ys`.

## 6. Overloaded HOL4 equations that have a different Lean form

* `TYPE_SUBST` has the two equations `TYPE_SUBST.eq_1` (Tyvar) and `TYPE_SUBST.eq_2`
  (`TYPE_SUBST i (Tyapp s tys) = Tyapp s (tys.map (TYPE_SUBST i))`). HOL4's third clause
  `TYPE_SUBST i (Fun ty1 ty2) = Fun (TYPE_SUBST i ty1) (TYPE_SUBST i ty2)` is an instance of
  the second (`Fun` is `Tyapp «fun» [_, _]`). It is not a separate equation lemma, but
  `simp [TYPE_SUBST]` proves it.
* `termsem0` has 7 equations: the four HOL4 clauses and the three `ARB` completion cases.
* `mergesortN_tail` has the HOL4 clauses. The last clause pattern is `n + 4` (HOL4 general
  case `n` after 0..3).

## 7. Things not translated (not needed by the targets)

`fresh_term`, `vfree_in`, `variant`, `subtract`, `insert`, `itlist`, `union`, `frees`,
`rename`, the `ConstDef` overload (holSyntaxExtra), `extends`, `LLOOKUP`, `mlstring_le/gt/ge`,
`holds`/`tuple`/`bigcross`/`is_model` (setSpec), the mlstring functions that the targets do
not use. Before you use any of them in stage 2, add the translation first.

## 8. holSemanticsExtra `Equalsem`

`Equalsem` is an ML value in holSemanticsExtraScript, not a constant. It is the last argument
of `interprets` in `is_std_interpretation_def`:
`λl. Abstract (HD l) (Funspace (HD l) boolset) (λx. Abstract (HD l) boolset (λy. Boolean (x = y)))`.
A statement that contains `^Equalsem` must contain this term, written in Lean as:

```lean
(fun l => abstract mem (HD l) (funspace mem (HD l) (boolset mem))
  (fun x => abstract mem (HD l) (boolset mem) (fun y => boolean mem (x = y))))
```
