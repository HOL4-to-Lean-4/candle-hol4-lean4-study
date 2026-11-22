# Conventions for the Lean translation of the Candle soundness development

These are the rules a stage-2 statement writer needs. Read this file before you
write any statement. Every HOL4 definition in the Lean files has a
`/- HOL4: ... -/` comment above it with the original text.

## 1. Modules, imports, namespaces, `open`

| HOL4 theory | Lean module | imports (HOL4 `Ancestors`) |
|---|---|---|
| HOL4 library constants | `CandleLean/Prelude/{Basic,Set,List,String,Words,FiniteMap,Sptree,ASCIInumbers,Mergesort}.lean` | Lean core + each other |
| `misc` | `CandleLean/Misc.lean` | Prelude (except Mergesort) |
| `mllist` | `CandleLean/Mllist.lean` | Misc, Prelude.Mergesort |
| `mlstring` | `CandleLean/Mlstring.lean` | Misc, Mllist |
| `setSpec` | `CandleLean/SetSpec.lean` | Misc |
| `holSyntaxLib` | `CandleLean/HolSyntaxLib.lean` | Mlstring |
| `holSyntax` | `CandleLean/HolSyntax.lean` | HolSyntaxLib |
| `holSyntaxExtra` | `CandleLean/HolSyntaxExtra.lean` | HolSyntax |
| `holSemantics` | `CandleLean/HolSemantics.lean` | HolSyntax, HolSyntaxExtra, SetSpec |
| `holSemanticsExtra` | `CandleLean/HolSemanticsExtra.lean` | all of the above |
| `holSoundness` | `CandleLean/HolSoundness.lean` | all of the above (it defines nothing) |

* All names are at the top level (no namespace). The one exception is the
  `sptree` library (`sptree.spt`, `sptree.insert`, `sptree.domain`, constructors
  `sptree.LN/LS/BN/BS`), because its `domain` and `insert` clash with other
  names.
* Datatype constructors are exported to the top level, so you can write `Tyvar`,
  `Tyapp`, `Var`, `Const`, `Comb`, `Abs`, `Clash`, `Result`, `ConstSpec`, `TypeDefn`,
  `NewType`, `NewConst`, `NewAxiom`, `dbVar`, `dbBound`, `dbConst`, `dbComb`,
  `dbAbs`, `BigList`, `BigAppend`, `Small`, `LESS`, `EQUAL`, `GREATER` and `implode`.
  The exception is `app_list`. Write its constructors qualified:
  `app_list.List`, `app_list.Append`, `app_list.Nil` (or `.List xs`, `.Append`
  and `.Nil` when the expected type is known), because `List` and `Append` are
  Lean names.
* Every statement file must start with
  ```lean
  import CandleLean            -- or the specific modules
  open Classical
  ```
  `open Classical` is required: HOL4 `if b then ...` on a proposition uses
  classical decidability, and the definitions were elaborated with it.
* The definitions are `noncomputable`, so use proofs, not `#eval`.

## 2. Type mapping

| HOL4 | Lean |
|---|---|
| `bool` | `Prop` **everywhere**: results of predicates, relation arguments `'a -> 'a -> bool`, and data such as `bool list` (`List Prop`) or the `neg:bool` argument of `sort2_tail`. `T` is `True`, `F` is `False`, and `b1 = b2` on booleans is `=` on `Prop`, which is `↔` by `propext`. |
| `num` | `Nat`. `SUC n` is `n + 1`. `DIV`/`MOD` are `/`/`%`; HOL4 and Lean agree also for division by 0. |
| `'a list` | `List α` |
| `'a option` | `Option α` (`NONE` is `none`, `SOME` is `some`) |
| `'a # 'b` | `α × β`. A HOL4 tuple `(a,b,c)` is `(a, b, c)` = `(a, (b, c))`. |
| `'a + 'b` | `α ⊕ β` |
| `one` / `unit` | `Unit` (the value `()`) |
| `'a set` = `'a -> bool` | `Set α` (defined as `α → Prop`, `Prelude/Set.lean`) |
| `char` | `char` (a structure with field `ORD : Nat` and `ORD < 256`). This is **not** Lean's `Char`. |
| `string` = `char list` | `string` (abbrev for `List char`) |
| `mlstring` | `mlstring` (inductive with the single constructor `implode : string → mlstring`) |
| `'a word`, `word8`, `word32` | `word d` (`d` = `dimindex`), `word8 = word 8`, `word32 = word 32` |
| `'a |-> 'b` (fmap) | `fmap α β` |
| `'a spt`, `num_set`, `num_map` | `sptree.spt α`; `num_set` and `num_map α` (misc) are abbrevs for `sptree.spt Unit` and `sptree.spt α` |
| `ordering` (= toto `cpn`) | `ordering` with constructors `LESS`, `EQUAL`, `GREATER` (not Lean's `Ordering`) |
| `type` (holSyntax) | `type` |
| `term` | `term` |
| `dbterm` (the datatype) | **`dbterm_`**. The name `dbterm` is the function `dbterm`. |
| `update` | `update` |
| `'a result` | `result α` |
| `'a app_list`, `'a app_list_ann` | `app_list α`, `app_list_ann α` |
| `tysig`, `tmsig`, `sig`, `thy` | `tysig := fmap mlstring Nat`, `tmsig := fmap mlstring type`, `sig := tysig × tmsig`, `thy := sig × Set term` |
| `'U tyass`, `'U tyval`, `'U tmass`, `'U tmval` | `tyass U`, `tyval U`, `tmass U`, `tmval U` |
| `'U interpretation`, `'U valuation` | `interpretation U := tyass U × tmass U`, `valuation U := tyval U × tmval U` |

Type variables are written as Lean implicit type arguments `{α : Type}`.
**Nonempty types:** every HOL4 type is nonempty. Lean needs a `[Nonempty α]`
instance for constants that use `ARB` or Hilbert choice. These are `HD`, `EL`,
`LAST`, `RESULT`, `CLASH`, `FAPPLY`, `FLOOKUP`, `FEVERY`, `FRANGE`, `FUN_FMAP`,
`OUTL`, all of setSpec except the `is_*`/`extensional` predicates, and all of
holSemantics that mentions `termsem`, `apply`, `abstract`, `funspace`, `boolset`,
`true_` or `HD`. For a statement over a generic type that uses one of these,
add `[Nonempty α]`, and for the set-theory universe add `{U : Type} [Nonempty U]`.
Adding `[Nonempty α]` is always faithful. The concrete types (`Nat`, `mlstring`,
`type`, `term`, `char`, `fmap`, lists, ...) have instances already.

## 3. The set-theory parameter `mem` (setSpec, holSemantics*)

HOL4 writes `^mem` (the variable `mem : 'U -> 'U -> bool`) as the first
argument of these constants and hides it behind overloads. In Lean `mem` is an
**explicit first argument**:

```lean
variable {U : Type} [Nonempty U] (mem : U → U → Prop)
```

| HOL4 (overload) | Lean |
|---|---|
| `x <: y` | `mem x y` |
| `is_set_theory ^mem` | `is_set_theory mem` |
| `s suchthat P` / `sub mem s P` | `sub mem s P` |
| `Pow y` | `power mem y` |
| `union mem s` | `union mem s` |
| `x + y` (upair) | `upair mem x y` |
| `∅` | `empty mem` |
| `Unit x` | `unit mem x` |
| `One` | `one mem` |
| `Two`, `boolset` | `two mem`, `boolset mem` (abbrev for `two mem`) |
| `(a,b)` (setSpec pair) | `pair mem a b` |
| `x ∪ y` (binary_union) | `binary_union mem x y` |
| `x × y` (CROSS) | `product mem x y` |
| `Relspace x y` | `relspace mem x y` |
| `Funspace x y` | `funspace mem x y` |
| `f ' x` | `apply mem f x` |
| `True`, `False` (setSpec) | **`true_ mem`**, **`false_ mem`** |
| `Boolean b` | `boolean mem b` (`b : Prop`) |
| `Abstract s t f` | `abstract mem s t f` |
| `inhabited s` | `inhabited mem s` (abbrev for `∃ x, mem x s`) |
| `is_type_assignment tysig δ` (= `is_type_assignment0 ^mem`) | `is_type_assignment mem tysig δ` |
| `is_type_valuation τ` | `is_type_valuation mem τ` |
| `typesem δ τ ty` (no mem) | `typesem δ τ ty` |
| `is_term_assignment tmsig δ γ` | `is_term_assignment mem tmsig δ γ` |
| `is_term_valuation tysig δ τ σ` | `is_term_valuation mem tysig δ τ σ` |
| `is_valuation tysig δ v` | `is_valuation mem tysig δ v` |
| `instance tmsig i name ty` (no mem) | **`instance_ tmsig i name ty`** (`instance` is a Lean keyword) |
| `termsem tmsig i v tm` (= `termsem0 ^mem`) | `termsem mem tmsig i v tm` |
| `i satisfies (sig,h,c)` | `satisfies mem i (sig, h, c)` |
| `is_interpretation sig i` | `is_interpretation mem sig i` |
| `is_std_type_assignment δ` | `is_std_type_assignment mem δ` |
| `γ interprets name on vs as f` | `interprets mem γ name vs f` |
| `is_std_interpretation i` | `is_std_interpretation mem i` |
| `i models thy` | `models mem i thy` |
| `(thy,h) \|= c` (= `entails0 ^mem`) | `entails mem (thy, h) c` |
| `is_structure sig i v` | `is_structure mem sig i v` |
| `^Equalsem [x]` (holSemanticsExtra ML value) | `Equalsem mem [x]` (a reducible abbrev for the lambda) |

The HOL4 constants with a trailing `0` (`termsem0`, `entails0`, ...) are the Lean
names without the `0`.

## 4. Name table (HOL4 → Lean). Names not listed here are identical in HOL4 and Lean.

### Renamed because of Lean keywords or name clashes
| HOL4 | Lean | module |
|---|---|---|
| holSyntax overload `Bool` | `Bool_` | HolSyntax |
| holSemantics `instance` | `instance_` | HolSemantics |
| setSpec `true`, `false` (`True`, `False` overloads) | `true_`, `false_` | SetSpec |
| mlstring `compare` | `compare_` | Mlstring |
| holSyntaxExtra `bind` | `bind_` | HolSyntaxExtra |
| holSyntaxExtra datatype `dbterm` | `dbterm_` (the function `dbterm` keeps its name) | HolSyntaxExtra |
| mlstring overload `toString` | `chr_to_str` | Mlstring |
| sptree `domain`, `insert`, `spt`, `LN/LS/BN/BS` | `sptree.domain`, `sptree.insert`, `sptree.spt`, `sptree.LN` ... | Prelude/Sptree |
| misc `app_list` constructors `List`, `Append`, `Nil` | `app_list.List`, `app_list.Append`, `app_list.Nil` | Misc |

### HOL4 library constants that are Lean core functions
| HOL4 | Lean |
|---|---|
| `[]`, `h::t`, `[a;b;c]` | `[]`, `h :: t`, `[a, b, c]` |
| `APPEND l1 l2`, `l1 ++ l2` | `l1 ++ l2` |
| `LENGTH` | `List.length` (`l.length`) |
| `MAP f l` | `List.map f l` (`l.map f`) |
| `REVERSE` | `List.reverse` |
| `TAKE n l`, `DROP n l` | `List.take n l`, `List.drop n l` |
| `FOLDR f e l`, `FOLDL f e l` | `List.foldr f e l`, `List.foldl f e l` (same argument order) |
| `FST`, `SND` | `Prod.fst`, `Prod.snd` (`p.1`, `p.2`) |
| `OPTION_MAP`, `OPTION_BIND` | `Option.map`, `Option.bind` |
| `f o g` | `f ∘ g` |
| `$= x` | `(fun y => x = y)` |
| `$+ 0n` | `(fun n => 0 + n)` or `HAdd.hAdd 0` |
| `λ(x,y). t` | `fun (x, y) => t` or `fun p => t[p.1/x, p.2/y]` |
| `∃!x. P x` | `(∃ x, P x) ∧ ∀ x y, P x ∧ P y → x = y` (HOL4's definition; Lean core has no `∃!`) |
| `@x. P x` | `Classical.epsilon (fun x => P x)` |
| `x ∈ s`, `x ∉ s` (`IN`) | `x ∈ s`, `x ∉ s` (instance `Membership α (Set α)`, `x ∈ s` is `s x`) |

### HOL4 library constants defined in `CandleLean/Prelude` (same name unless noted)
* **Basic** (`bool`, `combin`, `pair`, `sum`, `arithmetic`, `relation`, `toto`, `ternaryComparisons`):
  `ARB`, `I`, `K`, `C`, `UPDATE` (`(a =+ b) f` is `UPDATE a b f`), `UNCURRY`,
  `PAIR_MAP` (`f ## g` is `PAIR_MAP f g`), `LEX` (`R1 LEX R2` is `LEX R1 R2`),
  `ISL`, `OUTL`, `EVEN`, `DIV2`, `MAX`, `transitive`, `reflexive`, `irreflexive`,
  `antisymmetric`, `trichotomous`, `StrongOrder`, `StrongLinearOrder`,
  `inv_image`, `RC`, `RTC` (inductive: `RTC.refl`, `RTC.step`), `ordering`, `cpn`,
  `invert_comparison`, `TotOrd`, `TO_of_LinearOrder`.
* **Set** (`pred_set`): `Set`, `GSPEC`, `EMPTY`, `UNIV`, `INSERT`, `UNION`,
  `INTER`, `SUBSET`, `DISJOINT`, `IMAGE`, `FINITE`, `INFINITE` (abbrev `¬ FINITE s`),
  `INJ`, `SURJ`, `BIJ`, `PERMUTES` (abbrev; `f PERMUTES s` is `PERMUTES f s`).
  Notation: `∅` = `EMPTY`, `{a}` = `INSERT a EMPTY`, `{a, b}`,
  `s ∪ t` = `UNION s t`, `s ∩ t` = `INTER s t`, `x INSERT s` = `INSERT x s`.
  Set comprehension:
  `{x | P x}` (expands to `GSPEC (fun x => (x, P x))`), and
  `{(x, y) | P x y}` (expands to `GSPEC (fun (x, y) => ((x, y), P x y))`), as in HOL4.
  Other comprehensions, for example `{f x | P x}`, are `GSPEC (fun x => (f x, P x))`.
* **List** (`list`, `rich_list`, `indexedLists`, `alist`, `sorting`):
  `LIST_TO_SET` and `set` (**`set` is a macro for `LIST_TO_SET`**), `MEM` (abbrev
  `h ∈ LIST_TO_SET l`), `NULL`, `HD`, `TL`, `EL`, `FLAT`, `FILTER`, `EVERY`,
  `EXISTS`, `ALL_DISTINCT`, `ZIP` (**takes a pair**: `ZIP (l1, l2)`), `LAST`, `FRONT`,
  `SNOC`, `GENLIST`, `REV`, `LIST_REL`, `EVERY2` (abbrev for `LIST_REL`),
  `isPREFIX` (HOL4 `l1 ≼ l2` / `<<=`), `LLEX`, `OPT_MMAP`, `SPLITP`, `SEG`,
  `MAX_LIST`, `MAPi`, `ALOOKUP`, `PERM`, `SORTED`.
* **String** (`string`): `char`, `ORD` (structure field), `CHR`, `string`,
  `char_lt` (HOL4 `<` on chars), `string_lt` (HOL4 `<` on strings), `FIELDS`.
  Literals: the HOL4 char `#"c"` is `CHR n` (n = character code). Write
  `ch!"c"` (expands to `CHR 99`). The HOL4 string `"abc"` is `str!"abc"`
  (expands to `[CHR 97, CHR 98, CHR 99] : string`). `""` is `([] : string)`.
* **Words** (`words`, `fcp`, `bitstring`): `word`, `word8`, `word32`, `w2n`
  (structure field), `n2w`, `dimword`, `FCP`, `PAD_LEFT`, `zero_extend`,
  `fixwidth`, `shiftr`, `field`, `testbit`, `v2w`. The numerals `0w`, `1w`, `nw`
  are `n2w 0`, `n2w 1`, `n2w n` (give the type: `(n2w 0 : word32)`).
* **FiniteMap** (`finite_map`, `alist`): `is_fmap`, `fmap`, `fmap_REP`, `FEMPTY`,
  `FUPDATE` (HOL4 `f |+ (k,v)` is `FUPDATE f (k, v)`), `FAPPLY` (HOL4 `f ' x`
  on finite maps is `FAPPLY f x`; `$FAPPLY FEMPTY` is `FAPPLY FEMPTY`), `FDOM`,
  `FLOOKUP`, `FEVERY`, `FRANGE`, `FUN_FMAP`, `alist_to_fmap`.
* **Sptree**: `sptree.spt`, `sptree.insert`, `sptree.domain` (HOL4 `insert n () s`
  is `sptree.insert n () s`).
* **ASCIInumbers** (`numposrep`, `ASCIInumbers`): `l2n`, `n2l`, `s2n`, `n2s`,
  `HEX`, `UNHEX`, `num_from_hex_string`, `num_to_hex_string`.
* **Mergesort** (`mergesort`): `sort2_tail`, `sort3_tail`, `merge_tail`,
  `mergesortN_tail`, `mergesort_tail` (HOL4 `mergesort$mergesort_tail`).
  The `negate`/`neg` argument is a `Prop` (`F` is `False`).

### Package constants (all identical names except the renames above)
* misc: `app_list`, `append_aux`, `append`, `SmartAppend`, `max3`, `num_set`,
  `num_map`, `UPDATE_LIST` (HOL4 `f =++ l` is `UPDATE_LIST f l`), `find_index`,
  `splitlines`, `is_subseq`, `make_even`, `fmap_update`.
* mllist: `sort`.
* mlstring: `mlstring`, `implode`, `strlit` (abbrev for `implode`), `strlen`,
  `strsub`, `substring`, `concat`, `explode_aux`, `explode`, `strcat`
  (HOL4 `s1 ^ s2` is `strcat s1 s2`), `chr_to_str` (HOL4 `toString`),
  `compare_aux`, `compare_`, `mlstring_lt` (and `s1 < s2` via an `LT mlstring`
  instance), `flip_ord` (abbrev for `invert_comparison`), `app_list_ann`,
  `sum_sizes`, `make_app_list_ann`, `shrink`, `str_app_list_opt`,
  `char_to_word8`, `word8_to_char`.
  The HOL4 literal `«abc»` is **`mls!"abc"`** (expands to `implode (str!"abc")`).
  `«»` is `mls!""` (= `implode []`).
* setSpec: see §3.
* holSyntaxLib: `ALPHAVARS`, `REV_ASSOCD`, `result` (`Clash`, `Result`),
  `IS_RESULT`, `IS_CLASH`, `RESULT`, `CLASH`, `LIST_INSERT`, `LIST_UNION`,
  `INORDER_INSERT`, `STRING_SORT`.
* holSyntax: `type`, `Fun` (abbrev, `Fun s t = Tyapp mls!"fun" [s, t]`), `Bool_`,
  `domain`, `codomain`, `term`, `Equal` (abbrev), `dest_var`, `has_type`,
  `welltyped`, `typeof`, `RACONV`, `ACONV`, `type_lt`, `term_lt`, `term_cmp`,
  `type_cmp`, `ordav`, `orda`, `term_union`, `term_remove`, `term_image`,
  `VFREE_IN`, `CLOSED`, `VARIANT_PRIMES`, `VARIANT`, `TYPE_SUBST`, `is_instance`
  (abbrev), `VSUBST`, `sizeof`, `INST_CORE`, `INST`, `tyvars`, `tvars`,
  `equation` (infix **`s === t`**, right associative, precedence 60), `tysig`,
  `tmsig`, `sig`, `thy`, `tysof`, `tmsof`, `sigof`, `axsof`, `type_ok`, `term_ok`,
  `alpha_lt`, `hypset_ok`, `is_std_sig`, `theory_ok`, `proves`, `update`,
  `types_of_upd`, `consts_of_upd`, `type_list`, `const_list`, `axexts_of_upd`,
  `conexts_of_upd`, `axexts`, `conexts`, `axioms_of_upd`, `axiom_list`, `thyof`,
  `updates`.
* holSyntaxExtra: `subtype1`, `subtype` (abbrev `RTC subtype1`), `subterm1`,
  `subterm` (abbrev `RTC subterm1`), `dbterm_` (type), `bind_`, `db`, `dbVSUBST`,
  `dbVFREE_IN`, `dbINST`, `dbterm`, `bind_list_aux`, `bv_names`,
  `simple_subst`, `simple_inst`, `rename_bvars`, `fresh`, `ConstDef` (abbrev),
  `types_in`, `arities_match`.
* holSemantics / holSemanticsExtra: see §3. Also `tyaof i = i.1`, `tmaof i = i.2`,
  `tyvof v = v.1`, `tmvof v = v.2` (abbrevs). The HOL4 statements write `FST i` and
  `FST v`; use `i.1` and `v.1` (or `tyaof i`, `tyvof v`, which are the same by
  definition).

## 5. Infix and mixfix syntax

HOL4 word infixes become **prefix** functions:

| HOL4 | Lean |
|---|---|
| `tm has_type ty` | `has_type tm ty` |
| `thyh \|- c` | `proves thyh c`, e.g. `proves (thy, h) c` |
| `(thy,h) \|= c` | `entails mem (thy, h) c` |
| `i models thy` | `models mem i thy` |
| `i satisfies (sig,h,c)` | `satisfies mem i (sig, h, c)` |
| `upd updates ctxt` | `updates upd ctxt` |
| `ty1 subtype ty2`, `t1 subterm t2` | `subtype ty1 ty2`, `subterm t1 t2` |
| `R1 LEX R2` | `LEX R1 R2` |
| `f ## g` | `PAIR_MAP f g` |
| `(a =+ b) f` | `UPDATE a b f` |
| `f =++ l` | `UPDATE_LIST f l` |
| `s1 ^ s2` (mlstring) | `strcat s1 s2` |
| `l1 ≼ l2` | `isPREFIX l1 l2` |
| `f ' x` (finite map) | `FAPPLY f x` |
| `f ' x` (setSpec) | `apply mem f x` |
| `fm \|+ (k,v)` | `FUPDATE fm (k, v)` |
| `s === t` | `s === t` (Lean notation for `equation s t`) |

The HOL4 overloads `tysof`, `tmsof`, `sigof` and `axsof` depend on the type of
their argument. In Lean they are the type-class methods `tysof`, `tmsof`,
`sigof` and `axsof` (classes `HasTysof`, ...), with instances:
* `s : sig`: `tysof s = s.1`, `tmsof s = s.2`;
* `t : thy`: `sigof t = t.1`, `axsof t = t.2`, `tysof t = t.1.1`, `tmsof t = t.1.2`;
* `ctxt : List update`: `tysof ctxt = alist_to_fmap (type_list ctxt)`,
  `tmsof ctxt = alist_to_fmap (const_list ctxt)`,
  `sigof ctxt = (tysof ctxt, tmsof ctxt)`, `axsof ctxt = set (axiom_list ctxt)`.

The argument type must be known when the method is elaborated. Annotate a
binder if it is not, for example `∀ (thy : thy) h c, ...` or `∀ (Γ : sig) ...`.
HOL4 `FST sig` in a statement is `sig.1` (= `tysof sig`).

## 6. Inductive relations and their rules

| HOL4 | Lean constructors |
|---|---|
| `has_type` (4 unnamed rules) | `has_type.var`, `has_type.const`, `has_type.comb`, `has_type.abs` |
| `RACONV` | `RACONV.var`, `RACONV.const`, `RACONV.comb`, `RACONV.abs` |
| `proves` (`proves_ABS`, ...) | `proves.ABS`, `proves.ASSUME`, `proves.BETA`, `proves.DEDUCT_ANTISYM`, `proves.EQ_MP`, `proves.INST`, `proves.INST_TYPE`, `proves.MK_COMB`, `proves.REFL`, `proves.axioms` |
| `updates` | `updates.new_axiom`, `updates.new_constant`, `updates.new_specification`, `updates.new_type`, `updates.new_type_definition` |
| `subtype1` | `subtype1.intro` |
| `subterm1` | `subterm1.comb_left`, `.comb_right`, `.abs_body`, `.abs_var` |
| `RTC` | `RTC.refl`, `RTC.step` |
| `is_fmap` | `is_fmap.empty`, `is_fmap.update` |
| `type_lt`, `term_lt` | **definitions, not Lean `inductive`s** (see §7) |

HOL4 conjunctions of premises are curried Lean arguments. The HOL4 theorems
`X_rules`, `X_ind`, `X_cases` and `X_strongind` are not provided. In Lean they
are the constructors, the `X.rec`/`induction` tactic, and `cases`.

## 7. Modelling choices (where Lean could not say the HOL4 text directly)

1. **`bool` is `Prop`.** `if` on a proposition uses `Classical.propDecidable`.
   Equality of booleans is equality of propositions (= `↔` by `propext`).
2. **`ARB`** (`bool$ARB`, a constant with no definition in HOL4) is a
   `noncomputable opaque ARB {α} [Nonempty α] : α`, so nothing is provable
   about it. HOL4's `Define` fills the cases a pattern match leaves out with
   `ARB`, and the translations do the same. This affects `HD []`, `LAST []`,
   `RESULT (Clash _)`, `CLASH (Result _)`, `dest_var` of a non-variable, and
   `termsem` of `Abs t b` where `t` is not a `Var`.
3. **Constants from `new_specification`, and constants that are only partly
   specified** are defined as `Classical.epsilon` over **whole functions** that
   satisfy the HOL4 specification: `fresh`, `VARIANT_PRIMES`, `instance_`,
   `FUN_FMAP`, `SEG`, `CHR` (from the type bijection `char_BIJ`) and `OUTL`
   (from `new_recursive_definition` with only the `INL` case). Only the
   specification can be proved about them, after you show that a witness
   exists, for example with `Classical.epsilon_spec`. This matches HOL4,
   where only the specification is known. For example `CHR n` with `n ≥ 256`,
   `SEG (m+1) k []`, `FAPPLY f x` with `x ∉ FDOM f`, and `fresh s` for infinite
   `s` are unspecified.
4. **Hilbert choice `@`** is `Classical.epsilon` (setSpec `sub`, `power`,
   `union`, `upair`, `apply`).
5. **`type_lt` and `term_lt`.** The recursive occurrence is under `LLEX`/`LEX`,
   which Lean's `inductive` does not accept. They are defined as the least
   relation closed under the HOL4 rules: `type_lt a b := ∀ R, (rules hold for R)
   → R a b`. This is how HOL4's `IndDefLib` defines every inductive relation, so
   the meaning is the same. The rule theorems (for example `type_lt_thm`) must
   be proved from this definition.
6. **Words** are stored by their value: `word d = {w2n : Nat // w2n < 2^d}`
   (a structure). This is in bijection with HOL4's `bool[d]`, and bit `i` of
   the word is bit `i` of `w2n`. `n2w n = n % 2^d`. `FCP f` is the word whose
   bit `i` (for `i < d`) is `f i`. `v2w` is translated literally
   (`FCP i. testbit i v`). Only the widths 8 and 32 occur.
7. **`char`** is a structure with a field `ORD < 256` (HOL4's type definition),
   not Lean's `Char`.
8. **Finite maps** use HOL4's representation: functions `α → β ⊕ Unit` that
   satisfy the inductive `is_fmap`.
9. **`ZIP`** takes a pair, as in HOL4. Lean's `List.zip` is not used.
10. **Lean core functions** replace `LENGTH`, `MAP`, `REVERSE`, `TAKE`, `DROP`,
    `FOLDR`, `FOLDL`, `APPEND`, `FST`, `SND`, `OPTION_MAP` and `OPTION_BIND`.
    They agree with the HOL4 definitions on all inputs.
11. **`mergesortN_tail`**: HOL4's last clause `mergesortN_tail negate R n l` only
    applies to `n ≥ 4` (all smaller `n` are covered by the earlier clauses).
    Lean writes this pattern as `n + 4`.
12. **`TYPE_SUBST`**: the HOL4 third clause `TYPE_SUBST i (Fun ty1 ty2)` is an
    instance of the second, so Lean has only two clauses. The equation for
    `Fun` follows by unfolding (`simp [TYPE_SUBST]`).
13. **Pattern lambdas and `let (x,y) = e in ...`** are written with projections
    (`p.1`, `p.2`). These are equal to HOL4's `UNCURRY` forms.
14. **`instance_`, `termsem`** and other polymorphic `'U` constants take
    `{U : Type u} [Nonempty U]`.
15. **Literals**: `mls!"..."`, `str!"..."` and `ch!"..."` expand to `CHR`
    numerals, exactly like HOL4's literals. They are macros, not new constants.
16. **`setSpec` `∃!`** is expanded to HOL4's definition of `?!`.

## 8. Equation lemmas

Lean generates equation lemmas for every definition (`foo.eq_1`, `foo.eq_def`,
`unfold foo`, `simp [foo]`). These hold for the structural definitions and also
for the well-founded ones (`INST_CORE`, `term_union`, `FIELDS`, `merge_tail`,
`mergesortN_tail`, `compare_aux`, `n2l`, `sptree.insert`, `TYPE_SUBST`,
`tyvars`, `type_ok`, `typesem`, `arities_match`). For example `TYPE_SUBST.eq_2`
is `TYPE_SUBST i (Tyapp v tys) = Tyapp v (List.map (TYPE_SUBST i) tys)`.

## 9. Auxiliary lemmas (not HOL4 theorems; you can use them)

* `SPLITP_snd_length_le` (Prelude/String), used for the termination of `FIELDS`.
* `sizeof_REV_ASSOCD_aux`, `FILTER_mem_aux` and `sizeof_VSUBST_aux` (HolSyntax),
  used for the termination of `INST_CORE`. `sizeof_VSUBST_aux` is the special
  case of HOL4's `SIZEOF_VSUBST`. The target theorem `SIZEOF_VSUBST` must still
  be stated under its own name.
* `EVERY_attach_unattach`, `EVERY_wfParam` and `EVERY_unattach` (Prelude/List):
  `wf_preprocess` lemmas for recursion through `EVERY`.

## 10. What is not translated

Package definitions that no target statement or translated definition uses are
not translated. These are misc `the`, `read_bytearray`, `fromList2`, `tlookup`,
`enumerate`, `insert_atI`, `steps`, `steps_rel`, `all_words`, `eq_shape`,
`copy_shape` and `good_dimindex`, the mlstring functions other than those
listed above (for example `extract`, `tokens`, `fields`, `collate`), the mllist
functions other than `sort`, and the holSyntaxExtra `fresh_term`, `vfree_in`,
`variant`, `subtract`, `insert`, `itlist`, `union` and `frees`.
