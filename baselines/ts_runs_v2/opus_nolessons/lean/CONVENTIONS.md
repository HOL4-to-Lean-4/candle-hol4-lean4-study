# Conventions for the Lean translation (stage 1 -> stage 2)

## 1. Files, namespaces, opens

* Every declaration is in the namespace `CmlTS` (HOL4's `binary_ieee` internals: `CmlTS.ieee`).
* Start each file that states theorems with

  ```lean
  import CmlTS.<Module of the theory>      -- the module already imports its ancestors
  set_option autoImplicit false
  namespace CmlTS
  open Classical
  ```

  Work *inside* `namespace CmlTS` (do not merely `open CmlTS`): several names (`compare`, `Empty`,
  ...) also exist at the root, and inside the namespace the `CmlTS` one wins.
* One module per theory:
  `misc`->`CmlTS.Misc`, `mllist`->`Mllist`, `mlstring`->`Mlstring`, `location`->`Location`,
  `lprefix_lub`->`LprefixLub`, `ffi`->`Ffi`, `fpSem`->`FpSem`, `namespace`->`Namespace`,
  `namespaceProps`->`NamespaceProps`, `ast`->`Ast`, `semanticPrimitives`->`SemanticPrimitives`,
  `semanticPrimitivesProps`->`SemanticPrimitivesProps`, `evaluate`->`Evaluate`,
  `evaluateProps`->`EvaluateProps`, `semantics_min`->`SemanticsMin`, `typeSystem`->`TypeSystem`,
  `typeSoundInvariants`->`TypeSoundInvariants`, `weakening`->`Weakening`,
  `typeSysProps`->`TypeSysProps`, `typeSound`->`TypeSound`.
  A package constant lives in the module of its HOL4 theory. **A name that is not in the table of
  section 4 is identical in HOL4 and Lean** (including mutual companions such as `pats_bindings`,
  `pmatch_list`, `do_eq_list`, `concrete_v_list`, `FV_list/FV_pes/FV_defs`, `evaluate_match`,
  `evaluate_decs`, `type_ps`, `type_es`, `type_funs`, `type_ds`).
* HOL4 library constants: modules `CmlTS.Prelude.{Set,List,Fmap,Llist,String,Sptree,Mergesort,Real,BinaryIeee}`.

## 2. Types

| HOL4 | Lean |
|---|---|
| `bool` (result of a predicate, argument `P : 'a -> bool`, `extra_checks` of `type_d`/`type_ds`) | `Prop` (`T`/`F` = `True`/`False`; write `type_ds False tenv ...`) |
| `bool` inside data: `Loc b n`, `Eq_val b`, argument of `Boolv`, `neg` in mergesort, `flags` | `Bool` (`T`/`F` = `true`/`false`; a HOL4 `Eq_val (b = b')` is `Eq_val (decide (b = b'))`) |
| `num`, `int` | `Nat`, `Int` (`&n` = `(n : Int)`) |
| `'a option`, `SOME`, `NONE` | `Option α`, `some`, `none` |
| `'a # 'b`, `FST`, `SND` | `α × β`, `.1`/`Prod.fst`, `.2`/`Prod.snd` |
| `'a + 'b`, `INL`, `INR` | `α ⊕ β`, `.inl`, `.inr` |
| `unit` | `Unit` |
| `'a list` | `List α` |
| `'a set` = `'a -> bool` | `Set α` (`CmlTS.Set`, a def equal to `α → Prop`) |
| `char` | `char` = `Fin 256` |
| `string` | `string` = `List char` |
| `mlstring` | `mlstring` (constructor `strlit`) |
| `word8`, `word64`, `'a word` | `word8` = `BitVec 8`, `word64` = `BitVec 64`, `BitVec n` |
| `('a,'b) fmap`, `'a \|-> 'b` | `fmap α β` |
| `'a llist` | `llist α` |
| `'a spt`, `num_map`, `num_set` | `spt α`, `num_map α`, `num_set` |
| `ordering` / `cpn` | `ordering` |
| `real`, `('t,'w) float` | `real`, `ieee.float t w` |
| `('m,'n,'v) namespace` | `Namespace m n v` |
| `('m,'n) id` | `ident m n` |
| `v` (semanticPrimitives) | `val` |
| `t` (typeSystem) | `typ` |
| `('a,'b) result`, `'a error_result`, `'a store_v`, `'a match_result` | `result α β`, `error_result α`, `store_v α`, `match_result α` |
| `'ffi state`, `'ffi ffi_state`, `'ffi ffi_result`, `'ffi oracle_result`, `'ffi oracle` | `state ffiT`, `ffi_state ffiT`, ... with `{ffiT : Type}` |
| `'v sem_env` | `sem_env α` (fields `v`, `c`); almost always `sem_env val` |

* HOL4 type variables become implicit arguments `{α : Type}` (package constants take types in
  `Type`; Prelude constants are universe polymorphic).
* **Nonempty types.** HOL4 types are nonempty. Constants that can return an unspecified value take
  `[Nonempty α]`: `ARB SELECT THE HD EL FAPPLY nth lookup_vars dest_Refv` (`MAP3` and `type_def_to_ctMap` do not need
  one: they return lists). A polymorphic statement that uses one of them needs `[Nonempty α]` (faithful, since HOL4 types are
  nonempty). All concrete types have `Inhabited` instances.
* **Equality tests.** HOL4 is classical: no definition takes a `DecidableEq` argument; `open Classical`
  supplies all `Decidable` instances. Do not add `[DecidableEq α]` hypotheses.

## 3. Library constants that became Lean core functions or notation

| HOL4 | Lean |
|---|---|
| `MEM x l` | `x ∈ l` |
| `set l`, `LIST_TO_SET l` | `LIST_TO_SET l : Set α` |
| `LENGTH l`, `REVERSE l`, `l1 ++ l2`, `h::t` | `l.length`, `l.reverse` (`List.reverse l`), `l1 ++ l2`, `h :: t` |
| `MAP f l`, `FLAT l`, `TL l` | `l.map f`, `l.flatten`, `l.tail` (`TL [] = []` in both) |
| `TAKE n l`, `DROP n l` | `l.take n`, `l.drop n` |
| `FOLDR f e l`, `FOLDL f e l` | `List.foldr f e l`, `List.foldl f e l` |
| `ZIP (a,b)` (one pair argument) | `List.zip a b` |
| `MAP2 f a b` | `List.zipWith f a b` |
| `REPLICATE n x` | `List.replicate n x` |
| `LUPDATE e n l` | `l.set n e` |
| `oEL n l` | `l[n]?` |
| `isPREFIX a b`, `a ≼ b`, `a <<= b` | `a <+: b` |
| `IS_PREFIX a b` | `b <+: a` (**arguments flipped**, as in HOL4's overload) |
| `f o g` | `f ∘ g` (or a `fun`) |
| `$+ 0` | `fun x => 0 + x` (or `(0 + ·)`) |
| `n DIV m`, `n MOD m`, `SUC n` | `n / m`, `n % m`, `n + 1` |
| `x ∈ s`, `x NOTIN s` | `x ∈ s`, `¬ x ∈ s` |
| `{}`, `{x}`, `s ∪ t`, `s ∩ t`, `s DIFF t`, `s ⊆ t`, `x INSERT s` | `∅` (or `{}`), `{x}`, `s ∪ t`, `s ∩ t`, `s \ t`, `s ⊆ t`, `insert x s` |
| `{x \| P x}` | `{x \| P x}` (macro for `Set.of fun x => P x`; `{x : t \| P x}` also works) |
| `{f x \| P x}` | `{y \| ∃ x, y = f x ∧ P x}` |
| `!x::s. P x`, `∀(p,e)::set pes. Q` | `RES_FORALL s (fun x => P x)`, `RES_FORALL (LIST_TO_SET pes) (fun (p, e) => Q)` |
| `@x. P x` | `SELECT fun x => P x` |
| `call_FFI_rel^*`, `RTC R` | `RTC call_FFI_rel`, `RTC R` |
| `m \|+ (k,v)`, `m \|++ l`, `f ⊌ g` / `FUNION f g` | `m \|+ (k, v)`, `m \|++ l`, `f ⊌ g` / `FUNION f g` |
| `f SUBMAP g`, `f ⊑ g` | `SUBMAP f g` (prefix) |
| `f o_f m` | `o_f f m` (prefix), e.g. `o_f (Prod.snd ∘ Prod.snd) ctMap` |
| `FLOOKUP m k` | `FLOOKUP m k` |
| `«abc»` | `mls "abc"` (so `«»` is `mls ""`, `«::»` is `mls "::"`) |
| `"abc"` (string), `STRING c cs`, `#"c"` | `str_lit "abc"`, `c :: cs`, `ORD`/`CHR` forms |
| `<`, `<=` on `mlstring` | `<`, `≤` (instances `mlstring_lt`, `mlstring_le`); write `mlstring_gt a b`, `mlstring_ge a b` by name for `>`, `>=` |
| `<` etc. on `char` | `<` etc. of `Fin 256` (compares `ORD`) |
| `n2w`, `w2n`, `i2w`, `word_add`, `word_sub`, `word_and`, `word_or`, `word_xor`, `word_lsl/lsr/asr/ror` | same names (`abbrev`s for `BitVec` operations) |
| `i / j`, `i % j` on `int` | `int_div i j`, `int_mod i j` (floor division; unspecified for `j = 0`) |
| `Num i`, `ABS i`, `I x` | `Num i` (= `natAbs`, HOL4's definition), `ABS i`, `I x` |
| `s with f := x`, `<\| f := x \|>` | `{ s with f := x }`, `{ f := x }` |
| `case e of ...` | `match e with ...` |
| `λ(x,y). b` | `fun (x, y) => b` |
| `Short`, `Long`, ... constructors | see section 5 |

Library constants with their HOL4 name and own Lean definition:
`Set`: `ARB SELECT K I C UPDATE UNCURRY RTC UNIV DISJOINT IMAGE BIGUNION INJ SURJ BIJ FINITE CARD RES_FORALL ordering(LESS EQUAL GREATER) EVEN DIV2`;
`List`: `THE NULL HD EL EVERY EXISTS LIST_REL EVERY2 LIST_TO_SET ALL_DISTINCT REV COUNT_LIST SPLITP ALOOKUP`;
`Fmap`: `FEMPTY FUPDATE FDOM FAPPLY FUPDATE_LIST SUBMAP FUNION o_f FRANGE FEVERY alist_to_fmap FLOOKUP`;
`Llist`: `LNIL LCONS LHD LTL LTAKE LFINITE llength_rel LLENGTH llist_toList fromList LPREFIX`;
`String`: `ORD CHR TOKENS Num ABS int_div int_mod n2w w2n i2w word_*`;
`Sptree`: `lookup domain toListA toList` (`LN LS BN BS`);
`Mergesort`: `sort2_tail sort3_tail merge_tail mergesortN_tail mergesort_tail`;
`Real`: `real` and its operations; `BinaryIeee`: `rounding`, `ieee.*`, `fp64_*`.

Lemmas provided for later proofs: `EVERY_iff`, `EXISTS_iff`, `ALL_DISTINCT_iff` (to `List.Nodup`),
`Set.ext`, `fmap.ext`, `llist.ext`, `ALOOKUP_mem`, `nsSub_compute_def`, `fix_clock_IMP`.

## 4. Names that differ

| HOL4 | Lean | Module |
|---|---|---|
| type `semanticPrimitives$v` | `val` | SemanticPrimitives |
| type `typeSystem$t` | `typ` | TypeSystem |
| type `namespace$namespace` | `Namespace` | Namespace |
| type `namespace$id` | `ident` | Namespace |
| type `fpSem$fp_cmp` | `fp_cmp_t` (the function `fp_cmp` keeps its name) | FpSem |
| type abbreviation `ctMap` | `ctMap_t` | TypeSoundInvariants |
| `mllist$collate` | `mllist_collate` | Mllist |
| `mlstring$collate` | `mlstring_collate` | Mlstring |
| `semanticPrimitives$thunk_op` (function) | `do_thunk_op` (the type `thunk_op` keeps its name) | SemanticPrimitives |
| `llist$toList` | `llist_toList` (`toList` is sptree's) | Prelude.Llist |
| `binary_ieee$float_value`, `float_compare` (functions) | `ieee.get_float_value`, `ieee.get_float_compare` | Prelude.BinaryIeee |
| `binary_ieee$float_*`, `flags`, `fp_op`, ... | `ieee.float_*`, `ieee.flags`, `ieee.fp_op`, ...; type arguments `(:'t # 'w)` are `t w` | Prelude.BinaryIeee |
| overload `+++` | `extend_dec_env` (no notation) | SemanticPrimitives |
| overload `^` on mlstring | `strcat` (no notation) | Mlstring |
| overload `=++` | `UPDATE_LIST` (no notation) | Misc |
| `EVERY2` | `EVERY2` (abbrev of `LIST_REL`) | Prelude.List |
| `sem_env_c env`, `sem_env_v env` | `env.c`, `env.v` | |

HOL4 theorem names that would clash with definitions, or that occur twice:
`typeSysProps.type_subst` (clashes with the function; suggest `type_subst_thm`),
`semanticPrimitivesProps.concrete_v_list` (suggest `concrete_v_list_thm`),
`typeSysProps.tveLookup_freevars` (lines 624 and 731; suggest suffix `_lem` for the local one, 731),
`typeSound.EVERY_LIST_REL` (lines 50 and 1297; suggest suffix `_lem` for the local one, 50).

## 5. Constructors

Constructors are in the namespace of their type (`exp.Raise`, or `.Raise` where the type is known)
and are also exported to `CmlTS`, so `Raise e`, `Litv (IntLit n)`, `Rval v`, `Short x` can be written
directly inside `namespace CmlTS`. **Not exported** (they clash with Lean names or each other), so
qualify them or use the leading dot: all of `arith` (`arith.Add`, ...), `lit.Char`,
`store_v.Thunk`, `tenv_val_exp.Empty`, `Namespace.Bind`, all of `app_list`, all of `app_list_ann`,
all of `fp_cmp_t`, `fp_uop`, `fp_bop`, `fp_top`, and everything in `ieee`.

In patterns always prefer the leading dot (`| .Rerr (.Rabort .Rtype_error) => ...`): a misspelt
undotted constructor silently becomes a variable.

## 6. Inductive relations

HOL4 rule premises joined by `∧` became separate hypotheses, in HOL4 order. Two encodings:

* `type_e` (rules `Handle`, `Mat`) and `type_v` (rules `Conv_some`, `Conv_none`, `Closure`,
  `Recclosure`, `Vectorv`) have recursive occurrences under `∃`/`LIST_REL`/`EVERY`/`nsAll2`, which
  Lean's `inductive` rejects. Those rules take an arbitrary relation `R` with
  `∀ ..., R ... → type_e ...` (resp. `type_v`) and use `R` in that premise. The premises are monotone
  in `R`, so this defines the same least relation. The literal HOL4 rules are proved as
  `type_e.Handle'`, `type_e.Mat'`, `type_v.Conv_some'`, `type_v.Conv_none'`, `type_v.Closure'`,
  `type_v.Recclosure'`, `type_v.Vectorv'`; their inversions as `*_inv`.
* `type_p/type_ps`, `type_d/type_ds`, `RTC`, `LFINITE`, `llength_rel` are plain (mutual) inductives.

## 7. Other modelling choices

* **ARB.** `ARB : α` is `Classical.choice` on `Nonempty α`. Partial HOL4 `Definition`s
  (`MAP3 locnrow locn_rowupdate locncol locn_colupdate the_Litv_* dest_Refv FV_dec
  type_def_to_ctMap HD`) return `ARB` outside their patterns, which is what HOL4's definition package
  does. `THE NONE`, `CHR n` for `n ≥ 256`, and division by zero are unspecified in HOL4 and `ARB` here.
* **Nested recursion** (`check_freevars`, `check_freevars_ast`, `type_subst`, `deBruijn_inc`,
  `deBruijn_subst`, `check_type_names`, `type_name_subst`, `is_value`, `every_exp`, `nsMap`) uses
  well-founded recursion; Lean's equation lemmas are the HOL4 equations (e.g.
  `check_freevars dbmax tvs (Tapp ts tn) = EVERY (check_freevars dbmax tvs) ts` by
  `rw [check_freevars]`). Lambdas over pairs in `every_exp`/`nsMap` are written with projections
  (definitionally equal).
* **evaluate** is the HOL4 definition with `fix_clock` (`evaluate_def` before the clean-up),
  well-founded on `(clock, size)`; some matches carry an unused equation `_h` for the termination proof.
* **nsSub_compute** has an extra always-true conjunct for termination; `nsSub_compute_def` is the HOL4
  equation.
* **fmap** is a structure (`FLOOKUP : α → Option β` with finite support), extensional.
  `SUBMAP`, `FRANGE`, `FEVERY` are stated with `FLOOKUP` instead of `FDOM`/`FAPPLY` (equivalent).
* **llist** is HOL4's representation type (functions `Nat → Option α` closed under `lrep_ok`).
* **real** is built as Dedekind cuts (no Mathlib); operations on rationals are proved to agree with
  `Rat`. `sqrt` is HOL4's `root 2` by `SELECT`.
* **SELECT** (Hilbert choice) is `Classical.epsilon`.
* Polymorphism follows HOL4: e.g. `tenv_val_ok`, `tenv_ctor_ok`, `tenv_abbrev_ok`, `type_ctor`,
  `add_tenvE`, `build_ctor_tenv`, `type_def_to_ctMap`, `weakS`, `weakCT`, `store_type_extension`,
  `consistent_ctMap`, `ctMap_has_exns`, `ctMap_has_bools`, `tscheme_inst2`, `find_recfun`,
  `list_result`, `fix_clock` are generic. When Lean cannot infer a type argument, add an ascription,
  e.g. `tenv_ctor_ok (build_ctor_tenv tenvT tds tis : Namespace m conN _)` with `{m : Type}`, or
  `tenv_val_ok (nsEmpty : Namespace m n (Nat × typ))`.
* Free variables of a HOL4 theorem statement are implicitly universally quantified; make them explicit
  (or implicit) binders in Lean.
* `do_app`, `do_thunk_op` take the pair `(s, t)` as one argument, as in HOL4: `do_app (s, t) op vs`.
  `copy_array (src, off) len d`, `lookup_env s (i, j)`, `compiler_agrees f args (st, bs, ws)` likewise.
* `nsLookup`-style lambdas `\i v (tvs,t). P` are `fun _ v (tvs, t) => P`.
