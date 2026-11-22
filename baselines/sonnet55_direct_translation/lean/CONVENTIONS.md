# Conventions: HOL4 -> Lean 4 (stage 1, definitions)

## Layout
Each HOL4 theory is one module under `CandleLean/`; namespace `Candle.<Theory>` (capitalised).
Library constants live in `CandleLean/Prelude/{Basic,List,FMap,String,Sort}.lean`, namespace `HOL`.
Import order follows HOL4 Ancestors: Prelude.* -> Misc -> Mllist -> Mlstring -> SetSpec -> HolSyntaxLib -> HolSyntax -> HolSyntaxExtra -> HolSemantics -> HolSemanticsExtra -> HolSoundness.
Every file starts `noncomputable section` and `open Classical`.
Standard opens for statements:
`open HOL Candle.Misc Candle.Mllist Candle.Mlstring Candle.SetSpec Candle.HolSyntaxLib Candle.HolSyntax Candle.HolSyntaxExtra Candle.HolSemantics Candle.HolSemanticsExtra`.
Constructors of `type`, `term`, `update`, `result`, `mlstring`, `app_list`, `DbTerm` are `export`ed.

## Module of each name (HOL4 name -> Lean name)
Same name unless listed under "Renames".
- Prelude.Basic: sets (`HOL.Set`, UNIV, IMAGE, DISJOINT, FINITE, INFINITE, INJ, SURJ, BIJ, PERMUTES), OPTION_MAP, OPTION_BIND, FST, SND, UNCURRY, CURRY, PAIR_MAP, I, K, C, UPDATE, EXISTS_UNIQUE, reflexive, irreflexive, transitive, symmetric, antisymmetric, trichotomous, StrongOrder, StrongLinearOrder, RC, RTC, inv_image, LEX, MAX, MIN, EVEN, ODD, DIV2, ordering, LESS/EQUAL/GREATER, invert_comparison, TotOrd, TO_of_LinearOrder, LEAST.
- Prelude.List: LENGTH, MAP, FLAT, REVERSE, FOLDR, FOLDL, LIST_TO_SET, MEM, NULL, HD, TL, FILTER, EVERY, EXISTS, EL, LAST, FRONT, TAKE, DROP, SNOC, GENLIST, REPLICATE, ZIP, UNZIP, ALL_DISTINCT, SUM, MAX_LIST, SEG, LIST_REL, EVERY2, MAPi, OPT_MMAP, SPLITP, isPREFIX, LLEX, PERM, SORTED, ALOOKUP, REV.
- Prelude.FMap: FMap, FEMPTY, FDOM, FLOOKUP, FAPPLY, FUPDATE, FUNION, FRANGE, FEVERY, alist_to_fmap, FUN_FMAP.
- Prelude.String: char, ORD, CHR, string, FIELDS, l2n, n2l, s2n, n2s, HEX, UNHEX, num_from_hex_string, num_to_hex_string, word, word8, word32, dimword, n2w, w2n, v2n, v2w, spt (lookup, insert, domain), num_set.
- Prelude.Sort: sort2_tail, sort3_tail, merge_tail, mergesortN_tail, mergesort_tail.
- Misc (`Candle.Misc`): the, app_list, append_aux, append, SmartAppend, max3, UPDATE_LIST, find_index, splitlines, is_subseq, make_even, fmap_update.
- Mllist: sort, mapi, partition_aux, partition, foldl, foldli_aux, collate, LENGTH_AUX, map_rev', filter_rev', flat_rev'.
- Mlstring: mlstring, strlen, strsub, substring, concat, explode_aux, explode, extract, strcat, translate_aux, splitl_aux, tokens_aux, tokens, tokens_alt_aux, fields_aux, fields, fields_alt_aux, isStringThere_aux, compare_aux, collate_aux, collate, app_list_ann, sum_sizes, size_limit, make_app_list_ann, shrink, str_app_list_opt, char_to_word8, word8_to_char.
- SetSpec: extensional, is_separation, is_power, is_union, is_upair, is_set_theory, sub, power, union, upair, empty, one, two, pair, binary_union, product, relspace, funspace, apply, boolset, boolean, abstract.
- HolSyntaxLib: ALPHAVARS, REV_ASSOCD, result, IS_RESULT, IS_CLASH, RESULT, CLASH, LIST_INSERT, LIST_UNION, INORDER_INSERT, STRING_SORT.
- HolSyntax: type, term, Fun, domain, codomain, dest_var, has_type, welltyped, typeof, RACONV, ACONV, type_lt, type_llex, term_lt, term_cmp, type_cmp, ordav, orda, term_union, term_remove, term_image, VFREE_IN, CLOSED, VARIANT_PRIMES, VARIANT, TYPE_SUBST, is_instance, VSUBST, sizeof, INST_CORE, INST, tyvars, tvars, equation, tysig, tmsig, sig, thy, type_ok, term_ok, alpha_lt, hypset_ok, is_std_sig, theory_ok, proves, update, types_of_upd, consts_of_upd, type_list, const_list, axexts_of_upd, conexts_of_upd, axexts, conexts, axioms_of_upd, axiom_list, thyof, updates.
- HolSyntaxExtra: subtype1, subtype, subterm1, subterm, DbTerm, bind, db, dbVSUBST, dbVFREE_IN, dbINST, dbterm, bind_list_aux, bv_names, simple_subst, simple_inst, rename_bvars, fresh, fresh_term, vfree_in, variant, subtract, insert, itlist, union, frees, ConstDef, types_in, arities_match.
- HolSemantics: inhabited, tyass, is_type_assignment, tyval, is_type_valuation, typesem, tmass, is_term_assignment, tmval, is_term_valuation, interpretation, tyaof, tmaof, valuation, tyvof, tmvof, is_valuation, instance_, termsem, satisfies, is_interpretation, is_std_type_assignment, interprets, is_std_interpretation, models, entails, is_structure.
- HolSemanticsExtra: Equalsem. HolSoundness: nothing (empty namespace).

## Renames
`instance` -> `instance_`; `datatype dbterm` -> `DbTerm` (the function `dbterm` keeps its name); `Bool` (type constant) -> `BoolTy`; set-theory `true`/`false` -> `mtrue`/`mfalse`; `toString` -> `chr_to_str`; mlstring `compare` -> `mlstring_compare`; `set` (list to set) -> `HOL.LIST_TO_SET`; `Unit` -> `unit`; `X0 ^mem` -> `X mem`. Helper (not HOL4) names: `TYPE_SUBST_list`, `tyvars_list`, `type_ok_list`, `typesem_list` (+ `_eq` lemmas), `REV_ASSOCD_var_helper`, `sizeof_VSUBST_helper`, `variant_fvlen/_bound` (+ `_spec`), `strlen_strcat_prime_helper`, `MEM_iff/MEM_nil/MEM_cons/MEM_FILTER`, `FMap.ext`, `hchar`, `hstr`, `ml`.

## Type mappings
- `bool` = `Prop` (classical decidability from `open Classical`). Functions into bool are `-> Prop`.
- `num` = `Nat`; `int` = `Int`. Lean `/`, `%` conventions (`x/0 = 0`, `x%0 = x`).
- `'a set` = `HOL.Set a := a -> Prop`; `{x | p}` macro; instances Membership, EmptyCollection, Insert, Singleton, Union, Inter, SDiff, HasSubset. `FINITE s` = "s contained in some list".
- `('a,'b) fmap` = structure `HOL.FMap a b` (field `lookup : a -> Option b` + finite-support proof). Scoped `|+` is FUPDATE.
- `char` = structure `HOL.char` (val < 256), `ORD`, `CHR`; `string = List char`. Use `hchar 'a'`, `hstr "abc"` for literals.
- `mlstring` = single-constructor inductive (`implode`, alias `strlit`); `ml "abc"` for literals.
- `'a option` = `Option`; pairs = `Prod`; lists = `List`; `ordering` = `Ordering`.
- `word8`/`word32` = `BitVec 8`/`BitVec 32`; `n2w`, `w2n`, `v2w` provided.
- `'U` in set theory/semantics: carrier type `U` with explicit `mem : U -> U -> Prop` first argument; `[Inhabited U]` where HOL4 uses ARB or `@`.
- Type abbreviations are Lean `abbrev`.

## Notation
Scoped: `##` (PAIR_MAP), `=+` (UPDATE), `=++` (UPDATE_LIST), `|+` (FUPDATE), `===` (equation), `|-` (proves).

## Overloads
`tysof`, `tmsof`, `sigof`, `axsof` are classes `TysOf`, `TmsOf`, `SigOf`, `AxsOf` with instances for `sig`, `thy`, `List update` (as in HOL4). `^` on mlstring = `strcat`. No `<`/`<=` overloads on mlstring (use `mlstring_lt`).

## Modelling choices / deviations
- ARB = `default` via `[Inhabited _]`; `@` = `Classical.epsilon` or `Classical.choose` with dite default (sound: HOL4 theorems hold for all choices of unspecified values).
- Unspecified: `HD []`, `LAST []`, `EL` out of range, `FAPPLY` outside domain, `dest_var` of non-var are `default`; `TL [] = []`; `SEG` out of range `[]`; `RESULT (Clash t) = t`, `CLASH (Result t) = t`; `CHR n` for n >= 256 is `CHR 0`; `FUN_FMAP` on infinite set is `FEMPTY`; `termsem` on `Abs` of non-`Var` is `default`; `instance_` default is `tmaof i name []`; `sub`, `power`, `union`, `upair` use dite with default; `fresh`/`fresh_term` use epsilon over their spec; `VARIANT_PRIMES` uses `LEAST` (epsilon-based).
- ZIP truncates.
- Nested inductives (`type` with `Tyapp` list): mutual list functions `*_list` with equality lemmas to the `MAP`/`FOLDR`/`EVERY` forms.
- `type_lt` is a mutual inductive with `type_llex` (= `LLEX type_lt`); `LEX` unfolded in `term_lt`.
- Termination: `orda`, `INST_CORE` (via `sizeof_VSUBST_helper`), `FIELDS`, `n2l` by WF recursion with real proofs; `variant` uses measure `variant_bound`; `mergesortN_tail` has overlapping clauses, last applies for n >= 4. No `sorry` anywhere.
