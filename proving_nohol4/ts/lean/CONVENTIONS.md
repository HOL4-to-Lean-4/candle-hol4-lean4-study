# Conventions for stage 2 (theorem statements)

## 1. File header and namespaces

Every definition is in the namespace `CmlTS` (exceptions in section 3). Add the theorems of a
HOL4 theory to the Lean module of that theory, after the definitions, inside
`namespace CmlTS`, with

```lean
noncomputable section
open scoped Classical
```

(already at the top of each module). `open scoped Classical` makes every proposition decidable,
so `if` and `decide` work on any proposition, as in HOL4. Do not use the tactic/term `decide`
to *prove* things in these files; the instances are classical.

Imports between modules follow the HOL4 `Ancestors`; `import CmlTS` imports everything.
Library constants are in `CmlTS/Prelude/*.lean`.

## 2. How HOL4 types and notation map

| HOL4 | Lean |
|---|---|
| type variable `'a` | `{α : Type}` (universe 0) |
| `num` | `Nat` (`-` truncated, `DIV`/`MOD` = `/`,`%`; `SUC n` = `n + 1`) |
| `int` | `Int`; `&n` = `int_of_num n` (= `(n : Int)`) ; `/` = `int_div`, `%` = `int_mod` |
| `real` | `CmlTS.real` (only used by the floating-point prelude) |
| `bool` as a proposition (any formula, any function that *returns* `bool`) | `Prop` |
| `bool` as *data*: an argument of a function or constructor (`Loc b n`, `Boolv b`, `Eq_val b`, `type_d checks ..`, flags) | `Bool`; `T`/`F` = `true`/`false` |
| proposition used as `bool` data, e.g. `Eq_val (b = b')` | `Eq_val (decide (b = b'))` |
| `bool` data used as a proposition | `b = true` |
| `=` or `⇔` between formulas | `↔` |
| `char` | `char` = `Fin 256`; `ORD`, `CHR` (`CHR n` is `ARB` for n ≥ 256) |
| `string` | `string` = `List char` |
| `"abc"` | `str!"abc"` |
| `mlstring`, `strlit s` | `mlstring`, `strlit s` |
| `«abc»` | `ml!"abc"` (e.g. `«'a»` = `ml!"'a"`) |
| `'a word`, `word8`, `word64`, `5w` | `BitVec n`, `word8`, `word64`, `n2w 5` |
| `'a option`, `NONE`, `SOME x` | `Option α`, `none`, `some x` |
| `'a # 'b`, `FST`, `SND` | `α × β`, `Prod.fst`/`.1`, `Prod.snd`/`.2` |
| `λ(x,y). e` | `fun (x, y) => e` |
| `'a + 'b`, `INL`, `INR` | `α ⊕ β`, `Sum.inl`, `Sum.inr` |
| `unit`, `()` | `Unit`, `()` |
| `'a list`, `[]`, `x::xs`, `[a;b]` | `List α`, `[]`, `x :: xs`, `[a, b]` |
| `'a set` (`'a -> bool` as a set) | `Set α` (a `def` for `α → Prop`) |
| `('k,'v) fmap`, `'k \|-> 'v` | `fmap κ ν` |
| `'a llist` | `llist α` |
| `'a spt` | `spt α` |
| `('m,'n) id` | `ident m n` |
| `('m,'n,'v) namespace` | `Namespace m n v` |
| `v` (semantic values) | `value` |
| `t` (types of the type system) | `typ` |
| `ordering` | `ordering` (`ordering.LESS`, `.EQUAL`, `.GREATER`) |
| `f o g` | `f ∘ g` |
| `s with fld := e`, `<\|f := a\|>` | `{ s with fld := e }`, `{ f := a }` (add a type ascription if needed) |
| `case e of ...` | `match e with ...` |
| `let x = e in b` | `let x := e; b` |
| `∀(p,e)::set l. P` (RES_FORALL) | `∀ p e, (p, e) ∈ l → P` |
| `@x. P x` | `select (fun x => P x)` |
| `ARB` | `ARB` |

Free variables of a HOL4 theorem are universally quantified: make them binders of the Lean
theorem. HOL4 types are nonempty, Lean types need not be: where a statement uses `EL`, `HD`,
`THE`, `FAPPLY`, `nth`, `lookup_vars`, `dest_Refv` or `ARB` at a type variable `α`, add
`[Nonempty α]` (both components for a pair type). No other typeclass argument is needed, in
particular no `DecidableEq`.

### Unspecified values

HOL4 functions with missing cases, `HD []`, `THE NONE`, `CHR n` (n ≥ 256), `FAPPLY` outside the
domain, `int_div`/`int_mod` by 0 give `ARB`, defined as `Classical.choice` (an unknown element
of the type). `CARD` of an infinite set, `real.sqrt` of a negative real and `float_some_qnan` use
Hilbert choice (`select`, i.e. `Classical.epsilon`). No `opaque` is used.

### Lists: HOL4 constant -> Lean core function

`LENGTH l` `l.length`; `MAP f l` `l.map f`; `l1 ++ l2` same; `REVERSE l` `l.reverse`;
`FLAT l` `l.flatten`; `FOLDR f e l` `l.foldr f e`; `FOLDL f e l` `l.foldl f e`;
`TAKE n l` `l.take n`; `DROP n l` `l.drop n`; `ZIP (a,b)` `a.zip b` (truncates, as in HOL4);
`MAP2 f a b` `List.zipWith f a b` (truncates, as in HOL4); `REPLICATE n x` `List.replicate n x`;
`MEM x l` `x ∈ l`; `set l` `LIST_TO_SET l` (`x IN set l` may be written `x ∈ LIST_TO_SET l`,
which unfolds to `x ∈ l`).

Own definitions, same name and argument order as HOL4 (module `Prelude/ListLib`):
`NULL HD TL EL oEL LUPDATE EVERY EXISTS LIST_REL ALL_DISTINCT isPREFIX IS_PREFIX REV SPLITP
COUNT_LIST ALOOKUP`. `EVERY2` is `LIST_REL`. `a ≼ b` (`<<=`) is `isPREFIX a b`;
`IS_PREFIX a b` is `isPREFIX b a`.

### Sets (module `Prelude/PredSet`)

`x ∈ s`, `s ⊆ t`, `s ∪ t` (`UNION`), `s ∩ t` (`INTER`), `s \ t` (`DIFF`), `∅`, `{x}`,
`insert x s` (`INSERT`), `UNIV`, `IMAGE f s`, `DISJOINT s t`, `FINITE s`, `CARD s`, `INJ SURJ BIJ`,
`BIGUNION`, `LIST_TO_SET l`; `{x | P x}` is `setOf (fun x => P x)`. Equality of sets is `=`.
Precedence: in HOL4 `UNION` and `DIFF` are both left-associative at level 500, so `a ∪ b DIFF c`
is `(a ∪ b) DIFF c`; in Lean `\` binds tighter than `∪`. Always parenthesize. `a DIFF b ⊆ c`
is `(a \ b) ⊆ c`.

### Finite maps (module `Prelude/FiniteMap`)

`FEMPTY`, `FUPDATE f (k, v)` (`f |+ (k,v)`), `FUPDATE_LIST f l` (`f |++ l`), `FLOOKUP f k`,
`FAPPLY f k` (`f ' k`), `FDOM f`, `FRANGE f`, `FUNION f g` (`f ⊌ g`), `SUBMAP f g` (`f ⊑ g`),
`FEVERY P f`, `o_f g f` (`g o_f f`; `(SND o SND) o_f m` is `o_f (Prod.snd ∘ Prod.snd) m`),
`alist_to_fmap l`. `|++` and `⊌` are both left-associative at level 500 in HOL4:
`m |++ a1 |++ a2 = FEMPTY |++ a2 ⊌ (m |++ a1)` is
`FUPDATE_LIST (FUPDATE_LIST m a1) a2 = FUNION (FUPDATE_LIST FEMPTY a2) (FUPDATE_LIST m a1)`.

## 3. Names that differ from HOL4

Anything not listed here has the identical name in `CmlTS`.

### Types

| HOL4 type | Lean | module |
|---|---|---|
| `id` (namespace) | `ident` | Namespace |
| `namespace` | `Namespace` | Namespace |
| `v` (semanticPrimitives) | `value` | SemanticPrimitives |
| `t` (typeSystem) | `typ` | TypeSystem |
| `thunk_op` (ast; the constant `thunk_op` keeps its name) | `thunk_op_t` | Ast |
| `fp_cmp` (fpSem; the constant `fp_cmp` keeps its name) | `fp_cmp_t` | FpSem |
| `float_value`, `float_compare` (binary_ieee) | `float_value_t`, `float_compare_t` | Prelude/BinaryIeee |
| `'a store` (abbreviation) | `store_ty α` | SemanticPrimitives |
| `('ffi,'v) store_ffi` (abbreviation) | `store_ffi ffi V` | SemanticPrimitives |
| `ctMap` (abbreviation) | `ctMap_ty` | TypeSoundInvariants |

Other abbreviations keep their names: `alist modN varN conN typeN tvarN type_def num_set num_map
oracle_function oracle env_ctor env_val compiler_args compiler_fun eval_oracle_fun type_ident
tenv_abbrev tenv_ctor tenv_val tenv_store`. `sem_env value` is HOL4 `v sem_env`; `state ffi` is
`'ffi state` (`semanticPrimitives$state`); `result α β` is `('a,'b) result`.

### Constants

| HOL4 | Lean | module |
|---|---|---|
| `mllist$sort`, `mllist$nth`, `mllist$collate` | `mllist.sort`, `mllist.nth`, `mllist.collate` | Mllist |
| `mlstring$concat`, `str`, `compare`, `collate` | `mlstring.concat`, `.str`, `.compare`, `.collate` | Mlstring |
| `<`, `<=`, `>`, `>=` on mlstring | `mlstring_lt`, `mlstring_le`, `mlstring_gt`, `mlstring_ge` | Mlstring |
| `<` on char | `char_lt` | Prelude/StringLib |
| `s1 ^ s2` | `strcat s1 s2` | Mlstring |
| `sptree$toList` | `spt_toList` | Prelude/Sptree |
| `llist$toList` | `llist_toList` | Prelude/LList |
| `f =++ l` | `UPDATE_LIST f l` | Misc |
| `env1 +++ env2` | `extend_dec_env env1 env2` | SemanticPrimitives |
| `R^*` | `RTC R` | Prelude/Core |
| `ABS` (int) | `INT_ABS` | Prelude/Words |
| `UINT_MAXw` | `word_T` | Prelude/Words |
| `w1 ?? w2`, `&&`, `\|\|`, `<=+`, `@@` | `word_xor`, `word_and`, `word_or`, `word_ls`, `word_concat` | Prelude/Words |
| `sem_env_v env`, `sem_env_c env` | `env.v`, `env.c` | SemanticPrimitives |
| `locn` fields `.row`, `.col` | `locnrow`, `locncol` | Location |
| `real` operations | `+ - * / ≤ <` on `real`; `real.abs`, `real.inv`, `real.pow`, `real.sqrt`, `real.ofNum` | Prelude/Real |
| `$+ 0` | `fun x => 0 + x` | |
| `SUC` as a function | `Nat.succ` | |

### Constructors

A constructor lives in the namespace of its type. These are exported, so the bare HOL4 name
works (in terms and in patterns):
`UNKNOWNpt EOFpt POSN Locs strlit FFI_failed FFI_diverged Oracle_return Oracle_final MappedRead
MappedWrite ExtCall SharedMem IO_event Final_event FFI_return FFI_final Success Resource_limit_hit
FFI_outcome Diverge Terminate Fail Short Long W8 W64 Evaluated NotEvaluated AllocThunk UpdateThunk
ForceThunk BoolT IntT CharT StrT WordT Float64T`, all constructors of `op` (`Opapp`, `Arith`,
`Test`, `FFI`, `Eval`, ...), of `op_class`, `ast_t`, `pat`, `lop`, `dec`,
`TypeStamp ExnStamp Litv Conv Closure Recclosure Loc Vectorv Env Rtype_error Rtimeout_error
Rffi_error Rraise Rabort Rval Rerr Refv W8array Varray Thunk EvalDecs EvalOracle No_match
Match_type_error Match Eq_val Eq_type_error Exp Val BadRef NotThunk IsThunk Tvar Tvar_db Tapp
Bind_tvar Bind_name Ref_t W8array_t Varray_t`.

These must be qualified (they would clash with Lean or with each other):
`exp.Raise exp.Handle exp.Lit exp.Con exp.Var exp.Fun exp.App exp.Log exp.If exp.Mat exp.Let
exp.Letrec exp.Tannot exp.Lannot`; `lit.IntLit lit.Char lit.StrLit lit.Word8 lit.Word64
lit.Float64`; `arith.Add` ... `arith.FMA`; `shift.Lsl` ...; `opb.Lt opb.Gt opb.Leq opb.Geq`;
`test.Equal test.Compare test.AltCompare`; `tenv_val_exp.Empty`; `Namespace.Bind`;
`app_list.List` ...; `app_list_ann.BigList` ...; `spt.LN` ...; `ordering.LESS` ...;
`fp_cmp_t.*`, `fp_uop.*`, `fp_bop.*`, `fp_top.*`, `rounding.*`.

Beware of variables that shadow a name: after a binder `(op : op)`, `op.Opapp` is a field access
on the variable (write `Opapp`), and similarly for variables named `test`, `stamp`, `result`,
`state`, `value`, `exp`, `pat`, `dec`. If needed write `CmlTS.op` etc.

## 4. Inductive relations

`type_p`/`type_ps`, `type_e`/`type_es`/`type_funs`, `type_d`/`type_ds` and `type_v` have the HOL4
name and argument order. Arguments of `type_d`/`type_ds`: `Bool` (extra checks: HOL4 `F` is
`false`), `type_env`, `dec` / `List dec`, `Set type_ident`, `type_env`.
Lean does not allow a recursive occurrence under `∃`, `LIST_REL`, `EVERY` or `nsAll2` here, so:

* `type_e.handle`, `type_e.mat`: the `? bindings` is a choice function on the elements of `pes`.
  HOL4 forms: `type_e_Handle_aux`, `type_e_Mat_aux` (rules), `type_e_Handle_inv_aux`,
  `type_e_Mat_inv_aux` (inversion), proved in `TypeSystem`.
* `type_v`: `LIST_REL R vs ts` is equal lengths plus `R` at each index, `EVERY P vs` is `P` on all
  members, `nsAll2 R e1 e2` is `nsAll2 (fun _ _ _ => True) e1 e2` plus `R` on the values found at
  each identifier. HOL4 forms: `type_v_{conv,tup,closure,recclosure,vector}_aux` (rules) and
  `..._inv_aux` (inversions), proved in `TypeSoundInvariants`.

Statements never need the constructors of these relations.

## 5. Recursive functions

* Conjoined HOL4 definitions are Lean `mutual` blocks with all the HOL4 names:
  `pat_bindings`/`pats_bindings`, `pmatch`/`pmatch_list`, `do_eq`/`do_eq_list`,
  `concrete_v`/`concrete_v_list`, `FV`/`FV_list`/`FV_pes`/`FV_defs`,
  `evaluate`/`evaluate_match`/`evaluate_decs`.
* `evaluate` is the HOL4 `Definition` (with `fix_clock`); HOL4's cleaned-up equations are a theorem.
  `fix_clock` takes `s` and `s'` with possibly different 'ffi types, as in HOL4.
* `nsSub_compute` uses an auxiliary `alistSub_attach` for termination; the HOL4 equation is
  `nsSub_compute_def_aux`.
* `every_exp` and similar functions use `fun pe => f pe.2` for HOL4's `λ(p,e). f e`.
* `lookup` (sptree) pushes the recursive call into the branches of `if EVEN k`.
* All termination proofs are real proofs; there is no `sorry` anywhere.

## 6. Encodings of library types

* `fmap`: option-valued functions with finite support (HOL4: closure of the empty map under
  update). `FEVERY`, `FRANGE`, `SUBMAP`, `FUNION`, `o_f` are stated with `FLOOKUP`, equivalent to
  the HOL4 definitions and free of `Nonempty` arguments.
* `llist`: functions `Nat → Option α` that stay `none` once `none` (HOL4's `lrep_ok`).
* `CARD`: length of a duplicate-free enumeration, by Hilbert choice.
* `int_div`/`int_mod`: `Int.fdiv` / `i - i/j*j` for j ≠ 0.
* `'a word`: `BitVec n`; HOL4 has n ≥ 1, `BitVec 0` is extra. Only `word1`, `word8`, `word64` and the
  widths 11 and 52 occur, except in the polymorphic `shift_lookup`.
* `word_lsl`, `word_lsr`, `word_asr`, `word_ror`, `word_and`, ... are the `BitVec` operations;
  `word_ls` is `≤` on `w2n`.
* `real`: Dedekind cuts of `Rat`, operations with proofs that the sets are cuts; `sqrt` by Hilbert
  choice as in HOL4. `binary_ieee` and `machine_ieee` (fp64) are translated from HOL4 definition
  by definition, including the flags; type arguments `(:'t # 'w)` are the numbers `t w`.

## 7. Notes on particular targets

* `do_app_cases` (semanticPrimitivesProps) and `type_op_cases` (typeSysProps) have no written
  statement in HOL4: they are computed by simplification of `do_app (s,t) op vs = SOME (st',v)`
  and `type_op op ts t3`. State an equivalence between that formula and the disjunction of the
  cases of the definition (existentially quantified).
* Duplicate theorem names within a theory: `EVERY_LIST_REL` (typeSound lines 50 and 1297) and
  `tveLookup_freevars` (typeSysProps lines 624 and 731). Name the second `EVERY_LIST_REL_2` /
  `tveLookup_freevars_2`.
* Theorem names equal to a definition's name: `type_subst` (typeSysProps 1810) and
  `concrete_v_list` (semanticPrimitivesProps 228). Name the theorems `type_subst_thm` and
  `concrete_v_list_thm`.
* Records: `with_same_v`, `unchanged_env` are about `sem_env`; `unchanged_tenv` about `type_env`;
  `v_unchanged` (typeSound 57) has an unannotated `tenv with v := tenv.v`: in that context the field
  `v` of the last-declared record applies, `type_env`.
* Helper lemmas in the definition files end in `_aux` (or are `EVERY_iff_forall`, `EVERY_wfParam`,
  `EVERY_unattach`, `isCut_*`); they are not HOL4 theorems, do not count them as targets.

## 8. Modules and their names

* `Prelude/Core`: `ARB select I K C UPDATE UNCURRY THE RTC ordering`
* `Prelude/PredSet`: `Set setOf EMPTY UNIV INSERT SUBSET UNION INTER DIFF DISJOINT IMAGE INJ SURJ
  BIJ FINITE CARD BIGUNION LIST_TO_SET`
* `Prelude/ListLib`: see section 2
* `Prelude/FiniteMap`: see section 2
* `Prelude/LList`: `llist LNIL LCONS LHD LTL LTAKE LFINITE llength_rel LLENGTH llist_toList
  fromList LPREFIX`
* `Prelude/Sptree`: `spt lookup domain toListA spt_toList`
* `Prelude/Mergesort`: `sort2_tail sort3_tail merge_tail mergesortN_tail mergesort_tail`
* `Prelude/StringLib`: `char string ORD CHR char_lt TOKENS`, macro `str!`
* `Prelude/Words`: `int_of_num Num INT_ABS int_div int_mod word8 word64 dimword INT_MIN UINT_MAX
  INT_MAX w2n n2w w2w word_T word_1comp word_and word_or word_xor word_lsb word_msb word_2comp
  word_add word_sub word_ls word_lsl word_lsr word_asr word_ror word_bits word_extract word_join
  word_concat i2w`
* `Prelude/Real`: `real` and `real.*`
* `Prelude/BinaryIeee`: `float float_value_t float_to_real float_value float_is_* float_negate
  float_abs float_plus_* float_minus_* float_top float_bottom flags clear_flags invalidop_flags
  dividezero_flags rounding is_closest closest_such closest largest threshold round fp_op
  float_some_qnan float_round float_round_with_flags check_for_signalling float_sqrt float_add
  float_sub float_mul float_div float_mul_add float_compare_t float_compare float_less_than
  float_less_equal float_greater_than float_greater_equal float_equal fp64_*`
* `Misc`: `the app_list append_aux append MAP3 tlookup max3 num_set num_map UPDATE_LIST find_index
  between lookup_vars enumerate range`
* `Mllist`: `mllist.sort mllist.nth mllist.collate`
* `Mlstring`: `mlstring implode strlen strsub mlstring.concat explode_aux explode strcat
  mlstring.str tokens_aux tokens isStringThere_aux isSubstring_aux isSubstring compare_aux
  mlstring.compare mlstring_lt mlstring_le mlstring_gt mlstring_ge collate_aux mlstring.collate
  app_list_ann char_to_word8 word8_to_char empty_ffi`, macro `ml!`
* `Location`: `locn locnrow locn_rowupdate locncol locn_colupdate locs`
* `LprefixLub`: `lprefix_lub`
* `Ffi`: `ffi_outcome oracle_result shmem_op ffiname oracle_function oracle io_event final_event
  ffi_state ffi_result call_FFI outcome behaviour`
* `FpSem`: `fp_cmp_t fp_uop fp_bop fp_top fp_cmp`
* `Namespace`: `alist ident Namespace mk_id id_to_n id_to_mods nsLookup nsLookupMod nsEmpty nsAppend
  nsLift alist_to_ns nsBind nsBindList nsOptBind nsSing nsSub nsAll nsAll2 nsDom nsMap`
* `NamespaceProps`: `alist_rel_restr alistSub nsSub_compute`
* `Ast`: `lit shift arith modN varN conN typeN tvarN word_size thunk_mode thunk_op_t opb test
  prim_type op op_class getOpClass ast_t pat lop exp type_def dec pat_bindings pats_bindings
  every_exp`
* `SemanticPrimitives`: `stamp sem_env value env_ctor env_val bind_stamp chr_stamp div_stamp
  subscript_stamp bind_exn_v chr_exn_v div_exn_v sub_exn_v bool_type_num list_type_num abort
  error_result result store_v store_v_same_type store_ty store_lookup store_alloc store_assign
  compiler_args compiler_fun eval_decs_state eval_oracle_fun eval_oracle_state eval_state state
  do_con_check one_con_check build_conv lit_same_type match_result same_type same_ctor
  ctor_same_type Boolv pmatch pmatch_list can_pmatch_all build_rec_env find_recfun eq_result do_eq
  do_eq_list do_opapp v_to_list list_to_v v_to_char_list vs_to_string nat_to_v maybe_all_list
  v_to_word8 v_to_word8_list v_to_word64 v_to_word64_list lookup_env add_decs_generation
  add_env_generation declare_env concrete_v concrete_v_list compiler_agrees do_eval
  reset_env_generation copy_array ws_to_chars chars_to_ws shift8_lookup shift64_lookup exp_or_val
  store_ffi xor_bytes thunk_op check_type dest_Litv the_Litv_IntLit the_Litv_Word8 the_Litv_Word64
  the_Litv_Float64 the_Litv_Char the_Boolv num_cmp int_cmp do_test do_arith do_conversion do_app
  do_log do_if build_constrs build_tdefs check_dup_ctors combine_dec_result extend_dec_env
  dest_thunk_ret dest_thunk update_thunk`
* `SemanticPrimitivesProps`: `shift_lookup map_error_result map_result every_error_result
  every_result map_sv dest_Refv store_v_vs ctors_of_tdef FV FV_list FV_pes FV_defs FV_dec`
* `Evaluate`: `fix_clock dec_clock do_eval_res list_result evaluate evaluate_match evaluate_decs`
* `EvaluateProps`: `call_FFI_rel dest_IO_event io_events_mono is_clock_io_mono adj_clock`
* `SemanticsMin`: `evaluate_prog_with_clock semantics_prog`
* `TypeSystem`: `type_ident typ T*_num prim_type_nums Tarray Tbool Tchar Texn Tfn Tint Tlist Tref
  Tstring Ttup Tvector Tword64 Tword8 Tword8array Tdouble check_freevars check_freevars_ast
  type_subst deBruijn_inc deBruijn_subst tenv_val_exp bind_tvar opt_bind_name tveLookup tenv_abbrev
  tenv_ctor tenv_val type_env extend_dec_tenv lookup_varE lookup_var num_tvs bind_var_list t_of
  supported_test supported_arith supported_conversion type_op check_type_names type_name_subst
  check_ctor_tenv build_ctor_tenv is_value type_p type_ps type_e type_es type_funs tenv_add_tvs
  type_pe_determ tscheme_inst tenvLift type_d type_ds tscheme_inst2 weak_tenv`
* `TypeSoundInvariants`: `store_t tenv_store tenv_abbrev_ok tenv_ctor_ok tenv_val_ok tenv_ok
  tenv_val_exp_ok ctMap_ty ctMap_ok type_ctor add_tenvE type_v type_sv type_s ctMap_has_exns
  ctMap_has_lists ctMap_has_bools good_ctMap consistent_ctMap type_all_env type_sound_invariant`
* `TypeSysProps`: `type_pes deBruijn_subst_tenvE db_merge type_def_to_ctMap`
* `Weakening`: `weak_tenvE weakS weak weakCT`
* `TypeSound`: `store_type_extension`
