# Conventions for the HOL4 -> Lean 4 translation of CakeML `typeSound`

This file is for the writers of the 267 theorem statements (stage 2).
Every definition, datatype, inductive relation, type abbreviation and library constant needed by the
statements is already in `lean/CmlTS/**`.  The text of the original HOL4 definition is in a
`/- HOL4: ... -/` comment above each Lean declaration.

## 0. How to write a file that uses the definitions

```lean
import CmlTS            -- or the specific CmlTS.* modules (see section 8)
universe u v w
noncomputable section
open Classical          -- needed so that `if p then .. else ..` works for arbitrary Props
```

* There is **no** global `open` of the datatype namespaces (constructors such as `And`, `Add`, `Not`,
  `Sub`, `Char`, `List`, `Empty`, `Lit` clash with Lean).  Constructors are always written
  qualified by the name of their datatype: `exp.Lit`, `lit.IntLit`, `Value.Litv`, `arith.Add`, ...,
  or with the dot-shorthand `.IntLit n` when the expected type is known.
* Lean `namespace`s used by the translation: the datatype names (for constructors), `sptree`,
  `mlstring` (functions `compare`, `compare_aux`, `collate`, `collate_aux`), `mllist` (`collate`),
  `llist` (`llist.toList`), `FMap`, `Set`, `RealX`.  Every other constant is in the root namespace and
  has the name given in section 3 (HOL4 name when there is no entry).
* Each HOL4 `Datatype`/record becomes a Lean `inductive`/`structure`.  Record fields: `env.v`, `env.c`
  (HOL4 `sem_env_v env`, `sem_env_c env`), `st.clock`, `st.refs`, `st.ffi`, `st.next_type_stamp`,
  `st.next_exn_stamp`, `st.eval_state`, `tenv.v`, `tenv.c`, `tenv.t`, `ffi.oracle`, `ffi.ffi_state`,
  `ffi.io_events`.  Record update `r with f := x` is `{ r with f := x }`; the HOL4 record literal
  `<| v := a; c := b |>` is `⟨a, b⟩` (fields in HOL4 declaration order: `sem_env`: `v`, `c`;
  `type_env`: `v`, `c`, `t`) or `{ v := a, c := b }`.

## 1. Types

| HOL4 | Lean | notes |
|---|---|---|
| `bool` | `Prop` | **always**, also when used as data (`Eq_val`, `Loc`, `Boolv`, `extra_checks`, `Thunk` ...). `T`/`F` are `True`/`False`. HOL4 `if b then x else y` is Lean `if b then x else y` (needs `open Classical`). Boolean connectives `/\ \/ ~ ==> =` are `∧ ∨ ¬ → =`/`↔` (HOL4 `=` on bool is `=` on `Prop`, equivalent to `↔`). |
| `num` | `Nat` | `n - m` truncated, `DIV`/`MOD` = `/`,`%` (`n DIV 0 = 0` in Lean, unspecified in HOL4) |
| `int` | `Int` | `&n` is `int_of_num n` (`(n : Int)`) ; `~i` is `-i`; `i / j` is `int_div i j`, `i % j` is `int_mod i j` (floor division, `ARB` at 0); `Num i`, `ABS i` are `Num i`, `ABS i`; `I` is `id` |
| `char` | `char` (structure, 256 elements; `.val`, `ORD c`) | `CHR n` unspecified (ARB) for `n >= 256`.  `c1 < c2` is `ORD c1 < ORD c2` (instances `LT char`, `LE char`) |
| `string` (`char list`) | `string` (= `List char`) | Lean `String` literals are converted with `HOLstr "abc"` |
| `mlstring` | `mlstring` (constructor `mlstring.strlit`) | `«foo»` is `mlstr "foo"` (`mlstr : String → mlstring`); `«»` is `mlstr ""` |
| `'a list` | `List α` | `[x; y]` is `[x, y]`, `h::t` is `h :: t`, `l1 ++ l2` is `l1 ++ l2` |
| `'a option` | `Option α` | `SOME x`/`NONE` are `some x`/`none` |
| `'a # 'b` | `α × β` | `(a,b,c)` is `(a, b, c)`; `FST`/`SND` are available as `FST`,`SND` (or `.1`,`.2`) |
| `unit` | `Unit` | |
| `'a + 'b` (`INL`/`INR`) | `Sum α β` (`Sum.inl`/`Sum.inr`) | used by `do_arith`, `do_conversion` |
| `'a set` | `Set α` (`def Set α := α → Prop`) | membership `x ∈ s`, `∅` (`{}`), `{a}`, `insert a s` (`a INSERT s`), `s ∪ t` (`UNION`), `s ∩ t`, `s ⊆ t` (`SUBSET`), `DIFF s t`, `DISJOINT s t`, `IMAGE f s`, `BIGUNION P`, `UNIV` (`𝕌(:'a)`), `FINITE s`, `CARD s`, `BIJ f s t`, `INJ`, `SURJ`.  `{x | P x}` is `setOf (fun x => P x)` (or just `fun x => P x`).  `set l` (`LIST_TO_SET l`) is `LIST_TO_SET l`; `MEM x l` is `MEM x l`. `(∀(p,e)::set pes. P p e)` (RES_FORALL) is `∀ p e, (p, e) ∈ LIST_TO_SET pes → P p e`. |
| `('a,'b) fmap` | `FMap α β` | finite partial functions; `FEMPTY`, `FLOOKUP f x`, `FDOM f : Set α`, `FAPPLY f x` (`f ' x`, needs `Nonempty β`), `FUPDATE f (k,v)` (`f |+ (k,v)`), `FUPDATE_LIST f l` (`f |++ l`), `FUNION f g` (`f ⊌ g`), `FRANGE f : Set β`, `FEVERY P f` (`P : α × β → Prop`), `o_f f m` (HOL4 `f o_f m`), `SUBMAP f g` (`f ⊑ g`), `alist_to_fmap l`.  Infix notations `|+`, `|++`, `⊌` (all `infixl:480`) and `⊑` (`infix:450`) exist, but **parenthesize explicitly** since HOL4 and Lean precedences differ; `o_f` has no infix notation (write `o_f f m`).  Extensionality: `FMap.ext`. |
| `'a word` | `BitVec n`; `word8 = BitVec 8`, `word64 = BitVec 64`, `word n = BitVec n` | `n2w k`, `w2n w`, `i2w i`, `word_add/sub/and/or/xor`, `word_lsl/lsr/asr/ror w k` (k : Nat) |
| `'a llist` | `llist α` | `fromList l`, `LPREFIX`, `LNIL`, `LNTH` ... (`Prelude/Coalg.lean`) |
| `'a spt` | `spt α` (`spt.LN/LS/BN/BS`) | `sptree.lookup k t`, `sptree.domain t`, `sptree.toList t`; `num_set = spt Unit`, `num_map α = spt α` |
| `real` | not available; see `RealX` (section 5) | only inside `Prelude/Float.lean` |
| `ordering` | `ordering` (`ordering.LESS/EQUAL/GREATER`) | |
| `('m,'n) id` | `Ident M N` | HOL4 `id` clashes with Lean's `id` |
| `('m,'n,'v) namespace` | `Namespace M N V` | `namespace` is a Lean keyword |
| `v` (CakeML value) | `Value` | |
| `t` (CakeML type) | `Ty` | |
| `'ffi state` | `state α` | |
| `fp_cmp` (datatype) | `fp_cmp_ty` | the function `fp_cmp` keeps its name |
| `float_value` (datatype), `float_compare` (datatype) | `float_value_ty`, `float_compare_ty` | functions keep their names |

All other datatypes keep their HOL4 name: `lit shift arith word_size thunk_mode thunk_op opb test
prim_type op op_class ast_t pat lop exp dec stamp sem_env abort error_result result store_v
eval_decs_state eval_oracle_state eval_state match_result eq_result exp_or_val dest_thunk_ret
store_t tenv_val_exp type_env locn locs ffi_outcome oracle_result shmem_op ffiname io_event
final_event ffi_state ffi_result outcome behaviour mlstring app_list app_list_ann spt llist`.
Type abbreviations keep their names: `modN varN conN typeN tvarN type_def env_ctor env_val store store_ffi
compiler_args compiler_fun eval_oracle_fun oracle_function oracle alist type_ident tenv_abbrev tenv_ctor
tenv_val ctMap tenv_store num_set num_map`.

Type parameters: `'a result 'b`: `result α β`; `store_v α`; `error_result α`; `match_result α`;
`state α`/`ffi_state α` (HOL4 `'ffi`).  `ffi_state`, `state`, `oracle_result`, `ffi_result` take a
`Type u` argument; use `{α : Type}` in statements.  Several functions need `[Nonempty β]`-style
instances for `HD`, `EL`, `FAPPLY`, `ARB`; instances exist for all CakeML types (`Value`, `Ty`,
`lit`, `exp`, `char`, `Int`, `Nat`, `word`, `store_v α`, `Set α`, lists, ...).

## 2. Constructors (all qualified by the datatype name)

HOL4 constructor `C` of datatype `T` is `T.C`; unchanged names.  Examples: `lit.IntLit`, `lit.Char`,
`lit.Word8`, `exp.Handle`, `exp.Lit`, `exp.Con`, `exp.Var`, `exp.App`, `exp.Letrec`, `pat.Pcon`,
`pat.Pany`, `dec.Dlet`, `op.Opapp`, `op.Arith`, `arith.Add`, `opb.Lt`, `test.Compare`,
`prim_type.WordT`, `word_size.W8`, `thunk_mode.Evaluated`, `thunk_op.ForceThunk`, `Value.Litv`,
`Value.Conv`, `Value.Closure`, `Value.Recclosure`, `Value.Loc`, `Value.Vectorv`, `Value.Env`,
`stamp.TypeStamp`, `stamp.ExnStamp`, `result.Rval`, `result.Rerr`, `error_result.Rraise`,
`error_result.Rabort`, `abort.Rtype_error`, `abort.Rtimeout_error`, `abort.Rffi_error`,
`store_v.Refv/W8array/Varray/Thunk`, `match_result.Match/No_match/Match_type_error`,
`eq_result.Eq_val/Eq_type_error`, `exp_or_val.Exp/Val`, `Ident.Short/Long`, `Namespace.Bind`,
`Option`: `some`/`none`, `Ty.Tvar/Tvar_db/Tapp`, `tenv_val_exp.Empty/Bind_tvar/Bind_name`,
`store_t.Ref_t/W8array_t/Varray_t`, `behaviour.Diverge/Terminate/Fail`, `outcome.Success/
Resource_limit_hit/FFI_outcome`, `eval_state.EvalDecs/EvalOracle`, `dest_thunk_ret.BadRef/NotThunk/IsThunk`,
`locn.POSN`, `locs.Locs`, `app_list.List/Append/Nil`.
HOL4 `Loc T n` is `Value.Loc True n`; HOL4 `Boolv T` is `Boolv True`.

## 3. Constants whose Lean name differs from HOL4, and where every constant lives

(Only differences are listed in the first table; the second table lists the modules.)

| HOL4 | Lean | module |
|---|---|---|
| `id` (type) | `Ident` | `CmlTS.Namespace` |
| `namespace` (type) | `Namespace` | `CmlTS.Namespace` |
| `t` (type) | `Ty` | `CmlTS.TypeSystem` |
| `v` (type) | `Value` | `CmlTS.SemanticPrimitives` |
| `fp_cmp` (datatype) | `fp_cmp_ty` | `CmlTS.FpSem` |
| `thunk_op` (the function of semanticPrimitives; the datatype `thunk_op` of `ast` is unchanged) | `thunk_op'` | `CmlTS.SemanticPrimitives` |
| `mlstring$compare`, `compare_aux`, `collate`, `collate_aux` | `mlstring.compare`, `mlstring.compare_aux`, `mlstring.collate`, `mlstring.collate_aux` | `CmlTS.Mlstring` |
| `mllist$collate` | `mllist.collate` | `CmlTS.Mllist` |
| `mlstring$^` (`x ^ y`) | `strcat x y` | `CmlTS.Mlstring` |
| `mlstring` overloads `<`,`<=` | instances `LT mlstring`, `LE mlstring` (= `mlstring_lt`, `mlstring_le`); `>`,`>=` are **not** overloaded: use `mlstring_gt`, `mlstring_ge` | `CmlTS.Mlstring` |
| `sptree$lookup`, `domain`, `toList`, `toListA` | `sptree.lookup`, `sptree.domain`, `sptree.toList`, `sptree.toListA` | `CmlTS.Prelude.Coalg` |
| `llist$toList` | `llist.toList` | `CmlTS.Prelude.Coalg` |
| `set l` | `LIST_TO_SET l` | `CmlTS.Prelude.List` |
| `UNION`, `INTER`, `SUBSET`, `INSERT`, `EMPTY` | `∪`, `∩`, `⊆`, `insert`, `∅`  (also `IN x s` = `x ∈ s`) | `CmlTS.Prelude.Basic` |
| `o` (composition) | `∘` | core |
| `I` | `id` | core |
| `C f` | `flip f` | core |
| `APPEND` / `++` | `++` | core |
| `FILTER`, `SUM`, `GENLIST` (not used) | not translated | |
| `x ≼ y` (`isPREFIX`, `<<=`) | `x ≼ y` (notation for `isPREFIX x y`) | `CmlTS.Prelude.List` |
| `IS_PREFIX l1 l2` (= `isPREFIX l2 l1`) | `IS_PREFIX l1 l2` | `CmlTS.Prelude.List` |
| `EVERY2 R l1 l2` | `LIST_REL R l1 l2` | `CmlTS.Prelude.List` |
| `RTC R` / `R^*` | `RTC R` | `CmlTS.Prelude.Basic` |
| `f o_f m` | `o_f f m` | `CmlTS.Prelude.FMap` |
| `f \|+ (k,v)`, `f \|++ l`, `f ⊌ g`, `f ⊑ g` | same notation (see above) | `CmlTS.Prelude.FMap` |
| `new_env +++ env` | `new_env +++ env` (`infixl:480`, = `extend_dec_env new_env env`) | `CmlTS.SemanticPrimitives` |
| `f =++ l` | `f =++ l` (= `UPDATE_LIST f l`) | `CmlTS.Misc` |
| `fmap` | `FMap` | `CmlTS.Prelude.FMap` |
| `real`-valued binary_ieee functions | see section 5 | `CmlTS.Prelude.Float` |
| `fp64_*` | same names | `CmlTS.Prelude.Float` |
| `roundTiesToEven` ... (constructors of `rounding`) | `rounding.roundTiesToEven` ... | `CmlTS.Prelude.Float` |
| `FP_Add`, `FP_Sub`, ... (constructors) | `fp_bop.FP_Add`, ... (fpSem) and `fp_op.FP_Add` ... (binary_ieee) | `CmlTS.FpSem`, `CmlTS.Prelude.Float` |

Modules (import with `import CmlTS.<Module>`; `import CmlTS` imports everything):

* `Prelude.Basic`: `ARB FST SND UNCURRY CURRY UPDATE Set setOf UNIV IN DIFF DISJOINT IMAGE BIGUNION FINITE CARD INJ SURJ BIJ RTC`
* `Prelude.List`: `LIST_TO_SET MEM LENGTH MAP REVERSE FLAT FOLDL FOLDR TAKE DROP REPLICATE MAP2 ZIP NULL HD TL EL EVERY EXISTS ALL_DISTINCT LUPDATE REV COUNT_LIST LIST_REL oEL isPREFIX IS_PREFIX OPT_MMAP SPLITP TOKENS alist ALOOKUP`
* `Prelude.Num`: `char ORD CHR string STRING HOLstr ordering DIV2 int_of_num Num ABS int_div int_mod word word8 word64 n2w w2n i2w word_add word_sub word_and word_or word_xor word_lsl word_lsr word_asr word_ror`
* `Prelude.FMap`: `FMap FEMPTY FLOOKUP FDOM FAPPLY FUPDATE FUPDATE_LIST FUNION FRANGE FEVERY o_f SUBMAP alist_to_fmap`
* `Prelude.Coalg`: `spt num_map num_set sptree.* llist LNIL LNTH fromList LFINITE llength_rel LLENGTH LTAKE llist.toList LPREFIX`
* `Prelude.Sort`: `sort2_tail sort3_tail merge_tail mergesortN_tail mergesort_tail`
* `Prelude.Float`: `RealX float float_value_ty float_to_real float_value ... round ... fp64_to_float float_to_fp64 fp64_abs fp64_negate fp64_sqrt fp64_add fp64_sub fp64_mul fp64_div fp64_mul_add fp64_equal fp64_lessThan fp64_lessEqual fp64_greaterThan fp64_greaterEqual`
* `Misc`: `the app_list append_aux append MAP3 tlookup max3 UPDATE_LIST find_index between lookup_vars enumerate range`
* `Mllist`: `sort nth mllist.collate`
* `Mlstring`: `mlstring mlstr implode strlen strsub concat explode_aux explode strcat str tokens_aux tokens isStringThere_aux isSubstring_aux isSubstring mlstring.compare_aux mlstring.compare mlstring_lt mlstring_le mlstring_gt mlstring_ge mlstring.collate_aux mlstring.collate app_list_ann char_to_word8 word8_to_char empty_ffi`
* `Location`: `locn locnrow locn_rowupdate locncol locn_colupdate locs`
* `LprefixLub`: `lprefix_lub`
* `Ffi`: `ffi_outcome oracle_result shmem_op ffiname oracle_function oracle io_event final_event ffi_state ffi_result call_FFI outcome behaviour`
* `FpSem`: `fp_cmp_ty fp_uop fp_bop fp_top fp_cmp`
* `Namespace`: `Ident mk_id id_to_n id_to_mods Namespace nsLookup nsLookupMod nsEmpty nsAppend nsLift alist_to_ns nsBind nsBindList nsOptBind nsSing nsSub nsAll nsAll2 nsDom nsMap` (+ `nsMapAux`, theorems `nsMapAux_eq`, `nsMap_eq`)
* `NamespaceProps`: `alist_rel_restr alistSub nsSub_compute` (+ auxiliary `alist_rel_restr_mem`)
* `Ast`: `lit shift arith modN varN conN typeN tvarN word_size thunk_mode thunk_op opb test prim_type op op_class getOpClass ast_t pat lop exp type_def dec pat_bindings pats_bindings every_exp` (+ `every_exp_list/pes/funs`)
* `SemanticPrimitives`: everything of HOL4 `semanticPrimitives` (`stamp sem_env Value env_ctor env_val bind_stamp ... update_thunk`, `pmatch`/`pmatch_list`, `do_eq`/`do_eq_list`, `concrete_v`/`concrete_v_list`)
* `SemanticPrimitivesProps`: `shift_lookup map_error_result map_result every_error_result every_result map_sv dest_Refv store_v_vs ctors_of_tdef FV FV_list FV_pes FV_defs FV_dec`
* `Evaluate`: `fix_clock dec_clock do_eval_res list_result evaluate evaluate_match evaluate_decs` (+ auxiliary `fix_clock'`, lemmas)
* `EvaluateProps`: `call_FFI_rel dest_IO_event io_events_mono is_clock_io_mono adj_clock`
* `SemanticsMin`: `evaluate_prog_with_clock semantics_prog`
* `TypeSystem`: everything of HOL4 `typeSystem`, including `type_p type_ps type_e type_es type_funs type_d type_ds`
* `TypeSoundInvariants`: `store_t tenv_store tenv_abbrev_ok ... type_v type_sv type_s ... type_sound_invariant`
* `TypeSysProps`: `type_pes deBruijn_subst_tenvE db_merge type_def_to_ctMap`
* `Weakening`: `weak_tenvE weakS weak weakCT`
* `TypeSound`: `store_type_extension`

Auxiliary Lean-only declarations (not HOL4 constants; do not use in statements): `fix_clock'`,
`nsMapAux`, `every_exp_list/_pes/_funs`, `*_list` of `typeSystem` (`check_freevars_list`,
`check_freevars_ast_list`, `type_subst_list`, `deBruijn_inc_list`, `deBruijn_subst_list`,
`check_type_names_list`, `type_name_subst_list`, `is_value_list`; each has a `*_list_eq` theorem
stating it equals `EVERY`/`MAP`), `alist_rel_restr_mem`, `float_bias`, `ratAbs`, `UINT_MAXw`, helper
lemmas (`sizeOf_*`, `lex_helper`, `do_log_exp`, `do_if_exp`, `SPLITP_*`, ...).

## 4. Argument order and shape

Arguments are in the same order as HOL4, curried.  Differences that matter in statements:

* `type_v tvs ctMap tenvS v t`, `type_sv ctMap tenvS sv st`, `type_s ctMap envS tenvS`,
  `type_all_env ctMap tenvS env tenv`, `type_sound_invariant st env ctMap tenvS tids tenv`,
  `type_ctor ctMap id (n, stamp) (tvs, ts, ti)` (the second argument is the identifier).
* `type_p tvs tenv p t bindings`, `type_ps tvs tenv ps ts bindings`, `type_e tenv tenvE e t`,
  `type_es tenv tenvE es ts`, `type_funs tenv tenvE funs bindings`,
  `type_d extra_checks tenv d decls tenv'`, `type_ds extra_checks tenv ds decls tenv'`
  (`extra_checks : Prop`, so `type_ds F ...` is `type_ds False ...`; `decls : Set type_ident`).
* `evaluate st env es`, `evaluate_match st env v pes err_v`, `evaluate_decs st env ds`, all returning
  `state α × result _ Value`.  `semantics_prog st env prog behaviour`.
* `do_app (s, t) op vs : Option ((List (store_v Value) × ffi_state α) × result Value Value)`.
* `pmatch envC s p v env`, `pmatch_list envC s ps vs env`, `can_pmatch_all envC refs ps v`.
* `build_conv envC cn vs`, `do_con_check cenv n_opt l`, `one_con_check envc e`.
* `FOLDR f e l`, `FOLDL f e l`, `ZIP (l1, l2)` (takes a **pair**), `MAP2 f l1 l2`, `EL n l`, `TAKE n l`,
  `DROP n l`, `LUPDATE e n l`, `REPLICATE n x`, `LIST_REL R l1 l2`, `ALOOKUP l k`.
* `nsSub r env1 env2`, `nsAll f env`, `nsAll2 r env1 env2` with `r : Ident M N → V → V' → Prop`.
* `HOL4 (λ(x,y). t)` is `fun p => t[p.1/x, p.2/y]` (or `fun ⟨x, y⟩ => t`); `(case e of ...)` is
  `match e with ...`; `(? x. P)` is `∃ x, P`; `(! x. P)` is `∀ x, P`.
* Statements that are `Theorem foo = <proved term>` (`type_op_cases`, `do_app_cases`) have no
  explicit statement in the HOL4 source; they are the case analysis of `type_op op ts t3` resp.
  `do_app (s,t) op vs = SOME (st',v)` and should be stated in the natural expanded form
  (`type_op` and `do_app` are ordinary Lean definitions that `simp`/`unfold` can expand).

## 5. Modelling choices and deviations (important for faithfulness review)

* **bool is Prop** (section 1).  All HOL4 predicates are `Prop`-valued Lean functions.
* **Underspecification / `ARB`.**  Where HOL4 leaves a value unspecified Lean uses `ARB`
  (`Classical.choice`): `HD []`, `EL n l` for `n >= LENGTH l`, `FAPPLY f x` for `x ∉ FDOM f`, `CHR n`
  for `n >= 256`, `int_div i 0`, `int_mod i 0`, the unmatched cases of `MAP3`, `locnrow`,
  `locn_rowupdate`, `locncol`, `locn_colupdate`, `dest_Refv`, `the_Litv_*`, `type_def_to_ctMap`,
  `FV_dec` (for `Dmod`, `Dlocal`, `Denv`).  `ARB : α` needs `[Nonempty α]`.
* **Hilbert choice** is `Classical.epsilon`: `Num`, `closest_such`, `float_some_qnan`, `LLENGTH`.
* **`Num i`**: HOL4's `Num i = @n. if 0 <= i then i = &n else i = -&n` (so `Num (-5) = 5`).
* **Integer division**: floor division (`Int.fdiv`/`Int.fmod`) for non-zero divisors, as HOL4's `int_div`.
* **Characters**: a structure with `val < 256`; strings are `List char`.
* **`mlstring` ordering**: `mlstring.compare` etc. are translated exactly; they use `char` order.
* **Words**: `BitVec`; HOL4's `word_lsl/lsr/asr/ror` agree with `<<<`, `>>>`, `sshiftRight`,
  `rotateRight` (defined from the bit-wise HOL4 definitions' meaning, including shift amounts
  `>= width`).
* **Finite maps** are partial functions `α → Option β` with finite support (a subtype);
  `FAPPLY`/`FDOM`/`FRANGE`/`FEVERY`/`SUBMAP` are stated through `FLOOKUP` (equivalent to the HOL4
  definitions via `FLOOKUP_DEF`).
* **Sets** are predicates; `FINITE s` is "contained in a list"; `CARD` is the number of elements for
  finite sets and `0` otherwise (as HOL4).
* **llist**: `num -> option` with `IS_SOME (f (n+1)) ==> IS_SOME (f n)`, `LPREFIX` exactly as in HOL4
  (through `toList`, `LTAKE`).
* **Reals / IEEE-754.**  Lean core has no real numbers.  In `Prelude/Float.lean` all reals are
  `RealX` = a rational or the square root of a non-negative rational; the finite floats are exactly
  the rationals (`float_to_real : float t w → Rat`), `r1 + r2`, `r1 - r2`, `r1 * r2`, `r1 / r2` of floats
  are rationals, and `sqrt r` is `RealX.sqrt r`.  The comparisons used by `round` (`<=`, `<`,
  `>=`, `>` with rational thresholds; `abs (a - x) <= abs (b - x)`) are defined exactly (the last via
  `(a-x)^2 <= (b-x)^2 <=> (a-b)(a+b-2x) <= 0`).  The binary_ieee functions are generic in the widths
  `t w : Nat` (given explicitly instead of the `(:'t # 'w)` argument), `fp64_*` use `float 52 11`.
  Only `fp64_add/sub/mul/div/mul_add/sqrt/abs/negate/equal/lessThan/lessEqual/greaterThan/greaterEqual`
  are exposed because those are all that CakeML uses.  `float_some_qnan` and `closest_such` use
  Hilbert choice exactly as HOL4.
* **Inductive relations** (`type_p`, `type_ps`, `type_e`, `type_es`, `type_funs`, `type_d`, `type_ds`,
  `type_v`) are Lean `inductive` predicates with the same rules.  Rules are anonymous in HOL4, here
  they have names (`type_p.pany`, `type_e.handle`, `type_d.dlet_value`, `type_v.closure`, ...).
  Because Lean's positivity check forbids occurrences of the predicate inside other definitions or
  under `∃`:
  * conjunctions of premises are separate constructor arguments (equivalent);
  * `type_e.handle` / `type_e.mat` take a function `bs : pat → exp → List (varN × Ty)` (Skolemisation of
    `!((p,e) :: set pes). ?bindings. ...`; equivalent in classical logic) and three premises
    `∀ p e', (p, e') ∈ LIST_TO_SET pes → ...`;
  * in `type_v`, `LIST_REL (type_v ..) vs us` is `LENGTH vs = LENGTH us ∧ ∀ i v t, vs[i]? = some v →
    us[i]? = some t → type_v .. v t`, `EVERY (λv. type_v .. v t) vs` is `∀ v, MEM v vs → type_v .. v t`,
    and `nsAll2 (λi v (tvs,t). type_v tvs ctMap tenvS v t) env.v V` is `nsAll2 (λ_ _ _. T) env.v V`
    plus `∀ i v1 p, nsLookup env.v i = some v1 → nsLookup V i = some p → type_v p.1 ctMap tenvS v1 p.2`.
    This is equivalent because `nsLookup` is a function; the occurrences of `nsAll2` in
    `type_all_env` and in statements keep the plain definition.
  Statements about these relations simply use the predicates; their induction principles are the
  ones Lean generates (mutual structural recursors) -- not needed for statements.
* **Termination.**  `evaluate`/`evaluate_match`/`evaluate_decs` are one mutual well-founded recursion
  on `(clock, size)` with real termination proofs (no `sorry`).  As in HOL4 the definition uses
  `fix_clock`; inside Lean it is `fix_clock'` (a subtype carrying `clock <= old clock`), whose value
  is definitionally `fix_clock`.  `nsSub_compute` has an auxiliary membership-carrying version of
  `alistSub` for the recursion (proved equal by `alist_rel_restr_mem_eq`).  `TOKENS`,
  `mergesortN_tail`, `merge_tail`, `sptree.lookup`, `mlstring.compare_aux` are well-founded with proofs.
  Functions recursing through `EVERY`/`MAP` over nested datatypes use mutual structural recursion
  with auxiliary `*_list` functions (equal to the HOL4 text by the `*_list_eq` theorems).
* **`nsDom`**: HOL4 writes it with a pair-set-comprehension; it is the set of identifiers bound in the
  namespace: `fun n => ∃ v, nsLookup env n = some v`.
* **`is_clock_io_mono f s`**: `f : state α → state α × result β γ` for arbitrary `β γ`.
* **Out of scope / not translated** (not mentioned by any target): HOL4 library constants that no
  definition or target statement mentions.

## 6. Quick reference for tricky definitions

* `Boolv b` takes a `Prop` (`Boolv True`, `Boolv (b = b')`).
* `do_eq` returns `eq_result.Eq_val p` with `p : Prop`, e.g. `do_eq_Boolv : do_eq (Boolv b) (Boolv b') = eq_result.Eq_val (b = b')`.
* `check_dup_ctors (tvs, tn, condefs)` takes one triple argument.
* `type_def_to_ctMap tenvT next tds ids : List (stamp × (List tvarN × List Ty × type_ident))`.
* `lookup_vars`, `nth`, `find_index` as HOL4 (`find_index y l n`).
* `mlstr "abc"` for `«abc»`; the type-variable names `«'a»` are `mlstr "'a"`.
* `thunk_op'` (function) vs `thunk_op` (datatype).
* `sem_env Value` is HOL4 `v sem_env` (the parameter of `sem_env` is the value type).
