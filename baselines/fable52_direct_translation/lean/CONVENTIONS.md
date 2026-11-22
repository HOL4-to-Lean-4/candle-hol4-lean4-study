# CONVENTIONS for the Lean translation of the Candle soundness development

Stage 1 wrote the definitions. Stage 2 writes the 278 theorem statements on top of them.
This file gives the rules for stage 2. Read sections 1 to 5 before you write a statement.
Sections 6 to 9 are tables for look-up.

## 1. Files, namespace, header

| HOL4 theory | Lean module |
|---|---|
| HOL4 library (`bool`, `combin`, `pair`, `option`, `sum`, `arithmetic`, `relation`, `ternaryComparisons`, `toto`) | `CandleLean/Prelude/Basic.lean` |
| HOL4 library (`pred_set`) | `CandleLean/Prelude/PredSet.lean` |
| HOL4 library (`list`, `rich_list`, `indexedLists`, `sorting`, `alist$ALOOKUP`) | `CandleLean/Prelude/List.lean` |
| HOL4 library (`string`, `numposrep`, `ASCIInumbers`) | `CandleLean/Prelude/String.lean` |
| HOL4 library (`finite_map`, `alist$alist_to_fmap`, `sptree`) | `CandleLean/Prelude/FiniteMap.lean` |
| HOL4 library (`words`, `bitstring`) | `CandleLean/Prelude/Words.lean` |
| HOL4 library (`mergesort`) | `CandleLean/Prelude/Mergesort.lean` |
| `misc` | `CandleLean/Misc.lean` |
| `mllist` | `CandleLean/Mllist.lean` |
| `mlstring` | `CandleLean/Mlstring.lean` |
| `setSpec` | `CandleLean/SetSpec.lean` |
| `holSyntaxLib` | `CandleLean/HolSyntaxLib.lean` |
| `holSyntax` | `CandleLean/HolSyntax.lean` |
| `holSyntaxExtra` | `CandleLean/HolSyntaxExtra.lean` |
| `holSemantics` | `CandleLean/HolSemantics.lean` |
| `holSemanticsExtra` | `CandleLean/HolSemanticsExtra.lean` (only `Equalsem`) |
| `holSoundness` | `CandleLean/HolSoundness.lean` (no definitions) |

Module imports follow the HOL4 `Ancestors`. `Misc` imports all `Prelude` modules, so every
package module sees the whole prelude.

All declarations are in the one namespace `Candle`. There are two sub-namespaces only:
`Candle.sptree` (`sptree.insert`, `sptree.domain`) and the namespaces of the inductive types
(for example `app_list.List`, `has_type.var`, `proves.ABS`).

Put the theorems of a theory in the module of that theory, inside this block:

```lean
namespace Candle
noncomputable section
open Classical
set_option autoImplicit false   -- recommended: a misspelled constant becomes an error

-- theorems

end
end Candle
```

- `open Classical` is necessary: `if p then a else b` with a `p` that has no decidable
  instance uses `Classical.propDecidable`. The definitions were compiled in the same setting.
- Inside `namespace Candle` the HOL names take priority over Lean root names. Thus `compare`,
  `concat`, `sort`, `set`, `domain`, `union`, `sub`, `apply`, `unit`, `bind`, `I`, `K`, `C`, `S`
  are the HOL constants. Write `_root_.compare` and so on for the Lean ones.

### Names of the stage 2 theorems

Give each theorem its HOL4 name, in namespace `Candle` (for example
`theorem Candle.proves_sound`). The 278 target names are distinct. Two of them are also the
names of Lean constants, so these two theorems must have another name:

| HOL4 theorem | Lean theorem name |
|---|---|
| `holSyntaxExtra.RACONV` | `RACONV_thm` |
| `holSyntaxLib.REV_ASSOCD` | `REV_ASSOCD_thm` |

Stage 1 already proved the theorems in the next list, because Lean needs them or because
Lean has no equation lemma of that form. Their names are not target names. Do not declare
them again: `select_spec`, `OUTL_def`, `HD_def`, `LAST_DEF`, `SEG_def`, `MEM_def`, `CHR_ORD`,
`CHR_mk`, `ORD_CHR`, `LENGTH_SND_SPLITP_le`, `LENGTH_TL_le`, `RESULT_def`, `CLASH_def`,
`dest_var_def`, `MEM_FILTER_imp`, `sizeof_REV_ASSOCD`, `sizeof_VSUBST_termination`,
`EVERY_iff_forall_MEM`, `type_ok_def`, and the specifications in section 5.3 that are marked
"proved".

## 2. Types

| HOL4 | Lean | Notes |
|---|---|---|
| `bool` | `Prop` | Always, also as data: `bool list` is `List Prop`; a `bool` argument (`negate`, `b`) is a `Prop`. `T`, `F` are `True`, `False`. |
| `num` | `Nat` | `-`, `DIV`, `MOD` agree with Lean `-`, `/`, `%` on all inputs (this HOL4 has `m DIV 0 = 0`, `m MOD 0 = m`). `SUC n` is `SUC n` (reducible to `n + 1`). `x ** y` is `x ^ y`. Numerals `0n`, `1n` are `0`, `1`. |
| `int` | not used | |
| `'a`, `'b`, `'U` (type variables) | `{α : Type} [Nonempty α]` | Every HOL type is non-empty. Give each type variable of a statement a `[Nonempty _]` instance, always. Use `Type`, not `Type u`. |
| `'a -> 'b` | `α → β` | |
| `'a # 'b` | `α × β` | `(x,y)` is `(x, y)`. `'a # 'b # 'c` is `α × β × γ` (right nested, as in HOL). |
| `'a list` | `List α` | `[]`, `h::t`, `[a;b]` are `[]`, `h :: t`, `[a, b]`. `l1 ++ l2` is `l1 ++ l2`. |
| `'a option` | `Option α` | `NONE`, `SOME x` are `none`, `some x`. `case o of NONE => a \| SOME y => b` is a Lean `match`. |
| `'a + 'b`, `one`/`unit` | `Sum α β`, `Unit` | `()` is `()`. |
| `'a set` (= `'a -> bool`) | `Set α` (= `α → Prop`, `Candle.Set`) | See section 4. Sets can be infinite. |
| `'a \|-> 'b` | `fmap α β` | The HOL representation: a function `α → Sum β Unit` with `is_fmap`. See section 4. |
| `char` | `char` (`Candle.char`) | The type with 256 values (`val : Nat`, `isLt : val < 256`). NOT Lean's `Char`. |
| `string` (= `char list`) | `string` (= `List char`) | NOT Lean's `String`. |
| `mlstring` | `mlstring` | Constructor `implode : string → mlstring`; `strlit` is the same constructor. |
| `ordering` | `ordering` | `LESS`, `EQUAL`, `GREATER`. NOT Lean's `Ordering`. |
| `word8`, `word32`, `:N word` | `word8`, `word32`, `word N` (= `BitVec N`) | `dimword(:N)` is `dimword N`. |
| `bitstring` | `bitstring` (= `List Prop`) | |
| `'a spt`, `num_set`, `'a num_map` | `spt α`, `num_set`, `num_map α` | Constructors `LN`, `LS`, `BN`, `BS`. |
| `'a app_list` | `app_list α` | Constructors `app_list.List`, `app_list.Append`, `app_list.Nil`. They are NOT exported (a bare `List` would hide Lean's list type). |
| `'a app_list_ann` | `app_list_ann α` | `BigList`, `BigAppend`, `Small`. |
| `'a result` | `result α` | `Clash`, `Result`. |
| `type` | `type` | `Tyvar`, `Tyapp`. |
| `term` | `term` | `Var`, `Const`, `Comb`, `Abs`. |
| `update` | `update` | `ConstSpec`, `TypeDefn`, `NewType`, `NewConst`, `NewAxiom`. |
| `dbterm` (the type) | **`dbterm_ty`** | `dbVar`, `dbBound`, `dbConst`, `dbComb`, `dbAbs`. Renamed because the HOL constant `dbterm` (a function) keeps the name `dbterm`. |
| `tysig`, `tmsig`, `sig`, `thy` | `tysig`, `tmsig`, `sig`, `thy` | `fmap mlstring Nat`, `fmap mlstring type`, `tysig × tmsig`, `sig × Set term`. |
| `'U tyass`, `'U tyval`, `'U tmass`, `'U tmval`, `'U interpretation`, `'U valuation` | `tyass U`, `tyval U`, `tmass U`, `tmval U`, `interpretation U`, `valuation U` | |

**A bound variable hides a type of the same name.** HOL statements often use the variable
names `sig`, `thy`, `tysig`, `tmsig`. `∀ (sig : sig) (t : term), …` is correct. But after the
binder `sig`, the name `sig` is the variable, so `(sig : sig) (sig' : sig)` fails. Write the
type as `Candle.sig` (`Candle.thy`, `Candle.tysig`, `Candle.tmsig`) when a variable has that
name.

## 3. Logic, functions, literals

| HOL4 | Lean |
|---|---|
| `!x. P`, `?x. P` | `∀ x, P`, `∃ x, P` |
| `?!x. P x` | `EXISTS_UNIQUE (fun x => P x)` |
| `@x. P x` | `select (fun x => P x)` (needs `[Nonempty α]`) |
| `ARB` | `ARB` (needs `[Nonempty α]`; it is `select (fun _ => True)`) |
| `p ==> q`, `p /\ q`, `p \/ q`, `~p` | `p → q`, `p ∧ q`, `p ∨ q`, `¬ p` |
| `p <=> q` (and `=` between two `bool` formulas of a statement) | `p ↔ q` |
| `=` between `bool` terms that are data (`R x y <> neg`, `Boolean (x = y)`) | `=` / `≠` on `Prop` |
| `if b then x else y` | `if b then x else y` (with `open Classical`) |
| `let x = e in b` | `let x := e; b` |
| `\x. e` | `fun x => e` |
| `\(x,y). e` | `fun (x, y) => e` (same function as `fun p => e[FST p, SND p]`; the definitions use the `FST`/`SND` form) |
| `f o g` | `f ∘ g` |
| `I`, `K`, `C`, `S` | `I`, `K`, `C`, `S` (reducible) |
| `$+ 0n`, `$= x`, `(=) c` (operator sections) | `fun n => 0 + n`, `fun y => x = y`, `fun y => c = y` |
| `FST`, `SND` | `FST`, `SND` (reducible to `.1`, `.2`) |
| `UNCURRY f` | `UNCURRY f` |
| `f ## g` | `f ## g` (`PAIR_MAP f g`, infixr 80; `∘` binds tighter) |
| `R1 LEX R2` | `LEX R1 R2` (no infix) |
| `(a =+ b) f` | `UPDATE a b f` |
| `f =++ ls` | `UPDATE_LIST f ls` |
| `x < y`, `x <= y`, `x > y`, `x >= y` on `num` | the same in Lean |
| `MAX m n` | `MAX m n` |
| `EVEN n` | `EVEN n` (a `Prop`) |
| `#"a"` | `chr!"a"` (a one-character Lean string literal; `#"\n"` is `chr!"\n"`, `#"'"` is `chr!"'"`) |
| `"abc"`, `""` | `str!"abc"`, `str!""` (a `string`, that is a `List char`; `""` can also be `[]`) |
| `«abc»`, `«»` | `ml!"abc"`, `ml!""` (= `implode str!"abc"`) |
| `strlit s`, `implode s` | `strlit s`, `implode s` (the same constructor) |
| `a < b` on `char` | `char_lt a b` |
| `s < t` on `string` | `string_lt s t` |
| `s < t` on `mlstring` | `mlstring_lt s t` |
| `s1 ^ s2` on `mlstring` | `strcat s1 s2` (HOL `^` is left associative) |
| `toString c` (on a `char`) | `chr_to_str c` |
| `flip_ord` | `flip_ord` (reducible to `invert_comparison`) |
| `n2w n : word8`, `0w`, `1w` | `(n2w n : word8)`, `n2w 0`, `n2w 1` |

`chr!`, `str!`, `ml!` accept characters with a code below 256 only. Use ASCII.

Unspecified values. HOL4 leaves some values unspecified. The Lean definitions keep them
unspecified (they are made with `select`, that is `Classical.epsilon`):

- `HD []`, `LAST []`, `EL n l` for `n ≥ LENGTH l`, `SEG (SUC m) k []`, `OUTL (INR y)`,
  `CHR n` for `n ≥ 256`, `RESULT (Clash t)`, `CLASH (Result t)`, `dest_var` of a non-variable,
  `FAPPLY f x` for `x` not in `FDOM f` (it is `OUTL (INR ())`, one fixed value for each type),
  `FUN_FMAP f P` for infinite `P`.
- `termsem0 … (Abs v b)` for `v` not a `Var` is `ARB` (as in HOL4).

## 4. Sets and finite maps

Sets (`CandleLean/Prelude/PredSet.lean`):

| HOL4 | Lean |
|---|---|
| `x IN s`, `x NOTIN s` | `x ∈ s`, `x ∉ s` |
| `{}` / `EMPTY` / `∅` | `∅` (constant `EMPTY`) |
| `UNIV`, `univ(:'a)` | `UNIV`, `(UNIV : Set α)` |
| `x INSERT s` | `INSERT x s` |
| `{a}`, `{a; b}` | `{a}`, `{a, b}` (these are `INSERT a ∅`, `INSERT a (INSERT b ∅)`) |
| `s UNION t`, `s INTER t`, `s DIFF t` | `s ∪ t`, `s ∩ t`, `s \ t` (constants `UNION`, `INTER`, `DIFF`) |
| `s SUBSET t` | `s ⊆ t` (constant `SUBSET`) |
| `{x \| P x}` | `{x \| P x}` or `{x : τ \| P x}` (constant `setOf`) |
| `{(x,ty) \| P x ty}` (pattern on the left) | `{p \| ∃ x ty, p = (x, ty) ∧ P x ty}` |
| `{f x \| P x}` in general | `GSPEC (fun x => (f x, P x))` |
| `IMAGE f s`, `DISJOINT s t`, `FINITE s`, `INFINITE s` | the same names |
| `INJ f s t`, `SURJ f s t`, `BIJ f s t` | the same names |
| `f PERMUTES s` | `PERMUTES f s` |
| `set l` / `LIST_TO_SET l` | `set l` (reducible to `LIST_TO_SET l`) |
| `MEM x l` | `MEM x l` (reducible to Lean `x ∈ l`) |

`Set α` is `α → Prop`; `x ∈ s` is `s x` by definition. `FINITE` is the HOL4 definition
(`∀ P, P ∅ ∧ (∀ s, P s → ∀ e, P (INSERT e s)) → P s`).

Finite maps (`CandleLean/Prelude/FiniteMap.lean`):

| HOL4 | Lean |
|---|---|
| `FEMPTY` | `FEMPTY` |
| `f \|+ (k,v)` | `FUPDATE f (k, v)` |
| `f ' x` / `FAPPLY f x` / `$FAPPLY f` | `FAPPLY f x` / `FAPPLY f` (needs `[Nonempty β]`) |
| `FDOM f`, `FRANGE f`, `FLOOKUP f x`, `FEVERY P f`, `FUN_FMAP f s` | the same names |
| `alist_to_fmap l` | `alist_to_fmap l` |
| sptree `insert n v t`, `domain t` | `sptree.insert n v t`, `sptree.domain t` |

## 5. Overloads, notation, renamed constants

### 5.1 Renamed constants (all other constants keep their HOL4 name)

| HOL4 | Lean | Why |
|---|---|---|
| `true ^mem` (overload `True`) | `true0 mem` | `true` is Lean's `Bool.true` |
| `false ^mem` (overload `False`) | `false0 mem` | `false` is Lean's `Bool.false` |
| `Bool` (overload for `Tyapp «bool» []`) | `Bool'` | `Bool` is Lean's type |
| `instance` | `instance'` | `instance` is a Lean keyword |
| type `dbterm` | `dbterm_ty` | the constant `dbterm` has that name |
| `tysof ctxt`, `tmsof ctxt`, `sigof ctxt`, `axsof ctxt` (overloads at `update list`) | `tysof_ctxt`, `tmsof_ctxt`, `sigof_ctxt`, `axsof_ctxt` | Lean has no overloading by type |
| `mergesort$mergesort_tail` and the other `mergesort$` constants | `mergesort_tail`, … (no prefix) | |
| sptree `insert`, `domain` | `sptree.insert`, `sptree.domain` | `domain` is also the `holSyntax` constant |

### 5.2 Overloads and notation of the package

`mem` is always explicit and is the first argument. HOL4 writes `^mem` or hides it in an
overload; in Lean give it as `(mem : U → U → Prop)` with `{U : Type} [Nonempty U]`.

| HOL4 | Lean |
|---|---|
| `x <: y` | `mem x y` |
| `s suchthat P` | `sub mem s P` |
| `Pow x` | `power mem x` |
| `x + y` (on sets of the set theory) | `upair mem x y` |
| `∅` (of the set theory) | `empty mem` |
| `Unit x`, `One`, `Two` | `unit mem x`, `one mem`, `two mem` |
| `boolset` | `boolset mem` (reducible to `two mem`) |
| `(x,y)` (pair of the set theory) | `pair mem x y` |
| `x ∪ y` / `x UNION y` (of the set theory) | `binary_union mem x y` |
| `x × y` / `x CROSS y` (of the set theory) | `product mem x y` |
| `Relspace x y`, `Funspace x y` | `relspace mem x y`, `funspace mem x y` |
| `f ' x` (of the set theory) | `apply mem f x` |
| `True`, `False` (of the set theory) | `true0 mem`, `false0 mem` |
| `Boolean b` | `boolean mem b` |
| `Abstract d r f` | `abstract mem d r f` |
| `inhabited s` | `inhabited mem s` (reducible to `∃ x, mem x s`) |
| `is_type_assignment`, `is_type_valuation`, `is_term_assignment`, `is_term_valuation`, `is_valuation`, `is_interpretation`, `is_std_type_assignment`, `is_std_interpretation`, `is_structure` | `is_type_assignment0 mem`, `is_type_valuation0 mem`, `is_term_assignment0 mem`, `is_term_valuation0 mem`, `is_valuation0 mem`, `is_interpretation0 mem`, `is_std_type_assignment0 mem`, `is_std_interpretation0 mem`, `is_structure0 mem` |
| `termsem tmsig i v tm` | `termsem0 mem tmsig i v tm` |
| `i satisfies (sig,h,c)` | `satisfies0 mem i (sig, h, c)` |
| `γ interprets name on vs as f` | `interprets0 mem γ name vs f` |
| `i models thy` | `models0 mem i thy` |
| `(thy,h) \|= c`, `thyh \|= c` | `entails0 mem (thy, h) c`, `entails0 mem thyh c` |
| `^Equalsem` (ML antiquotation in `termsem_Equal`) | `Equalsem mem` |
| `typesem δ τ ty`, `instance tmsig i name ty` (no `mem`) | `typesem δ τ ty`, `instance' tmsig i name ty` |
| `Fun s t`, `Bool`, `Equal ty` | `Fun s t`, `Bool'`, `Equal ty` (reducible) |
| `tm has_type ty` | `has_type tm ty` |
| `s === t` | `s === t` (constant `equation`; infixr 60: tighter than `=`, `∧`, `↔`; looser than `::`, `++` and application) |
| `(thy,h) \|- c`, `thyh \|- c` | `proves (thy, h) c`, `proves thyh c` |
| `upd updates ctxt` | `updates upd ctxt` |
| `ty1 subtype ty2`, `tm1 subterm tm2` | `subtype ty1 ty2`, `subterm tm1 tm2` (reducible to `RTC subtype1 …`, `RTC subterm1 …`) |
| `is_instance ty0 ty` | `is_instance ty0 ty` (reducible to `∃ i, ty = TYPE_SUBST i ty0`) |
| `tysof sig`, `tmsof sig` (at a `sig`) | `tysof sig`, `tmsof sig` (reducible to `FST`, `SND`) |
| `sigof thy`, `axsof thy` (at a `thy`) | `sigof thy`, `axsof thy` |
| `tysof thy`, `tmsof thy` (at a `thy`) | `tysof (sigof thy)`, `tmsof (sigof thy)` |
| `tyaof i`, `tmaof i`, `tyvof v`, `tmvof v` | the same names (reducible to `FST`/`SND`) |
| `type_list`, `const_list`, `axexts`, `conexts`, `axioms_of_upd`, `axiom_list`, `thyof` | the same names |
| `EVERY2` | `EVERY2` (reducible to `LIST_REL`) |
| `l1 ≼ l2` / `l1 <<= l2` | `isPREFIX l1 l2` |
| `SOME`, `NONE`, `OPTION_MAP f x` | `some`, `none`, `OPTION_MAP f x` |

HOL4 statements often write `FST i`, `SND v`, `FST sig` where the overloads `tyaof`, `tmvof`,
`tysof` would also parse. Translate what the source says: `FST i` is `FST i`.

The rules of the inductive relations are constructors: `has_type.var/const/comb/abs`,
`RACONV.var/const/comb/abs`, `proves.ABS/ASSUME/BETA/DEDUCT_ANTISYM/EQ_MP/INST/INST_TYPE/MK_COMB/REFL/axioms`,
`updates.new_axiom/new_constant/new_specification/new_type/new_type_definition`,
`subtype1.intro`, `subterm1.comb_left/comb_right/abs_body/abs_var`, `RTC.refl/step`,
`is_fmap.empty/update`. `type_lt` and `term_lt` are not Lean `inductive`s (section 5.4).

### 5.3 Constants made by `new_specification` or with missing clauses

These constants are `select (fun f => specification f)`: an arbitrary function that
satisfies the HOL4 specification. The specification is in the comment above each definition.

| Constant | HOL4 specification | Lean theorem |
|---|---|---|
| `OUTL` | `OUTL (INL x) = x` | `OUTL_def`, proved |
| `HD` | `HD (h::t) = h` | `HD_def`, proved |
| `LAST` | `LAST (h::t) = if t = [] then h else LAST t` | `LAST_DEF`, proved |
| `SEG` | the three clauses of `rich_list$SEG` | `SEG_def`, proved |
| `CHR` | `CHR (ORD a) = a`, `r < 256 <=> ORD (CHR r) = r` | `CHR_ORD`, `ORD_CHR`, proved |
| `RESULT`, `CLASH` | `RESULT (Result t) = t`, `CLASH (Clash t) = t` | `RESULT_def`, `CLASH_def`, proved |
| `dest_var` | `dest_var (Var x ty) = (x,ty)` | `dest_var_def`, proved |
| `FUN_FMAP` | `FUN_FMAP_DEF`: `FINITE P ==> FDOM (FUN_FMAP f P) = P /\ !x. x IN P ==> FAPPLY (FUN_FMAP f P) x = f x` | not stated |
| `VARIANT_PRIMES` | `VARIANT_PRIMES_def` (the least number of primes that makes the name fresh) | not stated |
| `fresh` | `fresh_def`: `FINITE s ==> fresh s NOTIN s` | not stated |
| `instance'` | `instance_def` | not stated |

Where the table says "not stated", the Lean constant is defined, but its specification
theorem is not in the Lean files (stage 1 does not write theorems that a definition does not
need). The definition is faithful because HOL4 proved that the specification can be
satisfied. No target statement needs these four theorems; none of them is a target.

### 5.4 Other modelling choices

- `type_lt` and `term_lt` are HOL4 `Inductive` relations whose rules use the relation
  inside `LLEX` / `LEX`. Lean's `inductive` does not accept that. They are defined as HOL4
  defines an inductive relation: the intersection of all relations closed under the rules
  (`∀ P, rules P → P a0 a1`). The target theorems `type_lt_thm` and `term_lt_thm` state their
  case equations.
- `type_ok` is defined by well-founded recursion with `∀ a, MEM a args → type_ok tysig a`
  in place of `EVERY (type_ok tysig) args`. The theorem `type_ok_def` gives the HOL4
  equations. `TYPE_SUBST`, `tyvars`, `typesem`, `arities_match`, `INST_CORE`, `orda`,
  `term_union`, `merge_tail`, `mergesortN_tail`, `compare_aux`, `FIELDS`, `n2l`,
  `sptree.insert` are also by well-founded recursion; use their equation lemmas
  (`TYPE_SUBST.eq_1`, `simp [TYPE_SUBST]`, `rw [INST_CORE]`), not `rfl`.
- In `VSUBST`, `INST_CORE` and `rename_bvars`, a HOL `let (x,ty) = e in …` is written with
  `FST e` and `SND e`.
- `mergesortN_tail`: the last HOL4 clause (`n` general) applies exactly for `n ≥ 4`; the Lean
  clause has the pattern `n + 4`.
- `LIST_TO_SET l` is `fun x => x ∈ l` (Lean list membership) and `MEM x l` is `x ∈ l`.
  `MEM_def` states `MEM x l ↔ x ∈ LIST_TO_SET l`.
- `MAP`, `LENGTH`, `FLAT`, `FOLDR`, `FOLDL`, `REVERSE`, `TAKE`, `DROP`, `APPEND` are reducible
  abbreviations of `List.map`, `List.length`, `List.flatten`, `List.foldr`, `List.foldl`,
  `List.reverse`, `List.take`, `List.drop`, `++`. These functions are equal to the HOL4 ones
  on all inputs. The other list constants are defined by the HOL4 equations.
- Words: `word N` is `BitVec N`; `n2w` is `BitVec.ofNat`, `w2n` is `BitVec.toNat`.
  `v2w v` is the word whose bit `i` is `testbit i v`, with `testbit`, `field`, `fixwidth`,
  `shiftr`, `zero_extend` defined as in HOL4 on `List Prop`.
- `char`: `ORD c` is `c.val`. `chr!"a"` is `⟨97, _⟩`, which is equal to `CHR 97` (`CHR_mk`).
- No constant is `opaque`, and there is no `axiom`.

## 6. HOL4 library constants: Lean name and module

All in namespace `Candle`. "same" means that the Lean name is the HOL4 name.

`Prelude/Basic.lean`: `select` (`@`), `select_spec`, `ARB`, `EXISTS_UNIQUE` (`?!`), `K`, `S`,
`I`, `C`, `UPDATE` (`=+`), `FST`, `SND`, `UNCURRY`, `PAIR_MAP` (`##`), `LEX`, `OPTION_MAP`,
`OPTION_BIND`, `ISL`, `OUTL`, `SUC`, `MAX`, `EVEN`, `DIV2`, `transitive`, `reflexive`,
`irreflexive`, `trichotomous`, `RC`, `RTC`, `inv_image`, `StrongOrder`, `StrongLinearOrder`,
`ordering` (`LESS`, `EQUAL`, `GREATER`), `invert_comparison`, `flip_ord`, `TotOrd`,
`TO_of_LinearOrder`.

`Prelude/PredSet.lean`: `Set`, `setOf` (`{x | P}`), `GSPEC`, `EMPTY` (`∅`), `UNIV`, `SUBSET`
(`⊆`), `UNION` (`∪`), `INTER` (`∩`), `DIFF` (`\`), `INSERT`, `DISJOINT`, `IMAGE`, `INJ`, `SURJ`,
`BIJ`, `PERMUTES`, `FINITE`, `INFINITE`.

`Prelude/List.lean`: `NULL`, `HD`, `TL`, `APPEND` (`++`), `FLAT`, `LENGTH`, `MAP`,
`LIST_TO_SET`, `set`, `MEM`, `FILTER`, `FOLDR`, `FOLDL`, `EVERY`, `EXISTS`, `EL`, `LIST_REL`,
`EVERY2`, `ZIP` (takes a pair: `ZIP (l1, l2)`), `REVERSE`, `REV`, `LAST`, `FRONT`, `TAKE`,
`DROP`, `ALL_DISTINCT`, `isPREFIX` (`≼`), `SNOC`, `GENLIST`, `PAD_LEFT`, `LLEX`, `OPT_MMAP`,
`MAX_LIST`, `SEG`, `SPLITP`, `MAPi`, `PERM`, `SORTED`, `ALOOKUP`.

`Prelude/String.lean`: `char`, `string`, `chr!`, `str!`, `ORD`, `CHR`, `char_lt`, `string_lt`,
`FIELDS`, `l2n`, `n2l`, `s2n`, `n2s`, `HEX`, `UNHEX`, `num_from_hex_string`,
`num_to_hex_string`.

`Prelude/FiniteMap.lean`: `is_fmap`, `fmap`, `fmap_REP`, `FEMPTY`, `FUPDATE` (`|+`), `FAPPLY`
(`'`), `FDOM`, `FLOOKUP`, `FEVERY`, `FRANGE`, `FUN_FMAP`, `alist_to_fmap`, `spt` (`LN`, `LS`,
`BN`, `BS`), `num_set`, `num_map`, `sptree.insert`, `sptree.domain`.

`Prelude/Words.lean`: `word`, `word8`, `word32`, `dimword`, `n2w`, `w2n`, `bitstring`,
`zero_extend`, `fixwidth`, `shiftr`, `field`, `testbit`, `FCP_value` (helper, not a HOL4
constant), `v2w`.

`Prelude/Mergesort.lean`: `sort2_tail`, `sort3_tail`, `merge_tail`, `mergesortN_tail`,
`mergesort_tail`.

Argument order is the HOL4 order everywhere: `EL n l`, `TAKE n l`, `DROP n l`, `SEG n k l`,
`SNOC x l`, `GENLIST f n`, `FOLDL f e l`, `FOLDR f e l`, `FILTER P l`, `EVERY P l`,
`REV_ASSOCD a l d`, `ALOOKUP l k`, `FLOOKUP f k`, `find_index y l n`, `MEM x l`.

## 7. Package constants: Lean name and module

`Misc.lean`: `app_list`, `append_aux`, `append`, `SmartAppend`, `max3`, `UPDATE_LIST` (`=++`),
`find_index`, `splitlines`, `is_subseq`, `make_even`, `fmap_update`.

`Mllist.lean`: `sort`.

`Mlstring.lean`: `mlstring` (`implode`), `strlit`, `ml!`, `strlen`, `strsub`, `substring`,
`concat`, `explode_aux`, `explode`, `strcat` (`^`), `chr_to_str` (`toString`), `compare_aux`,
`compare`, `mlstring_lt` (`<`), `app_list_ann`, `char_to_word8`, `word8_to_char`.

`SetSpec.lean`: `extensional`, `is_separation`, `is_power`, `is_union`, `is_upair`,
`is_set_theory`, `sub`, `power`, `union`, `upair`, `empty`, `unit`, `one`, `two`, `boolset`,
`pair`, `binary_union`, `product`, `relspace`, `funspace`, `apply`, `true0`, `false0`,
`boolean`, `abstract`. All take `mem` first.

`HolSyntaxLib.lean`: `ALPHAVARS`, `REV_ASSOCD`, `result`, `IS_RESULT`, `IS_CLASH`, `RESULT`,
`CLASH`, `LIST_INSERT`, `LIST_UNION`, `INORDER_INSERT`, `STRING_SORT`.

`HolSyntax.lean`: `type`, `Fun`, `Bool'`, `domain`, `codomain`, `term`, `Equal`, `dest_var`,
`has_type`, `welltyped`, `typeof`, `RACONV`, `ACONV`, `type_lt`, `term_lt`, `term_cmp`,
`type_cmp`, `ordav`, `orda`, `term_union`, `term_remove`, `term_image`, `VFREE_IN`, `CLOSED`,
`VARIANT_PRIMES`, `VARIANT`, `TYPE_SUBST`, `is_instance`, `VSUBST`, `sizeof`, `INST_CORE`,
`INST`, `tyvars`, `tvars`, `equation` (`===`), `tysig`, `tmsig`, `sig`, `tysof`, `tmsof`,
`type_ok`, `term_ok`, `alpha_lt`, `hypset_ok`, `thy`, `sigof`, `axsof`, `is_std_sig`,
`theory_ok`, `proves`, `update`, `types_of_upd`, `consts_of_upd`, `type_list`, `tysof_ctxt`,
`const_list`, `tmsof_ctxt`, `sigof_ctxt`, `axexts_of_upd`, `conexts_of_upd`, `axexts`,
`conexts`, `axioms_of_upd`, `axiom_list`, `axsof_ctxt`, `thyof`, `updates`.

`HolSyntaxExtra.lean`: `subtype1`, `subtype`, `subterm1`, `subterm`, `dbterm_ty`, `bind`,
`db`, `dbVSUBST`, `dbVFREE_IN`, `dbINST`, `dbterm`, `bind_list_aux`, `bv_names`,
`simple_subst`, `simple_inst`, `rename_bvars`, `fresh`, `types_in`, `arities_match`.

`HolSemantics.lean`: `inhabited`, `tyass`, `is_type_assignment0`, `tyval`,
`is_type_valuation0`, `typesem`, `tmass`, `is_term_assignment0`, `tmval`,
`is_term_valuation0`, `interpretation`, `tyaof`, `tmaof`, `valuation`, `tyvof`, `tmvof`,
`is_valuation0`, `instance'`, `termsem0`, `satisfies0`, `is_interpretation0`,
`is_std_type_assignment0`, `interprets0`, `is_std_interpretation0`, `models0`, `entails0`,
`is_structure0`.

`HolSemanticsExtra.lean`: `Equalsem`.

Package definitions that no target needs are not translated (for example `LLOOKUP`,
`mlstring_le`, `fresh_term`, `vfree_in`, `variant`, `frees`, `ConstDef`, `extends`).

## 8. How to write a statement: examples

HOL4 (`holSoundness`):

```
Theorem proves_sound:
   is_set_theory ^mem ⇒ ∀thyh c. thyh |- c ⇒ thyh |= c
```

Lean:

```lean
theorem proves_sound {U : Type} [Nonempty U] (mem : U → U → Prop) :
    is_set_theory mem → ∀ thyh c, proves thyh c → entails0 mem thyh c := by
  sorry
```

HOL4 (`holSemanticsExtra`):

```
Theorem termsem_equation:
   is_set_theory ^mem ⇒
    ∀sig i v s t tmenv.
    is_structure sig i v ∧ term_ok sig (s === t) ∧ tmenv = tmsof sig
    ⇒ termsem tmenv i v (s === t) = Boolean (termsem tmenv i v s = termsem tmenv i v t)
```

Lean:

```lean
theorem termsem_equation {U : Type} [Nonempty U] (mem : U → U → Prop) :
    is_set_theory mem →
    ∀ (sig : sig) (i : interpretation U) (v : valuation U) (s t : term) (tmenv : tmsig),
      is_structure0 mem sig i v ∧ term_ok sig (s === t) ∧ tmenv = tmsof sig →
      termsem0 mem tmenv i v (s === t) =
        boolean mem (termsem0 mem tmenv i v s = termsem0 mem tmenv i v t) := by
  sorry
```

HOL4 (`misc`), with a free variable and a type variable:

```
Theorem find_index_shift_0:
   ∀ls x k. find_index x ls k = OPTION_MAP (λx. x + k) (find_index x ls 0)
```

Lean:

```lean
theorem find_index_shift_0 {α : Type} [Nonempty α] :
    ∀ (ls : List α) (x : α) (k : Nat),
      find_index x ls k = OPTION_MAP (fun x => x + k) (find_index x ls 0) := by
  sorry
```

Rules that these examples show:

1. Free variables of a HOL4 statement are universally quantified. Bind them in Lean (as
   arguments of the theorem or with `∀`), with their types when Lean cannot infer them.
2. Every type variable gets `{α : Type} [Nonempty α]`.
3. A statement that mentions `mem` (in HOL4: `^mem`, `<:`, or any overload of section 5.2)
   gets `{U : Type} [Nonempty U] (mem : U → U → Prop)`.
4. Keep the HOL4 quantifier order, the order of conjuncts, and the HOL4 variable names
   (rename only a variable that hides a constant or a type that the statement needs).
5. A theorem that HOL4 states as `Theorem name = <ML expression>` (`w2n_lt_256`,
   `splitlines_nil`, `subtype_Tyvar`, `subterm_Var`, `subterm_Const`, `type_lt_thm`,
   `term_lt_thm`) has no source statement: write the theorem that the expression produces.

## 9. Check list for stage 2

- No `Char`, `String`, `Bool`, `Ordering` of Lean in a statement: use `char`, `string`,
  `Prop`, `ordering`.
- `Bool'` (the HOL type `bool` of the object logic), `true0 mem`, `false0 mem`, `instance'`,
  `dbterm_ty`.
- `tysof thy` / `tmsof thy` at a theory: `tysof (sigof thy)` / `tmsof (sigof thy)`.
- `app_list.Nil`, `app_list.List xs`, `app_list.Append l1 l2`.
- `sptree.insert`, `sptree.domain`; `domain` alone is the `holSyntax` constant.
- `chr!"…"` takes a string literal with one character. `str!`, `ml!`, `chr!` are applied
  without parentheses: `Tyapp ml!"fun" [s, t]`.
- Theorem names `RACONV_thm` and `REV_ASSOCD_thm`.
