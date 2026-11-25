import CmlTS.Ast
import CmlTS.Namespace
import CmlTS.Ffi
import CmlTS.SemanticPrimitives
import CmlTS.NamespaceProps
/-
  Translation of HOL4 theory `semanticPrimitivesProps` (semanticPrimitivesPropsScript.sml):
  definitions.
-/
set_option autoImplicit false

namespace CmlTS
open Classical

/- HOL4:
Theorem with_same_v[simp]:
   (env:'v sem_env) with v := env.v = env
   (`{ env with v := x }` is `sem_env.mk x env.c`.  It is written with the constructor because Lean
   eta-reduces `{ env with v := env.v }` to `env` while elaborating the statement.) -/
theorem with_same_v {α : Type} (env : sem_env α) : sem_env.mk env.v env.c = env := by sorry

/- HOL4:
Theorem unchanged_env[simp]:
  !(env : 'a sem_env).
  <| v := env.v; c := env.c |> = env
   (With the constructor, because Lean eta-reduces `{ v := env.v, c := env.c }` to `env`.) -/
theorem unchanged_env {α : Type} :
    ∀ env : sem_env α, sem_env.mk env.v env.c = env := by sorry

/- HOL4:
Theorem with_same_clock:
   (st:'ffi semanticPrimitives$state) with clock := st.clock = st
   (`{ st with clock := x }` is `state.mk x st.refs ...`; with the constructor, because Lean
   eta-reduces `{ st with clock := st.clock }` to `st`.) -/
theorem with_same_clock {ffiT : Type} (st : state ffiT) :
    state.mk st.clock st.refs st.ffi st.next_type_stamp st.next_exn_stamp st.eval_state
      = st := by sorry

/- HOL4:
Theorem Boolv_11[simp]:
  Boolv b1 = Boolv b2 ⇔ (b1 = b2) -/
theorem Boolv_11 (b1 b2 : Bool) : Boolv b1 = Boolv b2 ↔ (b1 = b2) := by sorry

/- HOL4:
Theorem extend_dec_env_assoc[simp]:
   !env1 env2 env3.
    extend_dec_env env1 (extend_dec_env env2 env3)
    =
    extend_dec_env (extend_dec_env env1 env2) env3 -/
theorem extend_dec_env_assoc :
    ∀ env1 env2 env3 : sem_env val,
      extend_dec_env env1 (extend_dec_env env2 env3)
      =
      extend_dec_env (extend_dec_env env1 env2) env3 := by sorry

/- HOL4:
Definition shift_lookup_def[simp]:
  (shift_lookup Lsl = word_lsl) ∧
  (shift_lookup Lsr = word_lsr) ∧
  (shift_lookup Asr = word_asr) ∧
  (shift_lookup Ror = word_ror)
End -/
def shift_lookup {n : Nat} : shift → BitVec n → Nat → BitVec n
  | .Lsl => word_lsl
  | .Lsr => word_lsr
  | .Asr => word_asr
  | .Ror => word_ror

/- HOL4:
Theorem pat_bindings_accum:
 (!p acc. pat_bindings p acc = pat_bindings p [] ++ acc) ∧
 (!ps acc. pats_bindings ps acc = pats_bindings ps [] ++ acc) -/
theorem pat_bindings_accum :
    (∀ p acc, pat_bindings p acc = pat_bindings p [] ++ acc) ∧
    (∀ ps acc, pats_bindings ps acc = pats_bindings ps [] ++ acc) := by sorry

/- HOL4:
val eqs = LIST_CONJ (map TypeBase.case_eq_of
  [``:op``, ``:'a list``, ``:'a option``, ``:v``, ``:'a store_v``, ``:lit``,
   ``:eq_result``, ``:word_size``])

Theorem pair_case_eq[local]:
  pair_CASE x f = v ⇔ ?x1 x2. x = (x1,x2) ∧ f x1 x2 = v

Theorem pair_lam_lem[local]:
  !f v z. (let (x,y) = z in f x y) = v ⇔ ∃x1 x2. z = (x1,x2) ∧ (f x1 x2 = v)

Theorem do_app_cases =
  ``do_app (s,t) op vs = SOME (st',v)`` |>
  (SIMP_CONV (srw_ss()++COND_elim_ss) [PULL_EXISTS, do_app_def, eqs, pair_case_eq, pair_lam_lem] THENC
   SIMP_CONV (srw_ss()++COND_elim_ss) [LET_THM, eqs] THENC
   ALL_CONV)

   The source gives only the left-hand side and the conversion; the right-hand side below is
   reconstructed by hand from `do_app_def` and these rewrites:
   * one disjunct per constructor of `op`, in datatype order (`case_eq_of ``:op``); the disjuncts of
     `Opapp` and `Eval` are `F` and disappear;
   * `(if P then X else NONE) = SOME x` is `P ∧ X = SOME x` (`if_option_eq`), and other conditionals
     become `(¬P ∨ ..) ∧ (P ∨ ..)` (`COND_EXPAND`);
   * `SOME ((s,t),r) = SOME (st',v)` is `(s,t) = st' ∧ r = v`;
   * the cases over `v + v` (`do_arith`, `do_conversion`) and over `ffi_result` stay case
     expressions, because their case equalities are not among the rewrites; likewise `thunk_op`,
     `store_alloc`, `copy_array`, ... are not unfolded. -/
theorem do_app_cases {ffiT : Type} (s : List (store_v val)) (t : ffi_state ffiT) (op : CmlTS.op)
    (vs : List val) (st' : List (store_v val) × ffi_state ffiT) (v : result val val) :
    do_app (s, t) op vs = some (st', v) ↔
      (∃ a ty x, op = .Arith a ty ∧ EVERY (check_type ty) vs ∧ do_arith a ty vs = some x ∧
        (match x with
          | .inl exn => some ((s, t), .Rerr (.Rraise exn))
          | .inr res => some ((s, t), .Rval res) :
            Option ((List (store_v val) × ffi_state ffiT) × result val val)) = some (st', v)) ∨
      (∃ ty1 ty2 v1 x, op = .FromTo ty1 ty2 ∧ vs = [v1] ∧ check_type ty1 v1 ∧
        do_conversion v1 ty1 ty2 = some x ∧
        (match x with
          | .inl exn => some ((s, t), .Rerr (.Rraise exn))
          | .inr res => some ((s, t), .Rval res) :
            Option ((List (store_v val) × ffi_state ffiT) × result val val)) = some (st', v)) ∨
      (∃ ws sh n, op = .Shift ws sh n ∧
        ((ws = .W8 ∧ ∃ w, vs = [Litv (Word8 w)] ∧ (s, t) = st' ∧
            Rval (Litv (Word8 (shift8_lookup sh w n))) = v) ∨
         (ws = .W64 ∧ ∃ w, vs = [Litv (Word64 w)] ∧ (s, t) = st' ∧
            Rval (Litv (Word64 (shift64_lookup sh w n))) = v))) ∨
      (∃ v1 v2 b, op = .Equality ∧ vs = [v1, v2] ∧ do_eq v1 v2 = .Eq_val b ∧
        (s, t) = st' ∧ Rval (Boolv b) = v) ∨
      (∃ test test_ty v1 v2 b, op = .Test test test_ty ∧ vs = [v1, v2] ∧
        do_test test test_ty v1 v2 = .Eq_val b ∧ (s, t) = st' ∧ Rval (Boolv b) = v) ∨
      (∃ b lnum v1 s', op = .Opassign ∧ vs = [Loc b lnum, v1] ∧
        store_assign lnum (Refv v1) s = some s' ∧ (s', t) = st' ∧ Rval (Conv none []) = v) ∨
      (∃ v1 s' n, op = .Opref ∧ vs = [v1] ∧ store_alloc (Refv v1) s = (s', n) ∧
        (s', t) = st' ∧ Rval (Loc true n) = v) ∨
      (∃ b n v1, op = .Opderef ∧ vs = [Loc b n] ∧ store_lookup n s = some (Refv v1) ∧
        (s, t) = st' ∧ Rval v1 = v) ∨
      (∃ n w, op = .Aw8alloc ∧ vs = [Litv (IntLit n), Litv (Word8 w)] ∧
        (¬ (n < 0) ∨ ((s, t) = st' ∧ Rerr (Rraise sub_exn_v) = v)) ∧
        (n < 0 ∨
          ∃ s' lnum, store_alloc (W8array (List.replicate (Num (ABS n)) w)) s = (s', lnum) ∧
            (s', t) = st' ∧ Rval (Loc true lnum) = v)) ∨
      (∃ b lnum i ws, op = .Aw8sub ∧ vs = [Loc b lnum, Litv (IntLit i)] ∧
        store_lookup lnum s = some (W8array ws) ∧
        (¬ (i < 0) ∨ ((s, t) = st' ∧ Rerr (Rraise sub_exn_v) = v)) ∧
        (i < 0 ∨
          ((¬ (Num (ABS i) ≥ ws.length) ∨ ((s, t) = st' ∧ Rerr (Rraise sub_exn_v) = v)) ∧
           (Num (ABS i) ≥ ws.length ∨
            ((s, t) = st' ∧ Rval (Litv (Word8 (EL (Num (ABS i)) ws))) = v))))) ∨
      (∃ b n ws, op = .Aw8length ∧ vs = [Loc b n] ∧ store_lookup n s = some (W8array ws) ∧
        (s, t) = st' ∧ Rval (Litv (IntLit (ws.length : Int))) = v) ∨
      (∃ b lnum i w ws, op = .Aw8update ∧
        vs = [Loc b lnum, Litv (IntLit i), Litv (Word8 w)] ∧
        store_lookup lnum s = some (W8array ws) ∧
        (¬ (i < 0) ∨ ((s, t) = st' ∧ Rerr (Rraise sub_exn_v) = v)) ∧
        (i < 0 ∨
          ((¬ (Num (ABS i) ≥ ws.length) ∨ ((s, t) = st' ∧ Rerr (Rraise sub_exn_v) = v)) ∧
           (Num (ABS i) ≥ ws.length ∨
            ∃ s', store_assign lnum (W8array (ws.set (Num (ABS i)) w)) s = some s' ∧
              (s', t) = st' ∧ Rval (Conv none []) = v)))) ∨
      (∃ strng off len, op = .CopyStrStr ∧
        vs = [Litv (StrLit strng), Litv (IntLit off), Litv (IntLit len)] ∧
        (s, t) = st' ∧
        ((copy_array (explode strng, off) len none = none ∧ Rerr (Rraise sub_exn_v) = v) ∨
         (∃ cs, copy_array (explode strng, off) len none = some cs ∧
            Rval (Litv (StrLit (implode cs))) = v))) ∨
      (∃ strng off len b dst dstoff ws, op = .CopyStrAw8 ∧
        vs = [Litv (StrLit strng), Litv (IntLit off), Litv (IntLit len),
              Loc b dst, Litv (IntLit dstoff)] ∧
        store_lookup dst s = some (W8array ws) ∧
        ((copy_array (explode strng, off) len (some (ws_to_chars ws, dstoff)) = none ∧
            (s, t) = st' ∧ Rerr (Rraise sub_exn_v) = v) ∨
         (∃ cs s', copy_array (explode strng, off) len (some (ws_to_chars ws, dstoff)) = some cs ∧
            store_assign dst (W8array (chars_to_ws cs)) s = some s' ∧
            (s', t) = st' ∧ Rval (Conv none []) = v))) ∨
      (∃ b src off len ws, op = .CopyAw8Str ∧
        vs = [Loc b src, Litv (IntLit off), Litv (IntLit len)] ∧
        store_lookup src s = some (W8array ws) ∧
        (s, t) = st' ∧
        ((copy_array (ws, off) len none = none ∧ Rerr (Rraise sub_exn_v) = v) ∨
         (∃ ws', copy_array (ws, off) len none = some ws' ∧
            Rval (Litv (StrLit (implode (ws_to_chars ws')))) = v))) ∨
      (∃ b1 src off len b2 dst dstoff ws ds, op = .CopyAw8Aw8 ∧
        vs = [Loc b1 src, Litv (IntLit off), Litv (IntLit len),
              Loc b2 dst, Litv (IntLit dstoff)] ∧
        store_lookup src s = some (W8array ws) ∧
        store_lookup dst s = some (W8array ds) ∧
        ((copy_array (ws, off) len (some (ds, dstoff)) = none ∧
            (s, t) = st' ∧ Rerr (Rraise sub_exn_v) = v) ∨
         (∃ ws' s', copy_array (ws, off) len (some (ds, dstoff)) = some ws' ∧
            store_assign dst (W8array ws') s = some s' ∧
            (s', t) = st' ∧ Rval (Conv none []) = v))) ∨
      (∃ b dst str_arg bs new_bs s', op = .XorAw8Str_unsafe ∧
        vs = [Loc b dst, Litv (StrLit str_arg)] ∧
        store_lookup dst s = some (W8array bs) ∧
        xor_bytes ((explode str_arg).map (fun c => n2w (ORD c))) bs = some new_bs ∧
        store_assign dst (W8array new_bs) s = some s' ∧
        (s', t) = st' ∧ Rval (Conv none []) = v) ∨
      (∃ v1 ls, op = .Implode ∧ vs = [v1] ∧ v_to_char_list v1 = some ls ∧
        (s, t) = st' ∧ Rval (Litv (StrLit (implode ls))) = v) ∨
      (∃ strng, op = .Explode ∧ vs = [Litv (StrLit strng)] ∧
        (s, t) = st' ∧
        Rval (list_to_v ((explode strng).map (fun c => Litv (lit.Char c)))) = v) ∨
      (∃ strng i, op = .Strsub ∧ vs = [Litv (StrLit strng), Litv (IntLit i)] ∧
        (¬ (i < 0) ∨ ((s, t) = st' ∧ Rerr (Rraise sub_exn_v) = v)) ∧
        (i < 0 ∨
          ((¬ (Num (ABS i) ≥ strlen strng) ∨ ((s, t) = st' ∧ Rerr (Rraise sub_exn_v) = v)) ∧
           (Num (ABS i) ≥ strlen strng ∨
            ((s, t) = st' ∧ Rval (Litv (lit.Char (EL (Num (ABS i)) (explode strng)))) = v))))) ∨
      (∃ strng, op = .Strlen ∧ vs = [Litv (StrLit strng)] ∧
        (s, t) = st' ∧ Rval (Litv (IntLit (strlen strng : Int))) = v) ∨
      (∃ v1 vs' strng, op = .Strcat ∧ vs = [v1] ∧ v_to_list v1 = some vs' ∧
        vs_to_string vs' = some strng ∧ (s, t) = st' ∧ Rval (Litv (StrLit strng)) = v) ∨
      (∃ v1 vs', op = .VfromList ∧ vs = [v1] ∧ v_to_list v1 = some vs' ∧
        (s, t) = st' ∧ Rval (Vectorv vs') = v) ∨
      (∃ vs' i, op = .Vsub ∧ vs = [Vectorv vs', Litv (IntLit i)] ∧
        (¬ (i < 0) ∨ ((s, t) = st' ∧ Rerr (Rraise sub_exn_v) = v)) ∧
        (i < 0 ∨
          ((¬ (Num (ABS i) ≥ vs'.length) ∨ ((s, t) = st' ∧ Rerr (Rraise sub_exn_v) = v)) ∧
           (Num (ABS i) ≥ vs'.length ∨
            ((s, t) = st' ∧ Rval (EL (Num (ABS i)) vs') = v))))) ∨
      (∃ vs', op = .Vlength ∧ vs = [Vectorv vs'] ∧
        (s, t) = st' ∧ Rval (Litv (IntLit (vs'.length : Int))) = v) ∨
      (∃ n v1, op = .Aalloc ∧ vs = [Litv (IntLit n), v1] ∧
        (¬ (n < 0) ∨ ((s, t) = st' ∧ Rerr (Rraise sub_exn_v) = v)) ∧
        (n < 0 ∨
          ∃ s' lnum, store_alloc (Varray (List.replicate (Num (ABS n)) v1)) s = (s', lnum) ∧
            (s', t) = st' ∧ Rval (Loc true lnum) = v)) ∨
      (∃ s' lnum, op = .AallocEmpty ∧ vs = [Conv none []] ∧
        store_alloc (Varray []) s = (s', lnum) ∧
        (s', t) = st' ∧ Rval (Loc true lnum) = v) ∨
      (∃ s' lnum, op = .AallocFixed ∧ store_alloc (Varray vs) s = (s', lnum) ∧
        (s', t) = st' ∧ Rval (Loc true lnum) = v) ∨
      (∃ b lnum i vs', op = .Asub ∧ vs = [Loc b lnum, Litv (IntLit i)] ∧
        store_lookup lnum s = some (Varray vs') ∧
        (¬ (i < 0) ∨ ((s, t) = st' ∧ Rerr (Rraise sub_exn_v) = v)) ∧
        (i < 0 ∨
          ((¬ (Num (ABS i) ≥ vs'.length) ∨ ((s, t) = st' ∧ Rerr (Rraise sub_exn_v) = v)) ∧
           (Num (ABS i) ≥ vs'.length ∨
            ((s, t) = st' ∧ Rval (EL (Num (ABS i)) vs') = v))))) ∨
      (∃ b n ws, op = .Alength ∧ vs = [Loc b n] ∧ store_lookup n s = some (Varray ws) ∧
        (s, t) = st' ∧ Rval (Litv (IntLit (ws.length : Int))) = v) ∨
      (∃ b lnum i v1 vs', op = .Aupdate ∧ vs = [Loc b lnum, Litv (IntLit i), v1] ∧
        store_lookup lnum s = some (Varray vs') ∧
        (¬ (i < 0) ∨ ((s, t) = st' ∧ Rerr (Rraise sub_exn_v) = v)) ∧
        (i < 0 ∨
          ((¬ (Num (ABS i) ≥ vs'.length) ∨ ((s, t) = st' ∧ Rerr (Rraise sub_exn_v) = v)) ∧
           (Num (ABS i) ≥ vs'.length ∨
            ∃ s', store_assign lnum (Varray (vs'.set (Num (ABS i)) v1)) s = some s' ∧
              (s', t) = st' ∧ Rval (Conv none []) = v)))) ∨
      (∃ vs' i, op = .Vsub_unsafe ∧ vs = [Vectorv vs', Litv (IntLit i)] ∧
        (0 ≤ i ∧ Num i < vs'.length) ∧
        (s, t) = st' ∧ Rval (EL (Num i) vs') = v) ∨
      (∃ b lnum i vs', op = .Asub_unsafe ∧ vs = [Loc b lnum, Litv (IntLit i)] ∧
        store_lookup lnum s = some (Varray vs') ∧
        ¬ (i < 0) ∧ ¬ (Num (ABS i) ≥ vs'.length) ∧
        (s, t) = st' ∧ Rval (EL (Num (ABS i)) vs') = v) ∨
      (∃ b lnum i v1 vs' s', op = .Aupdate_unsafe ∧ vs = [Loc b lnum, Litv (IntLit i), v1] ∧
        store_lookup lnum s = some (Varray vs') ∧
        ¬ (i < 0) ∧ ¬ (Num (ABS i) ≥ vs'.length) ∧
        store_assign lnum (Varray (vs'.set (Num (ABS i)) v1)) s = some s' ∧
        (s', t) = st' ∧ Rval (Conv none []) = v) ∨
      (∃ b lnum i ws, op = .Aw8sub_unsafe ∧ vs = [Loc b lnum, Litv (IntLit i)] ∧
        store_lookup lnum s = some (W8array ws) ∧
        ¬ (i < 0) ∧ ¬ (Num (ABS i) ≥ ws.length) ∧
        (s, t) = st' ∧ Rval (Litv (Word8 (EL (Num (ABS i)) ws))) = v) ∨
      (∃ b lnum i w ws s', op = .Aw8update_unsafe ∧
        vs = [Loc b lnum, Litv (IntLit i), Litv (Word8 w)] ∧
        store_lookup lnum s = some (W8array ws) ∧
        ¬ (i < 0) ∧ ¬ (Num (ABS i) ≥ ws.length) ∧
        store_assign lnum (W8array (ws.set (Num (ABS i)) w)) s = some s' ∧
        (s', t) = st' ∧ Rval (Conv none []) = v) ∨
      (∃ th_op, op = .ThunkOp th_op ∧ do_thunk_op (s, t) th_op vs = some (st', v)) ∨
      (∃ x1 x2 xs ys, op = .ListAppend ∧ vs = [x1, x2] ∧
        v_to_list x1 = some xs ∧ v_to_list x2 = some ys ∧
        (s, t) = st' ∧ Rval (list_to_v (xs ++ ys)) = v) ∨
      (∃ i j, op = .ConfigGC ∧ vs = [Litv (IntLit i), Litv (IntLit j)] ∧
        (s, t) = st' ∧ Rval (Conv none []) = v) ∨
      (∃ n conf b lnum ws, op = .FFI n ∧ vs = [Litv (StrLit conf), Loc b lnum] ∧
        store_lookup lnum s = some (W8array ws) ∧
        (match call_FFI t (.ExtCall n) ((explode conf).map (fun c => n2w (ORD c))) ws with
          | .FFI_return t' ws' =>
            match store_assign lnum (W8array ws') s with
            | none => none
            | some s' => some ((s', t'), .Rval (.Conv none []))
          | .FFI_final outcome => some ((s, t), .Rerr (.Rabort (.Rffi_error outcome))) :
            Option ((List (store_v val) × ffi_state ffiT) × result val val)) = some (st', v)) ∨
      (∃ v1 l, op = .Env_id ∧ vs = v1 :: l ∧
        ((∃ gen id, v1 = Conv none [gen, id] ∧ l = [] ∧
            (s, t) = st' ∧ Rval (Conv none [gen, id]) = v) ∨
         (∃ env gen id, v1 = Env env (gen, id) ∧ l = [] ∧
            (s, t) = st' ∧ Rval (Conv none [nat_to_v gen, nat_to_v id]) = v))) := by sorry

/- HOL4:
Theorem build_rec_env_merge:
 ∀funs funs' env env'.
  build_rec_env funs env env' =
  nsAppend (alist_to_ns (MAP (λ(f,n,e). (f, Recclosure env funs f)) funs)) env'
   (`funs'` is unused; its HOL4 type is a type variable) -/
theorem build_rec_env_merge {α : Type} :
    ∀ (funs : List (varN × varN × exp)) (_funs' : α) (env : sem_env val)
      (env' : Namespace mlstring mlstring val),
      build_rec_env funs env env' =
      nsAppend (alist_to_ns (funs.map (fun (f, _, _) => (f, Recclosure env funs f)))) env' := by
  sorry

/- HOL4:
Theorem do_con_check_build_conv:
 !tenvC cn vs l.
  do_con_check tenvC cn l ⇒ ?v. build_conv tenvC cn vs = SOME v -/
theorem do_con_check_build_conv :
    ∀ tenvC cn vs l,
      do_con_check tenvC cn l → ∃ v, build_conv tenvC cn vs = some v := by sorry

/- HOL4:
Definition map_error_result_def[simp]:
  (map_error_result f (Rraise e) = Rraise (f e)) ∧
  (map_error_result f (Rabort a) = Rabort a)
End -/
def map_error_result {α β : Type} (f : α → β) : error_result α → error_result β
  | .Rraise e => .Rraise (f e)
  | .Rabort a => .Rabort a

/- HOL4:
Definition map_result_def[simp]:
  (map_result f1 f2 (Rval v) = Rval (f1 v)) ∧
  (map_result f1 f2 (Rerr e) = Rerr (map_error_result f2 e))
End -/
def map_result {α β γ δ : Type} (f1 : α → β) (f2 : γ → δ) : result α γ → result β δ
  | .Rval v => .Rval (f1 v)
  | .Rerr e => .Rerr (map_error_result f2 e)

/- HOL4:
Definition every_error_result_def[simp]:
  (every_error_result P (Rraise e) = P e) ∧
  (every_error_result P (Rabort a) = T)
End -/
def every_error_result {α : Type} (P : α → Prop) : error_result α → Prop
  | .Rraise e => P e
  | .Rabort _ => True

/- HOL4:
Definition every_result_def[simp]:
  (every_result P1 P2 (Rval v) = (P1 v)) ∧
  (every_result P1 P2 (Rerr e) = (every_error_result P2 e))
End -/
def every_result {α β : Type} (P1 : α → Prop) (P2 : β → Prop) : result α β → Prop
  | .Rval v => P1 v
  | .Rerr e => every_error_result P2 e

/- HOL4:
Definition map_sv_def[simp]:
  map_sv f (Refv v) = Refv (f v) ∧
  map_sv _ (W8array w) = (W8array w) ∧
  map_sv f (Varray vs) = (Varray (MAP f vs)) ∧
  map_sv f (Thunk m v) = (Thunk m (f v))
End -/
def map_sv {α β : Type} (f : α → β) : store_v α → store_v β
  | .Refv v => .Refv (f v)
  | .W8array w => .W8array w
  | .Varray vs => .Varray (vs.map f)
  | .Thunk m v => .Thunk m (f v)

/- HOL4:
Definition dest_Refv_def[simp]:
  dest_Refv (Refv v) = v
End
   (ARB on the other constructors) -/
noncomputable def dest_Refv {α : Type} [Nonempty α] : store_v α → α
  | .Refv v => v
  | _ => ARB

/- HOL4:
Definition store_v_vs_def[simp]:
  store_v_vs (Refv v) = [v] ∧
  store_v_vs (Varray vs) = vs ∧
  store_v_vs (W8array _) = [] ∧
  store_v_vs (Thunk _ v) = [v]
End -/
def store_v_vs {α : Type} : store_v α → List α
  | .Refv v => [v]
  | .Varray vs => vs
  | .W8array _ => []
  | .Thunk _ v => [v]

/- HOL4:
Definition ctors_of_tdef_def[simp]:
  ctors_of_tdef (_,_,condefs) = MAP FST condefs
End -/
def ctors_of_tdef {α β γ δ : Type} : α × β × List (γ × δ) → List γ
  | (_, _, condefs) => condefs.map Prod.fst

/- HOL4:
Definition FV_def[simp]:
  (FV (Raise e) = FV e) ∧
  (FV (Handle e pes) = FV e ∪ FV_pes pes) ∧
  (FV (Lit _) = {}) ∧
  (FV (Con _ ls) = FV_list ls) ∧
  (FV (Var id) = {id}) ∧
  (FV (Fun x e) = FV e DIFF {Short x}) ∧
  (FV (App _ es) = FV_list es) ∧
  (FV (Log _ e1 e2) = FV e1 ∪ FV e2) ∧
  (FV (If e1 e2 e3) = FV e1 ∪ FV e2 ∪ FV e3) ∧
  (FV (Mat e pes) = FV e ∪ FV_pes pes) ∧
  (FV (Let xo e b) = FV e ∪ (FV b DIFF (case xo of NONE => {} | SOME x => {Short x}))) ∧
  (FV (Letrec defs b) = FV_defs defs ∪ FV b DIFF set (MAP (Short o FST) defs)) ∧
  (FV (Tannot e t) = FV e) ∧
  (FV (Lannot e l) = FV e) ∧
  (FV_list [] = {}) ∧
  (FV_list (e::es) = FV e ∪ FV_list es) ∧
  (FV_pes [] = {}) ∧
  (FV_pes ((p,e)::pes) =
     (FV e DIFF (IMAGE Short (set (pat_bindings p [])))) ∪ FV_pes pes) ∧
  (FV_defs [] = {}) ∧
  (FV_defs ((_,x,e)::defs) =
     (FV e DIFF {Short x}) ∪ FV_defs defs)
End
   (HOL4 `UNION` and `DIFF` are both `Infixl 500`, so `a ∪ b DIFF c` is `(a ∪ b) DIFF c`.) -/
mutual
def FV : exp → Set (ident modN varN)
  | .Raise e => FV e
  | .Handle e pes => FV e ∪ FV_pes pes
  | .Lit _ => ∅
  | .Con _ ls => FV_list ls
  | .Var id => {id}
  | .Fun x e => FV e \ {.Short x}
  | .App _ es => FV_list es
  | .Log _ e1 e2 => FV e1 ∪ FV e2
  | .If e1 e2 e3 => (FV e1 ∪ FV e2) ∪ FV e3
  | .Mat e pes => FV e ∪ FV_pes pes
  | .Let xo e b =>
    FV e ∪ (FV b \ (match xo with | none => ∅ | some x => {.Short x}))
  | .Letrec defs b =>
    (FV_defs defs ∪ FV b) \ LIST_TO_SET (defs.map fun d => .Short d.1)
  | .Tannot e _ => FV e
  | .Lannot e _ => FV e
termination_by e => sizeOf e
def FV_list : List exp → Set (ident modN varN)
  | [] => ∅
  | e :: es => FV e ∪ FV_list es
termination_by es => sizeOf es
def FV_pes : List (pat × exp) → Set (ident modN varN)
  | [] => ∅
  | (p, e) :: pes =>
    (FV e \ IMAGE .Short (LIST_TO_SET (pat_bindings p []))) ∪ FV_pes pes
termination_by pes => sizeOf pes
def FV_defs : List (varN × varN × exp) → Set (ident modN varN)
  | [] => ∅
  | (_, x, e) :: defs => (FV e \ {.Short x}) ∪ FV_defs defs
termination_by defs => sizeOf defs
end

/- HOL4:
Theorem FV_pes_MAP:
   FV_pes pes = BIGUNION (IMAGE (λ(p,e). FV e DIFF (IMAGE Short (set (pat_bindings p [])))) (set pes)) -/
theorem FV_pes_MAP (pes : List (pat × exp)) :
    FV_pes pes = BIGUNION (IMAGE
      (fun (p, e) => FV e \ (IMAGE .Short (LIST_TO_SET (pat_bindings p []))))
      (LIST_TO_SET pes)) := by sorry

/- HOL4:
Theorem FV_defs_MAP:
   ∀ls. FV_defs ls = BIGUNION (IMAGE (λ(f,x,e). FV e DIFF {Short x}) (set ls)) -/
theorem FV_defs_MAP :
    ∀ ls, FV_defs ls =
      BIGUNION (IMAGE (fun (_, x, e) => FV e \ {.Short x}) (LIST_TO_SET ls)) := by sorry

/- HOL4:
Definition FV_dec_def[simp]:
  (FV_dec (Dlet locs p e) = FV (Mat e [(p,Lit ARB)])) ∧
  (FV_dec (Dletrec locs defs) = FV (Letrec defs (Lit ARB)))∧
  (FV_dec (Dtype _ _) = {}) ∧
  (FV_dec (Dtabbrev _ _ _ _) = {}) ∧
  (FV_dec (Dexn _ _ _) = {})
End
   (ARB on the other constructors) -/
noncomputable def FV_dec : dec → Set (ident modN varN)
  | .Dlet _ p e => FV (.Mat e [(p, .Lit ARB)])
  | .Dletrec _ defs => FV (.Letrec defs (.Lit ARB))
  | .Dtype _ _ => ∅
  | .Dtabbrev _ _ _ _ => ∅
  | .Dexn _ _ _ => ∅
  | _ => ARB

/- HOL4:
Theorem concrete_v_list[simp]:
  !xs. concrete_v_list xs = EVERY concrete_v xs -/
theorem concrete_v_list_thm :
    ∀ xs, concrete_v_list xs ↔ EVERY concrete_v xs := by sorry

/- HOL4:
Theorem prim_type_cases:
  ∀ty.
    ty = BoolT ∨
    ty = IntT ∨
    ty = CharT ∨
    ty = StrT ∨
    ty = WordT W8 ∨
    ty = WordT W64 ∨
    ty = Float64T -/
theorem prim_type_cases :
    ∀ ty,
      ty = BoolT ∨
      ty = IntT ∨
      ty = CharT ∨
      ty = StrT ∨
      ty = WordT W8 ∨
      ty = WordT W64 ∨
      ty = Float64T := by sorry

end CmlTS
