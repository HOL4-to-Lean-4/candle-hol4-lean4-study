import CmlTS.Ast
import CmlTS.Namespace
import CmlTS.Ffi
import CmlTS.SemanticPrimitives
import CmlTS.NamespaceProps

/-
HOL4 theory `semanticPrimitivesProps` (semanticPrimitivesPropsScript.sml).
-/

namespace CmlTS

noncomputable section

open scoped Classical

variable {α β γ δ : Type}

/- HOL4:
Definition shift_lookup_def[simp]:
  (shift_lookup Lsl = word_lsl) ∧
  (shift_lookup Lsr = word_lsr) ∧
  (shift_lookup Asr = word_asr) ∧
  (shift_lookup Ror = word_ror)
End -/
def shift_lookup {n : Nat} : shift → BitVec n → Nat → BitVec n
  | shift.Lsl => word_lsl
  | shift.Lsr => word_lsr
  | shift.Asr => word_asr
  | shift.Ror => word_ror

/- HOL4:
Definition map_error_result_def[simp]:
  (map_error_result f (Rraise e) = Rraise (f e)) ∧
  (map_error_result f (Rabort a) = Rabort a)
End -/
def map_error_result (f : α → β) : error_result α → error_result β
  | Rraise e => Rraise (f e)
  | Rabort a => Rabort a

/- HOL4:
Definition map_result_def[simp]:
  (map_result f1 f2 (Rval v) = Rval (f1 v)) ∧
  (map_result f1 f2 (Rerr e) = Rerr (map_error_result f2 e))
End -/
def map_result (f1 : α → β) (f2 : γ → δ) : result α γ → result β δ
  | Rval v => Rval (f1 v)
  | Rerr e => Rerr (map_error_result f2 e)

/- HOL4:
Definition every_error_result_def[simp]:
  (every_error_result P (Rraise e) = P e) ∧
  (every_error_result P (Rabort a) = T)
End -/
def every_error_result (P : α → Prop) : error_result α → Prop
  | Rraise e => P e
  | Rabort _ => True

/- HOL4:
Definition every_result_def[simp]:
  (every_result P1 P2 (Rval v) = (P1 v)) ∧
  (every_result P1 P2 (Rerr e) = (every_error_result P2 e))
End -/
def every_result (P1 : α → Prop) (P2 : β → Prop) : result α β → Prop
  | Rval v => P1 v
  | Rerr e => every_error_result P2 e

/- HOL4:
Definition map_sv_def[simp]:
  map_sv f (Refv v) = Refv (f v) ∧
  map_sv _ (W8array w) = (W8array w) ∧
  map_sv f (Varray vs) = (Varray (MAP f vs)) ∧
  map_sv f (Thunk m v) = (Thunk m (f v))
End -/
def map_sv (f : α → β) : store_v α → store_v β
  | Refv v => Refv (f v)
  | W8array w => W8array w
  | Varray vs => Varray (vs.map f)
  | Thunk m v => Thunk m (f v)

/- HOL4:
Definition dest_Refv_def[simp]:
  dest_Refv (Refv v) = v
End -/
def dest_Refv [Nonempty α] : store_v α → α
  | Refv v => v
  | _ => ARB

/- HOL4:
Definition store_v_vs_def[simp]:
  store_v_vs (Refv v) = [v] ∧
  store_v_vs (Varray vs) = vs ∧
  store_v_vs (W8array _) = [] ∧
  store_v_vs (Thunk _ v) = [v]
End -/
def store_v_vs : store_v α → List α
  | Refv v => [v]
  | Varray vs => vs
  | W8array _ => []
  | Thunk _ v => [v]

/- HOL4:
Definition ctors_of_tdef_def[simp]:
  ctors_of_tdef (_,_,condefs) = MAP FST condefs
End -/
def ctors_of_tdef : α × β × List (γ × δ) → List γ
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
(HOL4 parses `a ∪ b DIFF c` as `(a ∪ b) DIFF c`: both are left-associative at level 500) -/
mutual

def FV : exp → Set (ident modN varN)
  | exp.Raise e => FV e
  | exp.Handle e pes => FV e ∪ FV_pes pes
  | exp.Lit _ => ∅
  | exp.Con _ ls => FV_list ls
  | exp.Var id => {id}
  | exp.Fun x e => FV e \ {Short x}
  | exp.App _ es => FV_list es
  | exp.Log _ e1 e2 => FV e1 ∪ FV e2
  | exp.If e1 e2 e3 => (FV e1 ∪ FV e2) ∪ FV e3
  | exp.Mat e pes => FV e ∪ FV_pes pes
  | exp.Let xo e b =>
    FV e ∪ (FV b \ (match xo with
      | none => ∅
      | some x => {Short x}))
  | exp.Letrec defs b =>
    (FV_defs defs ∪ FV b) \ LIST_TO_SET (defs.map (Short ∘ Prod.fst))
  | exp.Tannot e _ => FV e
  | exp.Lannot e _ => FV e

def FV_list : List exp → Set (ident modN varN)
  | [] => ∅
  | e :: es => FV e ∪ FV_list es

def FV_pes : List (pat × exp) → Set (ident modN varN)
  | [] => ∅
  | (p, e) :: pes => (FV e \ IMAGE Short (LIST_TO_SET (pat_bindings p []))) ∪ FV_pes pes

def FV_defs : List (varN × varN × exp) → Set (ident modN varN)
  | [] => ∅
  | (_, x, e) :: defs => (FV e \ {Short x}) ∪ FV_defs defs

end

/- HOL4:
Definition FV_dec_def[simp]:
  (FV_dec (Dlet locs p e) = FV (Mat e [(p,Lit ARB)])) ∧
  (FV_dec (Dletrec locs defs) = FV (Letrec defs (Lit ARB)))∧
  (FV_dec (Dtype _ _) = {}) ∧
  (FV_dec (Dtabbrev _ _ _ _) = {}) ∧
  (FV_dec (Dexn _ _ _) = {})
End
(unspecified on Dmod, Dlocal and Denv) -/
def FV_dec : dec → Set (ident modN varN)
  | Dlet _ p e => FV (exp.Mat e [(p, exp.Lit ARB)])
  | Dletrec _ defs => FV (exp.Letrec defs (exp.Lit ARB))
  | Dtype _ _ => ∅
  | Dtabbrev _ _ _ _ => ∅
  | Dexn _ _ _ => ∅
  | _ => ARB

/-! ## Theorems -/

/- HOL4:
Theorem with_same_v[simp]:
   (env:'v sem_env) with v := env.v = env
(the update is written with the constructor: Lean eta-reduces `{ env with v := env.v }` to `env`) -/
theorem with_same_v {V : Type} (env : sem_env V) : sem_env.mk env.v env.c = env := rfl

/- HOL4:
Theorem unchanged_env[simp]:
  !(env : 'a sem_env).
  <| v := env.v; c := env.c |> = env
(written with the constructor: Lean eta-reduces `{ v := env.v, c := env.c }` to `env`) -/
theorem unchanged_env : ∀ env : sem_env α, sem_env.mk env.v env.c = env := fun _ => rfl

/- HOL4:
Theorem with_same_clock:
   (st:'ffi semanticPrimitives$state) with clock := st.clock = st
(the update is written with the constructor: Lean eta-reduces `{ st with clock := st.clock }` to
`st`) -/
theorem with_same_clock {ffi : Type} (st : state ffi) :
    state.mk st.clock st.refs st.ffi st.next_type_stamp st.next_exn_stamp st.eval_state = st := rfl

/- HOL4:
Theorem Boolv_11[simp]:
  Boolv b1 = Boolv b2 ⇔ (b1 = b2) -/
theorem Boolv_11 (b1 b2 : Bool) : Boolv b1 = Boolv b2 ↔ (b1 = b2) := by
  cases b1 <;> cases b2 <;> simp [Boolv]

/- HOL4:
Theorem extend_dec_env_assoc[simp]:
   !env1 env2 env3.
    extend_dec_env env1 (extend_dec_env env2 env3)
    =
    extend_dec_env (extend_dec_env env1 env2) env3 -/
theorem extend_dec_env_assoc :
    ∀ env1 env2 env3 : sem_env value,
      extend_dec_env env1 (extend_dec_env env2 env3) =
        extend_dec_env (extend_dec_env env1 env2) env3 := by
  intro env1 env2 env3
  simp [extend_dec_env, nsAppend_assoc]

mutual

theorem Aux.pat_bindings_accum1 :
    ∀ (p : pat) (acc : List varN), pat_bindings p acc = pat_bindings p [] ++ acc
  | Pany, acc => by simp [pat_bindings]
  | Pvar x, acc => by simp [pat_bindings]
  | Plit l, acc => by simp [pat_bindings]
  | Pcon c ps, acc => by
    simp only [pat_bindings]
    exact Aux.pats_bindings_accum1 ps acc
  | Pref p, acc => by
    simp only [pat_bindings]
    exact Aux.pat_bindings_accum1 p acc
  | Pas p i, acc => by
    simp only [pat_bindings]
    rw [Aux.pat_bindings_accum1 p (i :: acc), Aux.pat_bindings_accum1 p [i]]
    simp
  | Ptannot p t, acc => by
    simp only [pat_bindings]
    exact Aux.pat_bindings_accum1 p acc

theorem Aux.pats_bindings_accum1 :
    ∀ (ps : List pat) (acc : List varN), pats_bindings ps acc = pats_bindings ps [] ++ acc
  | [], acc => by simp [pats_bindings]
  | p :: ps, acc => by
    simp only [pats_bindings]
    rw [Aux.pats_bindings_accum1 ps (pat_bindings p acc),
      Aux.pats_bindings_accum1 ps (pat_bindings p []), Aux.pat_bindings_accum1 p acc]
    simp

end

/- HOL4:
Theorem pat_bindings_accum:
 (!p acc. pat_bindings p acc = pat_bindings p [] ++ acc) ∧
 (!ps acc. pats_bindings ps acc = pats_bindings ps [] ++ acc) -/
theorem pat_bindings_accum :
    (∀ (p : pat) (acc : List varN), pat_bindings p acc = pat_bindings p [] ++ acc) ∧
    (∀ (ps : List pat) (acc : List varN), pats_bindings ps acc = pats_bindings ps [] ++ acc) :=
  ⟨Aux.pat_bindings_accum1, Aux.pats_bindings_accum1⟩

/- HOL4:
Theorem do_app_cases =
  ``do_app (s,t) op vs = SOME (st',v)`` |>
  [HOL4 proof text removed]
(no written statement: the equivalence of the formula with the disjunction of the cases of
`do_app_def`; `thunk_op`, `do_arith`, `do_conversion`, `do_test`, `copy_array`, `store_alloc`
etc. are not unfolded) -/
set_option maxHeartbeats 8000000 in
theorem do_app_cases {ffi : Type} (s : List (store_v value)) (t : ffi_state ffi) (op : CmlTS.op)
    (vs : List value) (st' : List (store_v value) × ffi_state ffi) (v : result value value) :
    do_app (s, t) op vs = some (st', v) ↔
      (∃ a ty res, op = Arith a ty ∧ EVERY (check_type ty) vs ∧
        do_arith a ty vs = some (Sum.inr res) ∧ (s, t) = st' ∧ Rval res = v) ∨
      (∃ a ty exn, op = Arith a ty ∧ EVERY (check_type ty) vs ∧
        do_arith a ty vs = some (Sum.inl exn) ∧ (s, t) = st' ∧ Rerr (Rraise exn) = v) ∨
      (∃ ty1 ty2 v' res, op = FromTo ty1 ty2 ∧ vs = [v'] ∧ check_type ty1 v' ∧
        do_conversion v' ty1 ty2 = some (Sum.inr res) ∧ (s, t) = st' ∧ Rval res = v) ∨
      (∃ ty1 ty2 v' exn, op = FromTo ty1 ty2 ∧ vs = [v'] ∧ check_type ty1 v' ∧
        do_conversion v' ty1 ty2 = some (Sum.inl exn) ∧ (s, t) = st' ∧
        Rerr (Rraise exn) = v) ∨
      (∃ sh n w, op = Shift W8 sh n ∧ vs = [Litv (lit.Word8 w)] ∧ (s, t) = st' ∧
        Rval (Litv (lit.Word8 (shift8_lookup sh w n))) = v) ∨
      (∃ sh n w, op = Shift W64 sh n ∧ vs = [Litv (lit.Word64 w)] ∧ (s, t) = st' ∧
        Rval (Litv (lit.Word64 (shift64_lookup sh w n))) = v) ∨
      (∃ v1 v2 b, op = Equality ∧ vs = [v1, v2] ∧ do_eq v1 v2 = Eq_val b ∧ (s, t) = st' ∧
        Rval (Boolv b) = v) ∨
      (∃ test test_ty v1 v2 b, op = Test test test_ty ∧ vs = [v1, v2] ∧
        do_test test test_ty v1 v2 = Eq_val b ∧ (s, t) = st' ∧ Rval (Boolv b) = v) ∨
      (∃ b lnum v' s', op = Opassign ∧ vs = [Loc b lnum, v'] ∧
        store_assign lnum (Refv v') s = some s' ∧ (s', t) = st' ∧ Rval (Conv none []) = v) ∨
      (∃ v' s' n, op = Opref ∧ vs = [v'] ∧ store_alloc (Refv v') s = (s', n) ∧
        (s', t) = st' ∧ Rval (Loc true n) = v) ∨
      (∃ b n v', op = Opderef ∧ vs = [Loc b n] ∧ store_lookup n s = some (Refv v') ∧
        (s, t) = st' ∧ Rval v' = v) ∨
      (∃ n w, op = Aw8alloc ∧ vs = [Litv (lit.IntLit n), Litv (lit.Word8 w)] ∧ n < 0 ∧
        (s, t) = st' ∧ Rerr (Rraise sub_exn_v) = v) ∨
      (∃ n w s' lnum, op = Aw8alloc ∧ vs = [Litv (lit.IntLit n), Litv (lit.Word8 w)] ∧
        ¬ n < 0 ∧
        store_alloc (W8array (List.replicate (Num (INT_ABS (I n))) w)) s = (s', lnum) ∧
        (s', t) = st' ∧ Rval (Loc true lnum) = v) ∨
      (∃ b lnum i ws, op = Aw8sub ∧ vs = [Loc b lnum, Litv (lit.IntLit i)] ∧
        store_lookup lnum s = some (W8array ws) ∧ i < 0 ∧
        (s, t) = st' ∧ Rerr (Rraise sub_exn_v) = v) ∨
      (∃ b lnum i ws, op = Aw8sub ∧ vs = [Loc b lnum, Litv (lit.IntLit i)] ∧
        store_lookup lnum s = some (W8array ws) ∧ ¬ i < 0 ∧
        Num (INT_ABS (I i)) ≥ ws.length ∧
        (s, t) = st' ∧ Rerr (Rraise sub_exn_v) = v) ∨
      (∃ b lnum i ws, op = Aw8sub ∧ vs = [Loc b lnum, Litv (lit.IntLit i)] ∧
        store_lookup lnum s = some (W8array ws) ∧ ¬ i < 0 ∧
        ¬ Num (INT_ABS (I i)) ≥ ws.length ∧
        (s, t) = st' ∧ Rval (Litv (lit.Word8 (EL (Num (INT_ABS (I i))) ws))) = v) ∨
      (∃ b n ws, op = Aw8length ∧ vs = [Loc b n] ∧ store_lookup n s = some (W8array ws) ∧
        (s, t) = st' ∧ Rval (Litv (lit.IntLit (int_of_num ws.length))) = v) ∨
      (∃ b lnum i w ws, op = Aw8update ∧
        vs = [Loc b lnum, Litv (lit.IntLit i), Litv (lit.Word8 w)] ∧
        store_lookup lnum s = some (W8array ws) ∧ i < 0 ∧
        (s, t) = st' ∧ Rerr (Rraise sub_exn_v) = v) ∨
      (∃ b lnum i w ws, op = Aw8update ∧
        vs = [Loc b lnum, Litv (lit.IntLit i), Litv (lit.Word8 w)] ∧
        store_lookup lnum s = some (W8array ws) ∧ ¬ i < 0 ∧
        Num (INT_ABS (I i)) ≥ ws.length ∧
        (s, t) = st' ∧ Rerr (Rraise sub_exn_v) = v) ∨
      (∃ b lnum i w ws s', op = Aw8update ∧
        vs = [Loc b lnum, Litv (lit.IntLit i), Litv (lit.Word8 w)] ∧
        store_lookup lnum s = some (W8array ws) ∧ ¬ i < 0 ∧
        ¬ Num (INT_ABS (I i)) ≥ ws.length ∧
        store_assign lnum (W8array (LUPDATE w (Num (INT_ABS (I i))) ws)) s = some s' ∧
        (s', t) = st' ∧ Rval (Conv none []) = v) ∨
      (∃ strng off len, op = CopyStrStr ∧
        vs = [Litv (lit.StrLit strng), Litv (lit.IntLit off), Litv (lit.IntLit len)] ∧
        copy_array (explode strng, off) len none = none ∧
        (s, t) = st' ∧ Rerr (Rraise sub_exn_v) = v) ∨
      (∃ strng off len cs, op = CopyStrStr ∧
        vs = [Litv (lit.StrLit strng), Litv (lit.IntLit off), Litv (lit.IntLit len)] ∧
        copy_array (explode strng, off) len none = some cs ∧
        (s, t) = st' ∧ Rval (Litv (lit.StrLit (implode cs))) = v) ∨
      (∃ strng off len b dst dstoff ws, op = CopyStrAw8 ∧
        vs = [Litv (lit.StrLit strng), Litv (lit.IntLit off), Litv (lit.IntLit len),
          Loc b dst, Litv (lit.IntLit dstoff)] ∧
        store_lookup dst s = some (W8array ws) ∧
        copy_array (explode strng, off) len (some (ws_to_chars ws, dstoff)) = none ∧
        (s, t) = st' ∧ Rerr (Rraise sub_exn_v) = v) ∨
      (∃ strng off len b dst dstoff ws cs s', op = CopyStrAw8 ∧
        vs = [Litv (lit.StrLit strng), Litv (lit.IntLit off), Litv (lit.IntLit len),
          Loc b dst, Litv (lit.IntLit dstoff)] ∧
        store_lookup dst s = some (W8array ws) ∧
        copy_array (explode strng, off) len (some (ws_to_chars ws, dstoff)) = some cs ∧
        store_assign dst (W8array (chars_to_ws cs)) s = some s' ∧
        (s', t) = st' ∧ Rval (Conv none []) = v) ∨
      (∃ b src off len ws, op = CopyAw8Str ∧
        vs = [Loc b src, Litv (lit.IntLit off), Litv (lit.IntLit len)] ∧
        store_lookup src s = some (W8array ws) ∧
        copy_array (ws, off) len none = none ∧
        (s, t) = st' ∧ Rerr (Rraise sub_exn_v) = v) ∨
      (∃ b src off len ws ws', op = CopyAw8Str ∧
        vs = [Loc b src, Litv (lit.IntLit off), Litv (lit.IntLit len)] ∧
        store_lookup src s = some (W8array ws) ∧
        copy_array (ws, off) len none = some ws' ∧
        (s, t) = st' ∧ Rval (Litv (lit.StrLit (implode (ws_to_chars ws')))) = v) ∨
      (∃ b src off len b' dst dstoff ws ds, op = CopyAw8Aw8 ∧
        vs = [Loc b src, Litv (lit.IntLit off), Litv (lit.IntLit len),
          Loc b' dst, Litv (lit.IntLit dstoff)] ∧
        store_lookup src s = some (W8array ws) ∧ store_lookup dst s = some (W8array ds) ∧
        copy_array (ws, off) len (some (ds, dstoff)) = none ∧
        (s, t) = st' ∧ Rerr (Rraise sub_exn_v) = v) ∨
      (∃ b src off len b' dst dstoff ws ds ws' s', op = CopyAw8Aw8 ∧
        vs = [Loc b src, Litv (lit.IntLit off), Litv (lit.IntLit len),
          Loc b' dst, Litv (lit.IntLit dstoff)] ∧
        store_lookup src s = some (W8array ws) ∧ store_lookup dst s = some (W8array ds) ∧
        copy_array (ws, off) len (some (ds, dstoff)) = some ws' ∧
        store_assign dst (W8array ws') s = some s' ∧
        (s', t) = st' ∧ Rval (Conv none []) = v) ∨
      (∃ b dst str_arg bs new_bs s', op = XorAw8Str_unsafe ∧
        vs = [Loc b dst, Litv (lit.StrLit str_arg)] ∧
        store_lookup dst s = some (W8array bs) ∧
        xor_bytes ((explode str_arg).map (n2w ∘ ORD)) bs = some new_bs ∧
        store_assign dst (W8array new_bs) s = some s' ∧
        (s', t) = st' ∧ Rval (Conv none []) = v) ∨
      (∃ v' ls, op = Implode ∧ vs = [v'] ∧ v_to_char_list v' = some ls ∧
        (s, t) = st' ∧ Rval (Litv (lit.StrLit (implode ls))) = v) ∨
      (∃ strng, op = Explode ∧ vs = [Litv (lit.StrLit strng)] ∧
        (s, t) = st' ∧
        Rval (list_to_v ((explode strng).map (fun c => Litv (lit.Char c)))) = v) ∨
      (∃ strng i, op = Strsub ∧ vs = [Litv (lit.StrLit strng), Litv (lit.IntLit i)] ∧ i < 0 ∧
        (s, t) = st' ∧ Rerr (Rraise sub_exn_v) = v) ∨
      (∃ strng i, op = Strsub ∧ vs = [Litv (lit.StrLit strng), Litv (lit.IntLit i)] ∧
        ¬ i < 0 ∧ Num (INT_ABS (I i)) ≥ strlen strng ∧
        (s, t) = st' ∧ Rerr (Rraise sub_exn_v) = v) ∨
      (∃ strng i, op = Strsub ∧ vs = [Litv (lit.StrLit strng), Litv (lit.IntLit i)] ∧
        ¬ i < 0 ∧ ¬ Num (INT_ABS (I i)) ≥ strlen strng ∧
        (s, t) = st' ∧
        Rval (Litv (lit.Char (EL (Num (INT_ABS (I i))) (explode strng)))) = v) ∨
      (∃ strng, op = Strlen ∧ vs = [Litv (lit.StrLit strng)] ∧
        (s, t) = st' ∧ Rval (Litv (lit.IntLit (int_of_num (strlen strng)))) = v) ∨
      (∃ v' vs' strng, op = Strcat ∧ vs = [v'] ∧ v_to_list v' = some vs' ∧
        vs_to_string vs' = some strng ∧
        (s, t) = st' ∧ Rval (Litv (lit.StrLit strng)) = v) ∨
      (∃ v' vs', op = VfromList ∧ vs = [v'] ∧ v_to_list v' = some vs' ∧
        (s, t) = st' ∧ Rval (Vectorv vs') = v) ∨
      (∃ vs' i, op = Vsub ∧ vs = [Vectorv vs', Litv (lit.IntLit i)] ∧ i < 0 ∧
        (s, t) = st' ∧ Rerr (Rraise sub_exn_v) = v) ∨
      (∃ vs' i, op = Vsub ∧ vs = [Vectorv vs', Litv (lit.IntLit i)] ∧
        ¬ i < 0 ∧ Num (INT_ABS (I i)) ≥ vs'.length ∧
        (s, t) = st' ∧ Rerr (Rraise sub_exn_v) = v) ∨
      (∃ vs' i, op = Vsub ∧ vs = [Vectorv vs', Litv (lit.IntLit i)] ∧
        ¬ i < 0 ∧ ¬ Num (INT_ABS (I i)) ≥ vs'.length ∧
        (s, t) = st' ∧ Rval (EL (Num (INT_ABS (I i))) vs') = v) ∨
      (∃ vs', op = Vlength ∧ vs = [Vectorv vs'] ∧
        (s, t) = st' ∧ Rval (Litv (lit.IntLit (int_of_num vs'.length))) = v) ∨
      (∃ n v', op = Aalloc ∧ vs = [Litv (lit.IntLit n), v'] ∧ n < 0 ∧
        (s, t) = st' ∧ Rerr (Rraise sub_exn_v) = v) ∨
      (∃ n v' s' lnum, op = Aalloc ∧ vs = [Litv (lit.IntLit n), v'] ∧ ¬ n < 0 ∧
        store_alloc (Varray (List.replicate (Num (INT_ABS (I n))) v')) s = (s', lnum) ∧
        (s', t) = st' ∧ Rval (Loc true lnum) = v) ∨
      (∃ s' lnum, op = AallocEmpty ∧ vs = [Conv none []] ∧
        store_alloc (Varray []) s = (s', lnum) ∧
        (s', t) = st' ∧ Rval (Loc true lnum) = v) ∨
      (∃ s' lnum, op = AallocFixed ∧ store_alloc (Varray vs) s = (s', lnum) ∧
        (s', t) = st' ∧ Rval (Loc true lnum) = v) ∨
      (∃ b lnum i vs', op = Asub ∧ vs = [Loc b lnum, Litv (lit.IntLit i)] ∧
        store_lookup lnum s = some (Varray vs') ∧ i < 0 ∧
        (s, t) = st' ∧ Rerr (Rraise sub_exn_v) = v) ∨
      (∃ b lnum i vs', op = Asub ∧ vs = [Loc b lnum, Litv (lit.IntLit i)] ∧
        store_lookup lnum s = some (Varray vs') ∧ ¬ i < 0 ∧
        Num (INT_ABS (I i)) ≥ vs'.length ∧
        (s, t) = st' ∧ Rerr (Rraise sub_exn_v) = v) ∨
      (∃ b lnum i vs', op = Asub ∧ vs = [Loc b lnum, Litv (lit.IntLit i)] ∧
        store_lookup lnum s = some (Varray vs') ∧ ¬ i < 0 ∧
        ¬ Num (INT_ABS (I i)) ≥ vs'.length ∧
        (s, t) = st' ∧ Rval (EL (Num (INT_ABS (I i))) vs') = v) ∨
      (∃ b n ws, op = Alength ∧ vs = [Loc b n] ∧ store_lookup n s = some (Varray ws) ∧
        (s, t) = st' ∧ Rval (Litv (lit.IntLit (int_of_num ws.length))) = v) ∨
      (∃ b lnum i v' vs', op = Aupdate ∧ vs = [Loc b lnum, Litv (lit.IntLit i), v'] ∧
        store_lookup lnum s = some (Varray vs') ∧ i < 0 ∧
        (s, t) = st' ∧ Rerr (Rraise sub_exn_v) = v) ∨
      (∃ b lnum i v' vs', op = Aupdate ∧ vs = [Loc b lnum, Litv (lit.IntLit i), v'] ∧
        store_lookup lnum s = some (Varray vs') ∧ ¬ i < 0 ∧
        Num (INT_ABS (I i)) ≥ vs'.length ∧
        (s, t) = st' ∧ Rerr (Rraise sub_exn_v) = v) ∨
      (∃ b lnum i v' vs' s', op = Aupdate ∧ vs = [Loc b lnum, Litv (lit.IntLit i), v'] ∧
        store_lookup lnum s = some (Varray vs') ∧ ¬ i < 0 ∧
        ¬ Num (INT_ABS (I i)) ≥ vs'.length ∧
        store_assign lnum (Varray (LUPDATE v' (Num (INT_ABS (I i))) vs')) s = some s' ∧
        (s', t) = st' ∧ Rval (Conv none []) = v) ∨
      (∃ vs' i, op = Vsub_unsafe ∧ vs = [Vectorv vs', Litv (lit.IntLit i)] ∧
        0 ≤ i ∧ Num i < vs'.length ∧
        (s, t) = st' ∧ Rval (EL (Num i) vs') = v) ∨
      (∃ b lnum i vs', op = Asub_unsafe ∧ vs = [Loc b lnum, Litv (lit.IntLit i)] ∧
        store_lookup lnum s = some (Varray vs') ∧ ¬ i < 0 ∧
        ¬ Num (INT_ABS (I i)) ≥ vs'.length ∧
        (s, t) = st' ∧ Rval (EL (Num (INT_ABS (I i))) vs') = v) ∨
      (∃ b lnum i v' vs' s', op = Aupdate_unsafe ∧
        vs = [Loc b lnum, Litv (lit.IntLit i), v'] ∧
        store_lookup lnum s = some (Varray vs') ∧ ¬ i < 0 ∧
        ¬ Num (INT_ABS (I i)) ≥ vs'.length ∧
        store_assign lnum (Varray (LUPDATE v' (Num (INT_ABS (I i))) vs')) s = some s' ∧
        (s', t) = st' ∧ Rval (Conv none []) = v) ∨
      (∃ b lnum i ws, op = Aw8sub_unsafe ∧ vs = [Loc b lnum, Litv (lit.IntLit i)] ∧
        store_lookup lnum s = some (W8array ws) ∧ ¬ i < 0 ∧
        ¬ Num (INT_ABS (I i)) ≥ ws.length ∧
        (s, t) = st' ∧ Rval (Litv (lit.Word8 (EL (Num (INT_ABS (I i))) ws))) = v) ∨
      (∃ b lnum i w ws s', op = Aw8update_unsafe ∧
        vs = [Loc b lnum, Litv (lit.IntLit i), Litv (lit.Word8 w)] ∧
        store_lookup lnum s = some (W8array ws) ∧ ¬ i < 0 ∧
        ¬ Num (INT_ABS (I i)) ≥ ws.length ∧
        store_assign lnum (W8array (LUPDATE w (Num (INT_ABS (I i))) ws)) s = some s' ∧
        (s', t) = st' ∧ Rval (Conv none []) = v) ∨
      (∃ th_op, op = ThunkOp th_op ∧ thunk_op (s, t) th_op vs = some (st', v)) ∨
      (∃ x1 x2 xs ys, op = ListAppend ∧ vs = [x1, x2] ∧ v_to_list x1 = some xs ∧
        v_to_list x2 = some ys ∧ (s, t) = st' ∧ Rval (list_to_v (xs ++ ys)) = v) ∨
      (∃ i j, op = ConfigGC ∧ vs = [Litv (lit.IntLit i), Litv (lit.IntLit j)] ∧
        (s, t) = st' ∧ Rval (Conv none []) = v) ∨
      (∃ n conf b lnum ws t' ws' s', op = FFI n ∧
        vs = [Litv (lit.StrLit conf), Loc b lnum] ∧
        store_lookup lnum s = some (W8array ws) ∧
        call_FFI t (ExtCall n) ((explode conf).map (n2w ∘ ORD)) ws = FFI_return t' ws' ∧
        store_assign lnum (W8array ws') s = some s' ∧
        (s', t') = st' ∧ Rval (Conv none []) = v) ∨
      (∃ n conf b lnum ws outcome, op = FFI n ∧
        vs = [Litv (lit.StrLit conf), Loc b lnum] ∧
        store_lookup lnum s = some (W8array ws) ∧
        call_FFI t (ExtCall n) ((explode conf).map (n2w ∘ ORD)) ws = FFI_final outcome ∧
        (s, t) = st' ∧ Rerr (Rabort (Rffi_error outcome)) = v) ∨
      (∃ env gen id, op = Env_id ∧ vs = [Env env (gen, id)] ∧
        (s, t) = st' ∧ Rval (Conv none [nat_to_v gen, nat_to_v id]) = v) ∨
      (∃ gen id, op = Env_id ∧ vs = [Conv none [gen, id]] ∧
        (s, t) = st' ∧ Rval (Conv none [gen, id]) = v) := by
  constructor
  · intro h
    unfold do_app at h
    dsimp only at h
    split at h
    all_goals (repeat' (split at h))
    all_goals first
      | (cases h; done)
      | (simp only [Option.some.injEq, Prod.mk.injEq] at h
         obtain ⟨rfl, rfl⟩ := h
         simp only [reduceCtorEq, false_and, exists_false, false_or, or_false]
         first
           | ((repeat' first | exact True.intro | rfl | assumption | apply And.intro | apply Exists.intro); done)
           | (refine Or.inl ?_; (repeat' first | exact True.intro | rfl | assumption | apply And.intro | apply Exists.intro); done)
           | (refine Or.inr (Or.inl ?_); (repeat' first | exact True.intro | rfl | assumption | apply And.intro | apply Exists.intro); done)
           | (refine Or.inr (Or.inr ?_); (repeat' first | exact True.intro | rfl | assumption | apply And.intro | apply Exists.intro); done)
           | (refine Or.inr ?_; (repeat' first | exact True.intro | rfl | assumption | apply And.intro | apply Exists.intro); done)
         done)
      | (simp only [reduceCtorEq, false_and, exists_false, false_or, or_false])
    · rename_i hh
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      exact ⟨_, _, trivial, rfl, hh.1, hh.2, h.1, h.2⟩
    · exact ⟨_, rfl, h⟩
  · intro h
    repeat' (apply Or.elim h <;> clear h <;> intro h)
    all_goals (repeat' (obtain ⟨_, h⟩ := h))
    all_goals subst_vars
    all_goals simp only [do_app.eq_def]
    all_goals try (simp only [*, if_true, if_false]; done)
    rw [if_pos ⟨by assumption, by assumption⟩]

/- HOL4:
Theorem build_rec_env_merge:
 ∀funs funs' env env'.
  build_rec_env funs env env' =
  nsAppend (alist_to_ns (MAP (λ(f,n,e). (f, Recclosure env funs f)) funs)) env'
(`funs'` is unused, so its type is a type variable) -/
theorem build_rec_env_merge :
    ∀ (funs : List (varN × varN × exp)) (funs' : α) (env : sem_env value)
      (env' : Namespace mlstring mlstring value),
      build_rec_env funs env env' =
        nsAppend (alist_to_ns (funs.map (fun (f, _, _) => (f, Recclosure env funs f)))) env' := by
  intro funs _ env env'
  rw [nsAppend_to_nsBindList]
  unfold build_rec_env nsBindList
  rw [List.foldr_map]

/- HOL4:
Theorem do_con_check_build_conv:
 !tenvC cn vs l.
  do_con_check tenvC cn l ⇒ ?v. build_conv tenvC cn vs = SOME v -/
theorem do_con_check_build_conv :
    ∀ (tenvC : Namespace mlstring mlstring (Nat × stamp))
      (cn : Option (ident mlstring mlstring)) (vs : List value) (l : Nat),
      do_con_check tenvC cn l → ∃ v, build_conv tenvC cn vs = some v := by
  intro tenvC cn vs l h
  cases cn with
  | none => exact ⟨_, rfl⟩
  | some n =>
    simp only [do_con_check, build_conv] at h ⊢
    cases h2 : nsLookup tenvC n with
    | none => rw [h2] at h; exact h.elim
    | some p => exact ⟨_, rfl⟩

/- HOL4:
Theorem FV_pes_MAP:
   FV_pes pes = BIGUNION (IMAGE (λ(p,e). FV e DIFF (IMAGE Short (set (pat_bindings p [])))) (set pes)) -/
theorem FV_pes_MAP (pes : List (pat × exp)) :
    FV_pes pes =
      BIGUNION (IMAGE (fun (p, e) => FV e \ (IMAGE Short (LIST_TO_SET (pat_bindings p []))))
        (LIST_TO_SET pes)) := by
  induction pes with
  | nil =>
    simp only [FV_pes]
    apply Aux.set_ext
    intro x
    constructor
    · exact fun h => h.elim
    · rintro ⟨s, ⟨p, -, hp⟩, -⟩
      exact absurd hp (by simp [Aux.mem_LIST_TO_SET])
  | cons pe t ih =>
    obtain ⟨p, e⟩ := pe
    simp only [FV_pes]
    rw [ih]
    apply Aux.set_ext
    intro x
    constructor
    · rintro (h | ⟨s, ⟨p', hp, hm⟩, hx⟩)
      · exact ⟨_, ⟨(p, e), rfl, List.mem_cons_self⟩, h⟩
      · exact ⟨s, ⟨p', hp, List.mem_cons_of_mem _ hm⟩, hx⟩
    · rintro ⟨s, ⟨p', rfl, hm⟩, hx⟩
      rcases List.mem_cons.mp hm with rfl | hm
      · exact Or.inl hx
      · exact Or.inr ⟨_, ⟨p', rfl, hm⟩, hx⟩

/- HOL4:
Theorem FV_defs_MAP:
   ∀ls. FV_defs ls = BIGUNION (IMAGE (λ(f,x,e). FV e DIFF {Short x}) (set ls)) -/
theorem FV_defs_MAP :
    ∀ ls : List (varN × varN × exp),
      FV_defs ls =
        BIGUNION (IMAGE (fun (_, x, e) => FV e \ {Short x}) (LIST_TO_SET ls)) := by
  intro ls
  induction ls with
  | nil =>
    simp only [FV_defs]
    apply Aux.set_ext
    intro x
    constructor
    · exact fun h => h.elim
    · rintro ⟨s, ⟨p, -, hp⟩, -⟩
      exact absurd hp (by simp [Aux.mem_LIST_TO_SET])
  | cons pe t ih =>
    obtain ⟨f, y, e⟩ := pe
    simp only [FV_defs]
    rw [ih]
    apply Aux.set_ext
    intro x
    constructor
    · rintro (h | ⟨s, ⟨p', hp, hm⟩, hx⟩)
      · exact ⟨_, ⟨(f, y, e), rfl, List.mem_cons_self⟩, h⟩
      · exact ⟨s, ⟨p', hp, List.mem_cons_of_mem _ hm⟩, hx⟩
    · rintro ⟨s, ⟨p', rfl, hm⟩, hx⟩
      rcases List.mem_cons.mp hm with rfl | hm
      · exact Or.inl hx
      · exact Or.inr ⟨_, ⟨p', rfl, hm⟩, hx⟩

/- HOL4:
Theorem concrete_v_list[simp]:
  !xs. concrete_v_list xs = EVERY concrete_v xs
(named `concrete_v_list_thm`: `concrete_v_list` is the definition) -/
theorem concrete_v_list_thm :
    ∀ xs : List value, concrete_v_list xs ↔ EVERY concrete_v xs := by
  intro xs
  induction xs with
  | nil => simp [concrete_v_list, EVERY]
  | cons a t ih => simp [concrete_v_list, EVERY, ih]

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
    ∀ ty : prim_type,
      ty = BoolT ∨
      ty = IntT ∨
      ty = CharT ∨
      ty = StrT ∨
      ty = WordT W8 ∨
      ty = WordT W64 ∨
      ty = Float64T := by
  intro ty
  cases ty with
  | WordT sz => cases sz <;> simp
  | _ => simp

end

end CmlTS
