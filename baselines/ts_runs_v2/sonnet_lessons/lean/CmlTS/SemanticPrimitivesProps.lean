import CmlTS.Ast
import CmlTS.Namespace
import CmlTS.Ffi
import CmlTS.SemanticPrimitives
import CmlTS.NamespaceProps

/-!
# semanticPrimitivesProps (HOL4 theory `semanticPrimitivesProps`)

Definitions of this theory (the theorems are for stage 2).
-/

universe u v w

noncomputable section

open Classical

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
   Definition map_error_result_def[simp]:
     (map_error_result f (Rraise e) = Rraise (f e)) ∧
     (map_error_result f (Rabort a) = Rabort a)
   End -/
def map_error_result {α : Type u} {β : Type v} (f : α → β) : error_result α → error_result β
  | .Rraise e => .Rraise (f e)
  | .Rabort a => .Rabort a

/- HOL4:
   Definition map_result_def[simp]:
     (map_result f1 f2 (Rval v) = Rval (f1 v)) ∧
     (map_result f1 f2 (Rerr e) = Rerr (map_error_result f2 e))
   End -/
def map_result {α : Type u} {β : Type v} {γ : Type w} {δ : Type _} (f1 : α → γ) (f2 : β → δ) :
    result α β → result γ δ
  | .Rval v => .Rval (f1 v)
  | .Rerr e => .Rerr (map_error_result f2 e)

/- HOL4:
   Definition every_error_result_def[simp]:
     (every_error_result P (Rraise e) = P e) ∧
     (every_error_result P (Rabort a) = T)
   End -/
def every_error_result {α : Type u} (P : α → Prop) : error_result α → Prop
  | .Rraise e => P e
  | .Rabort _ => True

/- HOL4:
   Definition every_result_def[simp]:
     (every_result P1 P2 (Rval v) = (P1 v)) ∧
     (every_result P1 P2 (Rerr e) = (every_error_result P2 e))
   End -/
def every_result {α : Type u} {β : Type v} (P1 : α → Prop) (P2 : β → Prop) :
    result α β → Prop
  | .Rval v => P1 v
  | .Rerr e => every_error_result P2 e

/- HOL4:
   Definition map_sv_def[simp]:
     map_sv f (Refv v) = Refv (f v) ∧
     map_sv _ (W8array w) = (W8array w) ∧
     map_sv f (Varray vs) = (Varray (MAP f vs)) ∧
     map_sv f (Thunk m v) = (Thunk m (f v))
   End -/
def map_sv {α : Type u} {β : Type v} (f : α → β) : store_v α → store_v β
  | .Refv v => .Refv (f v)
  | .W8array w => .W8array w
  | .Varray vs => .Varray (MAP f vs)
  | .Thunk m v => .Thunk m (f v)

/- HOL4:
   Definition dest_Refv_def[simp]:
     dest_Refv (Refv v) = v
   End
   (other store values: unspecified, `ARB`) -/
def dest_Refv {α : Type u} [Nonempty α] : store_v α → α
  | .Refv v => v
  | _ => ARB

/- HOL4:
   Definition store_v_vs_def[simp]:
     store_v_vs (Refv v) = [v] ∧
     store_v_vs (Varray vs) = vs ∧
     store_v_vs (W8array _) = [] ∧
     store_v_vs (Thunk _ v) = [v]
   End -/
def store_v_vs {α : Type u} : store_v α → List α
  | .Refv v => [v]
  | .Varray vs => vs
  | .W8array _ => []
  | .Thunk _ v => [v]

/- HOL4:
   Definition ctors_of_tdef_def[simp]:
     ctors_of_tdef (_,_,condefs) = MAP FST condefs
   End -/
def ctors_of_tdef {α : Type u} {β : Type v} {γ : Type w} {δ : Type _}
    (td : α × β × List (γ × δ)) : List γ := MAP FST td.2.2

/- HOL4:
   (* free vars *)

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
   (`DIFF` and `∪` are both left-associative at the same precedence in HOL4, so the `Letrec` case is
   `(FV_defs defs ∪ FV b) DIFF set (...)`.) -/
mutual
def FV : exp → Set (Ident modN varN)
  | .Raise e => FV e
  | .Handle e pes => FV e ∪ FV_pes pes
  | .Lit _ => ∅
  | .Con _ ls => FV_list ls
  | .Var i => ({i} : Set (Ident modN varN))
  | .Fun x e => DIFF (FV e) {.Short x}
  | .App _ es => FV_list es
  | .Log _ e1 e2 => FV e1 ∪ FV e2
  | .If e1 e2 e3 => FV e1 ∪ FV e2 ∪ FV e3
  | .Mat e pes => FV e ∪ FV_pes pes
  | .Let xo e b =>
    FV e ∪ (DIFF (FV b) (match xo with | none => ∅ | some x => {.Short x}))
  | .Letrec defs b =>
    DIFF (FV_defs defs ∪ FV b) (LIST_TO_SET (MAP (Ident.Short ∘ FST) defs))
  | .Tannot e _ => FV e
  | .Lannot e _ => FV e
def FV_list : List exp → Set (Ident modN varN)
  | [] => ∅
  | e :: es => FV e ∪ FV_list es
def FV_pes : List (pat × exp) → Set (Ident modN varN)
  | [] => ∅
  | (p, e) :: pes =>
    DIFF (FV e) (IMAGE Ident.Short (LIST_TO_SET (pat_bindings p []))) ∪ FV_pes pes
def FV_defs : List (varN × varN × exp) → Set (Ident modN varN)
  | [] => ∅
  | (_, x, e) :: defs => DIFF (FV e) {.Short x} ∪ FV_defs defs
end

/- HOL4:
   Definition FV_dec_def[simp]:
     (FV_dec (Dlet locs p e) = FV (Mat e [(p,Lit ARB)])) ∧
     (FV_dec (Dletrec locs defs) = FV (Letrec defs (Lit ARB)))∧
     (FV_dec (Dtype _ _) = {}) ∧
     (FV_dec (Dtabbrev _ _ _ _) = {}) ∧
     (FV_dec (Dexn _ _ _) = {})
   End
   (`Dmod`, `Dlocal`, `Denv`: unspecified, `ARB`) -/
def FV_dec : dec → Set (Ident modN varN)
  | .Dlet _ p e => FV (.Mat e [(p, .Lit ARB)])
  | .Dletrec _ defs => FV (.Letrec defs (.Lit ARB))
  | .Dtype _ _ => ∅
  | .Dtabbrev _ _ _ _ => ∅
  | .Dexn _ _ _ => ∅
  | _ => ARB

/- HOL4: (env:'v sem_env) with v := env.v = env -/
theorem with_same_v {V : Type} (env : sem_env V) : { env with v := env.v } = env := by sorry

/- HOL4: !(env : 'a sem_env). <| v := env.v; c := env.c |> = env -/
theorem unchanged_env {V : Type} : ∀ (env : sem_env V), (⟨env.v, env.c⟩ : sem_env V) = env := by
  sorry

/- HOL4: (st:'ffi semanticPrimitives$state) with clock := st.clock = st -/
theorem with_same_clock {α : Type} (st : state α) : { st with clock := st.clock } = st := by
  sorry

/- HOL4: Boolv b1 = Boolv b2 ⇔ (b1 = b2) -/
theorem Boolv_11 (b1 b2 : Prop) : Boolv b1 = Boolv b2 ↔ (b1 = b2) := by sorry

/- HOL4: !env1 env2 env3.
    extend_dec_env env1 (extend_dec_env env2 env3)
    =
    extend_dec_env (extend_dec_env env1 env2) env3 -/
theorem extend_dec_env_assoc :
    ∀ env1 env2 env3 : sem_env Value,
      extend_dec_env env1 (extend_dec_env env2 env3)
        = extend_dec_env (extend_dec_env env1 env2) env3 := by
  sorry

/- HOL4: (!p acc. pat_bindings p acc = pat_bindings p [] ++ acc) ∧
 (!ps acc. pats_bindings ps acc = pats_bindings ps [] ++ acc) -/
theorem pat_bindings_accum :
    (∀ (p : pat) (acc : List varN), pat_bindings p acc = pat_bindings p [] ++ acc) ∧
    (∀ (ps : List pat) (acc : List varN), pats_bindings ps acc = pats_bindings ps [] ++ acc) := by
  sorry

/- HOL4: (no explicit statement in the source: `Theorem do_app_cases = ``do_app (s,t) op vs = SOME (st',v)`` |> (SIMP_CONV ...)`;
   the statement below is the expanded case analysis of `do_app_def`, case by case in the
   order of the definition, `thunk_op` left folded as in the HOL4 simp set) -/
theorem do_app_cases {α : Type} (s : List (store_v Value)) (t : ffi_state α) (o : op)
    (vs : List Value) (st' : List (store_v Value) × ffi_state α) (v : result Value Value) :
    do_app (s, t) o vs = some (st', v) ↔
      -- ListAppend
      (o = .ListAppend ∧ ∃ x1 x2 xs ys, vs = [x1, x2] ∧ v_to_list x1 = some xs ∧
          v_to_list x2 = some ys ∧ st' = (s, t) ∧ v = .Rval (list_to_v (xs ++ ys))) ∨
      -- Shift W8
      (∃ sop n, o = .Shift .W8 sop n ∧ ∃ w, vs = [.Litv (.Word8 w)] ∧ st' = (s, t) ∧
          v = .Rval (.Litv (.Word8 (shift8_lookup sop w n)))) ∨
      -- Shift W64
      (∃ sop n, o = .Shift .W64 sop n ∧ ∃ w, vs = [.Litv (.Word64 w)] ∧ st' = (s, t) ∧
          v = .Rval (.Litv (.Word64 (shift64_lookup sop w n)))) ∨
      -- Equality
      (o = .Equality ∧ ∃ v1 v2 b, vs = [v1, v2] ∧ do_eq v1 v2 = .Eq_val b ∧ st' = (s, t) ∧
          v = .Rval (Boolv b)) ∨
      -- Opassign
      (o = .Opassign ∧ ∃ b lnum x s', vs = [.Loc b lnum, x] ∧
          store_assign lnum (.Refv x) s = some s' ∧ st' = (s', t) ∧ v = .Rval (.Conv none [])) ∨
      -- Opref
      (o = .Opref ∧ ∃ x s' n, vs = [x] ∧ store_alloc (.Refv x) s = (s', n) ∧ st' = (s', t) ∧
          v = .Rval (.Loc True n)) ∨
      -- Opderef
      (o = .Opderef ∧ ∃ b n x, vs = [.Loc b n] ∧ store_lookup n s = some (.Refv x) ∧
          st' = (s, t) ∧ v = .Rval x) ∨
      -- Aw8alloc
      (o = .Aw8alloc ∧ ∃ n w, vs = [.Litv (.IntLit n), .Litv (.Word8 w)] ∧
          ((n < 0 ∧ st' = (s, t) ∧ v = .Rerr (.Rraise sub_exn_v)) ∨
           (¬ n < 0 ∧ ∃ s' lnum, store_alloc (.W8array (REPLICATE (Num (ABS (id n))) w)) s
              = (s', lnum) ∧ st' = (s', t) ∧ v = .Rval (.Loc True lnum)))) ∨
      -- Aw8sub
      (o = .Aw8sub ∧ ∃ b lnum i ws, vs = [.Loc b lnum, .Litv (.IntLit i)] ∧
          store_lookup lnum s = some (.W8array ws) ∧ st' = (s, t) ∧
          ((i < 0 ∧ v = .Rerr (.Rraise sub_exn_v)) ∨
           (¬ i < 0 ∧
            ((Num (ABS (id i)) ≥ LENGTH ws ∧ v = .Rerr (.Rraise sub_exn_v)) ∨
             (¬ Num (ABS (id i)) ≥ LENGTH ws ∧
                v = .Rval (.Litv (.Word8 (EL (Num (ABS (id i))) ws)))))))) ∨
      -- Aw8sub_unsafe
      (o = .Aw8sub_unsafe ∧ ∃ b lnum i ws, vs = [.Loc b lnum, .Litv (.IntLit i)] ∧
          store_lookup lnum s = some (.W8array ws) ∧ ¬ i < 0 ∧ ¬ Num (ABS (id i)) ≥ LENGTH ws ∧
          st' = (s, t) ∧ v = .Rval (.Litv (.Word8 (EL (Num (ABS (id i))) ws)))) ∨
      -- Aw8length
      (o = .Aw8length ∧ ∃ b n ws, vs = [.Loc b n] ∧ store_lookup n s = some (.W8array ws) ∧
          st' = (s, t) ∧ v = .Rval (.Litv (.IntLit (int_of_num (LENGTH ws))))) ∨
      -- Aw8update
      (o = .Aw8update ∧ ∃ b lnum i w ws,
          vs = [.Loc b lnum, .Litv (.IntLit i), .Litv (.Word8 w)] ∧
          store_lookup lnum s = some (.W8array ws) ∧
          ((i < 0 ∧ st' = (s, t) ∧ v = .Rerr (.Rraise sub_exn_v)) ∨
           (¬ i < 0 ∧
            ((Num (ABS (id i)) ≥ LENGTH ws ∧ st' = (s, t) ∧ v = .Rerr (.Rraise sub_exn_v)) ∨
             (¬ Num (ABS (id i)) ≥ LENGTH ws ∧ ∃ s',
                store_assign lnum (.W8array (LUPDATE w (Num (ABS (id i))) ws)) s = some s' ∧
                st' = (s', t) ∧ v = .Rval (.Conv none [])))))) ∨
      -- Aw8update_unsafe
      (o = .Aw8update_unsafe ∧ ∃ b lnum i w ws s',
          vs = [.Loc b lnum, .Litv (.IntLit i), .Litv (.Word8 w)] ∧
          store_lookup lnum s = some (.W8array ws) ∧ ¬ i < 0 ∧ ¬ Num (ABS (id i)) ≥ LENGTH ws ∧
          store_assign lnum (.W8array (LUPDATE w (Num (ABS (id i))) ws)) s = some s' ∧
          st' = (s', t) ∧ v = .Rval (.Conv none [])) ∨
      -- CopyStrStr
      (o = .CopyStrStr ∧ ∃ strng off len,
          vs = [.Litv (.StrLit strng), .Litv (.IntLit off), .Litv (.IntLit len)] ∧
          st' = (s, t) ∧
          ((copy_array (explode strng, off) len none = none ∧ v = .Rerr (.Rraise sub_exn_v)) ∨
           (∃ cs, copy_array (explode strng, off) len none = some cs ∧
              v = .Rval (.Litv (.StrLit (implode cs)))))) ∨
      -- CopyStrAw8
      (o = .CopyStrAw8 ∧ ∃ strng off len b dst dstoff ws,
          vs = [.Litv (.StrLit strng), .Litv (.IntLit off), .Litv (.IntLit len),
                .Loc b dst, .Litv (.IntLit dstoff)] ∧
          store_lookup dst s = some (.W8array ws) ∧
          ((copy_array (explode strng, off) len (some (ws_to_chars ws, dstoff)) = none ∧
              st' = (s, t) ∧ v = .Rerr (.Rraise sub_exn_v)) ∨
           (∃ cs s', copy_array (explode strng, off) len (some (ws_to_chars ws, dstoff))
                = some cs ∧
              store_assign dst (.W8array (chars_to_ws cs)) s = some s' ∧
              st' = (s', t) ∧ v = .Rval (.Conv none [])))) ∨
      -- CopyAw8Str
      (o = .CopyAw8Str ∧ ∃ b src off len ws,
          vs = [.Loc b src, .Litv (.IntLit off), .Litv (.IntLit len)] ∧
          store_lookup src s = some (.W8array ws) ∧ st' = (s, t) ∧
          ((copy_array (ws, off) len none = none ∧ v = .Rerr (.Rraise sub_exn_v)) ∨
           (∃ ws', copy_array (ws, off) len none = some ws' ∧
              v = .Rval (.Litv (.StrLit (implode (ws_to_chars ws'))))))) ∨
      -- CopyAw8Aw8
      (o = .CopyAw8Aw8 ∧ ∃ b1 src off len b2 dst dstoff ws ds,
          vs = [.Loc b1 src, .Litv (.IntLit off), .Litv (.IntLit len),
                .Loc b2 dst, .Litv (.IntLit dstoff)] ∧
          store_lookup src s = some (.W8array ws) ∧ store_lookup dst s = some (.W8array ds) ∧
          ((copy_array (ws, off) len (some (ds, dstoff)) = none ∧
              st' = (s, t) ∧ v = .Rerr (.Rraise sub_exn_v)) ∨
           (∃ ws' s', copy_array (ws, off) len (some (ds, dstoff)) = some ws' ∧
              store_assign dst (.W8array ws') s = some s' ∧
              st' = (s', t) ∧ v = .Rval (.Conv none [])))) ∨
      -- XorAw8Str_unsafe
      (o = .XorAw8Str_unsafe ∧ ∃ b dst str_arg bs new_bs s',
          vs = [.Loc b dst, .Litv (.StrLit str_arg)] ∧
          store_lookup dst s = some (.W8array bs) ∧
          xor_bytes (MAP (n2w ∘ ORD) (explode str_arg)) bs = some new_bs ∧
          store_assign dst (.W8array new_bs) s = some s' ∧
          st' = (s', t) ∧ v = .Rval (.Conv none [])) ∨
      -- Implode
      (o = .Implode ∧ ∃ x ls, vs = [x] ∧ v_to_char_list x = some ls ∧ st' = (s, t) ∧
          v = .Rval (.Litv (.StrLit (implode ls)))) ∨
      -- Explode
      (o = .Explode ∧ ∃ strng, vs = [.Litv (.StrLit strng)] ∧ st' = (s, t) ∧
          v = .Rval (list_to_v (MAP (fun c => Value.Litv (lit.Char c)) (explode strng)))) ∨
      -- Strsub
      (o = .Strsub ∧ ∃ strng i, vs = [.Litv (.StrLit strng), .Litv (.IntLit i)] ∧
          st' = (s, t) ∧
          ((i < 0 ∧ v = .Rerr (.Rraise sub_exn_v)) ∨
           (¬ i < 0 ∧
            ((Num (ABS (id i)) ≥ strlen strng ∧ v = .Rerr (.Rraise sub_exn_v)) ∨
             (¬ Num (ABS (id i)) ≥ strlen strng ∧
                v = .Rval (.Litv (.Char (EL (Num (ABS (id i))) (explode strng))))))))) ∨
      -- Strlen
      (o = .Strlen ∧ ∃ strng, vs = [.Litv (.StrLit strng)] ∧ st' = (s, t) ∧
          v = .Rval (.Litv (.IntLit (int_of_num (strlen strng))))) ∨
      -- Strcat
      (o = .Strcat ∧ ∃ x ys strng, vs = [x] ∧ v_to_list x = some ys ∧
          vs_to_string ys = some strng ∧ st' = (s, t) ∧ v = .Rval (.Litv (.StrLit strng))) ∨
      -- VfromList
      (o = .VfromList ∧ ∃ x ys, vs = [x] ∧ v_to_list x = some ys ∧ st' = (s, t) ∧
          v = .Rval (.Vectorv ys)) ∨
      -- Vsub_unsafe
      (o = .Vsub_unsafe ∧ ∃ ys i, vs = [.Vectorv ys, .Litv (.IntLit i)] ∧
          ((0 : Int) ≤ i ∧ Num i < LENGTH ys) ∧ st' = (s, t) ∧ v = .Rval (EL (Num i) ys)) ∨
      -- Vsub
      (o = .Vsub ∧ ∃ ys i, vs = [.Vectorv ys, .Litv (.IntLit i)] ∧ st' = (s, t) ∧
          ((i < 0 ∧ v = .Rerr (.Rraise sub_exn_v)) ∨
           (¬ i < 0 ∧
            ((Num (ABS (id i)) ≥ LENGTH ys ∧ v = .Rerr (.Rraise sub_exn_v)) ∨
             (¬ Num (ABS (id i)) ≥ LENGTH ys ∧ v = .Rval (EL (Num (ABS (id i))) ys)))))) ∨
      -- Vlength
      (o = .Vlength ∧ ∃ ys, vs = [.Vectorv ys] ∧ st' = (s, t) ∧
          v = .Rval (.Litv (.IntLit (int_of_num (LENGTH ys))))) ∨
      -- Aalloc
      (o = .Aalloc ∧ ∃ n x, vs = [.Litv (.IntLit n), x] ∧
          ((n < 0 ∧ st' = (s, t) ∧ v = .Rerr (.Rraise sub_exn_v)) ∨
           (¬ n < 0 ∧ ∃ s' lnum, store_alloc (.Varray (REPLICATE (Num (ABS (id n))) x)) s
              = (s', lnum) ∧ st' = (s', t) ∧ v = .Rval (.Loc True lnum)))) ∨
      -- AallocEmpty
      (o = .AallocEmpty ∧ vs = [.Conv none []] ∧ ∃ s' lnum, store_alloc (.Varray []) s = (s', lnum) ∧
          st' = (s', t) ∧ v = .Rval (.Loc True lnum)) ∨
      -- AallocFixed
      (o = .AallocFixed ∧ ∃ s' lnum, store_alloc (.Varray vs) s = (s', lnum) ∧
          st' = (s', t) ∧ v = .Rval (.Loc True lnum)) ∨
      -- Asub
      (o = .Asub ∧ ∃ b lnum i ys, vs = [.Loc b lnum, .Litv (.IntLit i)] ∧
          store_lookup lnum s = some (.Varray ys) ∧ st' = (s, t) ∧
          ((i < 0 ∧ v = .Rerr (.Rraise sub_exn_v)) ∨
           (¬ i < 0 ∧
            ((Num (ABS (id i)) ≥ LENGTH ys ∧ v = .Rerr (.Rraise sub_exn_v)) ∨
             (¬ Num (ABS (id i)) ≥ LENGTH ys ∧ v = .Rval (EL (Num (ABS (id i))) ys)))))) ∨
      -- Asub_unsafe
      (o = .Asub_unsafe ∧ ∃ b lnum i ys, vs = [.Loc b lnum, .Litv (.IntLit i)] ∧
          store_lookup lnum s = some (.Varray ys) ∧ ¬ i < 0 ∧ ¬ Num (ABS (id i)) ≥ LENGTH ys ∧
          st' = (s, t) ∧ v = .Rval (EL (Num (ABS (id i))) ys)) ∨
      -- Alength
      (o = .Alength ∧ ∃ b n ys, vs = [.Loc b n] ∧ store_lookup n s = some (.Varray ys) ∧
          st' = (s, t) ∧ v = .Rval (.Litv (.IntLit (int_of_num (LENGTH ys))))) ∨
      -- Aupdate
      (o = .Aupdate ∧ ∃ b lnum i x ys, vs = [.Loc b lnum, .Litv (.IntLit i), x] ∧
          store_lookup lnum s = some (.Varray ys) ∧
          ((i < 0 ∧ st' = (s, t) ∧ v = .Rerr (.Rraise sub_exn_v)) ∨
           (¬ i < 0 ∧
            ((Num (ABS (id i)) ≥ LENGTH ys ∧ st' = (s, t) ∧ v = .Rerr (.Rraise sub_exn_v)) ∨
             (¬ Num (ABS (id i)) ≥ LENGTH ys ∧ ∃ s',
                store_assign lnum (.Varray (LUPDATE x (Num (ABS (id i))) ys)) s = some s' ∧
                st' = (s', t) ∧ v = .Rval (.Conv none [])))))) ∨
      -- Aupdate_unsafe
      (o = .Aupdate_unsafe ∧ ∃ b lnum i x ys s', vs = [.Loc b lnum, .Litv (.IntLit i), x] ∧
          store_lookup lnum s = some (.Varray ys) ∧ ¬ i < 0 ∧ ¬ Num (ABS (id i)) ≥ LENGTH ys ∧
          store_assign lnum (.Varray (LUPDATE x (Num (ABS (id i))) ys)) s = some s' ∧
          st' = (s', t) ∧ v = .Rval (.Conv none [])) ∨
      -- ConfigGC
      (o = .ConfigGC ∧ ∃ i j, vs = [.Litv (.IntLit i), .Litv (.IntLit j)] ∧ st' = (s, t) ∧
          v = .Rval (.Conv none [])) ∨
      -- FFI
      (∃ n, o = .FFI n ∧ ∃ conf b lnum ws, vs = [.Litv (.StrLit conf), .Loc b lnum] ∧
          store_lookup lnum s = some (.W8array ws) ∧
          ((∃ t' ws' s', call_FFI t (.ExtCall n) (MAP (n2w ∘ ORD) (explode conf)) ws
                = .FFI_return t' ws' ∧
              store_assign lnum (.W8array ws') s = some s' ∧
              st' = (s', t') ∧ v = .Rval (.Conv none [])) ∨
           (∃ outcome, call_FFI t (.ExtCall n) (MAP (n2w ∘ ORD) (explode conf)) ws
                = .FFI_final outcome ∧
              st' = (s, t) ∧ v = .Rerr (.Rabort (.Rffi_error outcome))))) ∨
      -- Env_id (two cases)
      (o = .Env_id ∧ ∃ env gen gid, vs = [.Env env (gen, gid)] ∧ st' = (s, t) ∧
          v = .Rval (.Conv none [nat_to_v gen, nat_to_v gid])) ∨
      (o = .Env_id ∧ ∃ gen gid, vs = [.Conv none [gen, gid]] ∧ st' = (s, t) ∧
          v = .Rval (.Conv none [gen, gid])) ∨
      -- ThunkOp
      (∃ th_op, o = .ThunkOp th_op ∧ thunk_op' (s, t) th_op vs = some (st', v)) ∨
      -- Arith
      (∃ a ty, o = .Arith a ty ∧ EVERY (check_type ty) vs ∧
          ((∃ res, do_arith a ty vs = some (.inr res) ∧ st' = (s, t) ∧ v = .Rval res) ∨
           (∃ exn, do_arith a ty vs = some (.inl exn) ∧ st' = (s, t) ∧
              v = .Rerr (.Rraise exn)))) ∨
      -- FromTo
      (∃ ty1 ty2, o = .FromTo ty1 ty2 ∧ ∃ x, vs = [x] ∧ check_type ty1 x ∧
          ((∃ res, do_conversion x ty1 ty2 = some (.inr res) ∧ st' = (s, t) ∧
              v = .Rval res) ∨
           (∃ exn, do_conversion x ty1 ty2 = some (.inl exn) ∧ st' = (s, t) ∧
              v = .Rerr (.Rraise exn)))) ∨
      -- Test
      (∃ tst ty, o = .Test tst ty ∧ ∃ v1 v2 b, vs = [v1, v2] ∧ do_test tst ty v1 v2 = .Eq_val b ∧
          st' = (s, t) ∧ v = .Rval (Boolv b)) := by
  sorry

/- HOL4: ∀funs funs' env env'.
  build_rec_env funs env env' =
  nsAppend (alist_to_ns (MAP (λ(f,n,e). (f, Recclosure env funs f)) funs)) env'
  (`funs'` is unused in the body, so its HOL4 type is a free type variable) -/
theorem build_rec_env_merge {γ : Type} :
    ∀ (funs : List (varN × varN × exp)) (funs' : γ) (env : sem_env Value)
      (env' : Namespace modN varN Value),
      build_rec_env funs env env' =
        nsAppend (alist_to_ns (MAP (fun (f, n, e) => (f, Value.Recclosure env funs f)) funs)) env' := by
  sorry

/- HOL4: !tenvC cn vs l.
  do_con_check tenvC cn l ⇒ ?v. build_conv tenvC cn vs = SOME v -/
theorem do_con_check_build_conv :
    ∀ (tenvC : Namespace modN conN (Nat × stamp)) (cn : Option (Ident modN conN))
      (vs : List Value) (l : Nat),
      do_con_check tenvC cn l → ∃ v, build_conv tenvC cn vs = some v := by
  sorry

/- HOL4: FV_pes pes = BIGUNION (IMAGE (λ(p,e). FV e DIFF (IMAGE Short (set (pat_bindings p [])))) (set pes)) -/
theorem FV_pes_MAP (pes : List (pat × exp)) :
    FV_pes pes = BIGUNION (IMAGE (fun (p, e) =>
      DIFF (FV e) (IMAGE Ident.Short (LIST_TO_SET (pat_bindings p [])))) (LIST_TO_SET pes)) := by
  sorry

/- HOL4: ∀ls. FV_defs ls = BIGUNION (IMAGE (λ(f,x,e). FV e DIFF {Short x}) (set ls)) -/
theorem FV_defs_MAP :
    ∀ ls : List (varN × varN × exp),
      FV_defs ls = BIGUNION (IMAGE (fun (f, x, e) =>
        DIFF (FV e) ({Ident.Short x} : Set (Ident modN varN))) (LIST_TO_SET ls)) := by
  sorry

/- HOL4: !xs. concrete_v_list xs = EVERY concrete_v xs
   (Lean name `concrete_v_list_eq`: `concrete_v_list` is already the function) -/
theorem concrete_v_list_eq : ∀ xs : List Value, concrete_v_list xs = EVERY concrete_v xs := by
  sorry

/- HOL4: ∀ty.
    ty = BoolT ∨
    ty = IntT ∨
    ty = CharT ∨
    ty = StrT ∨
    ty = WordT W8 ∨
    ty = WordT W64 ∨
    ty = Float64T -/
theorem prim_type_cases :
    ∀ ty : prim_type,
      ty = .BoolT ∨ ty = .IntT ∨ ty = .CharT ∨ ty = .StrT ∨
      ty = .WordT .W8 ∨ ty = .WordT .W64 ∨ ty = .Float64T := by
  sorry

end
