import CmlTS
open CmlTS
open scoped Classical
namespace CmlTS
theorem restated_decs_type_sound_no_check {ffi : Type} :
    ∀ (st : state ffi) (env : sem_env value) (ds : List dec) (st' : state ffi)
      (r : result (sem_env value) value) (ctMap : ctMap_ty) (tenvS : tenv_store)
      (tenv : type_env) (tids : Set type_ident) (tenv' : type_env),
      evaluate_decs st env ds = (st', r) ∧
      type_ds false tenv ds tids tenv' ∧
      type_sound_invariant st env ctMap tenvS tids tenv
      →
      ∃ (ctMap' : ctMap_ty) (tenvS' : tenv_store),
        weakCT ctMap' ctMap ∧
        (FRANGE (o_f (Prod.snd ∘ Prod.snd) ctMap') \
          FRANGE (o_f (Prod.snd ∘ Prod.snd) ctMap)) ⊆ tids ∧
        store_type_extension tenvS tenvS' ∧
        (match r with
          | Rval env' =>
            type_all_env ctMap' tenvS' env' tenv' ∧
            type_sound_invariant st' (extend_dec_env env' env)
              ctMap' tenvS' ∅ (extend_dec_tenv tenv' tenv)
          | Rerr (Rraise err_v) =>
            type_v 0 ctMap' tenvS' err_v Texn ∧
            type_sound_invariant st' env ctMap' tenvS' ∅ tenv
          | Rerr (Rabort Rtype_error) => False
          | Rerr (Rabort Rtimeout_error) => True
          | Rerr (Rabort (Rffi_error _)) => True) := decs_type_sound_no_check
theorem restated_op_type_sound {ffi_ty : Type} :
    ∀ (ctMap : ctMap_ty) (tenvS : tenv_store) (vs : List value) (op : CmlTS.op)
      (ts : List typ) (t : typ) (store : List (store_v value)) (ffi : ffi_state ffi_ty),
      good_ctMap ctMap ∧
      op ≠ Opapp ∧
      type_s ctMap store tenvS ∧
      type_op op ts t ∧
      check_freevars 0 [] t ∧
      LIST_REL (type_v 0 ctMap tenvS) vs ts.reverse
      →
      ∃ (tenvS' : tenv_store) (store' : List (store_v value)) (ffi' : ffi_state ffi_ty)
        (r : result value value),
        store_type_extension tenvS tenvS' ∧
        type_s ctMap store' tenvS' ∧
        do_app (store, ffi) op vs.reverse = some ((store', ffi'), r) ∧
        (match r with
          | Rval v => type_v 0 ctMap tenvS' v t
          | Rerr (Rraise v) => type_v 0 ctMap tenvS' v Texn
          | Rerr (Rabort (Rffi_error _)) => True
          | Rerr (Rabort _) => False) := op_type_sound
#print axioms restated_op_type_sound
#print axioms restated_decs_type_sound_no_check
end CmlTS
