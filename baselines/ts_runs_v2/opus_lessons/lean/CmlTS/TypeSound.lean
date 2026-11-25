import CmlTS.Ast
import CmlTS.TypeSystem
import CmlTS.SemanticPrimitives
import CmlTS.FpSem
import CmlTS.Evaluate
import CmlTS.NamespaceProps
import CmlTS.SemanticPrimitivesProps
import CmlTS.EvaluateProps
import CmlTS.Weakening
import CmlTS.TypeSysProps
import CmlTS.TypeSoundInvariants
import CmlTS.SemanticsMin

/-
HOL4 theory `typeSound` (typeSoundScript.sml).
-/

namespace CmlTS

noncomputable section

open scoped Classical

/- HOL4:
Definition store_type_extension_def:
  store_type_extension tenvS1 tenvS2 =
  ?tenvS'. (tenvS2 = FUNION tenvS' tenvS1) ∧
           (!l. (FLOOKUP tenvS' l = NONE) ∨ (FLOOKUP tenvS1 l = NONE))
End -/
def store_type_extension {α β : Type} (tenvS1 tenvS2 : fmap α β) : Prop :=
  ∃ tenvS', tenvS2 = FUNION tenvS' tenvS1 ∧
    ∀ l, FLOOKUP tenvS' l = none ∨ FLOOKUP tenvS1 l = none

/- HOL4:
Theorem fst_triple[local]:
  (\ (x,y,z). x) = FST -/
theorem fst_triple {α β γ : Type} :
    (fun ((x, _, _) : α × β × γ) => x) = Prod.fst := by sorry

/- HOL4:
Theorem sing_list[local]:
  !l. LENGTH l = 1 ⇔ ?x. l = [x] -/
theorem sing_list {α : Type} :
    ∀ l : List α, l.length = 1 ↔ ∃ x, l = [x] := by sorry

/- HOL4:
Theorem EVERY_LIST_REL[local]:
  EVERY (\x. f x y) l = LIST_REL (\x y. f x y) l (REPLICATE (LENGTH l) y) -/
theorem EVERY_LIST_REL {α β : Type} (f : α → β → Prop) (y : β) (l : List α) :
    EVERY (fun x => f x y) l ↔
      LIST_REL (fun x y => f x y) l (List.replicate l.length y) := by sorry

/- HOL4:
Theorem v_unchanged[simp]:
  !tenv x. tenv with v := tenv.v = tenv -/
theorem v_unchanged {α : Type} :
    ∀ (tenv : type_env) (_x : α), { tenv with v := tenv.v } = tenv := by sorry

/- HOL4:
Theorem check_dup_ctors_thm:
  check_dup_ctors (tvs,tn,condefs) = ALL_DISTINCT (MAP FST condefs) -/
theorem check_dup_ctors_thm (tvs : List tvarN) (tn : mlstring)
    (condefs : List (mlstring × List ast_t)) :
    check_dup_ctors (tvs, tn, condefs) ↔ ALL_DISTINCT (condefs.map Prod.fst) := by sorry

/- HOL4:
Theorem prim_canonical_values_thm:
  (type_v tvs ctMap tenvS v Tint ∧ ctMap_ok ctMap ⇒ (∃n. v = Litv (IntLit n))) ∧
  (type_v tvs ctMap tenvS v Tchar ∧ ctMap_ok ctMap ⇒ (∃c. v = Litv (Char c))) ∧
  (type_v tvs ctMap tenvS v Tstring ∧ ctMap_ok ctMap ⇒ (∃s. v = Litv (StrLit s))) ∧
  (type_v tvs ctMap tenvS v Tword8 ∧ ctMap_ok ctMap ⇒ (∃n. v = Litv (Word8 n))) ∧
  (type_v tvs ctMap tenvS v Tword64 ∧ ctMap_ok ctMap ⇒ (∃n. v = Litv (Word64 n))) /\
  (type_v tvs ctMap tenvS v Tdouble /\ ctMap_ok ctMap ==> ∃n. v = Litv (Float64 n)) ∧
  (type_v tvs ctMap tenvS v (Ttup ts) ∧ ctMap_ok ctMap ⇒
   (∃vs. v = Conv NONE vs ∧ LENGTH ts = LENGTH vs)) ∧
  (type_v tvs ctMap tenvS v (Tfn t1 t2) ∧ ctMap_ok ctMap ⇒
   (∃env n e. v = Closure env n e) ∨
   (∃env funs n. v = Recclosure env funs n)) ∧
  (type_v tvs ctMap tenvS v (Tref t1) ∧ ctMap_ok ctMap ∧ type_s ctMap envS tenvS ⇒
   (∃n v2. v = Loc T n ∧ store_lookup n envS = SOME (Refv v2) ∧
           type_v 0 ctMap tenvS v2 t1)) ∧
  (type_v tvs ctMap tenvS v Tword8array ∧ ctMap_ok ctMap ∧ type_s ctMap envS tenvS ⇒
   (∃n ws. v = Loc T n ∧ store_lookup n envS = SOME (W8array ws) ∧
           FLOOKUP tenvS n = SOME W8array_t)) ∧
  (type_v tvs ctMap tenvS v (Tarray t) ∧ ctMap_ok ctMap ∧ type_s ctMap envS tenvS ⇒
   (∃n vs. v = Loc T n ∧ store_lookup n envS = SOME (Varray vs) ∧
           EVERY (\v. type_v 0 ctMap tenvS v t) vs ∧
           FLOOKUP tenvS n = SOME (Varray_t t))) ∧
  (type_v tvs ctMap tenvS v (Tvector t) ∧ ctMap_ok ctMap ⇒
   (?vs. v = Vectorv vs ∧ EVERY (\v. type_v tvs ctMap tenvS v t) vs)) -/
theorem prim_canonical_values_thm (tvs : Nat) (ctMap : ctMap_ty) (tenvS : tenv_store)
    (v : value) (ts : List typ) (t1 t2 : typ) (envS : List (store_v value)) (t : typ) :
    (type_v tvs ctMap tenvS v Tint ∧ ctMap_ok ctMap → (∃ n, v = Litv (lit.IntLit n))) ∧
    (type_v tvs ctMap tenvS v Tchar ∧ ctMap_ok ctMap → (∃ c, v = Litv (lit.Char c))) ∧
    (type_v tvs ctMap tenvS v Tstring ∧ ctMap_ok ctMap → (∃ s, v = Litv (lit.StrLit s))) ∧
    (type_v tvs ctMap tenvS v Tword8 ∧ ctMap_ok ctMap → (∃ n, v = Litv (lit.Word8 n))) ∧
    (type_v tvs ctMap tenvS v Tword64 ∧ ctMap_ok ctMap → (∃ n, v = Litv (lit.Word64 n))) ∧
    (type_v tvs ctMap tenvS v Tdouble ∧ ctMap_ok ctMap → ∃ n, v = Litv (lit.Float64 n)) ∧
    (type_v tvs ctMap tenvS v (Ttup ts) ∧ ctMap_ok ctMap →
      (∃ vs, v = Conv none vs ∧ ts.length = vs.length)) ∧
    (type_v tvs ctMap tenvS v (Tfn t1 t2) ∧ ctMap_ok ctMap →
      (∃ env n e, v = Closure env n e) ∨
      (∃ env funs n, v = Recclosure env funs n)) ∧
    (type_v tvs ctMap tenvS v (Tref t1) ∧ ctMap_ok ctMap ∧ type_s ctMap envS tenvS →
      (∃ n v2, v = Loc true n ∧ store_lookup n envS = some (Refv v2) ∧
        type_v 0 ctMap tenvS v2 t1)) ∧
    (type_v tvs ctMap tenvS v Tword8array ∧ ctMap_ok ctMap ∧ type_s ctMap envS tenvS →
      (∃ n ws, v = Loc true n ∧ store_lookup n envS = some (W8array ws) ∧
        FLOOKUP tenvS n = some W8array_t)) ∧
    (type_v tvs ctMap tenvS v (Tarray t) ∧ ctMap_ok ctMap ∧ type_s ctMap envS tenvS →
      (∃ n vs, v = Loc true n ∧ store_lookup n envS = some (Varray vs) ∧
        EVERY (fun v => type_v 0 ctMap tenvS v t) vs ∧
        FLOOKUP tenvS n = some (Varray_t t))) ∧
    (type_v tvs ctMap tenvS v (Tvector t) ∧ ctMap_ok ctMap →
      (∃ vs, v = Vectorv vs ∧ EVERY (fun v => type_v tvs ctMap tenvS v t) vs)) := by sorry

/- HOL4:
Theorem has_lists_v_to_list[local]:
  !ctMap tvs tenvS t3.
    ctMap_ok ctMap ∧
    ctMap_has_lists ctMap ∧
    type_v tvs ctMap tenvS v (Tlist t3)
    ⇒
    ?vs. v_to_list v = SOME vs ∧
         EVERY (\v. type_v tvs ctMap tenvS v t3) vs ∧
         (t3 = Tchar ⇒ ?vs. v_to_char_list v = SOME vs) ∧
         (t3 = Tstring ⇒ ∃str. vs_to_string vs = SOME str) -/
theorem has_lists_v_to_list (v : value) :
    ∀ (ctMap : ctMap_ty) (tvs : Nat) (tenvS : tenv_store) (t3 : typ),
      ctMap_ok ctMap ∧
      ctMap_has_lists ctMap ∧
      type_v tvs ctMap tenvS v (Tlist t3)
      →
      ∃ vs, v_to_list v = some vs ∧
        EVERY (fun v => type_v tvs ctMap tenvS v t3) vs ∧
        (t3 = Tchar → ∃ vs, v_to_char_list v = some vs) ∧
        (t3 = Tstring → ∃ str, vs_to_string vs = some str) := by sorry

/- HOL4:
Theorem ctor_canonical_values_thm:
  (type_v tvs ctMap tenvS v Tbool ∧ ctMap_ok ctMap ∧ ctMap_has_bools ctMap ⇒
   (∃b. v = Boolv b)) /\
  (type_v tvs ctMap tenvS v (Tlist t) ∧ ctMap_ok ctMap ∧ ctMap_has_lists ctMap ⇒
   ?vs.
     v_to_list v = SOME vs ∧
     EVERY (\v. type_v tvs ctMap tenvS v t) vs ∧
     (t = Tchar ⇒ ?vs. v_to_char_list v = SOME vs) ∧
     (t = Tstring ⇒ ∃str. vs_to_string vs = SOME str)) ∧
  (type_v tvs ctMap tenvS v (Tapp ts ti) ∧
   ctMap_ok ctMap ∧
   FLOOKUP ctMap stamp = SOME (tvs',ts',ti) ⇒
   (?cn n vs. same_type stamp (TypeStamp cn n) ∧ v = Conv (SOME (TypeStamp cn n)) vs) ∨
   (?n vs. same_type stamp (ExnStamp n) ∧ v = Conv (SOME (ExnStamp n)) vs)) -/
theorem ctor_canonical_values_thm (tvs : Nat) (ctMap : ctMap_ty) (tenvS : tenv_store)
    (v : value) (t : typ) (ts : List typ) (ti : type_ident) (stamp : CmlTS.stamp)
    (tvs' : List tvarN) (ts' : List typ) :
    (type_v tvs ctMap tenvS v Tbool ∧ ctMap_ok ctMap ∧ ctMap_has_bools ctMap →
      (∃ b, v = Boolv b)) ∧
    (type_v tvs ctMap tenvS v (Tlist t) ∧ ctMap_ok ctMap ∧ ctMap_has_lists ctMap →
      ∃ vs,
        v_to_list v = some vs ∧
        EVERY (fun v => type_v tvs ctMap tenvS v t) vs ∧
        (t = Tchar → ∃ vs, v_to_char_list v = some vs) ∧
        (t = Tstring → ∃ str, vs_to_string vs = some str)) ∧
    (type_v tvs ctMap tenvS v (Tapp ts ti) ∧
      ctMap_ok ctMap ∧
      FLOOKUP ctMap stamp = some (tvs', ts', ti) →
      (∃ cn n vs, same_type stamp (TypeStamp cn n) ∧ v = Conv (some (TypeStamp cn n)) vs) ∨
      (∃ n vs, same_type stamp (ExnStamp n) ∧ v = Conv (some (ExnStamp n)) vs)) := by sorry

/- HOL4:
Theorem same_type_refl[local]:
  !t. same_type t t -/
theorem same_type_refl : ∀ t : stamp, same_type t t := by sorry

/- HOL4:
Theorem eq_same_type[local]:
  (!v1 v2 tvs ctMap cns tenvS t.
     ctMap_ok ctMap ∧
     type_v tvs ctMap tenvS v1 t ∧
     type_v tvs ctMap tenvS v2 t
     ⇒
     do_eq v1 v2 ≠ Eq_type_error) ∧
  (!vs1 vs2 tvs ctMap cns tenvS ts.
     ctMap_ok ctMap ∧
     LIST_REL (type_v tvs ctMap tenvS) vs1 ts ∧
     LIST_REL (type_v tvs ctMap tenvS) vs2 ts
     ⇒
     do_eq_list vs1 vs2 ≠ Eq_type_error) -/
theorem eq_same_type {α β : Type} :
    (∀ (v1 v2 : value) (tvs : Nat) (ctMap : ctMap_ty) (_cns : α) (tenvS : tenv_store) (t : typ),
      ctMap_ok ctMap ∧
      type_v tvs ctMap tenvS v1 t ∧
      type_v tvs ctMap tenvS v2 t
      →
      do_eq v1 v2 ≠ Eq_type_error) ∧
    (∀ (vs1 vs2 : List value) (tvs : Nat) (ctMap : ctMap_ty) (_cns : β) (tenvS : tenv_store)
        (ts : List typ),
      ctMap_ok ctMap ∧
      LIST_REL (type_v tvs ctMap tenvS) vs1 ts ∧
      LIST_REL (type_v tvs ctMap tenvS) vs2 ts
      →
      do_eq_list vs1 vs2 ≠ Eq_type_error) := by sorry

/- HOL4:
Theorem type_env_conv_thm[local]:
  ∀ctMap envC tenvC.
    nsAll2 (type_ctor ctMap) envC tenvC ⇒
    ∀cn tvs ts tn ti.
      (nsLookup tenvC cn = SOME (tvs,ts,ti) ⇒
       ?cn' stamp.
         nsLookup envC cn = SOME (LENGTH ts,stamp) ∧
         FLOOKUP ctMap stamp = SOME (tvs, ts, ti)) ∧
      (nsLookup tenvC cn = NONE ⇒ nsLookup envC cn = NONE)
(`tn` and `cn'` are unused and have polymorphic types; HOL4 types are nonempty, hence
`[Nonempty ε]` for the existentially quantified `cn'`) -/
theorem type_env_conv_thm {σ α β γ m n δ ε : Type} [Nonempty ε] :
    ∀ (ctMap : fmap σ (α × List β × γ)) (envC : Namespace m n (Nat × σ))
      (tenvC : Namespace m n (α × List β × γ)),
      nsAll2 (type_ctor ctMap) envC tenvC →
      ∀ (cn : ident m n) (tvs : α) (ts : List β) (_tn : δ) (ti : γ),
        (nsLookup tenvC cn = some (tvs, ts, ti) →
          ∃ (_cn' : ε) (stamp : σ),
            nsLookup envC cn = some (ts.length, stamp) ∧
            FLOOKUP ctMap stamp = some (tvs, ts, ti)) ∧
        (nsLookup tenvC cn = none → nsLookup envC cn = none) := by sorry

/- HOL4:
Theorem type_funs_fst[local]:
  !tenv tenvE funs tenv'.
    type_funs tenv tenvE funs tenv'
    ⇒
    MAP FST funs = MAP FST tenv' -/
theorem type_funs_fst :
    ∀ (tenv : type_env) (tenvE : tenv_val_exp) (funs : List (varN × varN × exp))
      (tenv' : List (varN × typ)),
      type_funs tenv tenvE funs tenv'
      →
      funs.map Prod.fst = tenv'.map Prod.fst := by sorry

/- HOL4:
Theorem type_recfun_env_help[local]:
  ∀fn funs funs' ctMap tenv bindings tenvE env tenvS tvs bindings'.
    ALL_DISTINCT (MAP FST funs') ∧
    tenv_ok tenv ∧
    type_all_env ctMap tenvS env (tenv with v := add_tenvE tenvE tenv.v) ∧
    tenv_val_exp_ok tenvE ∧
    num_tvs tenvE = 0 ∧
    (!fn t. (ALOOKUP bindings fn = SOME t) ⇒ (ALOOKUP bindings' fn = SOME t)) ∧
    type_funs tenv (bind_var_list 0 bindings' (bind_tvar tvs tenvE)) funs' bindings' ∧
    type_funs tenv (bind_var_list 0 bindings' (bind_tvar tvs tenvE)) funs bindings
    ⇒
    LIST_REL (λ(x,y) (x',y'). x = x' ∧ (λ(tvs,t). type_v tvs ctMap tenvS y t) y')
             (MAP (λ(fn,n,e). (fn,Recclosure env funs' fn)) funs)
             (MAP (λ(x,t). (x,tvs,t)) bindings)
(the outer `fn` is unused and has a polymorphic type) -/
theorem type_recfun_env_help {α : Type} :
    ∀ (_fn : α) (funs funs' : List (varN × varN × exp)) (ctMap : ctMap_ty) (tenv : type_env)
      (bindings : List (varN × typ)) (tenvE : tenv_val_exp) (env : sem_env value)
      (tenvS : tenv_store) (tvs : Nat) (bindings' : List (varN × typ)),
      ALL_DISTINCT (funs'.map Prod.fst) ∧
      tenv_ok tenv ∧
      type_all_env ctMap tenvS env { tenv with v := add_tenvE tenvE tenv.v } ∧
      tenv_val_exp_ok tenvE ∧
      num_tvs tenvE = 0 ∧
      (∀ fn t, ALOOKUP bindings fn = some t → ALOOKUP bindings' fn = some t) ∧
      type_funs tenv (bind_var_list 0 bindings' (bind_tvar tvs tenvE)) funs' bindings' ∧
      type_funs tenv (bind_var_list 0 bindings' (bind_tvar tvs tenvE)) funs bindings
      →
      LIST_REL
        (fun ((x, y) : varN × value) ((x', y') : varN × Nat × typ) =>
          x = x' ∧ (fun ((tvs, t) : Nat × typ) => type_v tvs ctMap tenvS y t) y')
        (funs.map (fun (fn, _, _) => (fn, Recclosure env funs' fn)))
        (bindings.map (fun (x, t) => (x, tvs, t))) := by sorry

/- HOL4:
Theorem type_recfun_env[local]:
  ∀funs ctMap tenvS tvs tenv tenvE env bindings.
    tenv_ok tenv ∧
    type_all_env ctMap tenvS env (tenv with v := add_tenvE tenvE tenv.v) ∧
    tenv_val_exp_ok tenvE ∧
    num_tvs tenvE = 0 ∧
    type_funs tenv (bind_var_list 0 bindings (bind_tvar tvs tenvE)) funs bindings ∧
    ALL_DISTINCT (MAP FST funs)
    ⇒
    LIST_REL (λ(x,y) (x',y'). x = x' ∧ (λ(tvs,t). type_v tvs ctMap tenvS y t) y')
             (MAP (λ(fn,n,e). (fn,Recclosure env funs fn)) funs)
             (MAP (λ(x,t). (x,tvs,t)) bindings) -/
theorem type_recfun_env :
    ∀ (funs : List (varN × varN × exp)) (ctMap : ctMap_ty) (tenvS : tenv_store) (tvs : Nat)
      (tenv : type_env) (tenvE : tenv_val_exp) (env : sem_env value)
      (bindings : List (varN × typ)),
      tenv_ok tenv ∧
      type_all_env ctMap tenvS env { tenv with v := add_tenvE tenvE tenv.v } ∧
      tenv_val_exp_ok tenvE ∧
      num_tvs tenvE = 0 ∧
      type_funs tenv (bind_var_list 0 bindings (bind_tvar tvs tenvE)) funs bindings ∧
      ALL_DISTINCT (funs.map Prod.fst)
      →
      LIST_REL
        (fun ((x, y) : varN × value) ((x', y') : varN × Nat × typ) =>
          x = x' ∧ (fun ((tvs, t) : Nat × typ) => type_v tvs ctMap tenvS y t) y')
        (funs.map (fun (fn, _, _) => (fn, Recclosure env funs fn)))
        (bindings.map (fun (x, t) => (x, tvs, t))) := by sorry

/- HOL4:
val type_v_exn = SIMP_RULE (srw_ss()) [] (Q.prove (
  `!tvs cenv senv.
    ctMap_has_exns cenv ⇒
  type_v tvs cenv senv (Conv (SOME chr_stamp) []) Texn ∧
  type_v tvs cenv senv (Conv (SOME subscript_stamp) []) Texn ∧
  type_v tvs cenv senv (Conv (SOME bind_stamp) []) Texn ∧
  type_v tvs cenv senv (Conv (SOME div_stamp) []) Texn`, ...
(stated as in the `Q.prove`; `SIMP_RULE` gives a logically equivalent formula) -/
theorem type_v_exn :
    ∀ (tvs : Nat) (cenv : ctMap_ty) (senv : tenv_store),
      ctMap_has_exns cenv →
      type_v tvs cenv senv (Conv (some chr_stamp) []) Texn ∧
      type_v tvs cenv senv (Conv (some subscript_stamp) []) Texn ∧
      type_v tvs cenv senv (Conv (some bind_stamp) []) Texn ∧
      type_v tvs cenv senv (Conv (some div_stamp) []) Texn := by sorry

/- HOL4:
Theorem type_v_Boolv[local]:
  ctMap_has_bools ctMap ⇒ type_v tvs ctMap tenvS (Boolv b) Tbool -/
theorem type_v_Boolv (ctMap : ctMap_ty) (tvs : Nat) (tenvS : tenv_store) (b : Bool) :
    ctMap_has_bools ctMap → type_v tvs ctMap tenvS (Boolv b) Tbool := by sorry

/- HOL4:
Theorem remove_lambda_prod[local]:
  (\ (x,y). P x y) = (\xy. P (FST xy) (SND xy)) -/
theorem remove_lambda_prod {α β γ : Type} (P : α → β → γ) :
    (fun ((x, y) : α × β) => P x y) = (fun xy => P xy.1 xy.2) := by sorry

/- HOL4:
Theorem opapp_type_sound:
  !ctMap tenvS vs ts t.
    ctMap_ok ctMap ∧
    type_op Opapp ts t ∧
    LIST_REL (type_v 0 ctMap tenvS) vs ts
    ⇒
    ?env e tenv tenvE.
      tenv_ok tenv ∧
      tenv_val_exp_ok tenvE ∧
      num_tvs tenvE = 0 ∧
      type_all_env ctMap tenvS env (tenv with v := add_tenvE tenvE tenv.v) ∧
      type_e tenv tenvE e t ∧
      do_opapp vs = SOME (env,e) -/
theorem opapp_type_sound :
    ∀ (ctMap : ctMap_ty) (tenvS : tenv_store) (vs : List value) (ts : List typ) (t : typ),
      ctMap_ok ctMap ∧
      type_op Opapp ts t ∧
      LIST_REL (type_v 0 ctMap tenvS) vs ts
      →
      ∃ (env : sem_env value) (e : exp) (tenv : type_env) (tenvE : tenv_val_exp),
        tenv_ok tenv ∧
        tenv_val_exp_ok tenvE ∧
        num_tvs tenvE = 0 ∧
        type_all_env ctMap tenvS env { tenv with v := add_tenvE tenvE tenv.v } ∧
        type_e tenv tenvE e t ∧
        do_opapp vs = some (env, e) := by sorry

/- HOL4:
Theorem store_type_extension_weakS:
  !tenvS1 tenvS2.
    store_type_extension tenvS1 tenvS2 ⇒ weakS tenvS2 tenvS1 -/
theorem store_type_extension_weakS {α β : Type} :
    ∀ tenvS1 tenvS2 : fmap α β,
      store_type_extension tenvS1 tenvS2 → weakS tenvS2 tenvS1 := by sorry

/- HOL4:
Theorem store_type_extension_refl:
  !tenvS. store_type_extension tenvS tenvS -/
theorem store_type_extension_refl {α β : Type} :
    ∀ tenvS : fmap α β, store_type_extension tenvS tenvS := by sorry

/- HOL4:
Theorem store_type_extension_trans:
  !s1 s2 s3.
    store_type_extension s1 s2 ∧ store_type_extension s2 s3 ⇒
    store_type_extension s1 s3 -/
theorem store_type_extension_trans {α β : Type} :
    ∀ s1 s2 s3 : fmap α β,
      store_type_extension s1 s2 ∧ store_type_extension s2 s3 →
      store_type_extension s1 s3 := by sorry

/- HOL4:
Theorem store_assign_type_sound:
  !ctMap tenvS store sv st l.
    type_s ctMap store tenvS ∧
    FLOOKUP tenvS l = SOME st ∧
    type_sv ctMap tenvS sv st
    ⇒
    ?store'.
      store_assign l sv store = SOME store' ∧
      type_s ctMap store' tenvS -/
theorem store_assign_type_sound :
    ∀ (ctMap : ctMap_ty) (tenvS : tenv_store) (store : List (store_v value))
      (sv : store_v value) (st : store_t) (l : Nat),
      type_s ctMap store tenvS ∧
      FLOOKUP tenvS l = some st ∧
      type_sv ctMap tenvS sv st
      →
      ∃ store',
        store_assign l sv store = some store' ∧
        type_s ctMap store' tenvS := by sorry

/- HOL4:
Theorem store_alloc_type_sound:
  !ctMap tenvS store sv st.
    ctMap_ok ctMap ∧
    type_s ctMap store tenvS ∧
    type_sv ctMap tenvS sv st
    ⇒
    ?store' tenvS' n.
      store_type_extension tenvS tenvS' ∧
      store_alloc sv store = (store', n) ∧
      type_s ctMap store' tenvS' ∧
      FLOOKUP tenvS' n = SOME st -/
theorem store_alloc_type_sound :
    ∀ (ctMap : ctMap_ty) (tenvS : tenv_store) (store : List (store_v value))
      (sv : store_v value) (st : store_t),
      ctMap_ok ctMap ∧
      type_s ctMap store tenvS ∧
      type_sv ctMap tenvS sv st
      →
      ∃ (store' : List (store_v value)) (tenvS' : tenv_store) (n : Nat),
        store_type_extension tenvS tenvS' ∧
        store_alloc sv store = (store', n) ∧
        type_s ctMap store' tenvS' ∧
        FLOOKUP tenvS' n = some st := by sorry

/- HOL4:
Theorem type_v_list_to_v:
  !x xs t.
    type_v n ctMap tenvS x t /\
    v_to_list x = SOME xs ==>
    type_v n ctMap tenvS (list_to_v xs) t -/
theorem type_v_list_to_v (n : Nat) (ctMap : ctMap_ty) (tenvS : tenv_store) :
    ∀ (x : value) (xs : List value) (t : typ),
      type_v n ctMap tenvS x t ∧
      v_to_list x = some xs →
      type_v n ctMap tenvS (list_to_v xs) t := by sorry

/- HOL4:
Theorem type_v_list_to_v_APPEND:
  !xs ys t.
    ctMap_has_lists ctMap /\
    type_v 0 ctMap tenvS (list_to_v xs) (Tapp [t] Tlist_num) /\
    type_v 0 ctMap tenvS (list_to_v ys) (Tapp [t] Tlist_num)
    ==>
    type_v 0 ctMap tenvS (list_to_v (xs ++ ys)) (Tapp [t] Tlist_num) -/
theorem type_v_list_to_v_APPEND (ctMap : ctMap_ty) (tenvS : tenv_store) :
    ∀ (xs ys : List value) (t : typ),
      ctMap_has_lists ctMap ∧
      type_v 0 ctMap tenvS (list_to_v xs) (Tapp [t] Tlist_num) ∧
      type_v 0 ctMap tenvS (list_to_v ys) (Tapp [t] Tlist_num)
      →
      type_v 0 ctMap tenvS (list_to_v (xs ++ ys)) (Tapp [t] Tlist_num) := by sorry

/- HOL4:
Theorem do_eq_Boolv:
  do_eq (Boolv b) (Boolv b') = Eq_val (b = b') -/
theorem do_eq_Boolv (b b' : Bool) :
    do_eq (Boolv b) (Boolv b') = Eq_val (decide (b = b')) := by sorry

/- HOL4:
Theorem prim_canonical_Boolv_thm:
  (type_v tvs ctMap tenvS v Tbool ∧ ctMap_ok ctMap ∧ ctMap_has_bools ctMap ⇒
  (∃b. v = Boolv b)) -/
theorem prim_canonical_Boolv_thm (tvs : Nat) (ctMap : ctMap_ty) (tenvS : tenv_store)
    (v : value) :
    type_v tvs ctMap tenvS v Tbool ∧ ctMap_ok ctMap ∧ ctMap_has_bools ctMap →
    (∃ b, v = Boolv b) := by sorry

/- HOL4:
Theorem prim_canonical_Boolv_cases[local]:
  type_v tvs ctMap tenvS v (Tapp [] Tbool_num) ∧
  ctMap_ok ctMap ∧
  ctMap_has_bools ctMap ⇒
  v = Boolv T ∨ v = Boolv F -/
theorem prim_canonical_Boolv_cases (tvs : Nat) (ctMap : ctMap_ty) (tenvS : tenv_store)
    (v : value) :
    type_v tvs ctMap tenvS v (Tapp [] Tbool_num) ∧
    ctMap_ok ctMap ∧
    ctMap_has_bools ctMap →
    v = Boolv true ∨ v = Boolv false := by sorry

/- HOL4:
Theorem op_type_sound:
 !ctMap tenvS vs op ts t store (ffi : 'ffi ffi_state).
   good_ctMap ctMap ∧
   op ≠ Opapp ∧
   type_s ctMap store tenvS ∧
   type_op op ts t ∧
   check_freevars 0 [] t ∧
   LIST_REL (type_v 0 ctMap tenvS) vs (REVERSE ts)
 ⇒
 ?tenvS' store' ffi' r.
   store_type_extension tenvS tenvS' ∧
   type_s ctMap store' tenvS' ∧
   do_app (store,ffi) op (REVERSE vs) = SOME ((store', ffi'), r) ∧
   case r of
   | Rval v => type_v 0 ctMap tenvS' v t
   | Rerr (Rraise v) => type_v 0 ctMap tenvS' v Texn
   | Rerr (Rabort(Rffi_error _)) => T
   | Rerr (Rabort _) => F -/
theorem op_type_sound {ffi_ty : Type} :
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
          | Rerr (Rabort _) => False) := by sorry

/- HOL4:
Theorem build_conv_type_sound:
 !envC cn vs tvs ts ctMap tenvS ts' tn tenvC tvs' tenvE l.
 nsAll2 (type_ctor ctMap) envC tenvC ∧
 do_con_check envC (SOME cn) l ∧
 num_tvs tenvE = 0 ∧
 EVERY (check_freevars (num_tvs (bind_tvar tvs tenvE)) []) ts' ∧
 LENGTH tvs' = LENGTH ts' ∧
 LIST_REL (type_v tvs ctMap tenvS) vs
   (REVERSE (MAP (type_subst (alist_to_fmap (ZIP (tvs',ts')))) ts)) ∧
 nsLookup tenvC cn = SOME (tvs',ts,tn)
 ⇒
 ?v.
   build_conv envC (SOME cn) (REVERSE vs) = SOME v ∧
   type_v tvs ctMap tenvS v (Tapp ts' tn) -/
theorem build_conv_type_sound :
    ∀ (envC : Namespace mlstring mlstring (Nat × stamp)) (cn : ident mlstring mlstring)
      (vs : List value) (tvs : Nat) (ts : List typ) (ctMap : ctMap_ty) (tenvS : tenv_store)
      (ts' : List typ) (tn : type_ident)
      (tenvC : Namespace mlstring mlstring (List tvarN × List typ × type_ident))
      (tvs' : List tvarN) (tenvE : tenv_val_exp) (l : Nat),
      nsAll2 (type_ctor ctMap) envC tenvC ∧
      do_con_check envC (some cn) l ∧
      num_tvs tenvE = 0 ∧
      EVERY (check_freevars (num_tvs (bind_tvar tvs tenvE)) []) ts' ∧
      tvs'.length = ts'.length ∧
      LIST_REL (type_v tvs ctMap tenvS) vs
        (ts.map (type_subst (alist_to_fmap (tvs'.zip ts')))).reverse ∧
      nsLookup tenvC cn = some (tvs', ts, tn)
      →
      ∃ v,
        build_conv envC (some cn) vs.reverse = some v ∧
        type_v tvs ctMap tenvS v (Tapp ts' tn) := by sorry

/- HOL4:
Theorem same_ctor_and_same_tid:
   !stamp1 stamp2.
    same_ctor stamp1 stamp2 ∧
    same_type stamp1 stamp2
    ⇒
    stamp1 = stamp2 -/
theorem same_ctor_and_same_tid :
    ∀ stamp1 stamp2 : stamp,
      same_ctor stamp1 stamp2 ∧
      same_type stamp1 stamp2
      →
      stamp1 = stamp2 := by sorry

/- HOL4:
Theorem pat_type_sound:
  (∀(cenv : env_ctor) st p v bindings tenv ctMap tbindings t new_tbindings tenvS tvs.
   ctMap_ok ctMap ∧
   nsAll2 (type_ctor ctMap) cenv tenv.c ∧
   type_v tvs ctMap tenvS v t ∧
   type_p tvs tenv p t new_tbindings ∧
   type_s ctMap st tenvS ∧
   LIST_REL (λ(x,v) (x',t). x = x' ∧ type_v tvs ctMap tenvS v t) bindings tbindings
   ⇒
   pmatch cenv st p v bindings = No_match ∨
   (?bindings'.
     pmatch cenv st p v bindings = Match bindings' ∧
     LIST_REL (\ (x,v) (x',t). x = x' ∧ type_v tvs ctMap tenvS v t) bindings'
       (new_tbindings ++ tbindings))) ∧
  (∀(cenv : env_ctor) st ps vs bindings tenv ctMap tbindings new_tbindings ts tenvS tvs.
   ctMap_ok ctMap ∧
   nsAll2 (type_ctor ctMap) cenv tenv.c ∧
   LIST_REL (type_v tvs ctMap tenvS) vs ts ∧
   type_ps tvs tenv ps ts new_tbindings ∧
   type_s ctMap st tenvS ∧
   LIST_REL (λ(x,v) (x',t). x = x' ∧ type_v tvs ctMap tenvS v t) bindings tbindings
   ⇒
   pmatch_list cenv st ps vs bindings = No_match ∨
   (?bindings'.
     pmatch_list cenv st ps vs bindings = Match bindings' ∧
     LIST_REL (\ (x,v) (x',t). x = x' ∧ type_v tvs ctMap tenvS v t) bindings'
       (new_tbindings ++ tbindings))) -/
theorem pat_type_sound :
    (∀ (cenv : env_ctor) (st : List (store_v value)) (p : pat) (v : value)
        (bindings : List (varN × value)) (tenv : type_env) (ctMap : ctMap_ty)
        (tbindings : List (varN × typ)) (t : typ) (new_tbindings : List (varN × typ))
        (tenvS : tenv_store) (tvs : Nat),
      ctMap_ok ctMap ∧
      nsAll2 (type_ctor ctMap) cenv tenv.c ∧
      type_v tvs ctMap tenvS v t ∧
      type_p tvs tenv p t new_tbindings ∧
      type_s ctMap st tenvS ∧
      LIST_REL (fun ((x, v) : varN × value) ((x', t) : varN × typ) =>
        x = x' ∧ type_v tvs ctMap tenvS v t) bindings tbindings
      →
      pmatch cenv st p v bindings = No_match ∨
      (∃ bindings',
        pmatch cenv st p v bindings = Match bindings' ∧
        LIST_REL (fun ((x, v) : varN × value) ((x', t) : varN × typ) =>
          x = x' ∧ type_v tvs ctMap tenvS v t) bindings' (new_tbindings ++ tbindings))) ∧
    (∀ (cenv : env_ctor) (st : List (store_v value)) (ps : List pat) (vs : List value)
        (bindings : List (varN × value)) (tenv : type_env) (ctMap : ctMap_ty)
        (tbindings : List (varN × typ)) (new_tbindings : List (varN × typ)) (ts : List typ)
        (tenvS : tenv_store) (tvs : Nat),
      ctMap_ok ctMap ∧
      nsAll2 (type_ctor ctMap) cenv tenv.c ∧
      LIST_REL (type_v tvs ctMap tenvS) vs ts ∧
      type_ps tvs tenv ps ts new_tbindings ∧
      type_s ctMap st tenvS ∧
      LIST_REL (fun ((x, v) : varN × value) ((x', t) : varN × typ) =>
        x = x' ∧ type_v tvs ctMap tenvS v t) bindings tbindings
      →
      pmatch_list cenv st ps vs bindings = No_match ∨
      (∃ bindings',
        pmatch_list cenv st ps vs bindings = Match bindings' ∧
        LIST_REL (fun ((x, v) : varN × value) ((x', t) : varN × typ) =>
          x = x' ∧ type_v tvs ctMap tenvS v t) bindings' (new_tbindings ++ tbindings))) := by
  sorry

/- HOL4:
Theorem lookup_var_sound:
   !n tvs tenvE targs t ctMap tenvS env tenv.
    lookup_var n (bind_tvar tvs tenvE) tenv = SOME (LENGTH targs, t) ∧
    ctMap_ok ctMap ∧
    tenv_val_exp_ok tenvE ∧
    num_tvs tenvE = 0 ∧
    EVERY (check_freevars tvs []) targs ∧
    type_all_env ctMap tenvS env (tenv with v := add_tenvE tenvE tenv.v)
    ⇒
    ?v. nsLookup env.v n = SOME v ∧ type_v tvs ctMap tenvS v (deBruijn_subst 0 targs t) -/
theorem lookup_var_sound :
    ∀ (n : ident modN varN) (tvs : Nat) (tenvE : tenv_val_exp) (targs : List typ) (t : typ)
      (ctMap : ctMap_ty) (tenvS : tenv_store) (env : sem_env value) (tenv : type_env),
      lookup_var n (bind_tvar tvs tenvE) tenv = some (targs.length, t) ∧
      ctMap_ok ctMap ∧
      tenv_val_exp_ok tenvE ∧
      num_tvs tenvE = 0 ∧
      EVERY (check_freevars tvs []) targs ∧
      type_all_env ctMap tenvS env { tenv with v := add_tenvE tenvE tenv.v }
      →
      ∃ v, nsLookup env.v n = some v ∧
        type_v tvs ctMap tenvS v (deBruijn_subst 0 targs t) := by sorry

/- HOL4:
Theorem EVERY_REPLICATE:
  EVERY (\x. type_v tvs ctMap tenv x t') vs =
  EVERY (\x. type_v tvs ctMap tenv (FST x) (SND x)) (ZIP (vs, REPLICATE (LENGTH vs) t')) -/
theorem EVERY_REPLICATE (tvs : Nat) (ctMap : ctMap_ty) (tenv : tenv_store) (t' : typ)
    (vs : List value) :
    EVERY (fun x => type_v tvs ctMap tenv x t') vs ↔
    EVERY (fun x => type_v tvs ctMap tenv x.1 x.2)
      (vs.zip (List.replicate vs.length t')) := by sorry

/- HOL4:
Theorem EVERY_LIST_REL:
  EVERY (\ v. type_v n ctMap tenvS v t) vs =
  LIST_REL (type_v n ctMap tenvS) vs (REPLICATE (LENGTH vs) t)
(the second theorem of this name in the theory) -/
theorem EVERY_LIST_REL_2 (n : Nat) (ctMap : ctMap_ty) (tenvS : tenv_store) (t : typ)
    (vs : List value) :
    EVERY (fun v => type_v n ctMap tenvS v t) vs ↔
    LIST_REL (type_v n ctMap tenvS) vs (List.replicate vs.length t) := by sorry

/- HOL4:
Theorem exp_type_sound:
  (!(s:'ffi semanticPrimitives$state) env es r s' tenv tenvE ts tvs tenvS.
    evaluate s env es = (s', r) ∧
    tenv_ok tenv ∧
    tenv_val_exp_ok tenvE ∧
    good_ctMap ctMap ∧
    num_tvs tenvE = 0 ∧
    type_all_env ctMap tenvS env (tenv with v := add_tenvE tenvE tenv.v) ∧
    type_s ctMap s.refs tenvS ∧
    (tvs ≠ 0 ⇒ EVERY is_value es) ∧
    type_es tenv (bind_tvar tvs tenvE) es ts
    ⇒
    ∃tenvS'.
      type_s ctMap s'.refs tenvS' ∧
      store_type_extension tenvS tenvS' ∧
      s'.next_type_stamp = s.next_type_stamp ∧
      s'.next_exn_stamp = s.next_exn_stamp ∧
      case r of
         | Rval vs => LIST_REL (type_v tvs ctMap tenvS') vs ts
         | Rerr (Rraise v) => type_v 0 ctMap tenvS' v Texn
         | Rerr (Rabort Rtimeout_error) => T
         | Rerr (Rabort (Rffi_error _)) => T
         | Rerr (Rabort Rtype_error) => F) ∧
 (!(s:'ffi semanticPrimitives$state) env v pes err_v r s' tenv tenvE t1 t2 tvs tenvS.
    evaluate_match s env v pes err_v = (s', r) ∧
    tenv_ok tenv ∧
    tenv_val_exp_ok tenvE ∧
    good_ctMap ctMap ∧
    num_tvs tenvE = 0 ∧
    type_all_env ctMap tenvS env (tenv with v := add_tenvE tenvE tenv.v) ∧
    type_s ctMap s.refs tenvS ∧
    type_v tvs ctMap tenvS v t1 ∧
    type_v 0 ctMap tenvS err_v Texn ∧
    type_pes tvs tvs tenv tenvE pes t1 t2
    ⇒
    ∃tenvS'.
      type_s ctMap s'.refs tenvS' ∧
      store_type_extension tenvS tenvS' ∧
      s'.next_type_stamp = s.next_type_stamp ∧
      s'.next_exn_stamp = s.next_exn_stamp ∧
      case r of
         | Rval vs => type_v tvs ctMap tenvS' (HD vs) t2
         | Rerr (Rraise v) => type_v 0 ctMap tenvS' v Texn
         | Rerr (Rabort Rtimeout_error) => T
         | Rerr (Rabort (Rffi_error _)) => T
         | Rerr (Rabort Rtype_error) => F) -/
theorem exp_type_sound {ffi : Type} (ctMap : ctMap_ty) :
    (∀ (s : state ffi) (env : sem_env value) (es : List exp) (r : result (List value) value)
        (s' : state ffi) (tenv : type_env) (tenvE : tenv_val_exp) (ts : List typ) (tvs : Nat)
        (tenvS : tenv_store),
      evaluate s env es = (s', r) ∧
      tenv_ok tenv ∧
      tenv_val_exp_ok tenvE ∧
      good_ctMap ctMap ∧
      num_tvs tenvE = 0 ∧
      type_all_env ctMap tenvS env { tenv with v := add_tenvE tenvE tenv.v } ∧
      type_s ctMap s.refs tenvS ∧
      (tvs ≠ 0 → EVERY is_value es) ∧
      type_es tenv (bind_tvar tvs tenvE) es ts
      →
      ∃ tenvS' : tenv_store,
        type_s ctMap s'.refs tenvS' ∧
        store_type_extension tenvS tenvS' ∧
        s'.next_type_stamp = s.next_type_stamp ∧
        s'.next_exn_stamp = s.next_exn_stamp ∧
        (match r with
          | Rval vs => LIST_REL (type_v tvs ctMap tenvS') vs ts
          | Rerr (Rraise v) => type_v 0 ctMap tenvS' v Texn
          | Rerr (Rabort Rtimeout_error) => True
          | Rerr (Rabort (Rffi_error _)) => True
          | Rerr (Rabort Rtype_error) => False)) ∧
    (∀ (s : state ffi) (env : sem_env value) (v : value) (pes : List (pat × exp))
        (err_v : value) (r : result (List value) value) (s' : state ffi) (tenv : type_env)
        (tenvE : tenv_val_exp) (t1 t2 : typ) (tvs : Nat) (tenvS : tenv_store),
      evaluate_match s env v pes err_v = (s', r) ∧
      tenv_ok tenv ∧
      tenv_val_exp_ok tenvE ∧
      good_ctMap ctMap ∧
      num_tvs tenvE = 0 ∧
      type_all_env ctMap tenvS env { tenv with v := add_tenvE tenvE tenv.v } ∧
      type_s ctMap s.refs tenvS ∧
      type_v tvs ctMap tenvS v t1 ∧
      type_v 0 ctMap tenvS err_v Texn ∧
      type_pes tvs tvs tenv tenvE pes t1 t2
      →
      ∃ tenvS' : tenv_store,
        type_s ctMap s'.refs tenvS' ∧
        store_type_extension tenvS tenvS' ∧
        s'.next_type_stamp = s.next_type_stamp ∧
        s'.next_exn_stamp = s.next_exn_stamp ∧
        (match r with
          | Rval vs => type_v tvs ctMap tenvS' (HD vs) t2
          | Rerr (Rraise v) => type_v 0 ctMap tenvS' v Texn
          | Rerr (Rabort Rtimeout_error) => True
          | Rerr (Rabort (Rffi_error _)) => True
          | Rerr (Rabort Rtype_error) => False)) := by sorry

/- HOL4:
Theorem build_tdefs_build_tenv[local]:
  !tenvT (tds : type_def) (tids : type_ident list) next (ctMap : ctMap).
    EVERY (λ(_, _, ctors). ALL_DISTINCT (MAP FST ctors)) tds ∧
    LENGTH tds = LENGTH tids ⇒
    nsAll2
      (type_ctor (ctMap |++ REVERSE (type_def_to_ctMap tenvT next tds tids)))
      (build_tdefs next tds : env_ctor)
      (build_ctor_tenv tenvT tds tids) -/
theorem build_tdefs_build_tenv :
    ∀ (tenvT : Namespace mlstring mlstring (List mlstring × typ)) (tds : type_def)
      (tids : List type_ident) (next : Nat) (ctMap : ctMap_ty),
      EVERY (fun ((_, _, ctors) : List tvarN × typeN × List (conN × List ast_t)) =>
        ALL_DISTINCT (ctors.map Prod.fst)) tds ∧
      tds.length = tids.length →
      nsAll2
        (type_ctor (FUPDATE_LIST ctMap (type_def_to_ctMap tenvT next tds tids).reverse))
        (build_tdefs next tds : env_ctor)
        (build_ctor_tenv tenvT tds tids) := by sorry

/- HOL4:
Theorem type_sound_invariant_union[local]:
  type_sound_invariant st env ctMap tenvS (tids1 ∪ tids2) tenv
   ⇒
   type_sound_invariant st env ctMap tenvS tids1 tenv -/
theorem type_sound_invariant_union {ffi : Type} (st : state ffi) (env : sem_env value)
    (ctMap : ctMap_ty) (tenvS : tenv_store) (tids1 tids2 : Set type_ident)
    (tenv : type_env) :
    type_sound_invariant st env ctMap tenvS (tids1 ∪ tids2) tenv
    →
    type_sound_invariant st env ctMap tenvS tids1 tenv := by sorry

/- HOL4:
Theorem check_ctor_tenv_dups[local]:
  !tenvT tds. check_ctor_tenv tenvT tds ⇒ EVERY check_dup_ctors tds -/
theorem check_ctor_tenv_dups :
    ∀ (tenvT : Namespace modN typeN (List tvarN × typ))
      (tds : List (List tvarN × mlstring × List (conN × List ast_t))),
      check_ctor_tenv tenvT tds → EVERY check_dup_ctors tds := by sorry

/- HOL4:
Theorem type_all_env_extend:
   type_all_env ctMap tenvS env1 tenv1
    /\ type_all_env ctMap tenvS env2 tenv2
    ==> type_all_env ctMap tenvS (extend_dec_env env1 env2)
        (extend_dec_tenv tenv1 tenv2) -/
theorem type_all_env_extend (ctMap : ctMap_ty) (tenvS : tenv_store) (env1 : sem_env value)
    (tenv1 : type_env) (env2 : sem_env value) (tenv2 : type_env) :
    type_all_env ctMap tenvS env1 tenv1
      ∧ type_all_env ctMap tenvS env2 tenv2
      → type_all_env ctMap tenvS (extend_dec_env env1 env2)
        (extend_dec_tenv tenv1 tenv2) := by sorry

/- HOL4:
Theorem type_e_con_check:
 (!tenv tenvE e t.
   type_e tenv tenvE e t ⇒
   nsAll2 (type_ctor ctMap) envc tenv.c ⇒
   every_exp (one_con_check envc) e) ∧
 (!tenv tenvE es ts.
   type_es tenv tenvE es ts ⇒
   nsAll2 (type_ctor ctMap) envc tenv.c ⇒
   EVERY (every_exp (one_con_check envc)) es) ∧
 (!tenv tenvE funs env.
   type_funs tenv tenvE funs env ⇒
   nsAll2 (type_ctor ctMap) envc tenv.c ⇒
   EVERY (λ(f,n,e). every_exp (one_con_check envc) e) funs) -/
theorem type_e_con_check (ctMap : ctMap_ty)
    (envc : Namespace mlstring mlstring (Nat × stamp)) :
    (∀ (tenv : type_env) (tenvE : tenv_val_exp) (e : exp) (t : typ),
      type_e tenv tenvE e t →
      nsAll2 (type_ctor ctMap) envc tenv.c →
      every_exp (one_con_check envc) e) ∧
    (∀ (tenv : type_env) (tenvE : tenv_val_exp) (es : List exp) (ts : List typ),
      type_es tenv tenvE es ts →
      nsAll2 (type_ctor ctMap) envc tenv.c →
      EVERY (every_exp (one_con_check envc)) es) ∧
    (∀ (tenv : type_env) (tenvE : tenv_val_exp) (funs : List (varN × varN × exp))
        (env : List (varN × typ)),
      type_funs tenv tenvE funs env →
      nsAll2 (type_ctor ctMap) envc tenv.c →
      EVERY (fun ((_, _, e) : varN × varN × exp) => every_exp (one_con_check envc) e) funs) := by
  sorry

/- HOL4:
Theorem decs_type_sound_no_check:
  ∀(st:'ffi semanticPrimitives$state) env ds st' r ctMap tenvS tenv tids tenv'.
   evaluate_decs st env ds = (st',r) ∧
   type_ds F tenv ds tids tenv' ∧
   type_sound_invariant st env ctMap tenvS tids tenv
   ⇒
   ∃ctMap' tenvS'.
     weakCT ctMap' ctMap ∧
     FRANGE ((SND o SND) o_f ctMap') DIFF FRANGE ((SND o SND) o_f ctMap) ⊆ tids ∧
     store_type_extension tenvS tenvS' ∧
     case r of
     | Rval env' =>
       type_all_env ctMap' tenvS' env' tenv' ∧
       type_sound_invariant st' (extend_dec_env env' env)
         ctMap' tenvS' {} (extend_dec_tenv tenv' tenv)
     | Rerr (Rraise err_v) =>
       type_v 0 ctMap' tenvS' err_v Texn ∧
       type_sound_invariant st' env ctMap' tenvS' {} tenv
     | Rerr (Rabort Rtype_error) => F
     | Rerr (Rabort Rtimeout_error) => T
     | Rerr (Rabort(Rffi_error _)) => T -/
theorem decs_type_sound_no_check {ffi : Type} :
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
          | Rerr (Rabort (Rffi_error _)) => True) := by sorry

/- HOL4:
Theorem decs_type_sound:
  ∀(st:'ffi semanticPrimitives$state) env ds extra_checks st' r ctMap tenvS tenv tids tenv'.
   evaluate_decs st env ds = (st',r) ∧
   type_ds extra_checks tenv ds tids tenv' ∧
   type_sound_invariant st env ctMap tenvS tids tenv
   ⇒
   ∃ctMap' tenvS'.
     weakCT ctMap' ctMap ∧
     FRANGE ((SND o SND) o_f ctMap') DIFF FRANGE ((SND o SND) o_f ctMap) ⊆ tids ∧
     store_type_extension tenvS tenvS' ∧
     case r of
     | Rval env' =>
       type_all_env ctMap' tenvS' env' tenv' ∧
       type_sound_invariant st' (extend_dec_env env' env)
         ctMap' tenvS' {} (extend_dec_tenv tenv' tenv)
     | Rerr (Rraise err_v) =>
       type_v 0 ctMap' tenvS' err_v Texn ∧
       type_sound_invariant st' env ctMap' tenvS' {} tenv
     | Rerr (Rabort Rtype_error) => F
     | Rerr (Rabort (Rffi_error _)) => T
     | Rerr (Rabort Rtimeout_error) => T -/
theorem decs_type_sound {ffi : Type} :
    ∀ (st : state ffi) (env : sem_env value) (ds : List dec) (extra_checks : Bool)
      (st' : state ffi) (r : result (sem_env value) value) (ctMap : ctMap_ty)
      (tenvS : tenv_store) (tenv : type_env) (tids : Set type_ident) (tenv' : type_env),
      evaluate_decs st env ds = (st', r) ∧
      type_ds extra_checks tenv ds tids tenv' ∧
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
          | Rerr (Rabort (Rffi_error _)) => True
          | Rerr (Rabort Rtimeout_error) => True) := by sorry

/- HOL4:
Theorem semantics_type_sound:
  ∀(st:'ffi semanticPrimitives$state) env tops r checks ctMap tenvS tenv new_tenv tids.
   semantics_prog st env tops r ∧
   type_ds checks tenv tops tids new_tenv ∧
   type_sound_invariant st env ctMap tenvS tids tenv ⇒
   r ≠ Fail -/
theorem semantics_type_sound {ffi : Type} :
    ∀ (st : state ffi) (env : sem_env value) (tops : List dec) (r : behaviour)
      (checks : Bool) (ctMap : ctMap_ty) (tenvS : tenv_store) (tenv : type_env)
      (new_tenv : type_env) (tids : Set type_ident),
      semantics_prog st env tops r ∧
      type_ds checks tenv tops tids new_tenv ∧
      type_sound_invariant st env ctMap tenvS tids tenv →
      r ≠ Fail := by sorry

end

end CmlTS
