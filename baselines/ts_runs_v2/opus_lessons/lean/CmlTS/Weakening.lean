import CmlTS.Ast
import CmlTS.TypeSystem
import CmlTS.TypeSysProps
import CmlTS.NamespaceProps
import CmlTS.SemanticPrimitives
import CmlTS.TypeSoundInvariants

/-
HOL4 theory `weakening` (weakeningScript.sml).
-/

namespace CmlTS

noncomputable section

open scoped Classical

/- HOL4:
Definition weak_tenvE_def:
weak_tenvE tenv tenv' =
  (num_tvs tenv ≥ num_tvs tenv' ∧
   ∀n inc tvs t.
    (tveLookup n inc tenv' = SOME (tvs,t)) ⇔
    (tveLookup n inc tenv = SOME (tvs,t)))
End -/
def weak_tenvE (tenv tenv' : tenv_val_exp) : Prop :=
  num_tvs tenv ≥ num_tvs tenv' ∧
  ∀ n inc tvs t, tveLookup n inc tenv' = some (tvs, t) ↔ tveLookup n inc tenv = some (tvs, t)

/- HOL4:
Definition weakS_def:
weakS tenvS tenvS' ⇔ tenvS' SUBMAP tenvS
End -/
def weakS {α β : Type} (tenvS tenvS' : fmap α β) : Prop := SUBMAP tenvS' tenvS

/- HOL4:
Definition weak_def:
weak tenv' tenv ⇔
  tenv'.t = tenv.t ∧ weak_tenv tenv' tenv
End -/
def weak (tenv' tenv : type_env) : Prop := tenv'.t = tenv.t ∧ weak_tenv tenv' tenv

/- HOL4:
Definition weakCT_def:
weakCT cenv_impl cenv_spec ⇔ cenv_spec SUBMAP cenv_impl
End -/
def weakCT {α β : Type} (cenv_impl cenv_spec : fmap α β) : Prop := SUBMAP cenv_spec cenv_impl

/-! ## Theorems -/

/- HOL4:
Theorem weak_tenv_refl:
   !tenv. tenv_val_ok tenv.v ⇒ weak_tenv tenv tenv -/
theorem weak_tenv_refl : ∀ tenv : type_env, tenv_val_ok tenv.v → weak_tenv tenv tenv := by sorry

/- HOL4:
Theorem weakS_refl:
   !tenvS. weakS tenvS tenvS -/
theorem weakS_refl {α β : Type} : ∀ tenvS : fmap α β, weakS tenvS tenvS := by sorry

/- HOL4:
Theorem weak_tenvE_freevars[local]:
  !tenv tenv' tvs t.
  weak_tenvE tenv' tenv ∧
  check_freevars (num_tvs tenv) tvs t ⇒
  check_freevars (num_tvs tenv') tvs t -/
theorem weak_tenvE_freevars :
    ∀ (tenv tenv' : tenv_val_exp) (tvs : List mlstring) (t : typ),
      weak_tenvE tenv' tenv ∧ check_freevars (num_tvs tenv) tvs t →
      check_freevars (num_tvs tenv') tvs t := by sorry

/- HOL4:
Theorem weak_tenvE_bind[local]:
  !tenv tenv' n tvs t.
  weak_tenvE tenv' tenv ⇒
  weak_tenvE (Bind_name n tvs t tenv') (Bind_name n tvs t tenv) -/
theorem weak_tenvE_bind :
    ∀ (tenv tenv' : tenv_val_exp) (n : varN) (tvs : Nat) (t : typ),
      weak_tenvE tenv' tenv →
      weak_tenvE (Bind_name n tvs t tenv') (Bind_name n tvs t tenv) := by sorry

/- HOL4:
Theorem weak_tenvE_opt_bind[local]:
  !tenv tenv' n tvs t.
  weak_tenvE tenv' tenv ⇒
  weak_tenvE (opt_bind_name n tvs t tenv') (opt_bind_name n tvs t tenv) -/
theorem weak_tenvE_opt_bind :
    ∀ (tenv tenv' : tenv_val_exp) (n : Option mlstring) (tvs : Nat) (t : typ),
      weak_tenvE tenv' tenv →
      weak_tenvE (opt_bind_name n tvs t tenv') (opt_bind_name n tvs t tenv) := by sorry

/- HOL4:
Theorem weak_tenvE_bind_tvar[local]:
  !tenv tenv' tvs.
  weak_tenvE tenv' tenv ⇒
  weak_tenvE (bind_tvar tvs tenv') (bind_tvar tvs tenv) -/
theorem weak_tenvE_bind_tvar :
    ∀ (tenv tenv' : tenv_val_exp) (tvs : Nat),
      weak_tenvE tenv' tenv →
      weak_tenvE (bind_tvar tvs tenv') (bind_tvar tvs tenv) := by sorry

/- HOL4:
Theorem weak_tenvE_bind_tvar2[local]:
  !tenv tenv' n tvs t.
  tenv_val_exp_ok tenv ∧
  num_tvs tenv = 0 ∧
  weak_tenvE tenv' tenv ⇒
  weak_tenvE (bind_tvar tvs tenv') (bind_tvar 0 tenv)
(`n` and `t` are unused, so their types are type variables) -/
theorem weak_tenvE_bind_tvar2 {α β : Type} :
    ∀ (tenv tenv' : tenv_val_exp) (n : α) (tvs : Nat) (t : β),
      tenv_val_exp_ok tenv ∧ num_tvs tenv = 0 ∧ weak_tenvE tenv' tenv →
      weak_tenvE (bind_tvar tvs tenv') (bind_tvar 0 tenv) := by sorry

/- HOL4:
Theorem weak_tenvE_bind_var_list[local]:
  !bindings tenvE tenvE' n tvs t .
  weak_tenvE tenvE' tenvE ⇒
  weak_tenvE (bind_var_list tvs bindings tenvE') (bind_var_list tvs bindings tenvE)
(`n` and `t` are unused, so their types are type variables) -/
theorem weak_tenvE_bind_var_list {α β : Type} :
    ∀ (bindings : List (mlstring × typ)) (tenvE tenvE' : tenv_val_exp) (n : α) (tvs : Nat)
      (t : β),
      weak_tenvE tenvE' tenvE →
      weak_tenvE (bind_var_list tvs bindings tenvE') (bind_var_list tvs bindings tenvE) := by
  sorry

/- HOL4:
Theorem eLookupC_weak[local]:
  ∀cn tenv tenv' tvs ts tn.
    weak_tenv tenv' tenv ∧
    nsLookup tenv.c cn = SOME (tvs,ts,tn)
    ⇒
    nsLookup tenv'.c cn = SOME (tvs,ts,tn) -/
theorem eLookupC_weak :
    ∀ (cn : ident modN conN) (tenv tenv' : type_env) (tvs : List tvarN) (ts : List typ)
      (tn : type_ident),
      weak_tenv tenv' tenv ∧ nsLookup tenv.c cn = some (tvs, ts, tn) →
      nsLookup tenv'.c cn = some (tvs, ts, tn) := by sorry

/- HOL4:
Theorem eLookupV_weak[local]:
  ∀n tenv tenv' tvs t.
    weak_tenv tenv' tenv ∧
    nsLookup tenv.v n = SOME (tvs,t)
    ⇒
    ∃tvs' t'. nsLookup tenv'.v n = SOME (tvs',t') ∧ tscheme_inst (tvs,t) (tvs',t') -/
theorem eLookupV_weak :
    ∀ (n : ident modN varN) (tenv tenv' : type_env) (tvs : Nat) (t : typ),
      weak_tenv tenv' tenv ∧ nsLookup tenv.v n = some (tvs, t) →
      ∃ tvs' t', nsLookup tenv'.v n = some (tvs', t') ∧ tscheme_inst (tvs, t) (tvs', t') := by
  sorry

/- HOL4:
Theorem type_p_weakening:
 (!tvs tenv p t bindings. type_p tvs tenv p t bindings ⇒
    !tenv' tvs'. tvs' ≥ tvs ∧ weak tenv' tenv ⇒ type_p tvs' tenv' p t bindings) ∧
 (!tvs tenv ps ts bindings. type_ps tvs tenv ps ts bindings ⇒
    !tenv' tvs'. tvs' ≥ tvs ∧ weak tenv' tenv ⇒ type_ps tvs' tenv' ps ts bindings) -/
theorem type_p_weakening :
    (∀ (tvs : Nat) (tenv : type_env) (p : pat) (t : typ) (bindings : List (varN × typ)),
      type_p tvs tenv p t bindings →
      ∀ (tenv' : type_env) (tvs' : Nat), tvs' ≥ tvs ∧ weak tenv' tenv →
        type_p tvs' tenv' p t bindings) ∧
    (∀ (tvs : Nat) (tenv : type_env) (ps : List pat) (ts : List typ)
      (bindings : List (varN × typ)),
      type_ps tvs tenv ps ts bindings →
      ∀ (tenv' : type_env) (tvs' : Nat), tvs' ≥ tvs ∧ weak tenv' tenv →
        type_ps tvs' tenv' ps ts bindings) := by sorry

/- HOL4:
Theorem type_e_weakening_lem[local]:
  (!tenv tenvE e t. type_e tenv tenvE e t ⇒
    ∀tenv' tenvE'. weak tenv' tenv ∧ weak_tenvE tenvE' tenvE ⇒ type_e tenv' tenvE' e t) ∧
 (!tenv tenvE es ts. type_es tenv tenvE es ts ⇒
    ∀tenv' tenvE'. weak tenv' tenv ∧ weak_tenvE tenvE' tenvE ⇒ type_es tenv' tenvE' es ts) ∧
 (!tenv tenvE funs bindings. type_funs tenv tenvE funs bindings ⇒
    ∀tenv' tenvE'. weak tenv' tenv ∧ weak_tenvE tenvE' tenvE ⇒ type_funs tenv' tenvE' funs bindings) -/
theorem type_e_weakening_lem :
    (∀ (tenv : type_env) (tenvE : tenv_val_exp) (e : exp) (t : typ),
      type_e tenv tenvE e t →
      ∀ (tenv' : type_env) (tenvE' : tenv_val_exp),
        weak tenv' tenv ∧ weak_tenvE tenvE' tenvE → type_e tenv' tenvE' e t) ∧
    (∀ (tenv : type_env) (tenvE : tenv_val_exp) (es : List exp) (ts : List typ),
      type_es tenv tenvE es ts →
      ∀ (tenv' : type_env) (tenvE' : tenv_val_exp),
        weak tenv' tenv ∧ weak_tenvE tenvE' tenvE → type_es tenv' tenvE' es ts) ∧
    (∀ (tenv : type_env) (tenvE : tenv_val_exp) (funs : List (varN × varN × exp))
      (bindings : List (varN × typ)),
      type_funs tenv tenvE funs bindings →
      ∀ (tenv' : type_env) (tenvE' : tenv_val_exp),
        weak tenv' tenv ∧ weak_tenvE tenvE' tenvE → type_funs tenv' tenvE' funs bindings) := by
  sorry

/- HOL4:
Theorem type_e_weakening:
 (!tenv tenvE e t tenv' tenvE'.
   type_e tenv tenvE e t ∧ weak tenv' tenv ∧ weak_tenvE tenvE' tenvE ⇒ type_e tenv' tenvE' e t) ∧
 (!tenv tenvE es ts tenv' tenvE'.
   type_es tenv tenvE es ts ∧ weak tenv' tenv ∧ weak_tenvE tenvE' tenvE ⇒ type_es tenv' tenvE' es ts) ∧
 (!tenv tenvE funs bindings tenv' tenvE'.
   type_funs tenv tenvE funs bindings ∧ weak tenv' tenv ∧ weak_tenvE tenvE' tenvE ⇒ type_funs tenv' tenvE' funs bindings) -/
theorem type_e_weakening :
    (∀ (tenv : type_env) (tenvE : tenv_val_exp) (e : exp) (t : typ) (tenv' : type_env)
      (tenvE' : tenv_val_exp),
      type_e tenv tenvE e t ∧ weak tenv' tenv ∧ weak_tenvE tenvE' tenvE →
      type_e tenv' tenvE' e t) ∧
    (∀ (tenv : type_env) (tenvE : tenv_val_exp) (es : List exp) (ts : List typ)
      (tenv' : type_env) (tenvE' : tenv_val_exp),
      type_es tenv tenvE es ts ∧ weak tenv' tenv ∧ weak_tenvE tenvE' tenvE →
      type_es tenv' tenvE' es ts) ∧
    (∀ (tenv : type_env) (tenvE : tenv_val_exp) (funs : List (varN × varN × exp))
      (bindings : List (varN × typ)) (tenv' : type_env) (tenvE' : tenv_val_exp),
      type_funs tenv tenvE funs bindings ∧ weak tenv' tenv ∧ weak_tenvE tenvE' tenvE →
      type_funs tenv' tenvE' funs bindings) := by sorry

/- HOL4:
Theorem gt_0[local]:
  !x:num.x ≥ 0 -/
theorem gt_0 : ∀ x : Nat, x ≥ 0 := by sorry

/- HOL4:
Theorem weak_ctMap_lookup[local]:
  ∀ctMap ctMap' tvs ts stamp.
  weakCT ctMap' ctMap ∧
  FLOOKUP ctMap stamp = SOME (tvs,ts)
  ⇒
  FLOOKUP ctMap' stamp = SOME (tvs,ts)
(polymorphic in HOL4: nothing fixes the types of `stamp`, `tvs`, `ts`) -/
theorem weak_ctMap_lookup {α β γ : Type} :
    ∀ (ctMap ctMap' : fmap α (β × γ)) (tvs : β) (ts : γ) (stamp : α),
      weakCT ctMap' ctMap ∧ FLOOKUP ctMap stamp = some (tvs, ts) →
      FLOOKUP ctMap' stamp = some (tvs, ts) := by sorry

/- HOL4:
Theorem weakCT_refl:
 !ctMap. weakCT ctMap ctMap -/
theorem weakCT_refl {α β : Type} : ∀ ctMap : fmap α β, weakCT ctMap ctMap := by sorry

/- HOL4:
Theorem weakCT_trans:
 weakCT C1 C2 ∧ weakCT C2 C3 ⇒ weakCT C1 C3 -/
theorem weakCT_trans {α β : Type} (C1 C2 C3 : fmap α β) :
    weakCT C1 C2 ∧ weakCT C2 C3 → weakCT C1 C3 := by sorry

/- HOL4:
Theorem disjoint_env_weakCT:
 !ctMap ctMap'.
  DISJOINT (FDOM ctMap') (FDOM ctMap) ⇒
  weakCT (FUNION ctMap' ctMap) ctMap -/
theorem disjoint_env_weakCT {α β : Type} :
    ∀ ctMap ctMap' : fmap α β,
      DISJOINT (FDOM ctMap') (FDOM ctMap) → weakCT (FUNION ctMap' ctMap) ctMap := by sorry

/- HOL4:
Theorem type_tenv_ctor_weakening:
 !ctMap tenvC envC ctMap'.
  weakCT ctMap' ctMap ∧
  nsAll2 (type_ctor ctMap) envC tenvC
  ⇒
  nsAll2 (type_ctor ctMap') envC tenvC
(as polymorphic as in HOL4) -/
theorem type_tenv_ctor_weakening {m n σ α β γ : Type} :
    ∀ (ctMap : fmap σ (α × List β × γ)) (tenvC : Namespace m n (α × List β × γ))
      (envC : Namespace m n (Nat × σ)) (ctMap' : fmap σ (α × List β × γ)),
      weakCT ctMap' ctMap ∧ nsAll2 (type_ctor ctMap) envC tenvC →
      nsAll2 (type_ctor ctMap') envC tenvC := by sorry

/- HOL4:
Theorem type_tenv_val_weakening_lemma[local]:
  !ctMap tenvS tenvV envV ctMap' tenvS'.
  weakCT ctMap' ctMap ∧
  weakS tenvS' tenvS ∧
  nsAll2 (λi v (tvs,t).
          ∀tvs' ctMap' tenvS'.
            (tvs = 0 ∨ tvs = tvs') ∧
            weakCT ctMap' ctMap ∧
            weakS tenvS' tenvS
            ⇒
            type_v tvs' ctMap' tenvS' v t)
         envV tenvV
  ⇒
  nsAll2 (λi v (tvs,t). type_v tvs ctMap' tenvS' v t) envV tenvV -/
theorem type_tenv_val_weakening_lemma {m n : Type} :
    ∀ (ctMap : ctMap_ty) (tenvS : tenv_store) (tenvV : Namespace m n (Nat × typ))
      (envV : Namespace m n value) (ctMap' : ctMap_ty) (tenvS' : tenv_store),
      weakCT ctMap' ctMap ∧
      weakS tenvS' tenvS ∧
      nsAll2 (fun _ v (tvs, t) =>
          ∀ (tvs' : Nat) (ctMap' : ctMap_ty) (tenvS' : tenv_store),
            (tvs = 0 ∨ tvs = tvs') ∧ weakCT ctMap' ctMap ∧ weakS tenvS' tenvS →
            type_v tvs' ctMap' tenvS' v t)
        envV tenvV →
      nsAll2 (fun _ v (tvs, t) => type_v tvs ctMap' tenvS' v t) envV tenvV := by sorry

/- HOL4:
Theorem type_v_weakening:
 (!tvs ctMap tenvS v t. type_v tvs ctMap tenvS v t ⇒
    !tvs' ctMap' tenvS'.
      ((tvs = 0) ∨ (tvs = tvs')) ∧ weakCT ctMap' ctMap ∧ weakS tenvS' tenvS ⇒
      type_v tvs' ctMap' tenvS' v t) -/
theorem type_v_weakening :
    ∀ (tvs : Nat) (ctMap : ctMap_ty) (tenvS : tenv_store) (v : value) (t : typ),
      type_v tvs ctMap tenvS v t →
      ∀ (tvs' : Nat) (ctMap' : ctMap_ty) (tenvS' : tenv_store),
        (tvs = 0 ∨ tvs = tvs') ∧ weakCT ctMap' ctMap ∧ weakS tenvS' tenvS →
        type_v tvs' ctMap' tenvS' v t := by sorry

/- HOL4:
Theorem type_all_env_weakening:
 !ctMap tenvS tenv env ctMap' tenvS'.
  weakCT ctMap' ctMap ∧
  weakS tenvS' tenvS ∧
  type_all_env ctMap tenvS env tenv
  ⇒
  type_all_env ctMap' tenvS' env tenv -/
theorem type_all_env_weakening :
    ∀ (ctMap : ctMap_ty) (tenvS : tenv_store) (tenv : type_env) (env : sem_env value)
      (ctMap' : ctMap_ty) (tenvS' : tenv_store),
      weakCT ctMap' ctMap ∧ weakS tenvS' tenvS ∧ type_all_env ctMap tenvS env tenv →
      type_all_env ctMap' tenvS' env tenv := by sorry

/- HOL4:
Theorem type_sv_weakening:
 !ctMap tenvS st sv ctMap' tenvS'.
  type_sv ctMap tenvS sv st ∧
  weakCT ctMap' ctMap ∧
  weakS tenvS' tenvS
  ⇒
  type_sv ctMap' tenvS' sv st -/
theorem type_sv_weakening :
    ∀ (ctMap : ctMap_ty) (tenvS : tenv_store) (st : store_t) (sv : store_v value)
      (ctMap' : ctMap_ty) (tenvS' : tenv_store),
      type_sv ctMap tenvS sv st ∧ weakCT ctMap' ctMap ∧ weakS tenvS' tenvS →
      type_sv ctMap' tenvS' sv st := by sorry

/- HOL4:
Theorem type_s_weakening:
 !ctMap tenvS st ctMap'.
  type_s ctMap st tenvS ∧
  weakCT ctMap' ctMap
  ⇒
  type_s ctMap' st tenvS -/
theorem type_s_weakening :
    ∀ (ctMap : ctMap_ty) (tenvS : tenv_store) (st : List (store_v value)) (ctMap' : ctMap_ty),
      type_s ctMap st tenvS ∧ weakCT ctMap' ctMap → type_s ctMap' st tenvS := by sorry

/- HOL4:
Theorem weak_tenv_extend_dec_tenv:
   !tenv1 tenv2 tenv3.
    tenv_val_ok tenv1.v ∧
    weak_tenv tenv2 tenv3 ⇒
    weak_tenv (extend_dec_tenv tenv1 tenv2) (extend_dec_tenv tenv1 tenv3) -/
theorem weak_tenv_extend_dec_tenv :
    ∀ tenv1 tenv2 tenv3 : type_env,
      tenv_val_ok tenv1.v ∧ weak_tenv tenv2 tenv3 →
      weak_tenv (extend_dec_tenv tenv1 tenv2) (extend_dec_tenv tenv1 tenv3) := by sorry

end

end CmlTS
