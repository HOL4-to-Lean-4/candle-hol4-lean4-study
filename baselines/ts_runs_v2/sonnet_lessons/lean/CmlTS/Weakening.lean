import CmlTS.Ast
import CmlTS.TypeSystem
import CmlTS.TypeSysProps
import CmlTS.NamespaceProps
import CmlTS.SemanticPrimitives
import CmlTS.TypeSoundInvariants

/-!
# weakening (HOL4 theory `weakening`): weakening lemmas used in type soundness

Definitions of this theory (the theorems are for stage 2).
-/

universe u v w

noncomputable section

open Classical

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
  ∀ n inc tvs t,
    (tveLookup n inc tenv' = some (tvs, t)) ↔ (tveLookup n inc tenv = some (tvs, t))

/- HOL4:
   Definition weakS_def:
   weakS tenvS tenvS' ⇔ tenvS' SUBMAP tenvS
   End -/
def weakS (tenvS tenvS' : tenv_store) : Prop := SUBMAP tenvS' tenvS

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
def weakCT (cenv_impl cenv_spec : ctMap) : Prop := SUBMAP cenv_spec cenv_impl

/- HOL4: `weakS_def` / `weakCT_def` have no type annotations, so in HOL4 they are polymorphic in
   `('a,'b) fmap`; stage 1 specialised them to `tenv_store` / `ctMap`.  The polymorphic HOL4
   constants (needed by the polymorphic theorems `weakS_refl`, `weak_ctMap_lookup`,
   `weakCT_refl`, `weakCT_trans`, `disjoint_env_weakCT`):
   Definition weakS_def:  weakS tenvS tenvS' ⇔ tenvS' SUBMAP tenvS
   Definition weakCT_def: weakCT cenv_impl cenv_spec ⇔ cenv_spec SUBMAP cenv_impl -/
def weakS_poly {α : Type} {β : Type} (tenvS tenvS' : FMap α β) : Prop := SUBMAP tenvS' tenvS

def weakCT_poly {α : Type} {β : Type} (cenv_impl cenv_spec : FMap α β) : Prop :=
  SUBMAP cenv_spec cenv_impl

/- HOL4: !tenv. tenv_val_ok tenv.v ⇒ weak_tenv tenv tenv -/
theorem weak_tenv_refl : ∀ tenv : type_env, tenv_val_ok tenv.v → weak_tenv tenv tenv := by
  sorry

/- HOL4: !tenvS. weakS tenvS tenvS   (polymorphic in the fmap type, see `weakS_poly`) -/
theorem weakS_refl {α β : Type} : ∀ tenvS : FMap α β, weakS_poly tenvS tenvS := by
  sorry

/- HOL4: !tenv tenv' tvs t.
  weak_tenvE tenv' tenv ∧
  check_freevars (num_tvs tenv) tvs t ⇒
  check_freevars (num_tvs tenv') tvs t -/
theorem weak_tenvE_freevars :
    ∀ (tenv tenv' : tenv_val_exp) (tvs : List tvarN) (t : Ty),
      weak_tenvE tenv' tenv ∧ check_freevars (num_tvs tenv) tvs t →
      check_freevars (num_tvs tenv') tvs t := by
  sorry

/- HOL4: !tenv tenv' n tvs t.
  weak_tenvE tenv' tenv ⇒
  weak_tenvE (Bind_name n tvs t tenv') (Bind_name n tvs t tenv) -/
theorem weak_tenvE_bind :
    ∀ (tenv tenv' : tenv_val_exp) (n : varN) (tvs : Nat) (t : Ty),
      weak_tenvE tenv' tenv →
      weak_tenvE (.Bind_name n tvs t tenv') (.Bind_name n tvs t tenv) := by
  sorry

/- HOL4: !tenv tenv' n tvs t.
  weak_tenvE tenv' tenv ⇒
  weak_tenvE (opt_bind_name n tvs t tenv') (opt_bind_name n tvs t tenv) -/
theorem weak_tenvE_opt_bind :
    ∀ (tenv tenv' : tenv_val_exp) (n : Option varN) (tvs : Nat) (t : Ty),
      weak_tenvE tenv' tenv →
      weak_tenvE (opt_bind_name n tvs t tenv') (opt_bind_name n tvs t tenv) := by
  sorry

/- HOL4: !tenv tenv' tvs.
  weak_tenvE tenv' tenv ⇒
  weak_tenvE (bind_tvar tvs tenv') (bind_tvar tvs tenv) -/
theorem weak_tenvE_bind_tvar :
    ∀ (tenv tenv' : tenv_val_exp) (tvs : Nat),
      weak_tenvE tenv' tenv → weak_tenvE (bind_tvar tvs tenv') (bind_tvar tvs tenv) := by
  sorry

/- HOL4: !tenv tenv' n tvs t.
  tenv_val_exp_ok tenv ∧
  num_tvs tenv = 0 ∧
  weak_tenvE tenv' tenv ⇒
  weak_tenvE (bind_tvar tvs tenv') (bind_tvar 0 tenv)
  (`n` and `t` do not occur in the body: their HOL4 types are free type variables) -/
theorem weak_tenvE_bind_tvar2 {γ δ : Type} :
    ∀ (tenv tenv' : tenv_val_exp) (n : γ) (tvs : Nat) (t : δ),
      tenv_val_exp_ok tenv ∧ num_tvs tenv = 0 ∧ weak_tenvE tenv' tenv →
      weak_tenvE (bind_tvar tvs tenv') (bind_tvar 0 tenv) := by
  sorry

/- HOL4: !bindings tenvE tenvE' n tvs t .
  weak_tenvE tenvE' tenvE ⇒
  weak_tenvE (bind_var_list tvs bindings tenvE') (bind_var_list tvs bindings tenvE)
  (`n` and `t` do not occur in the body: their HOL4 types are free type variables) -/
theorem weak_tenvE_bind_var_list {γ δ : Type} :
    ∀ (bindings : List (varN × Ty)) (tenvE tenvE' : tenv_val_exp) (n : γ) (tvs : Nat) (t : δ),
      weak_tenvE tenvE' tenvE →
      weak_tenvE (bind_var_list tvs bindings tenvE') (bind_var_list tvs bindings tenvE) := by
  sorry

/- HOL4: ∀cn tenv tenv' tvs ts tn.
    weak_tenv tenv' tenv ∧
    nsLookup tenv.c cn = SOME (tvs,ts,tn)
    ⇒
    nsLookup tenv'.c cn = SOME (tvs,ts,tn) -/
theorem eLookupC_weak :
    ∀ (cn : Ident modN conN) (tenv tenv' : type_env) (tvs : List tvarN) (ts : List Ty)
      (tn : type_ident),
      weak_tenv tenv' tenv ∧ nsLookup tenv.c cn = some (tvs, ts, tn) →
      nsLookup tenv'.c cn = some (tvs, ts, tn) := by
  sorry

/- HOL4: ∀n tenv tenv' tvs t.
    weak_tenv tenv' tenv ∧
    nsLookup tenv.v n = SOME (tvs,t)
    ⇒
    ∃tvs' t'. nsLookup tenv'.v n = SOME (tvs',t') ∧ tscheme_inst (tvs,t) (tvs',t') -/
theorem eLookupV_weak :
    ∀ (n : Ident modN varN) (tenv tenv' : type_env) (tvs : Nat) (t : Ty),
      weak_tenv tenv' tenv ∧ nsLookup tenv.v n = some (tvs, t) →
      ∃ tvs' t', nsLookup tenv'.v n = some (tvs', t') ∧ tscheme_inst (tvs, t) (tvs', t') := by
  sorry

/- HOL4: (!tvs tenv p t bindings. type_p tvs tenv p t bindings ⇒
    !tenv' tvs'. tvs' ≥ tvs ∧ weak tenv' tenv ⇒ type_p tvs' tenv' p t bindings) ∧
 (!tvs tenv ps ts bindings. type_ps tvs tenv ps ts bindings ⇒
    !tenv' tvs'. tvs' ≥ tvs ∧ weak tenv' tenv ⇒ type_ps tvs' tenv' ps ts bindings) -/
theorem type_p_weakening :
    (∀ (tvs : Nat) (tenv : type_env) (p : pat) (t : Ty) (bindings : List (varN × Ty)),
      type_p tvs tenv p t bindings →
      ∀ (tenv' : type_env) (tvs' : Nat),
        tvs' ≥ tvs ∧ weak tenv' tenv → type_p tvs' tenv' p t bindings) ∧
    (∀ (tvs : Nat) (tenv : type_env) (ps : List pat) (ts : List Ty)
        (bindings : List (varN × Ty)),
      type_ps tvs tenv ps ts bindings →
      ∀ (tenv' : type_env) (tvs' : Nat),
        tvs' ≥ tvs ∧ weak tenv' tenv → type_ps tvs' tenv' ps ts bindings) := by
  sorry

/- HOL4: (!tenv tenvE e t. type_e tenv tenvE e t ⇒
    ∀tenv' tenvE'. weak tenv' tenv ∧ weak_tenvE tenvE' tenvE ⇒ type_e tenv' tenvE' e t) ∧
 (!tenv tenvE es ts. type_es tenv tenvE es ts ⇒
    ∀tenv' tenvE'. weak tenv' tenv ∧ weak_tenvE tenvE' tenvE ⇒ type_es tenv' tenvE' es ts) ∧
 (!tenv tenvE funs bindings. type_funs tenv tenvE funs bindings ⇒
    ∀tenv' tenvE'. weak tenv' tenv ∧ weak_tenvE tenvE' tenvE ⇒ type_funs tenv' tenvE' funs bindings) -/
theorem type_e_weakening_lem :
    (∀ (tenv : type_env) (tenvE : tenv_val_exp) (e : exp) (t : Ty),
      type_e tenv tenvE e t →
      ∀ (tenv' : type_env) (tenvE' : tenv_val_exp),
        weak tenv' tenv ∧ weak_tenvE tenvE' tenvE → type_e tenv' tenvE' e t) ∧
    (∀ (tenv : type_env) (tenvE : tenv_val_exp) (es : List exp) (ts : List Ty),
      type_es tenv tenvE es ts →
      ∀ (tenv' : type_env) (tenvE' : tenv_val_exp),
        weak tenv' tenv ∧ weak_tenvE tenvE' tenvE → type_es tenv' tenvE' es ts) ∧
    (∀ (tenv : type_env) (tenvE : tenv_val_exp) (funs : List (varN × varN × exp))
        (bindings : List (varN × Ty)),
      type_funs tenv tenvE funs bindings →
      ∀ (tenv' : type_env) (tenvE' : tenv_val_exp),
        weak tenv' tenv ∧ weak_tenvE tenvE' tenvE → type_funs tenv' tenvE' funs bindings) := by
  sorry

/- HOL4: (!tenv tenvE e t tenv' tenvE'.
   type_e tenv tenvE e t ∧ weak tenv' tenv ∧ weak_tenvE tenvE' tenvE ⇒ type_e tenv' tenvE' e t) ∧
 (!tenv tenvE es ts tenv' tenvE'.
   type_es tenv tenvE es ts ∧ weak tenv' tenv ∧ weak_tenvE tenvE' tenvE ⇒ type_es tenv' tenvE' es ts) ∧
 (!tenv tenvE funs bindings tenv' tenvE'.
   type_funs tenv tenvE funs bindings ∧ weak tenv' tenv ∧ weak_tenvE tenvE' tenvE ⇒ type_funs tenv' tenvE' funs bindings) -/
theorem type_e_weakening :
    (∀ (tenv : type_env) (tenvE : tenv_val_exp) (e : exp) (t : Ty) (tenv' : type_env)
        (tenvE' : tenv_val_exp),
      type_e tenv tenvE e t ∧ weak tenv' tenv ∧ weak_tenvE tenvE' tenvE →
      type_e tenv' tenvE' e t) ∧
    (∀ (tenv : type_env) (tenvE : tenv_val_exp) (es : List exp) (ts : List Ty)
        (tenv' : type_env) (tenvE' : tenv_val_exp),
      type_es tenv tenvE es ts ∧ weak tenv' tenv ∧ weak_tenvE tenvE' tenvE →
      type_es tenv' tenvE' es ts) ∧
    (∀ (tenv : type_env) (tenvE : tenv_val_exp) (funs : List (varN × varN × exp))
        (bindings : List (varN × Ty)) (tenv' : type_env) (tenvE' : tenv_val_exp),
      type_funs tenv tenvE funs bindings ∧ weak tenv' tenv ∧ weak_tenvE tenvE' tenvE →
      type_funs tenv' tenvE' funs bindings) := by
  sorry

/- HOL4: !x:num.x ≥ 0 -/
theorem gt_0 : ∀ x : Nat, x ≥ 0 := by
  sorry

/- HOL4: ∀ctMap ctMap' tvs ts stamp.
  weakCT ctMap' ctMap ∧
  FLOOKUP ctMap stamp = SOME (tvs,ts)
  ⇒
  FLOOKUP ctMap' stamp = SOME (tvs,ts)
  (polymorphic: `ctMap : ('a, 'b # 'c) fmap`, see `weakCT_poly`) -/
theorem weak_ctMap_lookup {α β γ : Type} :
    ∀ (ctMap ctMap' : FMap α (β × γ)) (tvs : β) (ts : γ) (stamp : α),
      weakCT_poly ctMap' ctMap ∧ FLOOKUP ctMap stamp = some (tvs, ts) →
      FLOOKUP ctMap' stamp = some (tvs, ts) := by
  sorry

/- HOL4: !ctMap. weakCT ctMap ctMap   (polymorphic, see `weakCT_poly`) -/
theorem weakCT_refl {α β : Type} : ∀ ctMap : FMap α β, weakCT_poly ctMap ctMap := by
  sorry

/- HOL4: weakCT C1 C2 ∧ weakCT C2 C3 ⇒ weakCT C1 C3   (polymorphic, see `weakCT_poly`) -/
theorem weakCT_trans {α β : Type} (C1 C2 C3 : FMap α β) :
    weakCT_poly C1 C2 ∧ weakCT_poly C2 C3 → weakCT_poly C1 C3 := by
  sorry

/- HOL4: !ctMap ctMap'.
  DISJOINT (FDOM ctMap') (FDOM ctMap) ⇒
  weakCT (FUNION ctMap' ctMap) ctMap   (polymorphic, see `weakCT_poly`) -/
theorem disjoint_env_weakCT {α β : Type} :
    ∀ ctMap ctMap' : FMap α β,
      DISJOINT (FDOM ctMap') (FDOM ctMap) → weakCT_poly (FUNION ctMap' ctMap) ctMap := by
  sorry

/- HOL4: !ctMap tenvC envC ctMap'.
  weakCT ctMap' ctMap ∧
  nsAll2 (type_ctor ctMap) envC tenvC
  ⇒
  nsAll2 (type_ctor ctMap') envC tenvC -/
theorem type_tenv_ctor_weakening :
    ∀ (ctMap : ctMap) (tenvC : tenv_ctor) (envC : Namespace modN conN (Nat × stamp))
      (ctMap' : _root_.ctMap),
      weakCT ctMap' ctMap ∧ nsAll2 (type_ctor ctMap) envC tenvC →
      nsAll2 (type_ctor ctMap') envC tenvC := by
  sorry

/- HOL4: !ctMap tenvS tenvV envV ctMap' tenvS'.
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
theorem type_tenv_val_weakening_lemma :
    ∀ (ctMap : ctMap) (tenvS : tenv_store) (tenvV : tenv_val) (envV : env_val)
      (ctMap' : _root_.ctMap) (tenvS' : tenv_store),
      weakCT ctMap' ctMap ∧
      weakS tenvS' tenvS ∧
      nsAll2 (fun _ v p =>
          ∀ (tvs' : Nat) (ctMap' : _root_.ctMap) (tenvS' : tenv_store),
            (p.1 = 0 ∨ p.1 = tvs') ∧
            weakCT ctMap' ctMap ∧
            weakS tenvS' tenvS →
            type_v tvs' ctMap' tenvS' v p.2)
        envV tenvV →
      nsAll2 (fun _ v p => type_v p.1 ctMap' tenvS' v p.2) envV tenvV := by
  sorry

/- HOL4: (!tvs ctMap tenvS v t. type_v tvs ctMap tenvS v t ⇒
    !tvs' ctMap' tenvS'.
      ((tvs = 0) ∨ (tvs = tvs')) ∧ weakCT ctMap' ctMap ∧ weakS tenvS' tenvS ⇒
      type_v tvs' ctMap' tenvS' v t) -/
theorem type_v_weakening :
    (∀ (tvs : Nat) (ctMap : ctMap) (tenvS : tenv_store) (v : Value) (t : Ty),
      type_v tvs ctMap tenvS v t →
      ∀ (tvs' : Nat) (ctMap' : _root_.ctMap) (tenvS' : tenv_store),
        ((tvs = 0) ∨ (tvs = tvs')) ∧ weakCT ctMap' ctMap ∧ weakS tenvS' tenvS →
        type_v tvs' ctMap' tenvS' v t) := by
  sorry

/- HOL4: !ctMap tenvS tenv env ctMap' tenvS'.
  weakCT ctMap' ctMap ∧
  weakS tenvS' tenvS ∧
  type_all_env ctMap tenvS env tenv
  ⇒
  type_all_env ctMap' tenvS' env tenv -/
theorem type_all_env_weakening :
    ∀ (ctMap : ctMap) (tenvS : tenv_store) (tenv : type_env) (env : sem_env Value)
      (ctMap' : _root_.ctMap) (tenvS' : tenv_store),
      weakCT ctMap' ctMap ∧ weakS tenvS' tenvS ∧ type_all_env ctMap tenvS env tenv →
      type_all_env ctMap' tenvS' env tenv := by
  sorry

/- HOL4: !ctMap tenvS st sv ctMap' tenvS'.
  type_sv ctMap tenvS sv st ∧
  weakCT ctMap' ctMap ∧
  weakS tenvS' tenvS
  ⇒
  type_sv ctMap' tenvS' sv st -/
theorem type_sv_weakening :
    ∀ (ctMap : ctMap) (tenvS : tenv_store) (st : store_t) (sv : store_v Value)
      (ctMap' : _root_.ctMap) (tenvS' : tenv_store),
      type_sv ctMap tenvS sv st ∧ weakCT ctMap' ctMap ∧ weakS tenvS' tenvS →
      type_sv ctMap' tenvS' sv st := by
  sorry

/- HOL4: !ctMap tenvS st ctMap'.
  type_s ctMap st tenvS ∧
  weakCT ctMap' ctMap
  ⇒
  type_s ctMap' st tenvS -/
theorem type_s_weakening :
    ∀ (ctMap : ctMap) (tenvS : tenv_store) (st : List (store_v Value)) (ctMap' : _root_.ctMap),
      type_s ctMap st tenvS ∧ weakCT ctMap' ctMap → type_s ctMap' st tenvS := by
  sorry

/- HOL4: !tenv1 tenv2 tenv3.
    tenv_val_ok tenv1.v ∧
    weak_tenv tenv2 tenv3 ⇒
    weak_tenv (extend_dec_tenv tenv1 tenv2) (extend_dec_tenv tenv1 tenv3) -/
theorem weak_tenv_extend_dec_tenv :
    ∀ tenv1 tenv2 tenv3 : type_env,
      tenv_val_ok tenv1.v ∧ weak_tenv tenv2 tenv3 →
      weak_tenv (extend_dec_tenv tenv1 tenv2) (extend_dec_tenv tenv1 tenv3) := by
  sorry

end
