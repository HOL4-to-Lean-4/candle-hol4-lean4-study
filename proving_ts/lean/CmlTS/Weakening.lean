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
theorem weak_tenv_refl : ∀ tenv : type_env, tenv_val_ok tenv.v → weak_tenv tenv tenv := by
  intro tenv h
  refine ⟨nsSub_refl (fun _ (p : Nat × typ) => check_freevars p.1 [] p.2) _ ?_ _ h,
    nsSub_refl (fun _ _ => True) _ (fun _ _ _ => rfl) _ (eALL_T _)⟩
  rintro n ⟨tvs, t⟩ ht
  refine ⟨(COUNT_LIST tvs).map Tvar_db, by simp [Aux.COUNT_LIST_eq], ht, ?_,
    deBruijn_subst_id.1 t tvs ht⟩
  rw [Aux.EVERY_map]
  intro i hi
  rw [Aux.COUNT_LIST_eq, List.mem_range] at hi
  exact Aux.cf_db.2 hi

/- HOL4:
Theorem weakS_refl:
   !tenvS. weakS tenvS tenvS -/
theorem weakS_refl {α β : Type} : ∀ tenvS : fmap α β, weakS tenvS tenvS := by
  intro tenvS
  exact Aux.SUBMAP_iff.2 fun _ _ h => h

/- HOL4:
Theorem weak_tenvE_freevars[local]:
  !tenv tenv' tvs t.
  weak_tenvE tenv' tenv ∧
  check_freevars (num_tvs tenv) tvs t ⇒
  check_freevars (num_tvs tenv') tvs t -/
theorem weak_tenvE_freevars :
    ∀ (tenv tenv' : tenv_val_exp) (tvs : List mlstring) (t : typ),
      weak_tenvE tenv' tenv ∧ check_freevars (num_tvs tenv) tvs t →
      check_freevars (num_tvs tenv') tvs t := by
  rintro tenv tenv' tvs t ⟨h, hc⟩
  exact check_freevars_add _ _ _ hc _ h.1

/- HOL4:
Theorem weak_tenvE_bind[local]:
  !tenv tenv' n tvs t.
  weak_tenvE tenv' tenv ⇒
  weak_tenvE (Bind_name n tvs t tenv') (Bind_name n tvs t tenv) -/
theorem weak_tenvE_bind :
    ∀ (tenv tenv' : tenv_val_exp) (n : varN) (tvs : Nat) (t : typ),
      weak_tenvE tenv' tenv →
      weak_tenvE (Bind_name n tvs t tenv') (Bind_name n tvs t tenv) := by
  rintro tenv tenv' n tvs t ⟨h1, h2⟩
  refine ⟨h1, fun x inc tvs' t' => ?_⟩
  simp only [tveLookup]
  split
  · exact Iff.rfl
  · exact h2 _ _ _ _

/- HOL4:
Theorem weak_tenvE_opt_bind[local]:
  !tenv tenv' n tvs t.
  weak_tenvE tenv' tenv ⇒
  weak_tenvE (opt_bind_name n tvs t tenv') (opt_bind_name n tvs t tenv) -/
theorem weak_tenvE_opt_bind :
    ∀ (tenv tenv' : tenv_val_exp) (n : Option mlstring) (tvs : Nat) (t : typ),
      weak_tenvE tenv' tenv →
      weak_tenvE (opt_bind_name n tvs t tenv') (opt_bind_name n tvs t tenv) := by
  intro tenv tenv' n tvs t h
  cases n with
  | none => exact h
  | some n => exact weak_tenvE_bind _ _ _ _ _ h

/- HOL4:
Theorem weak_tenvE_bind_tvar[local]:
  !tenv tenv' tvs.
  weak_tenvE tenv' tenv ⇒
  weak_tenvE (bind_tvar tvs tenv') (bind_tvar tvs tenv) -/
theorem weak_tenvE_bind_tvar :
    ∀ (tenv tenv' : tenv_val_exp) (tvs : Nat),
      weak_tenvE tenv' tenv →
      weak_tenvE (bind_tvar tvs tenv') (bind_tvar tvs tenv) := by
  rintro tenv tenv' tvs ⟨h1, h2⟩
  refine ⟨?_, fun x inc tvs' t' => ?_⟩
  · rw [Aux.num_tvs_bt, Aux.num_tvs_bt]; omega
  · rw [Aux.tveLookup_bt, Aux.tveLookup_bt]; exact h2 _ _ _ _

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
      weak_tenvE (bind_tvar tvs tenv') (bind_tvar 0 tenv) := by
  rintro tenv tenv' _ tvs _ ⟨hok, h0, h1, h2⟩
  refine ⟨?_, fun x inc tvs' t' => ?_⟩
  · rw [Aux.num_tvs_bt, Aux.num_tvs_bt]; omega
  · rw [Aux.tveLookup_bt, Aux.tveLookup_bt, ← h2]
    exact (tveLookup_no_tvs _ _ _ _ _ ⟨hok, h0⟩).trans
      (tveLookup_no_tvs _ _ _ _ _ ⟨hok, h0⟩).symm

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
  intro b E E' n tvs t h
  induction b with
  | nil => exact h
  | cons p b ih =>
    obtain ⟨x, t⟩ := p
    exact weak_tenvE_bind _ _ _ _ _ ih

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
      nsLookup tenv'.c cn = some (tvs, ts, tn) := by
  rintro cn tenv tenv' tvs ts tn ⟨h, hl⟩
  obtain ⟨v, hv, he⟩ := h.2.1 cn _ hl
  have he : (tvs, ts, tn) = v := he
  rw [hv, he]

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
  rintro n tenv tenv' tvs t ⟨h, hl⟩
  obtain ⟨⟨tvs', t'⟩, hv, he⟩ := h.1.1 n _ hl
  exact ⟨tvs', t', hv, he⟩

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
        type_ps tvs' tenv' ps ts bindings) := by
  apply Aux.type_p_ind
  case any =>
    rintro tvs tenv t h tenv' tvs' ⟨hge, hw⟩
    exact type_p.any _ _ _ (check_freevars_add _ _ _ h _ hge)
  case var =>
    rintro tvs tenv n t h tenv' tvs' ⟨hge, hw⟩
    exact type_p.var _ _ _ _ (check_freevars_add _ _ _ h _ hge)
  case intLit => intros; exact type_p.intLit _ _ _
  case char => intros; exact type_p.char _ _ _
  case strLit => intros; exact type_p.strLit _ _ _
  case word8 => intros; exact type_p.word8 _ _ _
  case word64 => intros; exact type_p.word64 _ _ _
  case con =>
    rintro tvs tenv cn ps ts tvs0 tn ts' b h1 h2 _ ih h3 tenv' tvs' ⟨hge, hw⟩
    refine type_p.con _ _ _ _ _ _ _ _ _ ?_ h2 (ih _ _ ⟨hge, hw⟩)
      (eLookupC_weak _ _ _ _ _ _ ⟨hw.2, h3⟩)
    rw [EVERY_iff_forall] at h1 ⊢
    exact fun t ht => check_freevars_add _ _ _ (h1 t ht) _ hge
  case tup => intro tvs tenv ps ts b _ ih tenv' tvs' hh; exact type_p.tup _ _ _ _ _ (ih _ _ hh)
  case ref => intro tvs tenv ps ts b _ ih tenv' tvs' hh; exact type_p.ref _ _ _ _ _ (ih _ _ hh)
  case pas =>
    intro tvs tenv p v t b _ ih tenv' tvs' hh
    exact type_p.pas _ _ _ _ _ _ (ih _ _ hh)
  case tannot =>
    intro tvs tenv p t b h1 h2 _ ih tenv' tvs' hh
    have := ih _ _ hh
    rw [← hh.2.1] at h2 this ⊢
    exact type_p.tannot _ _ _ _ _ h1 h2 this
  case nil => intros; exact type_ps.nil _ _
  case cons =>
    intro tvs tenv p ps t ts b b' _ _ ih1 ih2 tenv' tvs' hh
    exact type_ps.cons _ _ _ _ _ _ _ _ (ih1 _ _ hh) (ih2 _ _ hh)

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
  apply Aux.type_e_ind
  case intLit => intros; exact type_e.intLit _ _ _
  case char => intros; exact type_e.char _ _ _
  case strLit => intros; exact type_e.strLit _ _ _
  case word8 => intros; exact type_e.word8 _ _ _
  case word64 => intros; exact type_e.word64 _ _ _
  case float64 => intros; exact type_e.float64 _ _ _
  case raise =>
    rintro tenv E e t h _ ih tenv' E' ⟨hw, hE⟩
    exact type_e.raise _ _ _ _ (weak_tenvE_freevars _ _ _ _ ⟨hE, h⟩) (ih _ _ ⟨hw, hE⟩)
  case handle =>
    rintro tenv E e pes t bs _ h2 h3 h4 _ ih1 ih2 tenv' E' ⟨hw, hE⟩
    exact type_e.handle _ _ _ _ _ bs (ih1 _ _ ⟨hw, hE⟩) h2 h3
      (fun pe hpe => type_p_weakening.1 _ _ _ _ _ (h4 pe hpe) _ _ ⟨hE.1, hw⟩)
      (fun pe hpe => ih2 pe hpe _ _ ⟨hw, weak_tenvE_bind_var_list _ _ _ () _ () hE⟩)
  case con =>
    rintro tenv E cn es tvs tn ts' ts h1 h2 _ h4 ih tenv' E' ⟨hw, hE⟩
    refine type_e.con _ _ _ _ tvs _ _ ts ?_ h2 (ih _ _ ⟨hw, hE⟩)
      (eLookupC_weak _ _ _ _ _ _ ⟨hw.2, h4⟩)
    rw [EVERY_iff_forall] at h1 ⊢
    exact fun t ht => weak_tenvE_freevars _ _ _ _ ⟨hE, h1 t ht⟩
  case tup => intro tenv E es ts _ ih tenv' E' hh; exact type_e.tup _ _ _ _ (ih _ _ hh)
  case var =>
    rintro tenv E n t targs tvs rfl h1 h2 tenv' E' ⟨hw, hE⟩
    have h1' : EVERY (check_freevars (num_tvs E') []) targs := by
      rw [EVERY_iff_forall] at h1 ⊢
      exact fun t ht => weak_tenvE_freevars _ _ _ _ ⟨hE, h1 t ht⟩
    have hns : nsLookup tenv.v n = some (targs.length, t) → lookup_varE n E' = none →
        type_e tenv' E' (exp.Var n) (deBruijn_subst 0 targs t) := by
      intro hv hn
      obtain ⟨tvs', t', hv', subst, hlen, hc, he, rfl⟩ := eLookupV_weak _ _ _ _ _ ⟨hw.2, hv⟩
      subst hlen
      have := (deBruijn_subst2 (α := Unit) (β := Unit)).1 t' 0 subst targs () hc
      rw [deBruijn_inc0.2] at this
      rw [this]
      refine type_e.var _ _ _ _ _ _ (List.length_map _).symm ?_ ?_
      · rw [Aux.EVERY_map]
        rw [EVERY_iff_forall] at he
        exact fun t ht => deBruijn_subst_check_freevars2 _ _ _ _ () () ⟨he t ht, h1'⟩
      · unfold lookup_var
        rw [hn]
        exact hv'
    cases n with
    | Long mn id => exact hns h2 rfl
    | Short x =>
      have hlE : ∀ E, lookup_varE (Short x) E = tveLookup x 0 E := fun _ => rfl
      have h2' := h2
      unfold lookup_var at h2
      rw [hlE] at h2
      cases hl : tveLookup x 0 E with
      | some p =>
        rw [hl] at h2
        cases h2
        refine type_e.var _ _ _ _ _ _ rfl h1' ?_
        unfold lookup_var
        rw [hlE, (hE.2 _ _ _ _).1 hl]
      | none =>
        rw [hl] at h2
        refine hns h2 ?_
        rw [hlE]
        cases hl' : tveLookup x 0 E' with
        | none => rfl
        | some p =>
          obtain ⟨a, b⟩ := p
          rw [(hE.2 _ _ _ _).2 hl'] at hl
          cases hl
  case fn =>
    rintro tenv E n e t1 t2 h1 _ ih tenv' E' ⟨hw, hE⟩
    exact type_e.fn _ _ _ _ _ _ (weak_tenvE_freevars _ _ _ _ ⟨hE, h1⟩)
      (ih _ _ ⟨hw, weak_tenvE_bind _ _ _ _ _ hE⟩)
  case app =>
    rintro tenv E o es ts t _ h2 h3 ih tenv' E' ⟨hw, hE⟩
    exact type_e.app _ _ _ _ _ _ (ih _ _ ⟨hw, hE⟩) h2 (weak_tenvE_freevars _ _ _ _ ⟨hE, h3⟩)
  case log =>
    intro tenv E l e1 e2 _ _ ih1 ih2 tenv' E' hh
    exact type_e.log _ _ _ _ _ (ih1 _ _ hh) (ih2 _ _ hh)
  case ite =>
    intro tenv E e1 e2 e3 t _ _ _ ih1 ih2 ih3 tenv' E' hh
    exact type_e.if' _ _ _ _ _ _ (ih1 _ _ hh) (ih2 _ _ hh) (ih3 _ _ hh)
  case mat =>
    rintro tenv E e pes t1 t2 bs _ h2 h3 h4 _ ih1 ih2 tenv' E' ⟨hw, hE⟩
    exact type_e.mat _ _ _ _ _ _ bs (ih1 _ _ ⟨hw, hE⟩) h2 h3
      (fun pe hpe => type_p_weakening.1 _ _ _ _ _ (h4 pe hpe) _ _ ⟨hE.1, hw⟩)
      (fun pe hpe => ih2 pe hpe _ _ ⟨hw, weak_tenvE_bind_var_list _ _ _ () _ () hE⟩)
  case letc =>
    rintro tenv E n e1 e2 t1 t2 _ _ ih1 ih2 tenv' E' ⟨hw, hE⟩
    exact type_e.let' _ _ _ _ _ _ _ (ih1 _ _ ⟨hw, hE⟩)
      (ih2 _ _ ⟨hw, weak_tenvE_opt_bind _ _ _ _ _ hE⟩)
  case letrec =>
    rintro tenv E funs e t b _ _ ih1 ih2 tenv' E' ⟨hw, hE⟩
    exact type_e.letrec _ _ _ _ _ _
      (ih1 _ _ ⟨hw, weak_tenvE_bind_var_list _ _ _ () _ () hE⟩)
      (ih2 _ _ ⟨hw, weak_tenvE_bind_var_list _ _ _ () _ () hE⟩)
  case tannot =>
    intro tenv E e t h1 h2 _ ih tenv' E' hh
    have := ih _ _ hh
    rw [← hh.1.1] at h2 this ⊢
    exact type_e.tannot _ _ _ _ h1 h2 this
  case lannot => intro tenv E e l t _ ih tenv' E' hh; exact type_e.lannot _ _ _ _ _ (ih _ _ hh)
  case nil => intros; exact type_es.nil _ _
  case cons =>
    intro tenv E e es t ts _ _ ih1 ih2 tenv' E' hh
    exact type_es.cons _ _ _ _ _ _ (ih1 _ _ hh) (ih2 _ _ hh)
  case fnil => intros; exact type_funs.nil _ _
  case fcons =>
    rintro tenv E fn n e funs b t1 t2 h1 _ _ h4 ih1 ih2 tenv' E' ⟨hw, hE⟩
    exact type_funs.cons _ _ _ _ _ _ _ _ _ (weak_tenvE_freevars _ _ _ _ ⟨hE, h1⟩)
      (ih1 _ _ ⟨hw, weak_tenvE_bind _ _ _ _ _ hE⟩) (ih2 _ _ ⟨hw, hE⟩) h4

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
      type_funs tenv' tenvE' funs bindings) :=
  ⟨fun _ _ _ _ _ _ h => type_e_weakening_lem.1 _ _ _ _ h.1 _ _ h.2,
    fun _ _ _ _ _ _ h => type_e_weakening_lem.2.1 _ _ _ _ h.1 _ _ h.2,
    fun _ _ _ _ _ _ h => type_e_weakening_lem.2.2 _ _ _ _ h.1 _ _ h.2⟩

/- HOL4:
Theorem gt_0[local]:
  !x:num.x ≥ 0 -/
theorem gt_0 : ∀ x : Nat, x ≥ 0 := fun x => Nat.zero_le x

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
      FLOOKUP ctMap' stamp = some (tvs, ts) := by
  rintro m m' tvs ts s ⟨h, hl⟩
  exact Aux.SUBMAP_iff.1 h _ _ hl

/- HOL4:
Theorem weakCT_refl:
 !ctMap. weakCT ctMap ctMap -/
theorem weakCT_refl {α β : Type} : ∀ ctMap : fmap α β, weakCT ctMap ctMap := by
  intro m
  exact Aux.SUBMAP_iff.2 fun _ _ h => h

/- HOL4:
Theorem weakCT_trans:
 weakCT C1 C2 ∧ weakCT C2 C3 ⇒ weakCT C1 C3 -/
theorem weakCT_trans {α β : Type} (C1 C2 C3 : fmap α β) :
    weakCT C1 C2 ∧ weakCT C2 C3 → weakCT C1 C3 := by
  rintro ⟨h1, h2⟩
  exact Aux.SUBMAP_iff.2 fun x v h => Aux.SUBMAP_iff.1 h1 _ _ (Aux.SUBMAP_iff.1 h2 _ _ h)

/- HOL4:
Theorem disjoint_env_weakCT:
 !ctMap ctMap'.
  DISJOINT (FDOM ctMap') (FDOM ctMap) ⇒
  weakCT (FUNION ctMap' ctMap) ctMap -/
theorem disjoint_env_weakCT {α β : Type} :
    ∀ ctMap ctMap' : fmap α β,
      DISJOINT (FDOM ctMap') (FDOM ctMap) → weakCT (FUNION ctMap' ctMap) ctMap := by
  intro m m' h
  refine Aux.SUBMAP_iff.2 fun x v hx => ?_
  have : ¬ x ∈ FDOM m' := fun hm => Aux.disjoint_iff.1 h x hm (Aux.mem_FDOM.2 ⟨v, hx⟩)
  rw [Aux.FLOOKUP_FUNION, Aux.not_mem_FDOM.1 this]
  exact hx

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
      nsAll2 (type_ctor ctMap') envC tenvC := by
  rintro m tenvC envC m' ⟨hw, h⟩
  refine nsAll2_mono ?_ h
  rintro id ⟨n, s⟩ ⟨tvs, ts, ti⟩ ⟨h1, h2⟩
  exact ⟨Aux.SUBMAP_iff.1 hw _ _ h1, h2⟩

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
      nsAll2 (fun _ v (tvs, t) => type_v tvs ctMap' tenvS' v t) envV tenvV := by
  rintro m S tenvV envV m' S' ⟨h1, h2, h⟩
  refine nsAll2_mono ?_ h
  rintro id v ⟨tvs, t⟩ hv
  exact hv tvs m' S' ⟨Or.inr rfl, h1, h2⟩

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
        type_v tvs' ctMap' tenvS' v t := by
  have hEE : ∀ (tvs tvs' : Nat) (E : tenv_val_exp), (tvs = 0 ∨ tvs = tvs') →
      tenv_val_exp_ok E → num_tvs E = 0 →
      weak_tenvE (bind_tvar tvs' E) (bind_tvar tvs E) := by
    intro tvs tvs' E h hok h0
    have hrefl : weak_tenvE E E := ⟨Nat.le_refl _, fun _ _ _ _ => Iff.rfl⟩
    rcases h with rfl | rfl
    · exact weak_tenvE_bind_tvar2 _ _ () _ () ⟨hok, h0, hrefl⟩
    · exact weak_tenvE_bind_tvar _ _ _ hrefl
  intro tvs m S v t h
  induction h with
  | intLit => intros; exact type_v.intLit _ _ _ _
  | char => intros; exact type_v.char _ _ _ _
  | strLit => intros; exact type_v.strLit _ _ _ _
  | word8 => intros; exact type_v.word8 _ _ _ _
  | word64 => intros; exact type_v.word64 _ _ _ _
  | float64 => intros; exact type_v.float64 _ _ _ _
  | conv tvs m S vs tvs0 stamp ts' ts ti h1 h2 h3 h4 h5 ih =>
    rintro tvs' m' S' ⟨hor, hC, hS⟩
    refine type_v.conv _ _ _ _ tvs0 _ _ ts _ ?_ h2 h3
      (fun i v t hv ht => ih i v t hv ht _ _ _ ⟨hor, hC, hS⟩) (Aux.SUBMAP_iff.1 hC _ _ h5)
    rw [EVERY_iff_forall] at h1 ⊢
    exact fun t ht => check_freevars_add _ _ _ (h1 t ht) _ (by omega)
  | tup tvs m S vs ts h1 h2 ih =>
    rintro tvs' m' S' hh
    exact type_v.tup _ _ _ _ _ h1 fun i v t hv ht => ih i v t hv ht _ _ _ hh
  | closure tvs m S env tenv E n e t1 t2 ho hE h0 hc hv1 hv2 ht1 hte ih =>
    rintro tvs' m' S' ⟨hor, hC, hS⟩
    refine type_v.closure _ _ _ _ tenv E _ _ _ _ ho hE h0
      (type_tenv_ctor_weakening _ _ _ _ ⟨hC, hc⟩) hv1
      (fun i v p hv hp => ih i v p hv hp _ _ _ ⟨Or.inr rfl, hC, hS⟩)
      (check_freevars_add _ _ _ ht1 _ (by omega)) ?_
    exact type_e_weakening.1 _ _ _ _ _ _ ⟨hte, ⟨rfl, weak_tenv_refl _ ho.1⟩,
      weak_tenvE_bind _ _ _ _ _ (hEE _ _ _ hor hE h0)⟩
  | recclosure tvs m S env funs n t tenv E b ho hE h0 hc hv1 hv2 hf hl hd hm ih =>
    rintro tvs' m' S' ⟨hor, hC, hS⟩
    refine type_v.recclosure _ _ _ _ _ _ _ tenv E b ho hE h0
      (type_tenv_ctor_weakening _ _ _ _ ⟨hC, hc⟩) hv1
      (fun i v p hv hp => ih i v p hv hp _ _ _ ⟨Or.inr rfl, hC, hS⟩) ?_ hl hd hm
    exact type_e_weakening.2.2 _ _ _ _ _ _ ⟨hf, ⟨rfl, weak_tenv_refl _ ho.1⟩,
      weak_tenvE_bind_var_list _ _ _ () _ () (hEE _ _ _ hor hE h0)⟩
  | ref tvs m S n t h1 h2 =>
    rintro tvs' m' S' ⟨hor, hC, hS⟩
    exact type_v.ref _ _ _ _ _ h1 (Aux.SUBMAP_iff.1 hS _ _ h2)
  | w8array tvs m S n h =>
    rintro tvs' m' S' ⟨hor, hC, hS⟩
    exact type_v.w8array _ _ _ _ (Aux.SUBMAP_iff.1 hS _ _ h)
  | varray tvs m S n t h1 h2 =>
    rintro tvs' m' S' ⟨hor, hC, hS⟩
    exact type_v.varray _ _ _ _ _ h1 (Aux.SUBMAP_iff.1 hS _ _ h2)
  | vector tvs m S vs t h1 h2 ih =>
    rintro tvs' m' S' hh
    exact type_v.vector _ _ _ _ _ h1 fun v hv => ih v hv _ _ _ hh

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
      type_all_env ctMap' tenvS' env tenv := by
  rintro m S tenv env m' S' ⟨hC, hS, h1, h2⟩
  refine ⟨type_tenv_ctor_weakening _ _ _ _ ⟨hC, h1⟩, nsAll2_mono ?_ h2⟩
  rintro id v ⟨tvs, t⟩ hv
  exact type_v_weakening _ _ _ _ _ hv _ _ _ ⟨Or.inr rfl, hC, hS⟩

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
      type_sv ctMap' tenvS' sv st := by
  rintro m S st sv m' S' ⟨h, hC, hS⟩
  cases sv <;> cases st <;> try exact h
  · exact type_v_weakening _ _ _ _ _ h _ _ _ ⟨Or.inr rfl, hC, hS⟩
  · refine EVERY_iff_forall.2 fun v hv => ?_
    exact type_v_weakening _ _ _ _ _ (EVERY_iff_forall.1 h v hv) _ _ _ ⟨Or.inr rfl, hC, hS⟩

/- HOL4:
Theorem type_s_weakening:
 !ctMap tenvS st ctMap'.
  type_s ctMap st tenvS ∧
  weakCT ctMap' ctMap
  ⇒
  type_s ctMap' st tenvS -/
theorem type_s_weakening :
    ∀ (ctMap : ctMap_ty) (tenvS : tenv_store) (st : List (store_v value)) (ctMap' : ctMap_ty),
      type_s ctMap st tenvS ∧ weakCT ctMap' ctMap → type_s ctMap' st tenvS := by
  rintro m S st m' ⟨h, hC⟩ l
  obtain ⟨h1, h2⟩ := h l
  exact ⟨h1, fun st sv hh => type_sv_weakening _ _ _ _ _ _ ⟨h2 st sv hh, hC, weakS_refl _⟩⟩

/- HOL4:
Theorem weak_tenv_extend_dec_tenv:
   !tenv1 tenv2 tenv3.
    tenv_val_ok tenv1.v ∧
    weak_tenv tenv2 tenv3 ⇒
    weak_tenv (extend_dec_tenv tenv1 tenv2) (extend_dec_tenv tenv1 tenv3) -/
theorem weak_tenv_extend_dec_tenv :
    ∀ tenv1 tenv2 tenv3 : type_env,
      tenv_val_ok tenv1.v ∧ weak_tenv tenv2 tenv3 →
      weak_tenv (extend_dec_tenv tenv1 tenv2) (extend_dec_tenv tenv1 tenv3) := by
  rintro t1 t2 t3 ⟨h, h1, h2⟩
  obtain ⟨r1, r2⟩ := weak_tenv_refl _ h
  exact ⟨nsSub_nsAppend2 _ _ _ _ ⟨r1, h1⟩, nsSub_nsAppend2 _ _ _ _ ⟨r2, h2⟩⟩

end

end CmlTS
