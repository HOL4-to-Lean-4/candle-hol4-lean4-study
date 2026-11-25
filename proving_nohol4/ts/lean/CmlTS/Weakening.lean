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
  refine ⟨nsSub_refl (fun _ (p : Nat × typ) => check_freevars p.1 [] p.2) _ ?_ _
      (fun id p hp => h id p hp),
    nsSub_refl (fun _ _ => True) _ (fun _ _ _ => rfl) _ (eALL_T _)⟩
  rintro n ⟨tvs, t⟩ ht
  have ht : check_freevars tvs [] t := ht
  refine ⟨(COUNT_LIST tvs).map Tvar_db, by rw [List.length_map, Aux.COUNT_LIST_length], ht, ?_,
    deBruijn_subst_id.1 t tvs ht⟩
  rw [EVERY_iff_forall]
  intro x hx
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hx
  simp only [check_freevars]
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hk
  have hi' := hi
  rw [Aux.COUNT_LIST_length] at hi'
  have := Aux.EL_COUNT_LIST tvs i hi'
  rw [Aux.EL_eq _ _ hi] at this
  omega

/- HOL4:
Theorem weakS_refl:
   !tenvS. weakS tenvS tenvS -/
theorem weakS_refl {α β : Type} : ∀ tenvS : fmap α β, weakS tenvS tenvS :=
  fun _ _ h => ⟨h, rfl⟩

theorem Aux.weakS_iff {α β : Type} {s s' : fmap α β} :
    weakS s s' ↔ ∀ x y, FLOOKUP s' x = some y → FLOOKUP s x = some y := Aux.SUBMAP_iff

theorem Aux.weakCT_iff {α β : Type} {s s' : fmap α β} :
    weakCT s s' ↔ ∀ x y, FLOOKUP s' x = some y → FLOOKUP s x = some y := Aux.SUBMAP_iff

theorem Aux.weak_tenvE_refl (tenvE : tenv_val_exp) : weak_tenvE tenvE tenvE :=
  ⟨Nat.le_refl _, fun _ _ _ _ => Iff.rfl⟩

/- HOL4:
Theorem weak_tenvE_freevars[local]:
  !tenv tenv' tvs t.
  weak_tenvE tenv' tenv ∧
  check_freevars (num_tvs tenv) tvs t ⇒
  check_freevars (num_tvs tenv') tvs t -/
theorem weak_tenvE_freevars :
    ∀ (tenv tenv' : tenv_val_exp) (tvs : List mlstring) (t : typ),
      weak_tenvE tenv' tenv ∧ check_freevars (num_tvs tenv) tvs t →
      check_freevars (num_tvs tenv') tvs t :=
  fun _ _ _ _ ⟨h1, h2⟩ => check_freevars_add _ _ _ h2 _ h1.1

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
  | some x => exact weak_tenvE_bind _ _ _ _ _ h

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
  · rw [Aux.num_tvs_bind_tvar, Aux.num_tvs_bind_tvar]; omega
  · rw [Aux.tveLookup_bind_tvar, Aux.tveLookup_bind_tvar]
    exact h2 _ _ _ _

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
  rintro tenv tenv' - tvs - ⟨h0, h1, h2, h3⟩
  refine ⟨?_, fun x inc tvs' t' => ?_⟩
  · rw [Aux.num_tvs_bind_tvar, Aux.num_tvs_bind_tvar]; omega
  · rw [Aux.tveLookup_bind_tvar, Aux.tveLookup_bind_tvar, ← h3,
      tveLookup_no_tvs _ _ _ _ _ ⟨h0, h1⟩, tveLookup_no_tvs (inc + tvs) _ _ _ _ ⟨h0, h1⟩]

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
  intro bindings tenvE tenvE' n tvs t h
  induction bindings with
  | nil => exact h
  | cons p l ih =>
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
  rintro cn tenv tenv' tvs ts tn ⟨⟨-, h1, -⟩, h2⟩
  obtain ⟨y, hy, he⟩ := h1 _ _ h2
  have he : (tvs, ts, tn) = y := he
  rw [hy, he]

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
  rintro n tenv tenv' tvs t ⟨⟨⟨h1, -⟩, -⟩, h2⟩
  obtain ⟨⟨tvs', t'⟩, hy, he⟩ := h1 _ _ h2
  exact ⟨tvs', t', hy, he⟩

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
  refine Aux.type_p_ind
    (P := fun tvs tenv p t b => ∀ (tenv' : type_env) (tvs' : Nat),
      tvs' ≥ tvs ∧ weak tenv' tenv → type_p tvs' tenv' p t b)
    (Q := fun tvs tenv ps ts b => ∀ (tenv' : type_env) (tvs' : Nat),
      tvs' ≥ tvs ∧ weak tenv' tenv → type_ps tvs' tenv' ps ts b)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro tvs tenv t h tenv' tvs' hw
    exact type_p.any _ _ _ (check_freevars_add _ _ _ h _ hw.1)
  · intro tvs tenv x t h tenv' tvs' hw
    exact type_p.var _ _ _ _ (check_freevars_add _ _ _ h _ hw.1)
  · intro _ _ _ _ _ _; exact type_p.intLit _ _ _
  · intro _ _ _ _ _ _; exact type_p.char _ _ _
  · intro _ _ _ _ _ _; exact type_p.strLit _ _ _
  · intro _ _ _ _ _ _; exact type_p.word8 _ _ _
  · intro _ _ _ _ _ _; exact type_p.word64 _ _ _
  · intro tvs tenv cn ps ts tvs' tn ts' b h1 h2 h3 h4 ih tenv' tvs'' hw
    exact type_p.con _ _ _ _ _ _ _ _ _
      (Aux.EVERY_mono (fun x _ hx => check_freevars_add _ _ _ hx _ hw.1) h1) h2
      (ih tenv' tvs'' hw) (eLookupC_weak _ _ _ _ _ _ ⟨hw.2.2, h4⟩)
  · intro tvs tenv ps ts b h1 ih tenv' tvs' hw
    exact type_p.tup _ _ _ _ _ (ih tenv' tvs' hw)
  · intro tvs tenv p t b h1 ih tenv' tvs' hw
    exact type_p.ref _ _ _ _ _ (ih tenv' tvs' hw)
  · intro tvs tenv p v t b h1 ih tenv' tvs' hw
    exact type_p.pas _ _ _ _ _ _ (ih tenv' tvs' hw)
  · intro tvs tenv p t b h1 h2 h3 ih tenv' tvs' hw
    have := ih tenv' tvs' hw
    have ht := hw.2.1
    rw [← ht] at this h2 ⊢
    exact type_p.tannot _ _ _ _ _ h1 h2 this
  · intro _ _ _ _ _; exact type_ps.nil _ _
  · intro tvs tenv p ps t ts b b' h1 h2 ih1 ih2 tenv' tvs' hw
    exact type_ps.cons _ _ _ _ _ _ _ _ (ih1 tenv' tvs' hw) (ih2 tenv' tvs' hw)

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
  refine Aux.type_e_ind
    (P := fun tenv tenvE e t => ∀ (tenv' : type_env) (tenvE' : tenv_val_exp),
      weak tenv' tenv ∧ weak_tenvE tenvE' tenvE → type_e tenv' tenvE' e t)
    (Q := fun tenv tenvE es ts => ∀ (tenv' : type_env) (tenvE' : tenv_val_exp),
      weak tenv' tenv ∧ weak_tenvE tenvE' tenvE → type_es tenv' tenvE' es ts)
    (R := fun tenv tenvE funs bs => ∀ (tenv' : type_env) (tenvE' : tenv_val_exp),
      weak tenv' tenv ∧ weak_tenvE tenvE' tenvE → type_funs tenv' tenvE' funs bs)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro _ _ _ _ _ _; exact type_e.intLit _ _ _
  · intro _ _ _ _ _ _; exact type_e.char _ _ _
  · intro _ _ _ _ _ _; exact type_e.strLit _ _ _
  · intro _ _ _ _ _ _; exact type_e.word8 _ _ _
  · intro _ _ _ _ _ _; exact type_e.word64 _ _ _
  · intro _ _ _ _ _ _; exact type_e.float64 _ _ _
  · intro tenv tenvE e t h1 h2 ih tenv' tenvE' hw
    exact type_e.raise _ _ _ _ (weak_tenvE_freevars _ _ _ _ ⟨hw.2, h1⟩) (ih _ _ hw)
  · intro tenv tenvE e pes t bs h1 h2 h3 h4 h5 ih1 ih2 tenv' tenvE' hw
    exact type_e.handle _ _ _ _ _ bs (ih1 _ _ hw) h2 h3
      (fun pe hm => type_p_weakening.1 _ _ _ _ _ (h4 pe hm) _ _ ⟨hw.2.1, hw.1⟩)
      (fun pe hm => ih2 pe hm _ _ ⟨hw.1, weak_tenvE_bind_var_list _ _ _ () _ () hw.2⟩)
  · intro tenv tenvE cn es tvs tn ts' ts h1 h2 h3 h4 ih tenv' tenvE' hw
    exact type_e.con _ _ _ _ _ _ _ _
      (Aux.EVERY_mono (fun x _ hx => check_freevars_add _ _ _ hx _ hw.2.1) h1) h2 (ih _ _ hw)
      (eLookupC_weak _ _ _ _ _ _ ⟨hw.1.2, h4⟩)
  · intro tenv tenvE es ts h1 ih tenv' tenvE' hw
    exact type_e.tup _ _ _ _ (ih _ _ hw)
  · intro tenv tenvE n t targs tvs htv h1 h2 tenv' tenvE' hw
    have hE : ∀ x tvs t, lookup_varE x tenvE = some (tvs, t) ↔
        lookup_varE x tenvE' = some (tvs, t) := by
      intro x tvs t
      cases x with
      | Short y => exact hw.2.2 _ _ _ _
      | Long mn id => exact Iff.rfl
    have h1' := Aux.EVERY_mono (fun x _ hx => check_freevars_add _ _ _ hx _ hw.2.1) h1
    unfold lookup_var at h2
    cases hl : lookup_varE n tenvE with
    | some p =>
      rw [hl] at h2
      cases h2
      refine type_e.var _ _ _ _ _ _ htv h1' ?_
      unfold lookup_var
      rw [(hE _ _ _).mp hl]
    | none =>
      rw [hl] at h2
      obtain ⟨tvs', t', hlk, subst, hs1, hs2, hs3, hs4⟩ :=
        eLookupV_weak _ _ _ _ _ ⟨hw.1.2, h2⟩
      have hl' : lookup_varE n tenvE' = none := by
        cases hq : lookup_varE n tenvE' with
        | none => rfl
        | some p =>
          obtain ⟨a, b⟩ := p
          rw [(hE _ _ _).mpr hq] at hl
          cases hl
      have e := (deBruijn_subst2 (α := Unit) (β := Unit)).1 t' 0 subst targs ()
        (by rw [hs1]; exact hs2)
      rw [deBruijn_inc0.2, hs4] at e
      rw [e]
      refine type_e.var _ _ _ _ _ tvs' (by rw [List.length_map, hs1]) ?_ ?_
      · rw [EVERY_iff_forall] at hs3 ⊢
        intro x hx
        obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
        exact deBruijn_subst_check_freevars2 _ _ _ _ () () ⟨htv ▸ hs3 y hy, h1'⟩
      · unfold lookup_var
        rw [hl']
        exact hlk
  · intro tenv tenvE n e t1 t2 h1 h2 ih tenv' tenvE' hw
    exact type_e.fn _ _ _ _ _ _ (weak_tenvE_freevars _ _ _ _ ⟨hw.2, h1⟩)
      (ih _ _ ⟨hw.1, weak_tenvE_bind _ _ _ _ _ hw.2⟩)
  · intro tenv tenvE o es ts t h1 h2 h3 ih tenv' tenvE' hw
    exact type_e.app _ _ _ _ _ _ (ih _ _ hw) h2 (weak_tenvE_freevars _ _ _ _ ⟨hw.2, h3⟩)
  · intro tenv tenvE l e1 e2 h1 h2 ih1 ih2 tenv' tenvE' hw
    exact type_e.log _ _ _ _ _ (ih1 _ _ hw) (ih2 _ _ hw)
  · intro tenv tenvE e1 e2 e3 t h1 h2 h3 ih1 ih2 ih3 tenv' tenvE' hw
    exact type_e.if' _ _ _ _ _ _ (ih1 _ _ hw) (ih2 _ _ hw) (ih3 _ _ hw)
  · intro tenv tenvE e pes t1 t2 bs h1 h2 h3 h4 h5 ih1 ih2 tenv' tenvE' hw
    exact type_e.mat _ _ _ _ _ _ bs (ih1 _ _ hw) h2 h3
      (fun pe hm => type_p_weakening.1 _ _ _ _ _ (h4 pe hm) _ _ ⟨hw.2.1, hw.1⟩)
      (fun pe hm => ih2 pe hm _ _ ⟨hw.1, weak_tenvE_bind_var_list _ _ _ () _ () hw.2⟩)
  · intro tenv tenvE n e1 e2 t1 t2 h1 h2 ih1 ih2 tenv' tenvE' hw
    exact type_e.let' _ _ _ _ _ _ _ (ih1 _ _ hw)
      (ih2 _ _ ⟨hw.1, weak_tenvE_opt_bind _ _ _ _ _ hw.2⟩)
  · intro tenv tenvE funs e t bindings h1 h2 ih1 ih2 tenv' tenvE' hw
    have hw' := weak_tenvE_bind_var_list bindings _ _ () 0 () hw.2
    exact type_e.letrec _ _ _ _ _ bindings (ih1 _ _ ⟨hw.1, hw'⟩) (ih2 _ _ ⟨hw.1, hw'⟩)
  · intro tenv tenvE e t h1 h2 h3 ih tenv' tenvE' hw
    have := ih _ _ hw
    have ht := hw.1.1
    rw [← ht] at this h2 ⊢
    exact type_e.tannot _ _ _ _ h1 h2 this
  · intro tenv tenvE e l t h1 ih tenv' tenvE' hw
    exact type_e.lannot _ _ _ _ _ (ih _ _ hw)
  · intro _ _ _ _ _; exact type_es.nil _ _
  · intro tenv tenvE e es t ts h1 h2 ih1 ih2 tenv' tenvE' hw
    exact type_es.cons _ _ _ _ _ _ (ih1 _ _ hw) (ih2 _ _ hw)
  · intro _ _ _ _ _; exact type_funs.nil _ _
  · intro tenv tenvE fn n e funs bs t1 t2 h1 h2 h3 h4 ih1 ih2 tenv' tenvE' hw
    exact type_funs.cons _ _ _ _ _ _ _ _ _ (weak_tenvE_freevars _ _ _ _ ⟨hw.2, h1⟩)
      (ih1 _ _ ⟨hw.1, weak_tenvE_bind _ _ _ _ _ hw.2⟩) (ih2 _ _ hw) h4

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
theorem gt_0 : ∀ x : Nat, x ≥ 0 := Nat.zero_le

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
      FLOOKUP ctMap' stamp = some (tvs, ts) :=
  fun _ _ _ _ _ ⟨h1, h2⟩ => Aux.weakCT_iff.mp h1 _ _ h2

/- HOL4:
Theorem weakCT_refl:
 !ctMap. weakCT ctMap ctMap -/
theorem weakCT_refl {α β : Type} : ∀ ctMap : fmap α β, weakCT ctMap ctMap :=
  fun _ _ h => ⟨h, rfl⟩

/- HOL4:
Theorem weakCT_trans:
 weakCT C1 C2 ∧ weakCT C2 C3 ⇒ weakCT C1 C3 -/
theorem weakCT_trans {α β : Type} (C1 C2 C3 : fmap α β) :
    weakCT C1 C2 ∧ weakCT C2 C3 → weakCT C1 C3 := by
  rw [Aux.weakCT_iff, Aux.weakCT_iff, Aux.weakCT_iff]
  exact fun ⟨h1, h2⟩ x y h => h1 _ _ (h2 _ _ h)

/- HOL4:
Theorem disjoint_env_weakCT:
 !ctMap ctMap'.
  DISJOINT (FDOM ctMap') (FDOM ctMap) ⇒
  weakCT (FUNION ctMap' ctMap) ctMap -/
theorem disjoint_env_weakCT {α β : Type} :
    ∀ ctMap ctMap' : fmap α β,
      DISJOINT (FDOM ctMap') (FDOM ctMap) → weakCT (FUNION ctMap' ctMap) ctMap := by
  intro ctMap ctMap' h
  rw [Aux.DISJOINT_iff] at h
  rw [Aux.weakCT_iff]
  intro x y hx
  rw [Aux.FLOOKUP_FUNION]
  cases h2 : FLOOKUP ctMap' x with
  | none => exact hx
  | some z =>
    refine (h x ?_ ?_).elim
    · rw [Aux.mem_FDOM, h2]; simp
    · rw [Aux.mem_FDOM, hx]; simp

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
  rintro ctMap tenvC envC ctMap' ⟨h1, h2⟩
  rw [Aux.weakCT_iff] at h1
  refine nsAll2_mono ?_ h2
  rintro x ⟨n, stamp⟩ ⟨tvs, ts, ti⟩ ⟨h3, h4⟩
  exact ⟨h1 _ _ h3, h4⟩

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
  rintro ctMap tenvS tenvV envV ctMap' tenvS' ⟨h1, h2, h3⟩
  refine nsAll2_mono ?_ h3
  rintro x v ⟨tvs, t⟩ h
  exact h tvs ctMap' tenvS' ⟨Or.inr rfl, h1, h2⟩

theorem Aux.weak_bind_tvar {tvs tvs' : Nat} {tenvE : tenv_val_exp} (h : tvs = 0 ∨ tvs = tvs')
    (h1 : tenv_val_exp_ok tenvE) (h2 : num_tvs tenvE = 0) :
    weak_tenvE (bind_tvar tvs' tenvE) (bind_tvar tvs tenvE) := by
  rcases h with rfl | rfl
  · exact weak_tenvE_bind_tvar2 _ _ () _ () ⟨h1, h2, Aux.weak_tenvE_refl _⟩
  · exact Aux.weak_tenvE_refl _

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
  intro tvs ctMap tenvS v t h
  have hle : ∀ {tvs tvs' : Nat}, (tvs = 0 ∨ tvs = tvs') → tvs' ≥ tvs := by
    intro tvs tvs' h; omega
  induction h with
  | intLit => intros; exact type_v.intLit _ _ _ _
  | char => intros; exact type_v.char _ _ _ _
  | strLit => intros; exact type_v.strLit _ _ _ _
  | word8 => intros; exact type_v.word8 _ _ _ _
  | word64 => intros; exact type_v.word64 _ _ _ _
  | float64 => intros; exact type_v.float64 _ _ _ _
  | conv tvs ctMap tenvS vs tvs'' stamp ts' ts ti h1 h2 h3 h4 h5 ih =>
    rintro tvs' ctMap' tenvS' ⟨ht, hc, hs⟩
    exact type_v.conv _ _ _ _ _ _ _ _ _
      (Aux.EVERY_mono (fun x _ hx => check_freevars_add _ _ _ hx _ (hle ht)) h1) h2 h3
      (fun i v t hv htt => ih i v t hv htt _ _ _ ⟨ht, hc, hs⟩) (Aux.weakCT_iff.mp hc _ _ h5)
  | tup tvs ctMap tenvS vs ts h1 h2 ih =>
    rintro tvs' ctMap' tenvS' ⟨ht, hc, hs⟩
    exact type_v.tup _ _ _ _ _ h1 (fun i v t hv htt => ih i v t hv htt _ _ _ ⟨ht, hc, hs⟩)
  | closure tvs ctMap tenvS env tenv tenvE n e t1 t2 h1 h2 h3 h4 h5 h6 h7 h8 ih =>
    rintro tvs' ctMap' tenvS' ⟨ht, hc, hs⟩
    exact type_v.closure _ _ _ _ _ _ _ _ _ _ h1 h2 h3
      (type_tenv_ctor_weakening _ _ _ _ ⟨hc, h4⟩) h5
      (fun i v tt hv htt => ih i v tt hv htt _ _ _ ⟨Or.inr rfl, hc, hs⟩)
      (check_freevars_add _ _ _ h7 _ (hle ht))
      (type_e_weakening.1 _ _ _ _ _ _ ⟨h8, ⟨rfl, weak_tenv_refl _ h1.1⟩,
        weak_tenvE_bind _ _ _ _ _ (Aux.weak_bind_tvar ht h2 h3)⟩)
  | recclosure tvs ctMap tenvS env funs n t tenv tenvE bindings h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 ih =>
    rintro tvs' ctMap' tenvS' ⟨ht, hc, hs⟩
    exact type_v.recclosure _ _ _ _ _ _ _ _ _ _ h1 h2 h3
      (type_tenv_ctor_weakening _ _ _ _ ⟨hc, h4⟩) h5
      (fun i v tt hv htt => ih i v tt hv htt _ _ _ ⟨Or.inr rfl, hc, hs⟩)
      (type_e_weakening.2.2 _ _ _ _ _ _ ⟨h7, ⟨rfl, weak_tenv_refl _ h1.1⟩,
        weak_tenvE_bind_var_list _ _ _ () _ () (Aux.weak_bind_tvar ht h2 h3)⟩)
      h8 h9 h10
  | ref tvs ctMap tenvS n t h1 h2 =>
    rintro tvs' ctMap' tenvS' ⟨ht, hc, hs⟩
    exact type_v.ref _ _ _ _ _ h1 (Aux.weakS_iff.mp hs _ _ h2)
  | w8array tvs ctMap tenvS n h1 =>
    rintro tvs' ctMap' tenvS' ⟨ht, hc, hs⟩
    exact type_v.w8array _ _ _ _ (Aux.weakS_iff.mp hs _ _ h1)
  | varray tvs ctMap tenvS n t h1 h2 =>
    rintro tvs' ctMap' tenvS' ⟨ht, hc, hs⟩
    exact type_v.varray _ _ _ _ _ h1 (Aux.weakS_iff.mp hs _ _ h2)
  | vector tvs ctMap tenvS vs t h1 h2 ih =>
    rintro tvs' ctMap' tenvS' ⟨ht, hc, hs⟩
    exact type_v.vector _ _ _ _ _ h1 (fun v hv => ih v hv _ _ _ ⟨ht, hc, hs⟩)

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
  rintro ctMap tenvS tenv env ctMap' tenvS' ⟨hc, hs, h1, h2⟩
  refine ⟨type_tenv_ctor_weakening _ _ _ _ ⟨hc, h1⟩, nsAll2_mono ?_ h2⟩
  rintro x v ⟨tvs, t⟩ h
  exact type_v_weakening _ _ _ _ _ h _ _ _ ⟨Or.inr rfl, hc, hs⟩

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
  rintro ctMap tenvS st sv ctMap' tenvS' ⟨h, hc, hs⟩
  cases sv <;> cases st <;> simp only [type_sv] at h ⊢
  · exact type_v_weakening _ _ _ _ _ h _ _ _ ⟨Or.inr rfl, hc, hs⟩
  · exact Aux.EVERY_mono
      (fun v _ hv => type_v_weakening _ _ _ _ _ hv _ _ _ ⟨Or.inr rfl, hc, hs⟩) h

/- HOL4:
Theorem type_s_weakening:
 !ctMap tenvS st ctMap'.
  type_s ctMap st tenvS ∧
  weakCT ctMap' ctMap
  ⇒
  type_s ctMap' st tenvS -/
theorem type_s_weakening :
    ∀ (ctMap : ctMap_ty) (tenvS : tenv_store) (st : List (store_v value)) (ctMap' : ctMap_ty),
      type_s ctMap st tenvS ∧ weakCT ctMap' ctMap → type_s ctMap' st tenvS :=
  fun _ _ _ _ ⟨h, hc⟩ l =>
    ⟨(h l).1, fun st sv hh => type_sv_weakening _ _ _ _ _ _ ⟨(h l).2 st sv hh, hc, weakS_refl _⟩⟩

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
  rintro tenv1 tenv2 tenv3 ⟨h1, h2, h3⟩
  obtain ⟨h4, h5⟩ := weak_tenv_refl _ h1
  exact ⟨nsSub_nsAppend2 _ _ _ _ ⟨h4, h2⟩, nsSub_nsAppend2 _ _ _ _ ⟨h5, h3⟩⟩

end

end CmlTS
