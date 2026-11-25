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
import CmlTS.Proofs.TypeSoundAux

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
    (fun ((x, _, _) : α × β × γ) => x) = Prod.fst := by
  funext ⟨x, y, z⟩; rfl

/- HOL4:
Theorem sing_list[local]:
  !l. LENGTH l = 1 ⇔ ?x. l = [x] -/
theorem sing_list {α : Type} :
    ∀ l : List α, l.length = 1 ↔ ∃ x, l = [x] := fun _ => List.length_eq_one_iff

/- HOL4:
Theorem EVERY_LIST_REL[local]:
  EVERY (\x. f x y) l = LIST_REL (\x y. f x y) l (REPLICATE (LENGTH l) y) -/
theorem EVERY_LIST_REL {α β : Type} (f : α → β → Prop) (y : β) (l : List α) :
    EVERY (fun x => f x y) l ↔
      LIST_REL (fun x y => f x y) l (List.replicate l.length y) := by
  rw [EVERY_iff_forall]
  exact Aux.LR_replicate.symm

/- HOL4:
Theorem v_unchanged[simp]:
  !tenv x. tenv with v := tenv.v = tenv -/
theorem v_unchanged {α : Type} :
    ∀ (tenv : type_env) (_x : α), { tenv with v := tenv.v } = tenv := fun _ _ => rfl

/- HOL4:
Theorem check_dup_ctors_thm:
  check_dup_ctors (tvs,tn,condefs) = ALL_DISTINCT (MAP FST condefs) -/
theorem check_dup_ctors_thm (tvs : List tvarN) (tn : mlstring)
    (condefs : List (mlstring × List ast_t)) :
    check_dup_ctors (tvs, tn, condefs) ↔ ALL_DISTINCT (condefs.map Prod.fst) := by
  have : condefs.foldr (fun ((n, _) : mlstring × List ast_t) (x2 : List mlstring) =>
      if True then n :: x2 else x2) [] = condefs.map Prod.fst := by
    induction condefs with
    | nil => rfl
    | cons c cs ih =>
      rw [List.foldr_cons, ih]
      simp
  show ALL_DISTINCT (condefs.foldr (fun ((n, _) : mlstring × List ast_t) (x2 : List mlstring) =>
      if True then n :: x2 else x2) []) ↔ _
  rw [this]

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
      (∃ vs, v = Vectorv vs ∧ EVERY (fun v => type_v tvs ctMap tenvS v t) vs)) := by
  refine ⟨fun h => Aux.canon_int h.1 h.2, fun h => Aux.canon_char h.1 h.2,
    fun h => Aux.canon_str h.1 h.2, fun h => Aux.canon_word8 h.1 h.2,
    fun h => Aux.canon_word64 h.1 h.2, fun h => Aux.canon_double h.1 h.2, ?_,
    fun h => Aux.canon_fn h.1 h.2, ?_, ?_, ?_, ?_⟩
  · rintro ⟨h, hc⟩
    obtain ⟨vs, rfl, hl⟩ := Aux.canon_tup h hc
    exact ⟨vs, rfl, (Aux.LIST_REL_length hl).symm⟩
  · rintro ⟨h, hc, hs⟩
    obtain ⟨n, rfl, _, hl⟩ := Aux.canon_ref h hc
    obtain ⟨sv, h1, h2⟩ := Aux.type_s_lookup hs hl
    cases sv with
    | Refv v2 => exact ⟨n, v2, rfl, h1, h2⟩
    | _ => exact h2.elim
  · rintro ⟨h, hc, hs⟩
    obtain ⟨n, rfl, hl⟩ := Aux.canon_w8array h hc
    obtain ⟨sv, h1, h2⟩ := Aux.type_s_lookup hs hl
    cases sv with
    | W8array ws => exact ⟨n, ws, rfl, h1, hl⟩
    | _ => exact h2.elim
  · rintro ⟨h, hc, hs⟩
    obtain ⟨n, rfl, _, hl⟩ := Aux.canon_array h hc
    obtain ⟨sv, h1, h2⟩ := Aux.type_s_lookup hs hl
    cases sv with
    | Varray vs => exact ⟨n, vs, rfl, h1, h2, hl⟩
    | _ => exact h2.elim
  · rintro ⟨h, hc⟩
    obtain ⟨vs, rfl, _, hl⟩ := Aux.canon_vector h hc
    exact ⟨vs, rfl, EVERY_iff_forall.2 hl⟩

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
        (t3 = Tstring → ∃ str, vs_to_string vs = some str) := by
  rintro m tvs S t ⟨hc, hm, h⟩
  obtain ⟨vs, h1, h2, h3⟩ := Aux.list_canon hc hm t _ v (Nat.le_refl _) h
  exact ⟨vs, h1, EVERY_iff_forall.2 h2, h3⟩

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
      (∃ n vs, same_type stamp (ExnStamp n) ∧ v = Conv (some (ExnStamp n)) vs)) := by
  refine ⟨fun h => Aux.canon_bool h.1 h.2.1 h.2.2,
    fun h => has_lists_v_to_list v ctMap tvs tenvS t ⟨h.2.1, h.2.2, h.1⟩, ?_⟩
  rintro ⟨h, hc, hl⟩
  obtain ⟨s', vs, _, _, rfl, hs, _⟩ := Aux.type_v_con h hc hl
  cases s' with
  | TypeStamp cn n => exact Or.inl ⟨cn, n, vs, hs, rfl⟩
  | ExnStamp n => exact Or.inr ⟨n, vs, hs, rfl⟩

/- HOL4:
Theorem same_type_refl[local]:
  !t. same_type t t -/
theorem same_type_refl : ∀ t : stamp, same_type t t := by
  intro t; cases t <;> simp [same_type]

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
      do_eq_list vs1 vs2 ≠ Eq_type_error) := by
  refine ⟨?_, ?_⟩
  · rintro v1 v2 tvs m _ S t ⟨hc, h1, h2⟩
    exact Aux.do_eq_ok hc _ v1 (Nat.le_refl _) v2 t h1 h2
  · rintro vs1 vs2 tvs m _ S ts ⟨hc, h1, h2⟩
    exact Aux.do_eq_list_ok (fun v1 _ v2 t => Aux.do_eq_ok hc _ v1 (Nat.le_refl _) v2 t) h1 h2

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
        (nsLookup tenvC cn = none → nsLookup envC cn = none) := by
  rintro m envC tenvC h cn tvs ts _ ti
  refine ⟨fun hl => ?_, fun hl => (nsAll2_nsLookup_none _ _ _ _ h).2 hl⟩
  obtain ⟨⟨n, s⟩, h1, h2, rfl⟩ := nsAll2_nsLookup2 _ _ _ _ _ ⟨hl, h⟩
  exact ⟨Classical.choice inferInstance, s, h1, h2⟩

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
      funs.map Prod.fst = tenv'.map Prod.fst := fun _ _ _ _ h => (Aux.type_funs_fst h).symm

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
        (bindings.map (fun (x, t) => (x, tvs, t))) := by
  rintro _ funs funs' m tenv b E env S tvs b' ⟨hd, hok, henv, hE, h0, hsub, hf', hf⟩
  induction funs generalizing b with
  | nil => cases hf; trivial
  | cons f funs ih =>
    cases hf with
    | cons _ fn n e funs b t1 t2 h1 h2 h3 h4 =>
      refine ⟨⟨rfl, ?_⟩, ih b (fun x t hx => hsub x t ?_) h3⟩
      · have hl : ALOOKUP b' fn = some (Tfn t1 t2) := hsub fn _ (by simp [ALOOKUP])
        refine type_v_recclosure_aux _ _ _ _ _ _ _ tenv E b' hok hE h0 henv.1 henv.2 hf' hl hd ?_
        rw [← Aux.type_funs_fst hf']
        exact List.mem_map.2 ⟨_, Aux.ALOOKUP_mem hl, rfl⟩
      · simp only [ALOOKUP]
        rw [if_neg]
        · exact hx
        · rintro rfl
          rw [h4] at hx; cases hx

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
        (bindings.map (fun (x, t) => (x, tvs, t))) := by
  rintro funs m S tvs tenv E env b ⟨hok, henv, hE, h0, hf, hd⟩
  exact type_recfun_env_help () funs funs m tenv b E env S tvs b
    ⟨hd, hok, henv, hE, h0, fun _ _ h => h, hf, hf⟩

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
      type_v tvs cenv senv (Conv (some div_stamp) []) Texn := by
  rintro tvs m S ⟨h1, h2, h3, h4⟩
  exact ⟨Aux.type_v_conv_intro (ts := []) trivial rfl trivial h2,
    Aux.type_v_conv_intro (ts := []) trivial rfl trivial h4,
    Aux.type_v_conv_intro (ts := []) trivial rfl trivial h1,
    Aux.type_v_conv_intro (ts := []) trivial rfl trivial h3⟩

/- HOL4:
Theorem type_v_Boolv[local]:
  ctMap_has_bools ctMap ⇒ type_v tvs ctMap tenvS (Boolv b) Tbool -/
theorem type_v_Boolv (ctMap : ctMap_ty) (tvs : Nat) (tenvS : tenv_store) (b : Bool) :
    ctMap_has_bools ctMap → type_v tvs ctMap tenvS (Boolv b) Tbool := by
  rintro ⟨h1, h2, -⟩
  cases b
  · exact Aux.type_v_conv_intro (ts := []) trivial rfl trivial h2
  · exact Aux.type_v_conv_intro (ts := []) trivial rfl trivial h1

/- HOL4:
Theorem remove_lambda_prod[local]:
  (\ (x,y). P x y) = (\xy. P (FST xy) (SND xy)) -/
theorem remove_lambda_prod {α β γ : Type} (P : α → β → γ) :
    (fun ((x, y) : α × β) => P x y) = (fun xy => P xy.1 xy.2) := by
  funext ⟨x, y⟩; rfl

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
        do_opapp vs = some (env, e) := by
  rintro m S vs ts t ⟨hc, ho, hl⟩
  have hts : ∃ t2, ts = [Tfn t2 t, t2] := by
    rcases ts with _ | ⟨t1, _ | ⟨t2, _ | ⟨t3, ts⟩⟩⟩
    · exact ho.elim
    · exact ho.elim
    · exact ⟨t2, by rw [show t1 = Tfn t2 t from ho]⟩
    · exact ho.elim
  obtain ⟨t2, rfl⟩ := hts
  obtain ⟨v1, v2, rfl, hv1, hv2⟩ := Aux.LR2 hl
  have hc2 : check_freevars 0 [] t2 := type_v_freevars _ _ _ _ _ hv2
  rcases Aux.canon_fn hv1 hc with ⟨env, n, e, rfl⟩ | ⟨env, funs, n, rfl⟩
  · obtain ⟨tenv, E, t1', t2', he, hok, hE, h0, hcc, hvv, ht1, hte⟩ :=
      type_v_closure_inv_aux _ _ _ _ _ _ _ hv1
    cases he
    rw [bind_tvar0] at hte
    refine ⟨{ env with v := nsBind n v2 env.v }, e, tenv, Bind_name n 0 t2 E, hok,
      ⟨by rw [h0]; exact hc2, hE⟩, h0,
      ⟨hcc, nsAll2_nsBind _ _ _ _ _ _ ⟨hv2, hvv⟩⟩, hte, rfl⟩
  · obtain ⟨tenv, E, b, hok, hE, h0, hcc, hvv, hf, hlk, hd, hm⟩ :=
      type_v_recclosure_inv_aux _ _ _ _ _ _ _ hv1
    obtain ⟨x, e, hfr⟩ := type_funs_find_recfun (α := Unit) (β := Unit) _ () _ _ () _ _ _ ⟨hlk, hf⟩
    have hte := (type_recfun_lookup _ _ _ _ _ _ _ () _ _ ⟨hfr, hf, hlk⟩).1
    have hrec := type_recfun_env funs m S 0 tenv E env b ⟨hok, ⟨hcc, hvv⟩, hE, h0, hf, hd⟩
    rw [bind_tvar0] at hte hf
    refine ⟨{ env with v := nsBind x v2 (build_rec_env funs env env.v) }, e, tenv,
      Bind_name x 0 t2 (bind_var_list 0 b E), hok,
      ⟨by rw [num_tvs_bind_var_list, h0]; exact hc2,
        tenv_val_exp_ok_bvl_funs _ _ _ _ () _ ⟨hf, hE⟩⟩,
      by simp only [num_tvs]; rw [num_tvs_bind_var_list, h0],
      ⟨hcc, nsAll2_nsBind _ _ _ _ _ _ ⟨hv2, ?_⟩⟩, hte, ?_⟩
    · rw [build_rec_env_merge funs () env env.v, nsAppend_to_nsBindList, add_tenvE_bvl]
      exact nsAll2_nsBindList (fun _ v (p : Nat × typ) => type_v p.1 m S v p.2) _ _ _ _
        ⟨hrec, hvv⟩
    · have hd' : ALL_DISTINCT (funs.map (fun (f, _, _) => f)) := hd
      simp only [do_opapp]
      rw [if_pos hd', hfr]

/- HOL4:
Theorem store_type_extension_weakS:
  !tenvS1 tenvS2.
    store_type_extension tenvS1 tenvS2 ⇒ weakS tenvS2 tenvS1 -/
theorem store_type_extension_weakS {α β : Type} :
    ∀ tenvS1 tenvS2 : fmap α β,
      store_type_extension tenvS1 tenvS2 → weakS tenvS2 tenvS1 := fun _ _ h =>
  Aux.SUBMAP_iff.2 (Aux.ste_iff.1 h)

theorem Aux.ste_of_weakS {α β : Type} {S1 S2 : fmap α β} (h : weakS S2 S1) :
    store_type_extension S1 S2 := Aux.ste_iff.2 (Aux.SUBMAP_iff.1 h)

/- HOL4:
Theorem store_type_extension_refl:
  !tenvS. store_type_extension tenvS tenvS -/
theorem store_type_extension_refl {α β : Type} :
    ∀ tenvS : fmap α β, store_type_extension tenvS tenvS := fun _ =>
  Aux.ste_of_weakS (weakS_refl _)

/- HOL4:
Theorem store_type_extension_trans:
  !s1 s2 s3.
    store_type_extension s1 s2 ∧ store_type_extension s2 s3 ⇒
    store_type_extension s1 s3 -/
theorem store_type_extension_trans {α β : Type} :
    ∀ s1 s2 s3 : fmap α β,
      store_type_extension s1 s2 ∧ store_type_extension s2 s3 →
      store_type_extension s1 s3 := fun _ _ _ h =>
  Aux.ste_iff.2 fun x v hx => Aux.ste_iff.1 h.2 x v (Aux.ste_iff.1 h.1 x v hx)

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
        type_s ctMap store' tenvS := by
  rintro m S store sv st l ⟨hs, hl, hsv⟩
  obtain ⟨sv0, h1, h2⟩ := Aux.type_s_lookup hs hl
  rw [Aux.store_lookup_eq] at h1
  have hlt := (List.getElem?_eq_some_iff.1 h1).1
  refine ⟨LUPDATE sv l store, ?_, ?_⟩
  · unfold store_assign
    rw [if_pos]
    refine ⟨hlt, ?_⟩
    rw [Aux.EL_of_getElem? h1]
    cases st <;> cases sv0 <;> cases sv <;> first | exact trivial | exact h2.elim | exact hsv.elim
  · intro l'
    obtain ⟨a1, a2⟩ := hs l'
    rw [Aux.store_lookup_eq] at a1 a2 ⊢
    rw [Aux.LUPDATE_eq_set, List.getElem?_set]
    by_cases hll : l = l'
    · subst hll
      rw [if_pos rfl, if_pos hlt]
      refine ⟨⟨fun _ => ⟨sv, rfl⟩, fun _ => ⟨st, hl⟩⟩, ?_⟩
      rintro st' sv' ⟨b1, b2⟩
      rw [hl] at b1
      cases b1; cases b2
      exact hsv
    · rw [if_neg hll]
      exact ⟨a1, a2⟩

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
        FLOOKUP tenvS' n = some st := by
  rintro m S store sv st ⟨hc, hs, hsv⟩
  have hnone : FLOOKUP S store.length = none := by
    cases h : FLOOKUP S store.length with
    | none => rfl
    | some t =>
      obtain ⟨sv0, h1, _⟩ := Aux.type_s_lookup hs h
      rw [Aux.store_lookup_eq] at h1
      have := (List.getElem?_eq_some_iff.1 h1).1
      omega
  have hw : weakS (FUPDATE S (store.length, st)) S := by
    refine Aux.SUBMAP_iff.2 fun x v hx => ?_
    rw [Aux.FLOOKUP_FUPDATE, if_neg]
    · exact hx
    · rintro rfl; rw [hnone] at hx; cases hx
  refine ⟨store ++ [sv], FUPDATE S (store.length, st), store.length, Aux.ste_of_weakS hw, rfl,
    ?_, by rw [Aux.FLOOKUP_FUPDATE, if_pos rfl]⟩
  intro l
  obtain ⟨a1, a2⟩ := hs l
  rw [Aux.store_lookup_eq] at a1 a2 ⊢
  rw [Aux.FLOOKUP_FUPDATE]
  by_cases hll : l = store.length
  · subst hll
    rw [if_pos rfl, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
    refine ⟨⟨fun _ => ⟨sv, rfl⟩, fun _ => ⟨st, rfl⟩⟩, ?_⟩
    rintro st' sv' ⟨b1, b2⟩
    cases b1; cases b2
    exact type_sv_weakening _ _ _ _ _ _ ⟨hsv, weakCT_refl _, hw⟩
  · rw [if_neg hll]
    have he : (store ++ [sv])[l]? = store[l]? := by
      rcases Nat.lt_or_ge l store.length with h | h
      · exact List.getElem?_append_left h
      · rw [List.getElem?_eq_none h, List.getElem?_eq_none]
        rw [List.length_append, List.length_singleton]; omega
    rw [he]
    exact ⟨a1, fun st' sv' hh =>
      type_sv_weakening _ _ _ _ _ _ ⟨a2 st' sv' hh, weakCT_refl _, hw⟩⟩

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
      type_v n ctMap tenvS (list_to_v xs) t := by
  rintro x xs t ⟨h, hl⟩
  rw [← Aux.v_to_list_inv _ x xs (Nat.le_refl _) hl]
  exact h

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
      type_v 0 ctMap tenvS (list_to_v (xs ++ ys)) (Tapp [t] Tlist_num) := by
  rintro xs ys t ⟨hm, h1, h2⟩
  induction xs with
  | nil => exact h2
  | cons x xs ih =>
    obtain ⟨a, b⟩ := Aux.type_v_cons_inv hm h1
    exact Aux.type_v_cons hm a (ih b)

/- HOL4:
Theorem do_eq_Boolv:
  do_eq (Boolv b) (Boolv b') = Eq_val (b = b') -/
theorem do_eq_Boolv (b b' : Bool) :
    do_eq (Boolv b) (Boolv b') = Eq_val (decide (b = b')) := by
  cases b <;> cases b' <;> simp [Boolv, do_eq, do_eq_list, ctor_same_type, same_type]

/- HOL4:
Theorem prim_canonical_Boolv_thm:
  (type_v tvs ctMap tenvS v Tbool ∧ ctMap_ok ctMap ∧ ctMap_has_bools ctMap ⇒
  (∃b. v = Boolv b)) -/
theorem prim_canonical_Boolv_thm (tvs : Nat) (ctMap : ctMap_ty) (tenvS : tenv_store)
    (v : value) :
    type_v tvs ctMap tenvS v Tbool ∧ ctMap_ok ctMap ∧ ctMap_has_bools ctMap →
    (∃ b, v = Boolv b) := fun h => Aux.canon_bool h.1 h.2.1 h.2.2

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
    v = Boolv true ∨ v = Boolv false := by
  rintro ⟨h, hc, hb⟩
  obtain ⟨b, rfl⟩ := Aux.canon_bool h hc hb
  cases b <;> simp

section op_sound

variable {ffi_ty : Type} {m : ctMap_ty} {S : tenv_store} {op : CmlTS.op} {vs : List value}
  {t : typ} {store : List (store_v value)} {ffi : ffi_state ffi_ty}

def Aux.op_post (m : ctMap_ty) (S : tenv_store) (op : CmlTS.op) (vs : List value) (t : typ)
    (store : List (store_v value)) (ffi : ffi_state ffi_ty) : Prop :=
  ∃ (tenvS' : tenv_store) (store' : List (store_v value)) (ffi' : ffi_state ffi_ty)
    (r : result value value),
    store_type_extension S tenvS' ∧
    type_s m store' tenvS' ∧
    do_app (store, ffi) op vs = some ((store', ffi'), r) ∧
    (match r with
      | Rval v => type_v 0 m tenvS' v t
      | Rerr (Rraise v) => type_v 0 m tenvS' v Texn
      | Rerr (Rabort (Rffi_error _)) => True
      | Rerr (Rabort _) => False)

theorem Aux.op_val {v : value} (hs : type_s m store S) (hv : type_v 0 m S v t)
    (hd : do_app (store, ffi) op vs = some ((store, ffi), Rval v)) :
    Aux.op_post m S op vs t store ffi :=
  ⟨S, store, ffi, Rval v, store_type_extension_refl _, hs, hd, hv⟩

theorem Aux.op_exn {v : value} (hs : type_s m store S) (hv : type_v 0 m S v Texn)
    (hd : do_app (store, ffi) op vs = some ((store, ffi), Rerr (Rraise v))) :
    Aux.op_post m S op vs t store ffi :=
  ⟨S, store, ffi, Rerr (Rraise v), store_type_extension_refl _, hs, hd, hv⟩

theorem Aux.op_assign {v : value} {l : Nat} {sv : store_v value} {st : store_t}
    {ffi' : ffi_state ffi_ty} (hs : type_s m store S) (hl : FLOOKUP S l = some st)
    (hsv : type_sv m S sv st) (hv : type_v 0 m S v t)
    (hd : ∀ store', store_assign l sv store = some store' →
      do_app (store, ffi) op vs = some ((store', ffi'), Rval v)) :
    Aux.op_post m S op vs t store ffi := by
  obtain ⟨store', h1, h2⟩ := store_assign_type_sound m S store sv st l ⟨hs, hl, hsv⟩
  exact ⟨S, store', ffi', Rval v, store_type_extension_refl _, h2, hd _ h1, hv⟩

theorem Aux.op_alloc {sv : store_v value} {st : store_t} (hc : ctMap_ok m)
    (hs : type_s m store S) (hsv : type_sv m S sv st)
    (hd : ∀ store' n, store_alloc sv store = (store', n) →
      do_app (store, ffi) op vs = some ((store', ffi), Rval (Loc true n)))
    (hv : ∀ (S' : tenv_store) n, FLOOKUP S' n = some st → type_v 0 m S' (Loc true n) t) :
    Aux.op_post m S op vs t store ffi := by
  obtain ⟨store', S', n, h1, h2, h3, h4⟩ := store_alloc_type_sound m S store sv st ⟨hc, hs, hsv⟩
  exact ⟨S', store', ffi, Rval (Loc true n), h1, h3, hd _ _ h2, hv _ _ h4⟩

theorem Aux.lookup_w8 {l : Nat} (hs : type_s m store S) (hl : FLOOKUP S l = some W8array_t) :
    ∃ ws, store_lookup l store = some (W8array ws) := by
  obtain ⟨sv, h1, h2⟩ := Aux.type_s_lookup hs hl
  cases sv with
  | W8array ws => exact ⟨ws, h1⟩
  | _ => exact h2.elim

theorem Aux.lookup_arr {l : Nat} {t : typ} (hs : type_s m store S)
    (hl : FLOOKUP S l = some (Varray_t t)) :
    ∃ vs, store_lookup l store = some (Varray vs) ∧ ∀ v, v ∈ vs → type_v 0 m S v t := by
  obtain ⟨sv, h1, h2⟩ := Aux.type_s_lookup hs hl
  cases sv with
  | Varray vs => exact ⟨vs, h1, EVERY_iff_forall.1 h2⟩
  | _ => exact h2.elim

theorem Aux.lookup_ref {l : Nat} {t : typ} (hs : type_s m store S)
    (hl : FLOOKUP S l = some (Ref_t t)) :
    ∃ v, store_lookup l store = some (Refv v) ∧ type_v 0 m S v t := by
  obtain ⟨sv, h1, h2⟩ := Aux.type_s_lookup hs hl
  cases sv with
  | Refv v => exact ⟨v, h1, h2⟩
  | _ => exact h2.elim

theorem Aux.check_type_ok {v : value} {ty : prim_type} (hg : good_ctMap m)
    (h : type_v 0 m S v (t_of ty)) : check_type ty v := by
  rcases ty with _ | _ | _ | _ | (_ | _) | _
  · exact prim_canonical_Boolv_cases _ _ _ _ ⟨h, hg.1, hg.2.1⟩
  · exact Aux.canon_int h hg.1
  · exact Aux.canon_char h hg.1
  · exact Aux.canon_str h hg.1
  · exact Aux.canon_word8 h hg.1
  · exact Aux.canon_word64 h hg.1
  · exact Aux.canon_double h hg.1

theorem Aux.do_eq_val {v1 v2 : value} {t : typ} (hc : ctMap_ok m) (h1 : type_v 0 m S v1 t)
    (h2 : type_v 0 m S v2 t) : ∃ b, do_eq v1 v2 = Eq_val b := by
  cases h : do_eq v1 v2 with
  | Eq_val b => exact ⟨b, rfl⟩
  | Eq_type_error => exact absurd h (Aux.do_eq_ok hc _ v1 (Nat.le_refl _) v2 t h1 h2)

theorem Aux.do_arith_ok {a : arith} {ty : prim_type} (hg : good_ctMap m)
    (hv : ∀ v, v ∈ vs → type_v 0 m S v (t_of ty)) (hs : supported_arith a ty = some vs.length) :
    (∃ res, do_arith a ty vs = some (Sum.inr res) ∧ type_v 0 m S res (t_of ty)) ∨
      do_arith a ty vs = some (Sum.inl div_exn_v) := by
  rcases ty with _ | _ | _ | _ | (_ | _) | _
  · cases a <;> simp [supported_arith] at hs
    obtain ⟨x, rfl⟩ := List.length_eq_one_iff.1 hs.symm
    exact Or.inl ⟨_, rfl, type_v_Boolv _ _ _ _ hg.2.1⟩
  · cases a <;> simp [supported_arith] at hs
    all_goals
      obtain ⟨x, y, rfl⟩ := Aux.length_eq_two.1 hs.symm
      obtain ⟨i, rfl⟩ := Aux.canon_int (hv x (by simp)) hg.1
      obtain ⟨j, rfl⟩ := Aux.canon_int (hv y (by simp)) hg.1
    · exact Or.inl ⟨_, rfl, type_v.intLit _ _ _ _⟩
    · exact Or.inl ⟨_, rfl, type_v.intLit _ _ _ _⟩
    · exact Or.inl ⟨_, rfl, type_v.intLit _ _ _ _⟩
    · by_cases h0 : j = 0
      · exact Or.inr (by simp [do_arith, the_Litv_IntLit, h0])
      · exact Or.inl ⟨_, by simp [do_arith, the_Litv_IntLit, h0]; rfl, type_v.intLit _ _ _ _⟩
    · by_cases h0 : j = 0
      · exact Or.inr (by simp [do_arith, the_Litv_IntLit, h0])
      · exact Or.inl ⟨_, by simp [do_arith, the_Litv_IntLit, h0]; rfl, type_v.intLit _ _ _ _⟩
  · simp [supported_arith] at hs
  · simp [supported_arith] at hs
  · cases a <;> simp [supported_arith] at hs
    all_goals
      obtain ⟨x, y, rfl⟩ := Aux.length_eq_two.1 hs.symm
      exact Or.inl ⟨_, rfl, type_v.word8 _ _ _ _⟩
  · cases a <;> simp [supported_arith] at hs
    all_goals
      obtain ⟨x, y, rfl⟩ := Aux.length_eq_two.1 hs.symm
      exact Or.inl ⟨_, rfl, type_v.word64 _ _ _ _⟩
  · cases a <;> simp [supported_arith] at hs
    all_goals first
      | (obtain ⟨x, rfl⟩ := List.length_eq_one_iff.1 hs.symm
         exact Or.inl ⟨_, rfl, type_v.float64 _ _ _ _⟩)
      | (obtain ⟨x, y, rfl⟩ := Aux.length_eq_two.1 hs.symm
         exact Or.inl ⟨_, rfl, type_v.float64 _ _ _ _⟩)
      | (obtain ⟨x, y, z, rfl⟩ := Aux.length_eq_three.1 hs.symm
         exact Or.inl ⟨_, rfl, type_v.float64 _ _ _ _⟩)

theorem Aux.do_conversion_ok {v : value} {ty1 ty2 : prim_type}
    (hs : supported_conversion ty1 ty2) :
    (∃ res, do_conversion v ty1 ty2 = some (Sum.inr res) ∧ type_v 0 m S res (t_of ty2)) ∨
      do_conversion v ty1 ty2 = some (Sum.inl chr_exn_v) := by
  rcases ty1 with _ | _ | _ | _ | (_ | _) | _ <;>
  rcases ty2 with _ | _ | _ | _ | (_ | _) | _ <;> first
    | exact hs.elim
    | exact Or.inl ⟨_, rfl, type_v.intLit _ _ _ _⟩
    | exact Or.inl ⟨_, rfl, type_v.char _ _ _ _⟩
    | exact Or.inl ⟨_, rfl, type_v.word8 _ _ _ _⟩
    | exact Or.inl ⟨_, rfl, type_v.word64 _ _ _ _⟩
    | exact Or.inl ⟨_, rfl, type_v.float64 _ _ _ _⟩
    | (by_cases h : the_Litv_IntLit v < 0 ∨ the_Litv_IntLit v > 255
       · exact Or.inr (if_pos h)
       · exact Or.inl ⟨_, if_neg h, type_v.char _ _ _ _⟩)

theorem Aux.do_test_ok {v1 v2 : value} {test : CmlTS.test} {ty : prim_type} (hg : good_ctMap m)
    (h1 : type_v 0 m S v1 (t_of ty)) (h2 : type_v 0 m S v2 (t_of ty))
    (hs : supported_test test ty) : ∃ b, do_test test ty v1 v2 = Eq_val b := by
  cases test with
  | Equal =>
    simp only [do_test]
    rw [if_pos ⟨Aux.check_type_ok hg h1, Aux.check_type_ok hg h2⟩]
    split
    · exact ⟨_, rfl⟩
    · exact Aux.do_eq_val hg.1 h1 h2
  | Compare cmp =>
    simp only [supported_test, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl
    · obtain ⟨i, rfl⟩ := Aux.canon_int h1 hg.1
      obtain ⟨j, rfl⟩ := Aux.canon_int h2 hg.1
      exact ⟨_, rfl⟩
    · obtain ⟨i, rfl⟩ := Aux.canon_char h1 hg.1
      obtain ⟨j, rfl⟩ := Aux.canon_char h2 hg.1
      exact ⟨_, rfl⟩
    · obtain ⟨i, rfl⟩ := Aux.canon_word8 h1 hg.1
      obtain ⟨j, rfl⟩ := Aux.canon_word8 h2 hg.1
      exact ⟨_, rfl⟩
    · obtain ⟨i, rfl⟩ := Aux.canon_double h1 hg.1
      obtain ⟨j, rfl⟩ := Aux.canon_double h2 hg.1
      exact ⟨_, rfl⟩
  | AltCompare cmp => exact hs.elim

end op_sound

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
          | Rerr (Rabort _) => False) := by
  rintro m S vs op ts t store ffi ⟨hg, hop, hs, hto, hcf, hl⟩
  have hl := Aux.LIST_REL_reverse hl
  rw [List.reverse_reverse] at hl
  generalize vs.reverse = vs at hl
  show Aux.op_post m S op vs t store ffi
  have hc := hg.1
  have hm := hg.2.2.2
  obtain ⟨hchr, hsub, hbind, hdiv⟩ := type_v_exn 0 m S hg.2.2.1
  have hu : type_v 0 m S (Conv none []) (Ttup []) := type_v_tup_aux _ _ _ _ _ trivial
  have hcf1 : ∀ {t ti}, check_freevars 0 [] (Tapp [t] ti) → check_freevars 0 [] t :=
    fun h => Aux.cf_app.1 h _ (by simp)
  rw [type_op_cases] at hto
  rcases hto with ⟨t1, t2, rfl, _, _⟩ | ⟨sh, n, t1, rfl, rfl, rfl, rfl⟩ |
    ⟨sh, n, t1, rfl, rfl, rfl, rfl⟩ | ⟨t1, t2, rfl, rfl, rfl, rfl⟩ | ⟨a, ty, rfl, hev, rfl, hsup⟩ |
    ⟨ty1, ty2, t1, rfl, rfl, rfl, rfl, hsup⟩ | ⟨test, ty, t1, t2, rfl, rfl, rfl, rfl, rfl, hsup⟩ |
    ⟨t1, t2, rfl, rfl, rfl, rfl⟩ | ⟨t1, rfl, rfl, rfl⟩ | ⟨t1, rfl, rfl, rfl⟩ |
    ⟨t1, t2, rfl, rfl, rfl, rfl, rfl⟩ | ⟨t1, t2, rfl, rfl, rfl, rfl, rfl⟩ |
    ⟨t1, rfl, rfl, rfl, rfl⟩ | ⟨t1, t2, t3, rfl, rfl, rfl, rfl, rfl, rfl⟩ |
    ⟨t1, t2, t3, rfl, rfl, rfl, rfl, rfl, rfl⟩ |
    ⟨t1, t2, t3, t4, t5, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ |
    ⟨t1, t2, t3, rfl, rfl, rfl, rfl, rfl, rfl⟩ |
    ⟨t1, t2, t3, t4, t5, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ |
    ⟨t1, rfl, rfl, rfl, rfl⟩ | ⟨t1, rfl, rfl, rfl, rfl⟩ | ⟨t1, t2, rfl, rfl, rfl, rfl, rfl⟩ |
    ⟨t1, rfl, rfl, rfl, rfl⟩ | ⟨t1, rfl, rfl, rfl, rfl⟩ | ⟨t1, ctor, rfl, rfl, rfl, rfl⟩ |
    ⟨t1, t2, rfl, rfl, rfl, rfl⟩ | ⟨t1, ctor, rfl, rfl, rfl, rfl⟩ | ⟨t1, t2, rfl, rfl, rfl, rfl⟩ |
    ⟨t1, t2, rfl, rfl, rfl, rfl⟩ | ⟨t1, t2, rfl, rfl, rfl, rfl⟩ | ⟨t1, ctor, rfl, rfl, rfl, rfl⟩ |
    ⟨t1, t2, t3, rfl, rfl, rfl, rfl, rfl⟩ | ⟨t1, t2, rfl, rfl, rfl, rfl, rfl⟩ |
    ⟨n, t1, t2, rfl, rfl, rfl, rfl, rfl⟩ | ⟨t1, ctor, t2, rfl, rfl, rfl, rfl, rfl⟩
  · exact absurd rfl hop
  · -- Shift W8
    obtain ⟨v, rfl, hv⟩ := Aux.LR1 hl
    obtain ⟨w, rfl⟩ := Aux.canon_word8 hv hc
    exact Aux.op_val hs (type_v.word8 _ _ _ _) rfl
  · -- Shift W64
    obtain ⟨v, rfl, hv⟩ := Aux.LR1 hl
    obtain ⟨w, rfl⟩ := Aux.canon_word64 hv hc
    exact Aux.op_val hs (type_v.word64 _ _ _ _) rfl
  · -- Equality
    obtain ⟨v1, v2, rfl, hv1, hv2⟩ := Aux.LR2 hl
    obtain ⟨b, hb⟩ := Aux.do_eq_val hc hv1 hv2
    exact Aux.op_val (v := Boolv b) hs (type_v_Boolv _ _ _ _ hg.2.1)
      (by unfold do_app; dsimp only; rw [hb])
  · -- Arith
    rw [EVERY_iff_forall] at hev
    have hv : ∀ v, v ∈ vs → type_v 0 m S v (t_of ty) := by
      intro v hv
      obtain ⟨t, ht, hvt⟩ := Aux.LIST_REL_mem_left hl hv
      rw [hev t ht] at hvt
      exact hvt
    rw [← Aux.LIST_REL_length hl] at hsup
    have hck : EVERY (check_type ty) vs := EVERY_iff_forall.2 fun v h =>
      Aux.check_type_ok hg (hv v h)
    rcases Aux.do_arith_ok hg hv hsup with ⟨res, h1, h2⟩ | h1
    · exact Aux.op_val hs h2 (by unfold do_app; dsimp only; rw [if_pos hck, h1])
    · exact Aux.op_exn hs hdiv (by unfold do_app; dsimp only; rw [if_pos hck, h1]; rfl)
  · -- FromTo
    obtain ⟨v, rfl, hv⟩ := Aux.LR1 hl
    have hck := Aux.check_type_ok hg hv
    rcases Aux.do_conversion_ok (m := m) (S := S) (v := v) hsup with ⟨res, h1, h2⟩ | h1
    · exact Aux.op_val hs h2 (by unfold do_app; dsimp only; rw [if_pos hck, h1])
    · exact Aux.op_exn hs hchr (by unfold do_app; dsimp only; rw [if_pos hck, h1]; rfl)
  · -- Test
    obtain ⟨v1, v2, rfl, hv1, hv2⟩ := Aux.LR2 hl
    obtain ⟨b, hb⟩ := Aux.do_test_ok hg hv1 hv2 hsup
    exact Aux.op_val (v := Boolv b) hs (type_v_Boolv _ _ _ _ hg.2.1)
      (by unfold do_app; dsimp only; rw [hb])
  · -- Opassign
    obtain ⟨v1, v2, rfl, hv1, hv2⟩ := Aux.LR2 hl
    obtain ⟨n, rfl, _, hn⟩ := Aux.canon_ref hv1 hc
    exact Aux.op_assign (sv := Refv v2) hs hn hv2 hu
      (fun st' h => by unfold do_app; dsimp only; rw [h])
  · -- Opref
    obtain ⟨v, rfl, hv⟩ := Aux.LR1 hl
    exact Aux.op_alloc (sv := Refv v) (st := Ref_t t1) hc hs hv
      (fun st' n h => by unfold do_app; dsimp only; rw [h])
      (fun S' n h => type_v.ref _ _ _ _ _ (hcf1 hcf) h)
  · -- Opderef
    obtain ⟨v, rfl, hv⟩ := Aux.LR1 hl
    obtain ⟨n, rfl, _, hn⟩ := Aux.canon_ref hv hc
    obtain ⟨v, h1, h2⟩ := Aux.lookup_ref hs hn
    exact Aux.op_val hs h2 (by unfold do_app; dsimp only; rw [h1])
  · -- Aw8alloc
    obtain ⟨v1, v2, rfl, hv1, hv2⟩ := Aux.LR2 hl
    obtain ⟨i, rfl⟩ := Aux.canon_int hv1 hc
    obtain ⟨w, rfl⟩ := Aux.canon_word8 hv2 hc
    by_cases hi : i < 0
    · exact Aux.op_exn hs hsub (by unfold do_app; dsimp only; rw [if_pos hi]; rfl)
    · exact Aux.op_alloc (sv := W8array (List.replicate (Num (INT_ABS (I i))) w))
        (st := W8array_t) hc hs trivial
        (fun st' n h => by unfold do_app; dsimp only; rw [if_neg hi, h])
        (fun S' n h => type_v.w8array _ _ _ _ h)
  · -- Aw8sub
    obtain ⟨v1, v2, rfl, hv1, hv2⟩ := Aux.LR2 hl
    obtain ⟨n, rfl, hn⟩ := Aux.canon_w8array hv1 hc
    obtain ⟨i, rfl⟩ := Aux.canon_int hv2 hc
    obtain ⟨ws, h1⟩ := Aux.lookup_w8 hs hn
    by_cases hi : i < 0
    · exact Aux.op_exn hs hsub (by unfold do_app; dsimp only; rw [h1]; dsimp only; rw [if_pos hi]; rfl)
    · by_cases hle : Num (INT_ABS (I i)) ≥ ws.length
      · exact Aux.op_exn hs hsub
          (by unfold do_app; dsimp only; rw [h1]; dsimp only; rw [if_neg hi, if_pos hle]; rfl)
      · exact Aux.op_val hs (type_v.word8 _ _ _ _)
          (by unfold do_app; dsimp only; rw [h1]; dsimp only; rw [if_neg hi, if_neg hle])
  · -- Aw8length
    obtain ⟨v, rfl, hv⟩ := Aux.LR1 hl
    obtain ⟨n, rfl, hn⟩ := Aux.canon_w8array hv hc
    obtain ⟨ws, h1⟩ := Aux.lookup_w8 hs hn
    exact Aux.op_val hs (type_v.intLit _ _ _ _) (by unfold do_app; dsimp only; rw [h1])
  · -- Aw8update
    obtain ⟨v1, v2, v3, rfl, hv1, hv2, hv3⟩ := Aux.LR3 hl
    obtain ⟨n, rfl, hn⟩ := Aux.canon_w8array hv1 hc
    obtain ⟨i, rfl⟩ := Aux.canon_int hv2 hc
    obtain ⟨w, rfl⟩ := Aux.canon_word8 hv3 hc
    obtain ⟨ws, h1⟩ := Aux.lookup_w8 hs hn
    by_cases hi : i < 0
    · exact Aux.op_exn hs hsub (by unfold do_app; dsimp only; rw [h1]; dsimp only; rw [if_pos hi]; rfl)
    · by_cases hle : Num (INT_ABS (I i)) ≥ ws.length
      · exact Aux.op_exn hs hsub
          (by unfold do_app; dsimp only; rw [h1]; dsimp only; rw [if_neg hi, if_pos hle]; rfl)
      · exact Aux.op_assign (sv := W8array (LUPDATE w (Num (INT_ABS (I i))) ws)) hs hn trivial hu
          (fun st' h => by
            unfold do_app; dsimp only; rw [h1]; dsimp only; rw [if_neg hi, if_neg hle, h])
  · -- CopyStrStr
    obtain ⟨v1, v2, v3, rfl, hv1, hv2, hv3⟩ := Aux.LR3 hl
    obtain ⟨s, rfl⟩ := Aux.canon_str hv1 hc
    obtain ⟨i, rfl⟩ := Aux.canon_int hv2 hc
    obtain ⟨j, rfl⟩ := Aux.canon_int hv3 hc
    cases h : copy_array (explode s, i) j none with
    | none => exact Aux.op_exn hs hsub (by unfold do_app; dsimp only; rw [h]; rfl)
    | some cs => exact Aux.op_val hs (type_v.strLit _ _ _ _) (by unfold do_app; dsimp only; rw [h])
  · -- CopyStrAw8
    obtain ⟨v1, v2, v3, v4, v5, rfl, hv1, hv2, hv3, hv4, hv5⟩ := Aux.LR5 hl
    obtain ⟨s, rfl⟩ := Aux.canon_str hv1 hc
    obtain ⟨i, rfl⟩ := Aux.canon_int hv2 hc
    obtain ⟨j, rfl⟩ := Aux.canon_int hv3 hc
    obtain ⟨n, rfl, hn⟩ := Aux.canon_w8array hv4 hc
    obtain ⟨k, rfl⟩ := Aux.canon_int hv5 hc
    obtain ⟨ws, h1⟩ := Aux.lookup_w8 hs hn
    cases h : copy_array (explode s, i) j (some (ws_to_chars ws, k)) with
    | none =>
      exact Aux.op_exn hs hsub (by unfold do_app; dsimp only; rw [h1]; dsimp only; rw [h]; rfl)
    | some cs =>
      exact Aux.op_assign (sv := W8array (chars_to_ws cs)) hs hn trivial hu
        (fun st' h' => by unfold do_app; dsimp only; rw [h1]; dsimp only; rw [h]; dsimp only; rw [h'])
  · -- CopyAw8Str
    obtain ⟨v1, v2, v3, rfl, hv1, hv2, hv3⟩ := Aux.LR3 hl
    obtain ⟨n, rfl, hn⟩ := Aux.canon_w8array hv1 hc
    obtain ⟨i, rfl⟩ := Aux.canon_int hv2 hc
    obtain ⟨j, rfl⟩ := Aux.canon_int hv3 hc
    obtain ⟨ws, h1⟩ := Aux.lookup_w8 hs hn
    cases h : copy_array (ws, i) j none with
    | none =>
      exact Aux.op_exn hs hsub (by unfold do_app; dsimp only; rw [h1]; dsimp only; rw [h]; rfl)
    | some cs =>
      exact Aux.op_val hs (type_v.strLit _ _ _ _)
        (by unfold do_app; dsimp only; rw [h1]; dsimp only; rw [h])
  · -- CopyAw8Aw8
    obtain ⟨v1, v2, v3, v4, v5, rfl, hv1, hv2, hv3, hv4, hv5⟩ := Aux.LR5 hl
    obtain ⟨n', rfl, hn'⟩ := Aux.canon_w8array hv1 hc
    obtain ⟨i, rfl⟩ := Aux.canon_int hv2 hc
    obtain ⟨j, rfl⟩ := Aux.canon_int hv3 hc
    obtain ⟨n, rfl, hn⟩ := Aux.canon_w8array hv4 hc
    obtain ⟨k, rfl⟩ := Aux.canon_int hv5 hc
    obtain ⟨ws, h1⟩ := Aux.lookup_w8 hs hn'
    obtain ⟨ds, h2⟩ := Aux.lookup_w8 hs hn
    cases h : copy_array (ws, i) j (some (ds, k)) with
    | none =>
      exact Aux.op_exn hs hsub
        (by unfold do_app; dsimp only; rw [h1, h2]; dsimp only; rw [h]; rfl)
    | some cs =>
      exact Aux.op_assign (sv := W8array cs) hs hn trivial hu
        (fun st' h' => by
          unfold do_app; dsimp only; rw [h1, h2]; dsimp only; rw [h]; dsimp only; rw [h'])
  · -- Implode
    obtain ⟨v, rfl, hv⟩ := Aux.LR1 hl
    obtain ⟨_, _, _, h3, _⟩ := Aux.list_canon hc hm _ _ v (Nat.le_refl _) hv
    obtain ⟨cs, h⟩ := h3 rfl
    exact Aux.op_val hs (type_v.strLit _ _ _ _) (by unfold do_app; dsimp only; rw [h])
  · -- Explode
    obtain ⟨v, rfl, hv⟩ := Aux.LR1 hl
    obtain ⟨s, rfl⟩ := Aux.canon_str hv hc
    refine Aux.op_val hs (Aux.type_v_list_to_v_intro hm (Aux.cf_app.2 (by simp)) ?_) rfl
    intro x hx
    obtain ⟨c, _, rfl⟩ := List.mem_map.1 hx
    exact type_v.char _ _ _ _
  · -- Strsub
    obtain ⟨v1, v2, rfl, hv1, hv2⟩ := Aux.LR2 hl
    obtain ⟨s, rfl⟩ := Aux.canon_str hv1 hc
    obtain ⟨i, rfl⟩ := Aux.canon_int hv2 hc
    by_cases hi : i < 0
    · exact Aux.op_exn hs hsub (by unfold do_app; dsimp only; rw [if_pos hi]; rfl)
    · by_cases hle : Num (INT_ABS (I i)) ≥ strlen s
      · exact Aux.op_exn hs hsub (by unfold do_app; dsimp only; rw [if_neg hi, if_pos hle]; rfl)
      · exact Aux.op_val hs (type_v.char _ _ _ _)
          (by unfold do_app; dsimp only; rw [if_neg hi, if_neg hle])
  · -- Strlen
    obtain ⟨v, rfl, hv⟩ := Aux.LR1 hl
    obtain ⟨s, rfl⟩ := Aux.canon_str hv hc
    exact Aux.op_val hs (type_v.intLit _ _ _ _) rfl
  · -- Strcat
    obtain ⟨v, rfl, hv⟩ := Aux.LR1 hl
    obtain ⟨vs, h1, _, _, h4⟩ := Aux.list_canon hc hm _ _ v (Nat.le_refl _) hv
    obtain ⟨s, h⟩ := h4 rfl
    exact Aux.op_val hs (type_v.strLit _ _ _ _)
      (by unfold do_app; dsimp only; rw [h1]; dsimp only; rw [h])
  · -- VfromList
    obtain ⟨v, rfl, hv⟩ := Aux.LR1 hl
    obtain ⟨vs, h1, h2, _, _⟩ := Aux.list_canon hc hm t1 _ v (Nat.le_refl _) hv
    exact Aux.op_val hs (type_v.vector _ _ _ vs t1 (hcf1 hcf) h2)
      (by unfold do_app; dsimp only; rw [h1])
  · -- Vsub
    obtain ⟨v1, v2, rfl, hv1, hv2⟩ := Aux.LR2 hl
    obtain ⟨vs, rfl, _, hvs⟩ := Aux.canon_vector hv1 hc
    obtain ⟨i, rfl⟩ := Aux.canon_int hv2 hc
    by_cases hi : i < 0
    · exact Aux.op_exn hs hsub (by unfold do_app; dsimp only; rw [if_pos hi]; rfl)
    · by_cases hle : Num (INT_ABS (I i)) ≥ vs.length
      · exact Aux.op_exn hs hsub (by unfold do_app; dsimp only; rw [if_neg hi, if_pos hle]; rfl)
      · exact Aux.op_val hs (hvs _ (Aux.EL_mem (Nat.lt_of_not_le hle)))
          (by unfold do_app; dsimp only; rw [if_neg hi, if_neg hle])
  · -- Vlength
    obtain ⟨v, rfl, hv⟩ := Aux.LR1 hl
    obtain ⟨vs, rfl, _, hvs⟩ := Aux.canon_vector hv hc
    exact Aux.op_val hs (type_v.intLit _ _ _ _) rfl
  · -- Aalloc
    obtain ⟨v1, v2, rfl, hv1, hv2⟩ := Aux.LR2 hl
    obtain ⟨i, rfl⟩ := Aux.canon_int hv1 hc
    by_cases hi : i < 0
    · exact Aux.op_exn hs hsub (by unfold do_app; dsimp only; rw [if_pos hi]; rfl)
    · refine Aux.op_alloc (sv := Varray (List.replicate (Num (INT_ABS (I i))) v2))
        (st := Varray_t t2) hc hs ?_
        (fun st' n h => by unfold do_app; dsimp only; rw [if_neg hi, h])
        (fun S' n h => type_v.varray _ _ _ _ _ (hcf1 hcf) h)
      refine EVERY_iff_forall.2 fun x hx => ?_
      rw [(List.mem_replicate.1 hx).2]
      exact hv2
  · -- AallocEmpty
    obtain ⟨v1, rfl, hv1⟩ := Aux.LR1 hl
    obtain ⟨vs, rfl, hvs⟩ := Aux.canon_tup hv1 hc
    cases Aux.LR0 hvs
    exact Aux.op_alloc (sv := Varray []) (st := Varray_t t2) hc hs trivial
        (fun st' n h => by unfold do_app; dsimp only; rw [h])
        (fun S' n h => type_v.varray _ _ _ _ _ (hcf1 hcf) h)
  · -- Asub
    obtain ⟨v1, v2, rfl, hv1, hv2⟩ := Aux.LR2 hl
    obtain ⟨n, rfl, _, hn⟩ := Aux.canon_array hv1 hc
    obtain ⟨i, rfl⟩ := Aux.canon_int hv2 hc
    obtain ⟨vs, h1, hvs⟩ := Aux.lookup_arr hs hn
    by_cases hi : i < 0
    · exact Aux.op_exn hs hsub (by unfold do_app; dsimp only; rw [h1]; dsimp only; rw [if_pos hi]; rfl)
    · by_cases hle : Num (INT_ABS (I i)) ≥ vs.length
      · exact Aux.op_exn hs hsub
          (by unfold do_app; dsimp only; rw [h1]; dsimp only; rw [if_neg hi, if_pos hle]; rfl)
      · exact Aux.op_val hs (hvs _ (Aux.EL_mem (Nat.lt_of_not_le hle)))
          (by unfold do_app; dsimp only; rw [h1]; dsimp only; rw [if_neg hi, if_neg hle])
  · -- Alength
    obtain ⟨v, rfl, hv⟩ := Aux.LR1 hl
    obtain ⟨n, rfl, _, hn⟩ := Aux.canon_array hv hc
    obtain ⟨vs, h1, hvs⟩ := Aux.lookup_arr hs hn
    exact Aux.op_val hs (type_v.intLit _ _ _ _) (by unfold do_app; dsimp only; rw [h1])
  · -- Aupdate
    obtain ⟨v1, v2, v3, rfl, hv1, hv2, hv3⟩ := Aux.LR3 hl
    obtain ⟨n, rfl, _, hn⟩ := Aux.canon_array hv1 hc
    obtain ⟨i, rfl⟩ := Aux.canon_int hv2 hc
    obtain ⟨vs, h1, hvs⟩ := Aux.lookup_arr hs hn
    by_cases hi : i < 0
    · exact Aux.op_exn hs hsub (by unfold do_app; dsimp only; rw [h1]; dsimp only; rw [if_pos hi]; rfl)
    · by_cases hle : Num (INT_ABS (I i)) ≥ vs.length
      · exact Aux.op_exn hs hsub
          (by unfold do_app; dsimp only; rw [h1]; dsimp only; rw [if_neg hi, if_pos hle]; rfl)
      · refine Aux.op_assign (sv := Varray (LUPDATE v3 (Num (INT_ABS (I i))) vs)) hs hn ?_ hu
          (fun st' h => by
            unfold do_app; dsimp only; rw [h1]; dsimp only; rw [if_neg hi, if_neg hle, h])
        refine EVERY_iff_forall.2 fun x hx => ?_
        rw [Aux.LUPDATE_eq_set] at hx
        rcases List.mem_or_eq_of_mem_set hx with hx | rfl
        · exact hvs x hx
        · exact hv3
  · -- ConfigGC
    obtain ⟨v1, v2, rfl, hv1, hv2⟩ := Aux.LR2 hl
    obtain ⟨i, rfl⟩ := Aux.canon_int hv1 hc
    obtain ⟨j, rfl⟩ := Aux.canon_int hv2 hc
    exact Aux.op_val hs hu rfl
  · -- FFI
    obtain ⟨v1, v2, rfl, hv1, hv2⟩ := Aux.LR2 hl
    obtain ⟨s, rfl⟩ := Aux.canon_str hv1 hc
    obtain ⟨l, rfl, hn⟩ := Aux.canon_w8array hv2 hc
    obtain ⟨ws, h1⟩ := Aux.lookup_w8 hs hn
    cases h : call_FFI ffi (ExtCall n) ((explode s).map (n2w ∘ ORD)) ws with
    | FFI_return ffi' ws' =>
      exact Aux.op_assign (sv := W8array ws') (ffi' := ffi') hs hn trivial hu
        (fun st' h' => by unfold do_app; dsimp only; rw [h1]; dsimp only; rw [h]; dsimp only; rw [h'])
    | FFI_final outcome =>
      exact ⟨S, store, ffi, Rerr (Rabort (Rffi_error outcome)), store_type_extension_refl _, hs,
        by unfold do_app; dsimp only; rw [h1]; dsimp only; rw [h], trivial⟩
  · -- ListAppend
    obtain ⟨v1, v2, rfl, hv1, hv2⟩ := Aux.LR2 hl
    obtain ⟨xs, h1, _⟩ := Aux.list_canon hc hm t1 _ v1 (Nat.le_refl _) hv1
    obtain ⟨ys, h2, _⟩ := Aux.list_canon hc hm t1 _ v2 (Nat.le_refl _) hv2
    exact Aux.op_val hs (type_v_list_to_v_APPEND _ _ xs ys t1
      ⟨hm, type_v_list_to_v _ _ _ _ _ _ ⟨hv1, h1⟩, type_v_list_to_v _ _ _ _ _ _ ⟨hv2, h2⟩⟩)
      (by unfold do_app; dsimp only; rw [h1, h2])

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
        type_v tvs ctMap tenvS v (Tapp ts' tn) := by
  rintro envC cn vs tvs ts m S ts' tn tenvC tvs' E l ⟨hc, _, h0, he, hl, hr, hlk⟩
  obtain ⟨⟨k, s⟩, h1, h2, rfl⟩ := nsAll2_nsLookup2 _ _ _ _ _ ⟨hlk, hc⟩
  rw [Aux.num_tvs_bt, h0] at he
  refine ⟨Conv (some s) vs.reverse, by simp [build_conv, h1], ?_⟩
  refine Aux.type_v_conv_intro he hl ?_ h2
  have := Aux.LIST_REL_reverse hr
  rw [List.reverse_reverse] at this
  exact this

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
      stamp1 = stamp2 := fun _ _ h => h.1

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
  have key :
      (∀ (tvs : Nat) (tenv : type_env) (p : pat) (t : typ) (nb : List (varN × typ)),
        type_p tvs tenv p t nb →
        ∀ (cenv : env_ctor) (st : List (store_v value)) (v : value) (bs : List (varN × value))
          (m : ctMap_ty) (tb : List (varN × typ)) (S : tenv_store),
          ctMap_ok m → nsAll2 (type_ctor m) cenv tenv.c → type_v tvs m S v t → type_s m st S →
          LIST_REL (fun ((x, v) : varN × value) ((x', t) : varN × typ) =>
            x = x' ∧ type_v tvs m S v t) bs tb →
          pmatch cenv st p v bs = No_match ∨
          (∃ bs', pmatch cenv st p v bs = Match bs' ∧
            LIST_REL (fun ((x, v) : varN × value) ((x', t) : varN × typ) =>
              x = x' ∧ type_v tvs m S v t) bs' (nb ++ tb))) ∧
      (∀ (tvs : Nat) (tenv : type_env) (ps : List pat) (ts : List typ) (nb : List (varN × typ)),
        type_ps tvs tenv ps ts nb →
        ∀ (cenv : env_ctor) (st : List (store_v value)) (vs : List value)
          (bs : List (varN × value))
          (m : ctMap_ty) (tb : List (varN × typ)) (S : tenv_store),
          ctMap_ok m → nsAll2 (type_ctor m) cenv tenv.c → LIST_REL (type_v tvs m S) vs ts →
          type_s m st S →
          LIST_REL (fun ((x, v) : varN × value) ((x', t) : varN × typ) =>
            x = x' ∧ type_v tvs m S v t) bs tb →
          pmatch_list cenv st ps vs bs = No_match ∨
          (∃ bs', pmatch_list cenv st ps vs bs = Match bs' ∧
            LIST_REL (fun ((x, v) : varN × value) ((x', t) : varN × typ) =>
              x = x' ∧ type_v tvs m S v t) bs' (nb ++ tb))) := by
    apply Aux.type_p_ind
    case any =>
      intro tvs tenv t _ cenv st v bs m tb S hm hc hv hs hb
      exact Or.inr ⟨bs, by simp [pmatch], hb⟩
    case var =>
      intro tvs tenv n t _ cenv st v bs m tb S hm hc hv hs hb
      exact Or.inr ⟨(n, v) :: bs, by simp [pmatch], ⟨rfl, hv⟩, hb⟩
    case intLit =>
      intro tvs tenv n cenv st v bs m tb S hm hc hv hs hb
      obtain ⟨i, rfl⟩ := Aux.canon_int hv hm
      by_cases h : n = i
      · exact Or.inr ⟨bs, by simp [pmatch, h], hb⟩
      · exact Or.inl (by simp [pmatch, h, lit_same_type])
    case char =>
      intro tvs tenv n cenv st v bs m tb S hm hc hv hs hb
      obtain ⟨i, rfl⟩ := Aux.canon_char hv hm
      by_cases h : n = i
      · exact Or.inr ⟨bs, by simp [pmatch, h], hb⟩
      · exact Or.inl (by simp [pmatch, h, lit_same_type])
    case strLit =>
      intro tvs tenv n cenv st v bs m tb S hm hc hv hs hb
      obtain ⟨i, rfl⟩ := Aux.canon_str hv hm
      by_cases h : n = i
      · exact Or.inr ⟨bs, by simp [pmatch, h], hb⟩
      · exact Or.inl (by simp [pmatch, h, lit_same_type])
    case word8 =>
      intro tvs tenv n cenv st v bs m tb S hm hc hv hs hb
      obtain ⟨i, rfl⟩ := Aux.canon_word8 hv hm
      by_cases h : n = i
      · exact Or.inr ⟨bs, by simp [pmatch, h], hb⟩
      · exact Or.inl (by simp [pmatch, h, lit_same_type])
    case word64 =>
      intro tvs tenv n cenv st v bs m tb S hm hc hv hs hb
      obtain ⟨i, rfl⟩ := Aux.canon_word64 hv hm
      by_cases h : n = i
      · exact Or.inr ⟨bs, by simp [pmatch, h], hb⟩
      · exact Or.inl (by simp [pmatch, h, lit_same_type])
    case con =>
      intro tvs tenv cn ps ts tvs' tn ts' b h1 h2 hps ih h3 cenv st v bs m tb S hm hc hv hs hb
      obtain ⟨⟨k, s⟩, c1, c2, rfl⟩ := nsAll2_nsLookup2 _ _ _ _ _ ⟨h3, hc⟩
      obtain ⟨s', vs, tvs'', ts0, rfl, d0, d1, d2, d3, d4⟩ := Aux.type_v_con hv hm c2
      have hlen : ps.length = ts.length := by
        have := type_ps_length _ _ _ _ _ hps
        simpa using this
      rw [pmatch, c1]
      simp only
      rw [if_pos ⟨d0, hlen⟩]
      by_cases hss : same_ctor s s'
      · rw [if_pos hss]
        cases (show s = s' from hss)
        rw [c2] at d4; cases d4
        have hl2 := Aux.LIST_REL_length d3
        rw [List.length_map] at hl2
        rw [if_pos hl2]
        exact ih cenv st vs bs m tb S hm hc d3 hs hb
      · rw [if_neg hss]
        exact Or.inl rfl
    case tup =>
      intro tvs tenv ps ts b hps ih cenv st v bs m tb S hm hc hv hs hb
      obtain ⟨vs, rfl, hl⟩ := Aux.canon_tup hv hm
      have hlen : ps.length = vs.length :=
        (type_ps_length _ _ _ _ _ hps).trans (Aux.LIST_REL_length hl).symm
      rw [pmatch, if_pos hlen]
      exact ih cenv st vs bs m tb S hm hc hl hs hb
    case ref =>
      intro tvs tenv p t b _ ih cenv st v bs m tb S hm hc hv hs hb
      obtain ⟨n, rfl, _, hl⟩ := Aux.canon_ref hv hm
      obtain ⟨sv, hsv1, hsv2⟩ := Aux.type_s_lookup hs hl
      cases sv with
      | Refv v2 =>
        rw [pmatch, hsv1]
        exact ih cenv st v2 bs m tb S hm hc (type_v_weakening _ _ _ _ _ hsv2 _ _ _
          ⟨Or.inl rfl, weakCT_refl _, weakS_refl _⟩) hs hb
      | _ => exact hsv2.elim
    case pas =>
      intro tvs tenv p x t b _ ih cenv st v bs m tb S hm hc hv hs hb
      rw [pmatch, List.append_assoc]
      exact ih cenv st v ((x, v) :: bs) m ((x, t) :: tb) S hm hc hv hs ⟨⟨rfl, hv⟩, hb⟩
    case tannot =>
      intro tvs tenv p t b _ _ _ ih cenv st v bs m tb S hm hc hv hs hb
      rw [pmatch]
      exact ih cenv st v bs m tb S hm hc hv hs hb
    case nil =>
      intro tvs tenv cenv st vs bs m tb S hm hc hv hs hb
      cases Aux.LR0 hv
      exact Or.inr ⟨bs, by simp [pmatch_list], hb⟩
    case cons =>
      intro tvs tenv p ps t ts b b' _ _ ih1 ih2 cenv st vs bs m tb S hm hc hv hs hb
      obtain ⟨v, vs, rfl, hv1, hv2⟩ := Aux.LRc hv
      rw [pmatch_list]
      rcases ih1 cenv st v bs m tb S hm hc hv1 hs hb with h | ⟨bs', h, hb'⟩
      · left
        rw [h]
        rcases ih2 cenv st vs bs m tb S hm hc hv2 hs hb with h' | ⟨bs'', h', _⟩ <;> rw [h']
      · rw [h, List.append_assoc]
        exact ih2 cenv st vs bs' m (b ++ tb) S hm hc hv2 hs hb'
  refine ⟨?_, ?_⟩
  · rintro cenv st p v bs tenv m tb t nb S tvs ⟨hm, hc, hv, hp, hs, hb⟩
    exact key.1 _ _ _ _ _ hp cenv st v bs m tb S hm hc hv hs hb
  · rintro cenv st p v bs tenv m tb nb t S tvs ⟨hm, hc, hv, hp, hs, hb⟩
    exact key.2 _ _ _ _ _ hp cenv st v bs m tb S hm hc hv hs hb

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
        type_v tvs ctMap tenvS v (deBruijn_subst 0 targs t) := by
  rintro n tvs E targs t m S env tenv ⟨hl, hm, hE, h0, he, henv⟩
  have hadd : nsLookup (add_tenvE E tenv.v) n = some (targs.length, t) := by
    unfold lookup_var at hl
    cases n with
    | Long mn id => exact nsLookup_add_tenvE3 _ _ _ _ _ _ hl
    | Short x =>
      have hlE : ∀ E, lookup_varE (Short x) E = tveLookup x 0 E := fun _ => rfl
      rw [hlE, Aux.tveLookup_bt] at hl
      cases hx : tveLookup x (0 + tvs) E with
      | some p =>
        rw [hx] at hl
        cases hl
        exact nsLookup_add_tenvE1 _ _ _ _ _ _ ⟨tveLookup_freevars _ _ _ _ _ ⟨hE, h0, hx⟩, hx⟩
      | none =>
        rw [hx] at hl
        exact nsLookup_add_tenvE2 _ _ _ _ _ _ ⟨hx, hl⟩
  obtain ⟨v, hv, ht⟩ := nsAll2_nsLookup2 _ _ _ _ _ ⟨hadd, henv.2⟩
  exact ⟨v, hv, type_subst_thm targs tvs _ _ _ _ _ ht
    ⟨rfl, hm, he, type_v_freevars _ _ _ _ _ ht⟩⟩

/- HOL4:
Theorem EVERY_REPLICATE:
  EVERY (\x. type_v tvs ctMap tenv x t') vs =
  EVERY (\x. type_v tvs ctMap tenv (FST x) (SND x)) (ZIP (vs, REPLICATE (LENGTH vs) t')) -/
theorem EVERY_REPLICATE (tvs : Nat) (ctMap : ctMap_ty) (tenv : tenv_store) (t' : typ)
    (vs : List value) :
    EVERY (fun x => type_v tvs ctMap tenv x t') vs ↔
    EVERY (fun x => type_v tvs ctMap tenv x.1 x.2)
      (vs.zip (List.replicate vs.length t')) := by
  induction vs with
  | nil => simp [EVERY]
  | cons v vs ih => simp [EVERY, List.replicate_succ, ih]

/- HOL4:
Theorem EVERY_LIST_REL:
  EVERY (\ v. type_v n ctMap tenvS v t) vs =
  LIST_REL (type_v n ctMap tenvS) vs (REPLICATE (LENGTH vs) t)
(the second theorem of this name in the theory) -/
theorem EVERY_LIST_REL_2 (n : Nat) (ctMap : ctMap_ty) (tenvS : tenv_store) (t : typ)
    (vs : List value) :
    EVERY (fun v => type_v n ctMap tenvS v t) vs ↔
    LIST_REL (type_v n ctMap tenvS) vs (List.replicate vs.length t) := by
  rw [EVERY_iff_forall, Aux.LR_replicate]

section exp_sound

variable {ffi : Type}

def Aux.ehyp (m : ctMap_ty) (s : state ffi) (env : sem_env value) (tenv : type_env)
    (E : tenv_val_exp) (S : tenv_store) : Prop :=
  tenv_ok tenv ∧ tenv_val_exp_ok E ∧ good_ctMap m ∧ num_tvs E = 0 ∧
    type_all_env m S env { tenv with v := add_tenvE E tenv.v } ∧ type_s m s.refs S

def Aux.epost (m : ctMap_ty) (S : tenv_store) (s s' : state ffi) (res : tenv_store → Prop) :
    Prop :=
  ∃ S' : tenv_store, type_s m s'.refs S' ∧ store_type_extension S S' ∧
    s'.next_type_stamp = s.next_type_stamp ∧ s'.next_exn_stamp = s.next_exn_stamp ∧ res S'

def Aux.eerr (m : ctMap_ty) (e : error_result value) (S : tenv_store) : Prop :=
  match e with
  | Rraise v => type_v 0 m S v Texn
  | Rabort Rtimeout_error => True
  | Rabort (Rffi_error _) => True
  | Rabort Rtype_error => False

def Aux.eres (m : ctMap_ty) (tvs : Nat) (ts : List typ) (r : result (List value) value)
    (S : tenv_store) : Prop :=
  match r with
  | Rval vs => LIST_REL (type_v tvs m S) vs ts
  | Rerr e => Aux.eerr m e S

def Aux.mres (m : ctMap_ty) (tvs : Nat) (t : typ) (r : result (List value) value)
    (S : tenv_store) : Prop :=
  match r with
  | Rval vs => type_v tvs m S (HD vs) t
  | Rerr e => Aux.eerr m e S

theorem Aux.ehyp_step {m : ctMap_ty} {s s1 : state ffi} {env : sem_env value} {tenv : type_env}
    {E : tenv_val_exp} {S S1 : tenv_store} (h : Aux.ehyp m s env tenv E S)
    (hs : type_s m s1.refs S1) (hx : store_type_extension S S1) :
    Aux.ehyp m s1 env tenv E S1 :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, type_all_env_weakening _ _ _ _ _ _
    ⟨weakCT_refl _, store_type_extension_weakS _ _ hx, h.2.2.2.2.1⟩, hs⟩

theorem Aux.epost_trans {m : ctMap_ty} {s s1 s2 : state ffi} {S S1 : tenv_store}
    {res : tenv_store → Prop} (hx : store_type_extension S S1)
    (h1 : s1.next_type_stamp = s.next_type_stamp) (h2 : s1.next_exn_stamp = s.next_exn_stamp)
    (h : Aux.epost m S1 s1 s2 res) : Aux.epost m S s s2 res := by
  obtain ⟨S2, a1, a2, a3, a4, a5⟩ := h
  exact ⟨S2, a1, store_type_extension_trans _ _ _ ⟨hx, a2⟩, a3.trans h1, a4.trans h2, a5⟩

theorem Aux.epost_refl {m : ctMap_ty} {s : state ffi} {S : tenv_store}
    {res : tenv_store → Prop} (hs : type_s m s.refs S) (h : res S) : Aux.epost m S s s res :=
  ⟨S, hs, store_type_extension_refl _, rfl, rfl, h⟩

theorem Aux.es1 {tenv : type_env} {E : tenv_val_exp} {e : exp} {ts : List typ} :
    type_es tenv E [e] ts ↔ ∃ t, ts = [t] ∧ type_e tenv E e t := by
  constructor
  · intro h
    obtain ⟨t, ht, hr⟩ : ∃ t, ts = [t] ∧ type_e tenv E e t := by
      cases h with
      | cons _ _ _ t ts h1 h2 => cases h2; exact ⟨t, rfl, h1⟩
    exact ⟨t, ht, hr⟩
  · rintro ⟨t, rfl, h⟩
    exact type_es.cons _ _ _ _ _ _ h (type_es.nil _ _)

theorem Aux.es_reverse {tenv : type_env} {E : tenv_val_exp} {es : List exp} {ts : List typ}
    (h : type_es tenv E es ts) : type_es tenv E es.reverse ts.reverse :=
  (type_es_list_rel _ _ _ _).2 (Aux.LIST_REL_reverse ((type_es_list_rel _ _ _ _).1 h))

theorem Aux.can_pmatch {m : ctMap_ty} {cenv : env_ctor} {tenv : type_env}
    {st : List (store_v value)} {S : tenv_store} {tvs : Nat} {v : value} {t : typ}
    {ps : List pat} (hm : ctMap_ok m) (hc : nsAll2 (type_ctor m) cenv tenv.c)
    (hs : type_s m st S) (hv : type_v tvs m S v t)
    (hp : ∀ p, p ∈ ps → ∃ b, type_p tvs tenv p t b) : can_pmatch_all cenv st ps v := by
  rw [can_pmatch_all_EVERY, EVERY_iff_forall]
  intro p hmem
  obtain ⟨b, hb⟩ := hp p hmem
  rcases pat_type_sound.1 cenv st p v [] tenv m [] t b S tvs ⟨hm, hc, hv, hb, hs, trivial⟩ with
    h | ⟨b', h, _⟩ <;> rw [h] <;> simp

theorem Aux.rec_env_ok {m : ctMap_ty} {S : tenv_store} {tenv : type_env} {E : tenv_val_exp}
    {env : sem_env value} {funs : List (varN × varN × exp)} {b : List (varN × typ)} {tvs : Nat}
    (hok : tenv_ok tenv)
    (henv : type_all_env m S env { tenv with v := add_tenvE E tenv.v })
    (hE : tenv_val_exp_ok E) (h0 : num_tvs E = 0)
    (hf : type_funs tenv (bind_var_list 0 b (bind_tvar tvs E)) funs b) :
    nsAll2 (fun _ v (p : Nat × typ) => type_v p.1 m S v p.2) (build_rec_env funs env env.v)
      (add_tenvE (bind_var_list tvs b E) tenv.v) := by
  have hd : ALL_DISTINCT (funs.map Prod.fst) := type_funs_distinct _ _ _ _ hf
  have hrec := type_recfun_env funs m S tvs tenv E env b ⟨hok, henv, hE, h0, hf, hd⟩
  rw [build_rec_env_merge funs () env env.v, nsAppend_to_nsBindList, add_tenvE_bvl]
  exact nsAll2_nsBindList (fun _ v (p : Nat × typ) => type_v p.1 m S v p.2) _ _ _ _
    ⟨hrec, henv.2⟩

theorem Aux.getOpClass_FunApp {o : op} (h : getOpClass o = FunApp) : o = Opapp := by
  cases o <;> simp [getOpClass] at h ⊢
  split at h <;> cases h

theorem Aux.getOpClass_Force {o : op} (h : getOpClass o = Force) : ∃ th, o = ThunkOp th := by
  cases o <;> simp [getOpClass] at h ⊢

theorem Aux.getOpClass_Eval {o : op} (h : getOpClass o = EvalOp) : o = Eval := by
  cases o <;> simp [getOpClass] at h ⊢
  split at h <;> cases h

theorem Aux.do_log_bool (l : lop) (b : Bool) (e : exp) :
    do_log l (Boolv b) e = some (Exp e) ∨ do_log l (Boolv b) e = some (Val (Boolv b)) := by
  cases l <;> cases b <;> simp [do_log, Boolv_11]

theorem Aux.exp_sound (m : ctMap_ty) :
    (∀ (s : state ffi) (env : sem_env value) (es : List exp),
      ∀ (r : result (List value) value) (s' : state ffi) (tenv : type_env) (E : tenv_val_exp)
        (ts : List typ) (tvs : Nat) (S : tenv_store),
        evaluate s env es = (s', r) → Aux.ehyp m s env tenv E S →
        (tvs ≠ 0 → EVERY is_value es) → type_es tenv (bind_tvar tvs E) es ts →
        Aux.epost m S s s' (Aux.eres m tvs ts r)) ∧
    (∀ (s : state ffi) (env : sem_env value) (v : value) (pes : List (pat × exp))
        (err_v : value),
      ∀ (r : result (List value) value) (s' : state ffi) (tenv : type_env) (E : tenv_val_exp)
        (t1 t2 : typ) (tvs : Nat) (S : tenv_store),
        evaluate_match s env v pes err_v = (s', r) → Aux.ehyp m s env tenv E S →
        type_v tvs m S v t1 → type_v 0 m S err_v Texn → type_pes tvs tvs tenv E pes t1 t2 →
        Aux.epost m S s s' (Aux.mres m tvs t2 r)) ∧
    (∀ (s : state ffi) (env : sem_env value) (ds : List dec), True) := by
  have h0 : ∀ {tvs : Nat} {e : exp}, ¬ is_value e → (tvs ≠ 0 → EVERY is_value [e]) → tvs = 0 := by
    intro tvs e he h
    apply Classical.byContradiction
    intro hn
    exact he (h hn).1
  -- the result of `evaluate_match` as a result of `evaluate`
  have hM : ∀ {s s' : state ffi} {env : sem_env value} {v : value} {pes : List (pat × exp)}
      {err_v : value} {r : result (List value) value} {S0 : tenv_store} {s0 : state ffi}
      {tvs : Nat} {t : typ}, evaluate_match s env v pes err_v = (s', r) →
      Aux.epost m S0 s0 s' (Aux.mres m tvs t r) → Aux.epost m S0 s0 s' (Aux.eres m tvs [t] r) := by
    intro s s' env v pes err_v r S0 s0 tvs t he h
    obtain ⟨S', a1, a2, a3, a4, a5⟩ := h
    refine ⟨S', a1, a2, a3, a4, ?_⟩
    cases r with
    | Rerr e => exact a5
    | Rval vs =>
      obtain ⟨x, rfl⟩ := List.length_eq_one_iff.1 (evaluate_length.2.1 _ _ _ _ _ _ _ he)
      exact ⟨a5, trivial⟩
  apply Aux.full_evaluate_ind
  case nil =>
    intro s env r s' tenv E ts tvs S he hh _ ht
    rw [evaluate] at he
    cases he
    cases ht
    exact Aux.epost_refl hh.2.2.2.2.2 trivial
  case cons2 =>
    intro s env e1 e2 es ih1 ih2 r s' tenv E ts tvs S he hh hv ht
    cases ht with
    | cons _ _ _ t ts h1 h2 =>
      rw [Aux.evaluate_cons2] at he
      rcases hev : evaluate s env [e1] with ⟨s1, v1 | e⟩
      · rw [hev] at he
        dsimp only at he
        obtain ⟨S1, a1, a2, a3, a4, a5⟩ := ih1 _ _ tenv E [t] tvs S hev hh
          (fun h => ⟨(hv h).1, trivial⟩) (Aux.es1.2 ⟨t, rfl, h1⟩)
        obtain ⟨x, rfl, hx⟩ := Aux.LR1 a5
        have hh1 := Aux.ehyp_step hh a1 a2
        refine Aux.epost_trans a2 a3 a4 ?_
        rcases hev2 : evaluate s1 env (e2 :: es) with ⟨s2, vs | e⟩
        · rw [hev2] at he
          cases he
          obtain ⟨S2, b1, b2, b3, b4, b5⟩ := ih2 _ _ hev _ _ tenv E ts tvs S1 hev2 hh1
            (fun h => (hv h).2) h2
          exact ⟨S2, b1, b2, b3, b4, type_v_weakening _ _ _ _ _ hx _ _ _
            ⟨Or.inr rfl, weakCT_refl _, store_type_extension_weakS _ _ b2⟩, b5⟩
        · rw [hev2] at he
          cases he
          exact ih2 _ _ hev _ _ tenv E ts tvs S1 hev2 hh1 (fun h => (hv h).2) h2
      · rw [hev] at he
        cases he
        exact ih1 _ _ tenv E [t] tvs S hev hh
          (fun h => ⟨(hv h).1, trivial⟩) (Aux.es1.2 ⟨t, rfl, h1⟩)
  case lit =>
    intro s env l r s' tenv E ts tvs S he hh _ ht
    rw [evaluate] at he
    cases he
    replace ht := Aux.es1.1 ht
    obtain ⟨t, rfl, ht⟩ := ht
    refine Aux.epost_refl hh.2.2.2.2.2 ⟨?_, trivial⟩
    cases ht with
    | intLit => exact type_v.intLit _ _ _ _
    | char => exact type_v.char _ _ _ _
    | strLit => exact type_v.strLit _ _ _ _
    | word8 => exact type_v.word8 _ _ _ _
    | word64 => exact type_v.word64 _ _ _ _
    | float64 => exact type_v.float64 _ _ _ _
  case raise =>
    intro s env e ih r s' tenv E ts tvs S he hh hv ht
    cases h0 (by simp [is_value]) hv
    replace ht := Aux.es1.1 ht
    obtain ⟨t, rfl, ht⟩ := ht
    cases ht with
    | raise _ _ _ h1 h2 =>
      rw [evaluate] at he
      rcases hev : evaluate s env [e] with ⟨s1, v | e'⟩
      · rw [hev] at he
        cases he
        obtain ⟨S1, a1, a2, a3, a4, a5⟩ := ih _ _ tenv E [Texn] 0 S hev hh
          (fun h => absurd rfl h) (Aux.es1.2 ⟨_, rfl, h2⟩)
        obtain ⟨x, rfl, hx⟩ := Aux.LR1 a5
        exact ⟨S1, a1, a2, a3, a4, hx⟩
      · rw [hev] at he
        cases he
        exact ih _ _ tenv E [Texn] 0 S hev hh
          (fun h => absurd rfl h) (Aux.es1.2 ⟨_, rfl, h2⟩)
  case handle =>
    intro s env e pes ih1 ih2 r s' tenv E ts tvs S he hh hv ht
    cases h0 (by simp [is_value]) hv
    replace ht := Aux.es1.1 ht
    obtain ⟨t, rfl, ht⟩ := ht
    rw [bind_tvar0] at ht
    obtain ⟨h1, _, h3⟩ := type_e_Handle_inv_aux _ _ _ _ _ ht
    rw [hh.2.2.2.1] at h3
    rw [Aux.evaluate_Handle] at he
    have hsub := fun r s' hev => ih1 r s' tenv E [t] 0 S hev hh
      (fun h => absurd rfl h) (Aux.es1.2 ⟨_, rfl, by rw [bind_tvar0]; exact h1⟩)
    rcases hev : evaluate s env [e] with ⟨s1, v | v | a⟩
    · rw [hev] at he
      cases he
      exact hsub _ _ hev
    · rw [hev] at he
      dsimp only at he
      obtain ⟨S1, a1, a2, a3, a4, a5⟩ := hsub _ _ hev
      have a5 : type_v 0 m S1 v Texn := a5
      have hh1 := Aux.ehyp_step hh a1 a2
      have hcan : can_pmatch_all env.c s1.refs (pes.map Prod.fst) v := by
        refine Aux.can_pmatch (tenv := tenv) hh.2.2.1.1 hh1.2.2.2.2.1.1 a1 a5 ?_
        intro p hp
        obtain ⟨⟨p', e'⟩, hpe, rfl⟩ := List.mem_map.1 hp
        obtain ⟨b, _, hb, _⟩ := h3 p' e' hpe
        exact ⟨b, hb⟩
      rw [if_pos hcan] at he
      exact Aux.epost_trans a2 a3 a4 (hM he
        (ih2 _ _ hev hcan _ _ tenv E Texn t 0 S1 he hh1 a5 a5 h3))
    · rw [hev] at he
      cases he
      exact hsub _ _ hev
  case con =>
    intro s env cn es ih r s' tenv E ts tvs S he hh hv ht
    replace ht := Aux.es1.1 ht
    obtain ⟨t, rfl, ht⟩ := ht
    have hvr : tvs ≠ 0 → EVERY is_value es.reverse := by
      intro h
      have := (hv h).1
      rw [is_value, EVERY_iff_forall] at this
      exact EVERY_iff_forall.2 fun x hx => this x (List.mem_reverse.1 hx)
    rw [evaluate] at he
    cases ht with
    | con _ cn es tvs' tn ts' ts h1 h2 h3 h4 =>
      have hlen := type_es_length _ _ _ _ h3
      rw [List.length_map] at hlen
      obtain ⟨⟨k, st⟩, b1, b2, rfl⟩ := nsAll2_nsLookup2 _ _ _ _ _ ⟨h4, hh.2.2.2.2.1.1⟩
      have hck : do_con_check env.c (some cn) es.length := by
        simp only [do_con_check]
        rw [b1]; exact hlen
      rw [if_pos hck] at he
      have hsub := fun r s' hev => ih hck r s' tenv E _ tvs S hev hh hvr (Aux.es_reverse h3)
      rcases hev : evaluate s env es.reverse with ⟨s1, vs | e⟩
      · rw [hev] at he
        dsimp only at he
        obtain ⟨S1, a1, a2, a3, a4, a5⟩ := hsub _ _ hev
        obtain ⟨v, hb, hvt⟩ := build_conv_type_sound env.c cn vs tvs ts m S1 ts' tn tenv.c tvs' E
          es.length ⟨hh.2.2.2.2.1.1, hck, hh.2.2.2.1, h1, h2, a5, h4⟩
        rw [hb] at he
        cases he
        exact ⟨S1, a1, a2, a3, a4, hvt, trivial⟩
      · rw [hev] at he
        cases he
        exact hsub _ _ hev
    | tup _ es ts h1 =>
      rw [if_pos (show do_con_check env.c none es.length from trivial)] at he
      have hsub := fun r s' hev => ih trivial r s' tenv E _ tvs S hev hh hvr (Aux.es_reverse h1)
      rcases hev : evaluate s env es.reverse with ⟨s1, vs | e⟩
      · rw [hev] at he
        cases he
        obtain ⟨S1, a1, a2, a3, a4, a5⟩ := hsub _ _ hev
        have a5 := Aux.LIST_REL_reverse a5
        rw [List.reverse_reverse] at a5
        exact ⟨S1, a1, a2, a3, a4, type_v_tup_aux _ _ _ _ _ a5, trivial⟩
      · rw [hev] at he
        cases he
        exact hsub _ _ hev
  case var =>
    intro s env n r s' tenv E ts tvs S he hh _ ht
    replace ht := Aux.es1.1 ht
    obtain ⟨t, rfl, ht⟩ := ht
    cases ht with
    | var _ n t targs tvs' h1 h2 h3 =>
      subst h1
      rw [Aux.num_tvs_bt, hh.2.2.2.1] at h2
      obtain ⟨v, b1, b2⟩ := lookup_var_sound n tvs E targs t m S env tenv
        ⟨h3, hh.2.2.1.1, hh.2.1, hh.2.2.2.1, h2, hh.2.2.2.2.1⟩
      rw [evaluate, b1] at he
      cases he
      exact Aux.epost_refl hh.2.2.2.2.2 ⟨b2, trivial⟩
  case func =>
    intro s env x e r s' tenv E ts tvs S he hh _ ht
    replace ht := Aux.es1.1 ht
    obtain ⟨t, rfl, ht⟩ := ht
    rw [evaluate] at he
    cases he
    cases ht with
    | fn _ n e t1 t2 h1 h2 =>
      rw [Aux.num_tvs_bt, hh.2.2.2.1] at h1
      exact Aux.epost_refl hh.2.2.2.2.2 ⟨type_v_closure_aux _ _ _ _ tenv E _ _ _ _ hh.1 hh.2.1
        hh.2.2.2.1 hh.2.2.2.2.1.1 hh.2.2.2.2.1.2 h1 h2, trivial⟩
  case app =>
    intro s env o es ih1 ih2 ih3 ih4 r s' tenv E ts tvs S he hh hv ht
    cases h0 (by simp [is_value]) hv
    replace ht := Aux.es1.1 ht
    obtain ⟨t, rfl, ht⟩ := ht
    cases ht with
    | app _ o es ts t h1 h2 h3 =>
      rw [bind_tvar0, hh.2.2.2.1] at h3
      have hsub := fun r s' hev => ih1 r s' tenv E _ 0 S hev hh (fun h => absurd rfl h)
        (Aux.es_reverse h1)
      rw [Aux.evaluate_App] at he
      rcases hev : evaluate s env es.reverse with ⟨s1, vs | e⟩
      · rw [hev] at he
        dsimp only at he
        obtain ⟨S1, a1, a2, a3, a4, a5⟩ := hsub _ _ hev
        refine Aux.epost_trans a2 a3 a4 ?_
        cases hcl : getOpClass o with
        | FunApp =>
          cases Aux.getOpClass_FunApp hcl
          have a6 := Aux.LIST_REL_reverse a5
          rw [List.reverse_reverse] at a6
          obtain ⟨env', e, tenv', E', b1, b2, b3, b4, b5, b6⟩ :=
            opapp_type_sound m S1 vs.reverse ts t ⟨hh.2.2.1.1, h2, a6⟩
          rw [hcl] at he
          dsimp only at he
          rw [b6] at he
          dsimp only at he
          by_cases hck : s1.clock = 0
          · rw [if_pos hck] at he
            cases he
            exact Aux.epost_refl a1 trivial
          · rw [if_neg hck] at he
            exact ih2 _ _ _ _ hev hcl b6 hck _ _ tenv' E' [t] 0 S1 he
              ⟨b1, b2, hh.2.2.1, b3, b4, a1⟩ (fun h => absurd rfl h)
              (Aux.es1.2 ⟨t, rfl, by rw [bind_tvar0]; exact b5⟩)
        | Force =>
          obtain ⟨th, rfl⟩ := Aux.getOpClass_Force hcl
          exact h2.elim
        | EvalOp =>
          cases Aux.getOpClass_Eval hcl
          exact h2.elim
        | Simple =>
          rw [hcl] at he
          dsimp only at he
          have hop : o ≠ Opapp := by rintro rfl; cases hcl
          obtain ⟨S2, st2, ffi2, r2, b1, b2, b3, b4⟩ := op_type_sound m S1 vs o ts t s1.refs s1.ffi
            ⟨hh.2.2.1, hop, a1, h2, h3, a5⟩
          rw [b3] at he
          cases he
          refine ⟨S2, b2, b1, rfl, rfl, ?_⟩
          rcases r2 with v | v | (_ | _ | _)
          · exact ⟨b4, trivial⟩
          · exact b4
          · exact b4.elim
          · exact b4.elim
          · exact trivial
      · rw [hev] at he
        cases he
        exact hsub _ _ hev
  case log =>
    intro s env l e1 e2 ih1 ih2 r s' tenv E ts tvs S he hh hv ht
    cases h0 (by simp [is_value]) hv
    replace ht := Aux.es1.1 ht
    obtain ⟨t, rfl, ht⟩ := ht
    cases ht with
    | log _ _ _ _ h1 h2 =>
      have hsub := fun r s' hev => ih1 r s' tenv E [Tbool] 0 S hev hh (fun h => absurd rfl h)
        (Aux.es1.2 ⟨_, rfl, h1⟩)
      rw [Aux.evaluate_Log] at he
      rcases hev : evaluate s env [e1] with ⟨s1, vs | e⟩
      · rw [hev] at he
        dsimp only at he
        obtain ⟨S1, a1, a2, a3, a4, a5⟩ := hsub _ _ hev
        obtain ⟨x, rfl, hx⟩ := Aux.LR1 a5
        obtain ⟨b, rfl⟩ := Aux.canon_bool hx hh.2.2.1.1 hh.2.2.1.2.1
        refine Aux.epost_trans a2 a3 a4 ?_
        have hhd : HD [Boolv b] = Boolv b := rfl
        rw [hhd] at he
        rcases Aux.do_log_bool l b e2 with hl | hl
        · rw [hl] at he
          exact ih2 _ _ _ hev (by rw [hhd]; exact hl) _ _ tenv E [Tbool] 0 S1 he
            (Aux.ehyp_step hh a1 a2) (fun h => absurd rfl h) (Aux.es1.2 ⟨_, rfl, h2⟩)
        · rw [hl] at he
          cases he
          exact Aux.epost_refl a1 ⟨hx, trivial⟩
      · rw [hev] at he
        cases he
        exact hsub _ _ hev
  case ite =>
    intro s env e1 e2 e3 ih1 ih2 r s' tenv E ts tvs S he hh hv ht
    cases h0 (by simp [is_value]) hv
    replace ht := Aux.es1.1 ht
    obtain ⟨t, rfl, ht⟩ := ht
    cases ht with
    | if' _ _ _ _ _ h1 h2 h3 =>
      have hsub := fun r s' hev => ih1 r s' tenv E [Tbool] 0 S hev hh (fun h => absurd rfl h)
        (Aux.es1.2 ⟨_, rfl, h1⟩)
      rw [Aux.evaluate_If] at he
      rcases hev : evaluate s env [e1] with ⟨s1, vs | e⟩
      · rw [hev] at he
        dsimp only at he
        obtain ⟨S1, a1, a2, a3, a4, a5⟩ := hsub _ _ hev
        obtain ⟨x, rfl, hx⟩ := Aux.LR1 a5
        obtain ⟨b, rfl⟩ := Aux.canon_bool hx hh.2.2.1.1 hh.2.2.1.2.1
        refine Aux.epost_trans a2 a3 a4 ?_
        have hhd : HD [Boolv b] = Boolv b := rfl
        rw [hhd] at he
        have hi : do_if (Boolv b) e2 e3 = some (if b = true then e2 else e3) := by
          cases b <;> simp [do_if, Boolv_11]
        rw [hi] at he
        refine ih2 _ _ _ hev (by rw [hhd]; exact hi) _ _ tenv E [t] 0 S1 he
            (Aux.ehyp_step hh a1 a2) (fun h => absurd rfl h) (Aux.es1.2 ⟨_, rfl, ?_⟩)
        split
        · exact h2
        · exact h3
      · rw [hev] at he
        cases he
        exact hsub _ _ hev
  case mat =>
    intro s env e pes ih1 ih2 r s' tenv E ts tvs S he hh hv ht
    cases h0 (by simp [is_value]) hv
    replace ht := Aux.es1.1 ht
    obtain ⟨t, rfl, ht⟩ := ht
    rw [bind_tvar0] at ht
    obtain ⟨t1, h1, _, h3⟩ := type_e_Mat_inv_aux _ _ _ _ _ ht
    rw [hh.2.2.2.1] at h3
    rw [Aux.evaluate_Mat] at he
    have hsub := fun r s' hev => ih1 r s' tenv E [t1] 0 S hev hh
      (fun h => absurd rfl h) (Aux.es1.2 ⟨_, rfl, by rw [bind_tvar0]; exact h1⟩)
    rcases hev : evaluate s env [e] with ⟨s1, v | e'⟩
    · rw [hev] at he
      dsimp only at he
      obtain ⟨S1, a1, a2, a3, a4, a5⟩ := hsub _ _ hev
      obtain ⟨x, rfl, hx⟩ := Aux.LR1 a5
      have hhd : HD [x] = x := rfl
      rw [hhd] at he
      have hh1 := Aux.ehyp_step hh a1 a2
      have hcan : can_pmatch_all env.c s1.refs (pes.map Prod.fst) x := by
        refine Aux.can_pmatch (tenv := tenv) hh.2.2.1.1 hh1.2.2.2.2.1.1 a1 hx ?_
        intro p hp
        obtain ⟨⟨p', e'⟩, hpe, rfl⟩ := List.mem_map.1 hp
        obtain ⟨b, _, hb, _⟩ := h3 p' e' hpe
        exact ⟨b, hb⟩
      rw [if_pos hcan] at he
      exact Aux.epost_trans a2 a3 a4 (hM he
        (ih2 _ _ hev hcan _ _ tenv E t1 t 0 S1 he hh1 hx
          (type_v_exn 0 m S1 hh.2.2.1.2.2.1).2.2.1 h3))
    · rw [hev] at he
      cases he
      exact hsub _ _ hev
  case letc =>
    intro s env xo e1 e2 ih1 ih2 r s' tenv E ts tvs S he hh hv ht
    cases h0 (by simp [is_value]) hv
    replace ht := Aux.es1.1 ht
    obtain ⟨t, rfl, ht⟩ := ht
    rw [bind_tvar0] at ht
    cases ht with
    | let' _ _ _ _ t1 _ h1 h2 =>
      have hsub := fun r s' hev => ih1 r s' tenv E [t1] 0 S hev hh (fun h => absurd rfl h)
        (Aux.es1.2 ⟨_, rfl, by rw [bind_tvar0]; exact h1⟩)
      rw [Aux.evaluate_Let] at he
      rcases hev : evaluate s env [e1] with ⟨s1, vs | e⟩
      · rw [hev] at he
        dsimp only at he
        obtain ⟨S1, a1, a2, a3, a4, a5⟩ := hsub _ _ hev
        obtain ⟨x, rfl, hx⟩ := Aux.LR1 a5
        refine Aux.epost_trans a2 a3 a4 ?_
        have hhd : HD [x] = x := rfl
        have hh1 := Aux.ehyp_step hh a1 a2
        refine ih2 _ _ hev _ _ tenv (opt_bind_name xo 0 t1 E) [t] 0 S1 he ?_
          (fun h => absurd rfl h) (Aux.es1.2 ⟨_, rfl, by rw [bind_tvar0]; exact h2⟩)
        rw [hhd]
        cases xo with
        | none => exact hh1
        | some n =>
          refine ⟨hh1.1, ⟨?_, hh1.2.1⟩, hh1.2.2.1, hh1.2.2.2.1,
            ⟨hh1.2.2.2.2.1.1, nsAll2_nsBind _ _ _ _ _ _ ⟨hx, hh1.2.2.2.2.1.2⟩⟩, a1⟩
          rw [hh1.2.2.2.1]
          exact type_v_freevars _ _ _ _ _ hx
      · rw [hev] at he
        cases he
        exact hsub _ _ hev
  case letrec =>
    intro s env funs e ih r s' tenv E ts tvs S he hh hv ht
    cases h0 (by simp [is_value]) hv
    replace ht := Aux.es1.1 ht
    obtain ⟨t, rfl, ht⟩ := ht
    rw [bind_tvar0] at ht
    cases ht with
    | letrec _ _ _ _ b h1 h2 =>
      have hd := type_funs_distinct _ _ _ _ h1
      rw [evaluate, if_pos hd] at he
      refine ih hd _ _ tenv (bind_var_list 0 b E) [t] 0 S he ?_ (fun h => absurd rfl h)
        (Aux.es1.2 ⟨_, rfl, by rw [bind_tvar0]; exact h2⟩)
      exact ⟨hh.1, tenv_val_exp_ok_bvl_funs _ _ _ _ () _ ⟨h1, hh.2.1⟩, hh.2.2.1,
        by rw [num_tvs_bind_var_list]; exact hh.2.2.2.1,
        ⟨hh.2.2.2.2.1.1, Aux.rec_env_ok hh.1 hh.2.2.2.2.1 hh.2.1 hh.2.2.2.1
          (by rw [bind_tvar0]; exact h1)⟩, hh.2.2.2.2.2⟩
  case tannot =>
    intro s env e t ih r s' tenv E ts tvs S he hh hv ht
    replace ht := Aux.es1.1 ht
    obtain ⟨t, rfl, ht⟩ := ht
    rw [evaluate] at he
    cases ht with
    | tannot _ _ _ _ _ h =>
      refine ih _ _ tenv E _ tvs S he hh (fun hn => ⟨?_, trivial⟩) (Aux.es1.2 ⟨_, rfl, h⟩)
      have := (hv hn).1
      rw [is_value] at this
      exact this
  case lannot =>
    intro s env e t ih r s' tenv E ts tvs S he hh hv ht
    replace ht := Aux.es1.1 ht
    obtain ⟨t, rfl, ht⟩ := ht
    rw [evaluate] at he
    cases ht with
    | lannot _ _ _ _ h =>
      refine ih _ _ tenv E _ tvs S he hh (fun hn => ⟨?_, trivial⟩) (Aux.es1.2 ⟨_, rfl, h⟩)
      have := (hv hn).1
      rw [is_value] at this
      exact this
  case mnil =>
    intro s env v err_v r s' tenv E t1 t2 tvs S he hh _ herr _
    rw [evaluate_match] at he
    cases he
    exact Aux.epost_refl hh.2.2.2.2.2 herr
  case mcons =>
    intro s env v p e pes err_v ih1 ih2 r s' tenv E t1 t2 tvs S he hh hv herr hpes
    obtain ⟨b, hd, hp, hte⟩ := hpes p e List.mem_cons_self
    rw [evaluate_match, if_pos hd] at he
    rcases pat_type_sound.1 env.c s.refs p v [] tenv m [] t1 b S tvs
      ⟨hh.2.2.1.1, hh.2.2.2.2.1.1, hv, hp, hh.2.2.2.2.2, trivial⟩ with hpm | ⟨b', hpm, hb'⟩
    · rw [hpm] at he
      exact ih1 hd hpm _ _ tenv E t1 t2 tvs S he hh hv herr
        (fun p e hpe => hpes p e (List.mem_cons_of_mem _ hpe))
    · rw [hpm] at he
      rw [List.append_nil] at hb'
      have := ih2 _ hd hpm _ _ tenv (bind_var_list tvs b E) [t2] 0 S he ?_
        (fun h => absurd rfl h) (Aux.es1.2 ⟨_, rfl, by rw [bind_tvar0]; exact hte⟩)
      · obtain ⟨S', a1, a2, a3, a4, a5⟩ := this
        refine ⟨S', a1, a2, a3, a4, ?_⟩
        cases r with
        | Rerr e => exact a5
        | Rval vs =>
          obtain ⟨x, rfl, hx⟩ := Aux.LR1 a5
          exact type_v_weakening _ _ _ _ _ hx _ _ _ ⟨Or.inl rfl, weakCT_refl _, weakS_refl _⟩
      · refine ⟨hh.1, type_p_bvl.1 _ _ _ _ _ hp _ hh.2.1, hh.2.2.1,
          by rw [num_tvs_bind_var_list]; exact hh.2.2.2.1, ⟨hh.2.2.2.2.1.1, ?_⟩, hh.2.2.2.2.2⟩
        show nsAll2 (fun _ v (p : Nat × typ) => type_v p.1 m S v p.2)
          (nsAppend (alist_to_ns b') env.v) (add_tenvE (bind_var_list tvs b E) tenv.v)
        rw [nsAppend_to_nsBindList, add_tenvE_bvl]
        refine nsAll2_nsBindList (fun _ v (p : Nat × typ) => type_v p.1 m S v p.2) _ _ _ _
          ⟨?_, hh.2.2.2.2.1.2⟩
        rw [Aux.LIST_REL_map_right]
        exact Aux.LIST_REL_mono (fun _ _ _ _ h => h) hb'
  all_goals intros; trivial

end exp_sound

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
          | Rerr (Rabort Rtype_error) => False)) := by
  refine ⟨?_, ?_⟩
  · rintro s env es r s' tenv E ts tvs S ⟨he, h1, h2, h3, h4, h5, h6, h7, h8⟩
    obtain ⟨S', a1, a2, a3, a4, a5⟩ := (Aux.exp_sound ctMap).1 s env es r s' tenv E ts tvs S he
      ⟨h1, h2, h3, h4, h5, h6⟩ h7 h8
    refine ⟨S', a1, a2, a3, a4, ?_⟩
    rcases r with v | v | (_ | _ | _) <;> exact a5
  · rintro s env v pes err_v r s' tenv E t1 t2 tvs S ⟨he, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
    obtain ⟨S', a1, a2, a3, a4, a5⟩ := (Aux.exp_sound ctMap).2.1 s env v pes err_v r s' tenv E
      t1 t2 tvs S he ⟨h1, h2, h3, h4, h5, h6⟩ h7 h8 h9
    refine ⟨S', a1, a2, a3, a4, ?_⟩
    rcases r with v | v | (_ | _ | _) <;> exact a5

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
        (build_ctor_tenv tenvT tds tids) := by
  intro tenvT tds
  induction tds with
  | nil =>
    rintro tids next m ⟨_, hl⟩
    cases tids with
    | nil => exact nsAll2_nsEmpty _
    | cons id tids => simp at hl
  | cons td tds ih =>
    rintro tids next m ⟨hd, hl⟩
    obtain ⟨tvs, tn, ctors⟩ := td
    cases tids with
    | nil => simp at hl
    | cons id tids =>
      have hl' : tds.length = tids.length := by simpa using hl
      obtain ⟨hd1, hd2⟩ := hd
      have hd1 : ALL_DISTINCT (ctors.map Prod.fst) := hd1
      rw [Aux.ALL_DISTINCT_iff] at hd1
      rw [build_tdefs, build_ctor_tenv, type_def_to_ctMap, List.reverse_append]
      have hfold : ∀ (a b : List (stamp × List tvarN × List typ × type_ident)),
          FUPDATE_LIST m (a ++ b) = FUPDATE_LIST (FUPDATE_LIST m a) b := by
        intro a b
        unfold FUPDATE_LIST
        rw [List.foldl_append]
      refine nsAll2_nsAppend _ _ _ _ _ ⟨?_, ?_⟩
      · rw [hfold]
        exact ih tids (next + 1) _ ⟨hd2, hl'⟩
      · refine nsAll2_alist_to_ns _ _ _ ?_
        refine Aux.LIST_REL_reverse ?_
        unfold build_constrs
        rw [Aux.LIST_REL_map_left, Aux.LIST_REL_map_right, Aux.LIST_REL_refl_iff]
        rintro ⟨cn, ts⟩ hm
        refine ⟨rfl, ?_, by simp⟩
        rw [← List.reverse_append, Aux.FLOOKUP_FUPDATE_LIST, List.reverse_reverse,
          Aux.ALOOKUP_append]
        have hnone : ALOOKUP (type_def_to_ctMap tenvT (next + 1) tds tids)
            (TypeStamp cn next) = none := by
          cases hx : ALOOKUP (type_def_to_ctMap tenvT (next + 1) tds tids)
            (TypeStamp cn next) with
          | none => rfl
          | some x =>
            obtain ⟨cn', i, he, h1, h2⟩ := mem_type_def_to_ctMap _ _ _ _ _ _
              ⟨Aux.ALOOKUP_mem hx, hl'⟩
            cases he
            omega
        rw [hnone]
        have hsome : ALOOKUP ((ctors.map (fun ((cn, ts) : conN × List ast_t) =>
            (TypeStamp cn next, (tvs, ts.map (type_name_subst tenvT), id)))).reverse)
            (TypeStamp cn next) = some (tvs, ts.map (type_name_subst tenvT), id) := by
          refine Aux.ALOOKUP_of_mem ?_ ?_
          · rw [List.map_reverse, List.map_map]
            refine (List.reverse_perm _).nodup_iff.2 ?_
            have he : (Prod.fst ∘ fun ((cn, ts) : conN × List ast_t) =>
                (TypeStamp cn next, (tvs, ts.map (type_name_subst tenvT), id))) =
                (fun cn => TypeStamp cn next) ∘ Prod.fst := by
              funext ⟨a, b⟩; rfl
            rw [he, ← List.map_map]
            refine List.Pairwise.map _ (fun a b hab h => hab ?_) hd1
            cases h; rfl
          · rw [List.mem_reverse]
            exact List.mem_map.2 ⟨(cn, ts), hm, rfl⟩
        simp only
        rw [hsome]

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
    type_sound_invariant st env ctMap tenvS tids1 tenv := by
  rintro ⟨h1, h2, ⟨h3, h3'⟩, h4, h5⟩
  refine ⟨h1, h2, ⟨?_, h3'⟩, h4, h5⟩
  rw [Aux.disjoint_iff] at h3 ⊢
  exact fun x hx => h3 x (Or.inl hx)

/- HOL4:
Theorem check_ctor_tenv_dups[local]:
  !tenvT tds. check_ctor_tenv tenvT tds ⇒ EVERY check_dup_ctors tds -/
theorem check_ctor_tenv_dups :
    ∀ (tenvT : Namespace modN typeN (List tvarN × typ))
      (tds : List (List tvarN × mlstring × List (conN × List ast_t))),
      check_ctor_tenv tenvT tds → EVERY check_dup_ctors tds := by
  intro tenvT tds h
  induction tds with
  | nil => trivial
  | cons td tds ih =>
    obtain ⟨tvs, tn, cs⟩ := td
    exact ⟨h.1, ih h.2.2.2.2⟩

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
        (extend_dec_tenv tenv1 tenv2) := by
  rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
  exact ⟨nsAll2_nsAppend _ _ _ _ _ ⟨h1, h3⟩, nsAll2_nsAppend _ _ _ _ _ ⟨h2, h4⟩⟩

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
  have hT : ∀ e, (∀ cn es, e ≠ exp.Con cn es) → one_con_check envc e := by
    intro e he
    cases e <;> first | trivial | exact absurd rfl (he _ _)
  apply Aux.type_e_ind
  case intLit => intros; simp [every_exp, one_con_check]
  case char => intros; simp [every_exp, one_con_check]
  case strLit => intros; simp [every_exp, one_con_check]
  case word8 => intros; simp [every_exp, one_con_check]
  case word64 => intros; simp [every_exp, one_con_check]
  case float64 => intros; simp [every_exp, one_con_check]
  case raise => intro tenv E e t _ _ ih hh; rw [every_exp]; exact ⟨trivial, ih hh⟩
  case handle =>
    intro tenv E e pes t bs _ _ _ _ _ ih1 ih2 hh
    rw [every_exp, EVERY_iff_forall]
    exact ⟨trivial, ih1 hh, fun pe hpe => ih2 pe hpe hh⟩
  case con =>
    intro tenv E cn es tvs tn ts' ts _ _ hes hl ih hh
    rw [every_exp]
    refine ⟨?_, ih hh⟩
    obtain ⟨⟨k, s⟩, h1, _, rfl⟩ := nsAll2_nsLookup2 _ _ _ _ _ ⟨hl, hh⟩
    have := type_es_length _ _ _ _ hes
    rw [List.length_map] at this
    simp only [one_con_check, do_con_check]
    rw [h1]
    exact this
  case tup =>
    intro tenv E es ts _ ih hh
    rw [every_exp]
    exact ⟨trivial, ih hh⟩
  case var => intros; rw [every_exp]; trivial
  case fn => intro tenv E n e t1 t2 _ _ ih hh; rw [every_exp]; exact ⟨trivial, ih hh⟩
  case app => intro tenv E o es ts t _ _ _ ih hh; rw [every_exp]; exact ⟨trivial, ih hh⟩
  case log =>
    intro tenv E l e1 e2 _ _ ih1 ih2 hh
    rw [every_exp]; exact ⟨trivial, ih1 hh, ih2 hh⟩
  case ite =>
    intro tenv E e1 e2 e3 t _ _ _ ih1 ih2 ih3 hh
    rw [every_exp]; exact ⟨trivial, ih1 hh, ih2 hh, ih3 hh⟩
  case mat =>
    intro tenv E e pes t1 t2 bs _ _ _ _ _ ih1 ih2 hh
    rw [every_exp, EVERY_iff_forall]
    exact ⟨trivial, ih1 hh, fun pe hpe => ih2 pe hpe hh⟩
  case letc =>
    intro tenv E n e1 e2 t1 t2 _ _ ih1 ih2 hh
    rw [every_exp]; exact ⟨trivial, ih1 hh, ih2 hh⟩
  case letrec =>
    intro tenv E funs e t b _ _ ih1 ih2 hh
    rw [every_exp]
    exact ⟨trivial, ih2 hh, ih1 hh⟩
  case tannot => intro tenv E e t _ _ _ ih hh; rw [every_exp]; exact ⟨trivial, ih hh⟩
  case lannot => intro tenv E e l t _ ih hh; rw [every_exp]; exact ⟨trivial, ih hh⟩
  case nil => intros; trivial
  case cons => intro tenv E e es t ts _ _ ih1 ih2 hh; exact ⟨ih1 hh, ih2 hh⟩
  case fnil => intros; trivial
  case fcons =>
    intro tenv E fn n e funs b t1 t2 _ _ _ _ ih1 ih2 hh
    exact ⟨ih1 hh, ih2 hh⟩

section decs_sound

variable {ffi : Type}

def Aux.ids (m : ctMap_ty) : Set type_ident := FRANGE (o_f (Prod.snd ∘ Prod.snd) m)

theorem Aux.mem_ids {m : ctMap_ty} {ti : type_ident} :
    ti ∈ Aux.ids m ↔ ∃ s a b, FLOOKUP m s = some (a, b, ti) := by
  constructor
  · rintro ⟨s, hs⟩
    rw [Aux.FLOOKUP_o_f, Option.map_eq_some_iff] at hs
    obtain ⟨⟨a, b, c⟩, h1, rfl⟩ := hs
    exact ⟨s, a, b, h1⟩
  · rintro ⟨s, a, b, h⟩
    exact ⟨s, by rw [Aux.FLOOKUP_o_f, h]; rfl⟩

def Aux.dres (m' : ctMap_ty) (S' : tenv_store) (env : sem_env value) (tenv tenv' : type_env)
    (st' : state ffi) (r : result (sem_env value) value) : Prop :=
  match r with
  | Rval env' => type_all_env m' S' env' tenv' ∧
      type_sound_invariant st' (extend_dec_env env' env) m' S' ∅ (extend_dec_tenv tenv' tenv)
  | Rerr (Rraise v) => type_v 0 m' S' v Texn ∧ type_sound_invariant st' env m' S' ∅ tenv
  | Rerr (Rabort Rtype_error) => False
  | Rerr (Rabort Rtimeout_error) => True
  | Rerr (Rabort (Rffi_error _)) => True

def Aux.dpost (m : ctMap_ty) (S : tenv_store) (env : sem_env value) (tenv tenv' : type_env)
    (tids : Set type_ident) (st' : state ffi) (r : result (sem_env value) value) : Prop :=
  ∃ (m' : ctMap_ty) (S' : tenv_store), weakCT m' m ∧ (Aux.ids m' \ Aux.ids m) ⊆ tids ∧
    store_type_extension S S' ∧ Aux.dres m' S' env tenv tenv' st' r

theorem Aux.cons_mono {st st' : state ffi} {tids : Set type_ident} {m : ctMap_ty}
    (h : consistent_ctMap st tids m) (h1 : st.next_type_stamp ≤ st'.next_type_stamp)
    (h2 : st.next_exn_stamp ≤ st'.next_exn_stamp) : consistent_ctMap st' (∅ : Set type_ident) m :=
  ⟨Aux.disjoint_iff.2 fun _ h => False.elim h, fun cn id =>
    ⟨fun hx => Nat.lt_of_lt_of_le ((h.2 cn id).1 hx) h1,
      fun hx => Nat.lt_of_lt_of_le ((h.2 cn id).2 hx) h2⟩⟩

theorem Aux.tsi_ids {st : state ffi} {env : sem_env value} {m : ctMap_ty} {S : tenv_store}
    {t1 t2 : Set type_ident} {tenv : type_env} (h : type_sound_invariant st env m S t1 tenv)
    (hd : ∀ ti, ti ∈ t2 → ¬ ti ∈ Aux.ids m) : type_sound_invariant st env m S t2 tenv :=
  ⟨h.1, h.2.1, ⟨Aux.disjoint_iff.2 hd, h.2.2.1.2⟩, h.2.2.2.1, h.2.2.2.2⟩

theorem Aux.tsi_disj {st : state ffi} {env : sem_env value} {m : ctMap_ty} {S : tenv_store}
    {t1 : Set type_ident} {tenv : type_env} (h : type_sound_invariant st env m S t1 tenv) :
    ∀ ti, ti ∈ t1 → ¬ ti ∈ Aux.ids m := Aux.disjoint_iff.1 h.2.2.1.1

theorem Aux.env_weak {m m' : ctMap_ty} {S S' : tenv_store} {env : sem_env value}
    {tenv : type_env} (h : type_all_env m S env tenv) (hC : weakCT m' m)
    (hS : store_type_extension S S') : type_all_env m' S' env tenv :=
  type_all_env_weakening _ _ _ _ _ _ ⟨hC, store_type_extension_weakS _ _ hS, h⟩

/-- Results that leave the constructor map alone. -/
theorem Aux.dpost_val {st st' : state ffi} {env env' : sem_env value} {m : ctMap_ty}
    {S S' : tenv_store} {tids tids' : Set type_ident} {tenv tenv' : type_env}
    (h : type_sound_invariant st env m S tids tenv) (hok : tenv_ok tenv')
    (hS : store_type_extension S S') (hs : type_s m st'.refs S')
    (h1 : st.next_type_stamp ≤ st'.next_type_stamp)
    (h2 : st.next_exn_stamp ≤ st'.next_exn_stamp)
    (henv : type_all_env m S' env' tenv') :
    Aux.dpost m S env tenv tenv' tids' st' (Rval env') :=
  ⟨m, S', weakCT_refl _, fun _ hx => absurd hx.1 hx.2, hS, henv,
    extend_dec_tenv_ok _ _ ⟨hok, h.1⟩, h.2.1, Aux.cons_mono h.2.2.1 h1 h2,
    type_all_env_extend _ _ _ _ _ _ ⟨henv, Aux.env_weak h.2.2.2.1 (weakCT_refl _) hS⟩, hs⟩

theorem Aux.dpost_raise {st st' : state ffi} {env : sem_env value} {m : ctMap_ty}
    {S S' : tenv_store} {tids tids' : Set type_ident} {tenv tenv' : type_env} {v : value}
    (h : type_sound_invariant st env m S tids tenv)
    (hS : store_type_extension S S') (hs : type_s m st'.refs S')
    (h1 : st.next_type_stamp ≤ st'.next_type_stamp)
    (h2 : st.next_exn_stamp ≤ st'.next_exn_stamp)
    (hv : type_v 0 m S' v Texn) :
    Aux.dpost m S env tenv tenv' tids' st' (Rerr (Rraise v)) :=
  ⟨m, S', weakCT_refl _, fun _ hx => absurd hx.1 hx.2, hS, hv,
    h.1, h.2.1, Aux.cons_mono h.2.2.1 h1 h2, Aux.env_weak h.2.2.2.1 (weakCT_refl _) hS, hs⟩

theorem Aux.dlet_sound {st st' : state ffi} {env : sem_env value} {l : locs} {p : pat} {e : exp}
    {r : result (sem_env value) value} {m : ctMap_ty} {S : tenv_store} {tenv : type_env}
    {tids tids' : Set type_ident} {tvs : Nat} {t : typ} {b : List (varN × typ)}
    (he : evaluate_decs st env [Dlet l p e] = (st', r))
    (h : type_sound_invariant st env m S tids tenv)
    (hv : tvs ≠ 0 → is_value e) (hd : ALL_DISTINCT (pat_bindings p []))
    (hp : type_p tvs tenv p t b) (ht : type_e tenv (bind_tvar tvs tenv_val_exp.Empty) e t) :
    Aux.dpost m S env tenv { v := alist_to_ns (tenv_add_tvs tvs b), c := nsEmpty, t := nsEmpty }
      tids' st' r := by
  obtain ⟨hok, hg, hcons, henv, hs⟩ := h
  have hck := (type_e_con_check m env.c).1 _ _ _ _ ht henv.1
  rw [evaluate_decs, if_pos ⟨hd, hck⟩] at he
  have hsub := fun r s' hev => (Aux.exp_sound m).1 st env [e] r s' tenv tenv_val_exp.Empty [t] tvs S
    hev ⟨hok, trivial, hg, rfl, henv, hs⟩ (fun hn => ⟨hv hn, trivial⟩) (Aux.es1.2 ⟨t, rfl, ht⟩)
  rcases hev : evaluate st env [e] with ⟨s1, vs | e'⟩
  · rw [hev] at he
    dsimp only at he
    obtain ⟨S1, a1, a2, a3, a4, a5⟩ := hsub _ _ hev
    obtain ⟨x, rfl, hx⟩ := Aux.LR1 a5
    have hhd : HD [x] = x := rfl
    rw [hhd] at he
    rcases pat_type_sound.1 env.c s1.refs p x [] tenv m [] t b S1 tvs
      ⟨hg.1, henv.1, hx, hp, a1, trivial⟩ with hpm | ⟨b', hpm, hb'⟩
    · rw [hpm] at he
      cases he
      exact Aux.dpost_raise ⟨hok, hg, hcons, henv, hs⟩ a2 a1 (Nat.le_of_eq a3.symm)
        (Nat.le_of_eq a4.symm) (type_v_exn 0 m S1 hg.2.2.1).2.2.1
    · rw [hpm] at he
      rw [List.append_nil] at hb'
      cases he
      refine Aux.dpost_val ⟨hok, hg, hcons, henv, hs⟩
        ⟨Aux.tenv_add_tvs_ok (type_p_freevars.1 _ _ _ _ _ hp).2, nsAll_nsEmpty _, nsAll_nsEmpty _⟩
        a2 a1 (Nat.le_of_eq a3.symm) (Nat.le_of_eq a4.symm) ⟨nsAll2_nsEmpty _, ?_⟩
      refine nsAll2_alist_to_ns (fun _ v (p : Nat × typ) => type_v p.1 m S1 v p.2) _ _ ?_
      unfold tenv_add_tvs
      rw [Aux.LIST_REL_map_right]
      exact Aux.LIST_REL_mono (fun _ _ _ _ h => h) hb'
  · rw [hev] at he
    cases he
    obtain ⟨S1, a1, a2, a3, a4, a5⟩ := hsub _ _ hev
    rcases e' with v | _ | _ | _
    · exact Aux.dpost_raise ⟨hok, hg, hcons, henv, hs⟩ a2 a1 (Nat.le_of_eq a3.symm)
        (Nat.le_of_eq a4.symm) a5
    · exact a5.elim
    · exact ⟨m, S1, weakCT_refl _, fun _ hx => absurd hx.1 hx.2, a2, trivial⟩
    · exact ⟨m, S1, weakCT_refl _, fun _ hx => absurd hx.1 hx.2, a2, trivial⟩

theorem Aux.dtype_sound {st : state ffi} {env : sem_env value} {m : ctMap_ty} {S : tenv_store}
    {tenv : type_env} {tdefs : type_def} {tids : List type_ident} {tenvT : tenv_abbrev}
    (h : type_sound_invariant st env m S (LIST_TO_SET tids) tenv)
    (h1 : ALL_DISTINCT tids)
    (h2 : DISJOINT (LIST_TO_SET tids) (LIST_TO_SET (Tlist_num :: (Tbool_num :: prim_type_nums))))
    (h3 : check_ctor_tenv (nsAppend tenvT tenv.t) tdefs)
    (h4 : tids.length = tdefs.length) (hT : tenv_abbrev_ok tenvT) :
    Aux.dpost m S env tenv
      { v := nsEmpty, c := build_ctor_tenv (nsAppend tenvT tenv.t) tdefs tids, t := tenvT }
      (LIST_TO_SET tids) { st with next_type_stamp := st.next_type_stamp + tdefs.length }
      (Rval { v := nsEmpty, c := build_tdefs st.next_type_stamp tdefs }) := by
  have hdis := Aux.tsi_disj h
  obtain ⟨hok, hg, hcons, henv, hs⟩ := h
  have hTT : tenv_abbrev_ok (nsAppend tenvT tenv.t) := nsAll_nsAppend _ _ _ ⟨hT, hok.2.2⟩
  generalize hl : type_def_to_ctMap (nsAppend tenvT tenv.t) st.next_type_stamp tdefs tids = l
  have hlk : ∀ s, FLOOKUP (FUPDATE_LIST m l.reverse) s =
      match ALOOKUP l s with | some v => some v | none => FLOOKUP m s := by
    intro s
    rw [Aux.FLOOKUP_FUPDATE_LIST, List.reverse_reverse]
    cases ALOOKUP l s <;> rfl
  have hkey : ∀ s x, ALOOKUP l s = some x → ∃ cn i, s = TypeStamp cn i ∧
      st.next_type_stamp ≤ i ∧ i < st.next_type_stamp + tdefs.length := by
    intro s x hx
    rw [← hl] at hx
    exact mem_type_def_to_ctMap _ _ _ _ _ _ ⟨Aux.ALOOKUP_mem hx, h4.symm⟩
  have hid : ∀ s x, ALOOKUP l s = some x → x.2.2 ∈ tids := by
    intro s x hx
    rw [← hl] at hx
    exact type_def_to_ctMap_mem s x _ _ _ _ ⟨hx, h4.symm⟩
  have hold : ∀ cn i, i < st.next_type_stamp → ALOOKUP l (TypeStamp cn i) = none := by
    intro cn i hi
    cases hx : ALOOKUP l (TypeStamp cn i) with
    | none => rfl
    | some x =>
      obtain ⟨cn', i', he, b1, _⟩ := hkey _ _ hx
      cases he
      omega
  have hexn : ∀ i, ALOOKUP l (ExnStamp i) = none := by
    intro i
    cases hx : ALOOKUP l (ExnStamp i) with
    | none => rfl
    | some x => obtain ⟨cn', i', he, _⟩ := hkey _ _ hx; cases he
  have hfresh : ∀ s x, FLOOKUP m s = some x → ALOOKUP l s = none := by
    intro s x hx
    cases s with
    | TypeStamp cn i => exact hold cn i ((hcons.2 cn i).1 (Aux.mem_FDOM.2 ⟨x, hx⟩))
    | ExnStamp i => exact hexn i
  have hweak : weakCT (FUPDATE_LIST m l.reverse) m := by
    refine Aux.SUBMAP_iff.2 fun s x hx => ?_
    rw [hlk, hfresh s x hx]
    exact hx
  have hsub : (Aux.ids (FUPDATE_LIST m l.reverse) \ Aux.ids m) ⊆ LIST_TO_SET tids := by
    rintro ti ⟨hx, hn⟩
    obtain ⟨s, a, b, hx⟩ := Aux.mem_ids.1 hx
    rw [hlk] at hx
    cases hx' : ALOOKUP l s with
    | some x =>
      rw [hx'] at hx
      cases hx
      exact hid _ _ hx'
    | none =>
      rw [hx'] at hx
      exact absurd (Aux.mem_ids.2 ⟨s, a, b, hx⟩) hn
  have hokm : ctMap_ok (FUPDATE_LIST m l.reverse) := by
    have hu : FUPDATE_LIST m l.reverse = FUNION (FUPDATE_LIST FEMPTY l.reverse) m :=
      fupdate2_union m [] l.reverse
    rw [hu]
    refine ctMap_ok_merge_imp _ _ ⟨?_, ?_, hg.1⟩
    · refine Aux.disjoint_iff.2 fun ti hx hy => ?_
      obtain ⟨s, a, b, hx⟩ := Aux.mem_ids.1 hx
      rw [Aux.FLOOKUP_FUPDATE_LIST, List.reverse_reverse] at hx
      cases hx' : ALOOKUP l s with
      | none => rw [hx'] at hx; cases hx
      | some x =>
        rw [hx'] at hx
        cases hx
        exact hdis _ (hid _ _ hx') hy
    · rw [← hl]
      refine ctMap_ok_type_defs _ _ _ _ ⟨h1, ?_, h4.symm, h3, hTT⟩
      rw [Aux.disjoint_iff] at h2 ⊢
      exact fun x hx hp => h2 x hx (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hp))
  have hw : ∀ s x, FLOOKUP m s = some x → FLOOKUP (FUPDATE_LIST m l.reverse) s = some x :=
    Aux.SUBMAP_iff.1 hweak
  have hgood : good_ctMap (FUPDATE_LIST m l.reverse) := by
    obtain ⟨_, ⟨b1, b2, b3⟩, ⟨e1, e2, e3, e4⟩, ⟨c1, c2, c3⟩⟩ := hg
    refine ⟨hokm, ⟨hw _ _ b1, hw _ _ b2, fun cn hcn => ?_⟩,
      ⟨hw _ _ e1, hw _ _ e2, hw _ _ e3, hw _ _ e4⟩,
      ⟨hw _ _ c1, hw _ _ c2, fun cn hcn => ?_⟩⟩
    · rw [hlk, hold cn _ ((hcons.2 _ _).1 (Aux.mem_FDOM.2 ⟨_, b1⟩))]
      exact b3 cn hcn
    · rw [hlk, hold cn _ ((hcons.2 _ _).1 (Aux.mem_FDOM.2 ⟨_, c1⟩))]
      exact c3 cn hcn
  have hcons' : consistent_ctMap
      { st with next_type_stamp := st.next_type_stamp + tdefs.length } (∅ : Set type_ident)
      (FUPDATE_LIST m l.reverse) := by
    refine ⟨Aux.disjoint_iff.2 fun _ h => False.elim h, fun cn id => ⟨fun hx => ?_, fun hx => ?_⟩⟩
    · obtain ⟨x, hx⟩ := Aux.mem_FDOM.1 hx
      rw [hlk] at hx
      show id < st.next_type_stamp + tdefs.length
      cases hx' : ALOOKUP l (TypeStamp cn id) with
      | some y =>
        obtain ⟨cn', i', he, _, b2⟩ := hkey _ _ hx'
        cases he
        exact b2
      | none =>
        rw [hx'] at hx
        have := (hcons.2 cn id).1 (Aux.mem_FDOM.2 ⟨x, hx⟩)
        omega
    · obtain ⟨x, hx⟩ := Aux.mem_FDOM.1 hx
      rw [hlk, hexn] at hx
      exact (hcons.2 cn id).2 (Aux.mem_FDOM.2 ⟨x, hx⟩)
  have hdist : EVERY (fun ((_, _, ctors) : List tvarN × typeN × List (conN × List ast_t)) =>
      ALL_DISTINCT (ctors.map Prod.fst)) tdefs := by
    have := EVERY_iff_forall.1 (check_ctor_tenv_dups _ _ h3)
    refine EVERY_iff_forall.2 ?_
    rintro ⟨tvs, tn, cs⟩ hx
    exact (check_dup_ctors_thm tvs tn cs).1 (this _ hx)
  have henv' : type_all_env (FUPDATE_LIST m l.reverse) S
      { v := nsEmpty, c := build_tdefs st.next_type_stamp tdefs }
      { v := nsEmpty, c := build_ctor_tenv (nsAppend tenvT tenv.t) tdefs tids, t := tenvT } := by
    refine ⟨?_, nsAll2_nsEmpty _⟩
    rw [← hl]
    exact build_tdefs_build_tenv _ _ _ _ _ ⟨hdist, h4.symm⟩
  refine ⟨FUPDATE_LIST m l.reverse, S, hweak, hsub, store_type_extension_refl _, henv', ?_, hgood,
    hcons', type_all_env_extend _ _ _ _ _ _
      ⟨henv', Aux.env_weak henv hweak (store_type_extension_refl _)⟩,
    type_s_weakening _ _ _ _ ⟨hs, hweak⟩⟩
  exact extend_dec_tenv_ok _ _ ⟨⟨nsAll_nsEmpty _, check_ctor_tenv_ok _ _ _ ⟨h4.symm, h3, hTT⟩, hT⟩,
    hok⟩

theorem Aux.dexn_sound {st : state ffi} {env : sem_env value} {m : ctMap_ty} {S : tenv_store}
    {tenv : type_env} {cn : conN} {ts : List ast_t} {tids tids' : Set type_ident}
    (h : type_sound_invariant st env m S tids tenv)
    (h1 : EVERY (check_freevars_ast []) ts) (h2 : EVERY (check_type_names tenv.t) ts) :
    Aux.dpost m S env tenv
      { v := nsEmpty, c := nsSing cn ([], ts.map (type_name_subst tenv.t), Texn_num), t := nsEmpty }
      tids' { st with next_exn_stamp := st.next_exn_stamp + 1 }
      (Rval { v := nsEmpty, c := nsSing cn (ts.length, ExnStamp st.next_exn_stamp) }) := by
  obtain ⟨hok, hg, hcons, henv, hs⟩ := h
  rw [EVERY_iff_forall] at h1 h2
  have hcf : EVERY (check_freevars 0 []) (ts.map (type_name_subst tenv.t)) := by
    rw [Aux.EVERY_map]
    exact fun t ht => check_freevars_type_name_subst _ _ _ _ ⟨hok.2.2, h2 t ht, h1 t ht⟩
  generalize hm' : FUPDATE m (ExnStamp st.next_exn_stamp,
    (([], ts.map (type_name_subst tenv.t), Texn_num) :
      List tvarN × List typ × type_ident)) = m'
  have hlk : ∀ s, FLOOKUP m' s = if s = ExnStamp st.next_exn_stamp then
      some ([], ts.map (type_name_subst tenv.t), Texn_num) else FLOOKUP m s := by
    intro s; rw [← hm']; rfl
  have hnew : ∀ x, FLOOKUP m (ExnStamp st.next_exn_stamp) = some x → False := by
    intro x hx
    exact Nat.lt_irrefl _ ((hcons.2 cn _).2 (Aux.mem_FDOM.2 ⟨x, hx⟩))
  have hw : ∀ s x, FLOOKUP m s = some x → FLOOKUP m' s = some x := by
    intro s x hx
    rw [hlk, if_neg]
    · exact hx
    · rintro rfl; exact hnew x hx
  have hweak : weakCT m' m := Aux.SUBMAP_iff.2 hw
  have hinv : ∀ s x, FLOOKUP m' s = some x → (s = ExnStamp st.next_exn_stamp ∧
      x = ([], ts.map (type_name_subst tenv.t), Texn_num)) ∨ FLOOKUP m s = some x := by
    intro s x hx
    rw [hlk] at hx
    split at hx
    · rename_i hs; cases hx; exact Or.inl ⟨hs, rfl⟩
    · exact Or.inr hx
  have hexn : ∀ s a b, FLOOKUP m s = some (a, b, Texn_num) → ∃ i, s = ExnStamp i := by
    intro s a b hx
    cases s with
    | ExnStamp i => exact ⟨i, rfl⟩
    | TypeStamp cn i => exact absurd (by simp [prim_type_nums]) (hg.1.2.2.1 _ _ _ _ _ hx)
  have hokm : ctMap_ok m' := by
    obtain ⟨c1, c2, c3, c4⟩ := hg.1
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro s x hx
      rcases hinv s x hx with ⟨rfl, rfl⟩ | hx
      · exact hcf
      · exact c1 s x hx
    · intro i a b ti hx
      rcases hinv _ _ hx with ⟨_, he⟩ | hx
      · cases he; exact ⟨rfl, rfl⟩
      · exact c2 _ _ _ _ hx
    · intro cn i a b ti hx
      rcases hinv _ _ hx with ⟨he, _⟩ | hx
      · cases he
      · exact c3 _ _ _ _ _ hx
    · rintro s1 a1 b1 ti s2 a2 b2 ⟨hx, hy⟩
      rcases hinv _ _ hx with ⟨rfl, he⟩ | hx <;> rcases hinv _ _ hy with ⟨rfl, he'⟩ | hy
      · trivial
      · cases he
        obtain ⟨i, rfl⟩ := hexn _ _ _ hy
        trivial
      · cases he'
        obtain ⟨i, rfl⟩ := hexn _ _ _ hx
        trivial
      · exact c4 _ _ _ _ _ _ _ ⟨hx, hy⟩
  have hty : ∀ cn i, FLOOKUP m' (TypeStamp cn i) = FLOOKUP m (TypeStamp cn i) := by
    intro cn i
    rw [hlk, if_neg (by simp)]
  have hgood : good_ctMap m' := by
    obtain ⟨_, ⟨b1, b2, b3⟩, ⟨e1, e2, e3, e4⟩, ⟨c1, c2, c3⟩⟩ := hg
    exact ⟨hokm, ⟨hw _ _ b1, hw _ _ b2, fun cn hcn => by rw [hty]; exact b3 cn hcn⟩,
      ⟨hw _ _ e1, hw _ _ e2, hw _ _ e3, hw _ _ e4⟩,
      ⟨hw _ _ c1, hw _ _ c2, fun cn hcn => by rw [hty]; exact c3 cn hcn⟩⟩
  have henv' : type_all_env m' S
      { v := nsEmpty, c := nsSing cn (ts.length, ExnStamp st.next_exn_stamp) }
      { v := nsEmpty, c := nsSing cn ([], ts.map (type_name_subst tenv.t), Texn_num),
        t := nsEmpty } := by
    refine ⟨(nsAll2_nsSing _ _ _ _ _).2 ⟨rfl, ?_, by simp⟩, nsAll2_nsEmpty _⟩
    rw [hlk, if_pos rfl]
  refine ⟨m', S, hweak, ?_, store_type_extension_refl _, henv', ?_, hgood, ?_,
    type_all_env_extend _ _ _ _ _ _
      ⟨henv', Aux.env_weak henv hweak (store_type_extension_refl _)⟩,
    type_s_weakening _ _ _ _ ⟨hs, hweak⟩⟩
  · rintro ti ⟨hx, hn⟩
    obtain ⟨s, a, b, hx⟩ := Aux.mem_ids.1 hx
    rcases hinv _ _ hx with ⟨_, he⟩ | hx
    · cases he
      exact absurd (Aux.mem_ids.2 ⟨_, _, _, hg.2.2.1.1⟩) hn
    · exact absurd (Aux.mem_ids.2 ⟨s, a, b, hx⟩) hn
  · exact extend_dec_tenv_ok _ _ ⟨⟨nsAll_nsEmpty _, (nsAll_nsSing _ _ _).2 hcf, nsAll_nsEmpty _⟩,
      hok⟩
  · refine ⟨Aux.disjoint_iff.2 fun _ h => False.elim h, fun cn' id => ⟨fun hx => ?_, fun hx => ?_⟩⟩
    · obtain ⟨x, hx⟩ := Aux.mem_FDOM.1 hx
      rw [hty] at hx
      exact (hcons.2 cn' id).1 (Aux.mem_FDOM.2 ⟨x, hx⟩)
    · obtain ⟨x, hx⟩ := Aux.mem_FDOM.1 hx
      show id < st.next_exn_stamp + 1
      rcases hinv _ _ hx with ⟨he, _⟩ | hx
      · cases he; omega
      · have := (hcons.2 cn' id).2 (Aux.mem_FDOM.2 ⟨x, hx⟩)
        omega

/-- Composition of two lists of declarations. -/
theorem Aux.dseq {st1 st2 : state ffi} {env env1 : sem_env value} {m : ctMap_ty}
    {S : tenv_store} {tenv tenv1 tenv2 : type_env} {d1 d2 : Set type_ident} {st : state ffi}
    {r2 : result (sem_env value) value}
    (h : type_sound_invariant st env m S (d1 ∪ d2) tenv) (hd : DISJOINT d1 d2)
    (h1 : Aux.dpost m S env tenv tenv1 d1 st1 (Rval env1))
    (h2 : ∀ m1 S1, type_sound_invariant st1 (extend_dec_env env1 env) m1 S1 d2
        (extend_dec_tenv tenv1 tenv) →
      Aux.dpost m1 S1 (extend_dec_env env1 env) (extend_dec_tenv tenv1 tenv) tenv2 d2 st2 r2) :
    ∃ (m1 m2 : ctMap_ty) (S1 S2 : tenv_store), weakCT m2 m ∧ weakCT m2 m1 ∧
      (Aux.ids m2 \ Aux.ids m) ⊆ (d1 ∪ d2) ∧
      store_type_extension S S2 ∧ store_type_extension S1 S2 ∧ type_all_env m1 S1 env1 tenv1 ∧
      Aux.dres m2 S2 (extend_dec_env env1 env) (extend_dec_tenv tenv1 tenv) tenv2 st2 r2 := by
  have hdis := Aux.tsi_disj h
  obtain ⟨m1, S1, a1, a2, a3, a4, a5⟩ := h1
  have ht : type_sound_invariant st1 (extend_dec_env env1 env) m1 S1 d2
      (extend_dec_tenv tenv1 tenv) := by
    refine Aux.tsi_ids a5 fun ti hti hx => ?_
    by_cases hm : ti ∈ Aux.ids m
    · exact hdis ti (Or.inr hti) hm
    · exact Aux.disjoint_iff.1 hd ti (a2 ti ⟨hx, hm⟩) hti
  obtain ⟨m2, S2, b1, b2, b3, b4⟩ := h2 m1 S1 ht
  refine ⟨m1, m2, S1, S2, weakCT_trans _ _ _ ⟨b1, a1⟩, b1, ?_,
    store_type_extension_trans _ _ _ ⟨a3, b3⟩, b3, a4, b4⟩
  rintro ti ⟨hx, hn⟩
  by_cases hm : ti ∈ Aux.ids m1
  · exact Or.inl (a2 ti ⟨hm, hn⟩)
  · exact Or.inr (b2 ti ⟨hx, hm⟩)

theorem Aux.dpost_sub {m : ctMap_ty} {S : tenv_store} {env : sem_env value}
    {tenv tenv1 tenv' : type_env} {d1 d2 : Set type_ident} {st' : state ffi}
    {e : error_result value}
    (h : Aux.dpost m S env tenv tenv1 d1 st' (Rerr e)) (hd : d1 ⊆ d2) :
    Aux.dpost m S env tenv tenv' d2 st' (Rerr e) := by
  obtain ⟨m1, S1, a1, a2, a3, a4⟩ := h
  refine ⟨m1, S1, a1, fun x hx => hd x (a2 x hx), a3, ?_⟩
  rcases e with v | _ | _ | _ <;> exact a4

theorem Aux.decs_sound :
    (∀ (st : state ffi) (env : sem_env value) (es : List exp), True) ∧
    (∀ (st : state ffi) (env : sem_env value) (v : value) (pes : List (pat × exp))
      (err_v : value), True) ∧
    (∀ (st : state ffi) (env : sem_env value) (ds : List dec),
      ∀ (st' : state ffi) (r : result (sem_env value) value) (m : ctMap_ty) (S : tenv_store)
        (tenv : type_env) (tids : Set type_ident) (tenv' : type_env),
        evaluate_decs st env ds = (st', r) → type_ds false tenv ds tids tenv' →
        type_sound_invariant st env m S tids tenv →
        Aux.dpost m S env tenv tenv' tids st' r) := by
  apply Aux.full_evaluate_ind
  case dnil =>
    intro st env st' r m S tenv tids tenv' he ht h
    rw [evaluate_decs] at he
    cases he
    obtain ⟨rfl, rfl⟩ := (type_ds_empty _ _ _ _).1 ht
    exact Aux.dpost_val h tenv_ok_empty (store_type_extension_refl _) h.2.2.2.2 (Nat.le_refl _)
      (Nat.le_refl _) ⟨nsAll2_nsEmpty _, nsAll2_nsEmpty _⟩
  case dcons2 =>
    intro st env d1 d2 ds ih1 ih2 st' r m S tenv tids tenv' he ht h
    cases ht with
    | cons _ _ _ tenv1 tenv2 t1 t2 h1 h2 h3 =>
      rw [Aux.evaluate_decs_cons2] at he
      have hsub := fun st1 r1 hev => ih1 st1 r1 m S tenv t1 tenv1 hev
        ((type_ds_sing _ _ _ _ _).2 h1) (type_sound_invariant_union _ _ _ _ _ _ _ h)
      rcases hev : evaluate_decs st env [d1] with ⟨st1, env1 | e⟩
      · rw [hev] at he
        dsimp only at he
        rcases hev2 : evaluate_decs st1 (extend_dec_env env1 env) (d2 :: ds) with ⟨st2, r2⟩
        rw [hev2] at he
        cases he
        obtain ⟨m1, m2, S1, S2, c1, c2, c3, c4, c5, c6, c7⟩ := Aux.dseq h h3 (hsub _ _ hev)
          (fun m1 S1 ht1 => ih2 _ _ hev st2 r2 m1 S1 _ _ _ hev2 h2 ht1)
        refine ⟨m2, S2, c1, c3, c4, ?_⟩
        rcases r2 with env2 | v | _ | _ | _
        · refine ⟨type_all_env_extend _ _ _ _ _ _ ⟨c7.1, Aux.env_weak c6 c2 c5⟩, ?_⟩
          have := c7.2
          rw [extend_dec_env_assoc, extend_dec_tenv_assoc] at this
          exact this
        · exact ⟨c7.1, h.1, c7.2.2.1, c7.2.2.2.1, Aux.env_weak h.2.2.2.1 c1 c4, c7.2.2.2.2.2⟩
        · exact c7
        · trivial
        · trivial
      · rw [hev] at he
        cases he
        exact Aux.dpost_sub (hsub _ _ hev) (fun _ hx => Or.inl hx)
  case dlet =>
    intro st env l p e _ st' r m S tenv tids tenv' he ht h
    have ht := (type_ds_sing _ _ _ _ _).1 ht
    cases ht with
    | dlet_poly tvs _ _ _ t b _ h1 h2 h3 h4 _ =>
      exact Aux.dlet_sound he h (fun _ => h1) h2 h3 h4
    | dlet_mono _ _ _ t b _ _ h2 h3 h4 =>
      exact Aux.dlet_sound he h (fun hn => absurd rfl hn) h2 h3 (by rw [bind_tvar0]; exact h4)
  case dletrec =>
    intro st env l funs st' r m S tenv tids tenv' he ht h
    have ht := (type_ds_sing _ _ _ _ _).1 ht
    have hok := type_d_tenv_ok_helper.1 _ _ _ _ _ ht h.1
    cases ht with
    | dletrec _ _ b tvs _ h1 _ =>
      have hd := type_funs_distinct _ _ _ _ h1
      have hck := (type_e_con_check m env.c).2.2 _ _ _ _ h1 h.2.2.2.1.1
      rw [evaluate_decs, if_pos ⟨hd, hck⟩] at he
      cases he
      refine Aux.dpost_val h hok (store_type_extension_refl _) h.2.2.2.2 (Nat.le_refl _)
        (Nat.le_refl _) ⟨nsAll2_nsEmpty _, ?_⟩
      rw [build_rec_env_merge funs () env nsEmpty, (nsAppend_nsEmpty _).1]
      exact nsAll2_alist_to_ns (fun _ v (p : Nat × typ) => type_v p.1 m S v p.2) _ _
        (type_recfun_env funs m S tvs tenv tenv_val_exp.Empty env b
          ⟨h.1, h.2.2.2.1, trivial, rfl, h1, hd⟩)
  case dtype =>
    intro st env l tds st' r m S tenv tids tenv' he ht h
    have ht := (type_ds_sing _ _ _ _ _).1 ht
    cases ht with
    | dtype _ _ ids tenvT _ h1 h2 h3 h4 h5 =>
      rw [evaluate_decs, if_pos (check_ctor_tenv_dups _ _ h3)] at he
      cases he
      exact Aux.dtype_sound h h1 h2 h3 h4 (by rw [h5]; exact Aux.tenvT_ok)
  case dtabbrev =>
    intro st env l tvs tn t st' r m S tenv tids tenv' he ht h
    have ht := (type_ds_sing _ _ _ _ _).1 ht
    have hok := type_d_tenv_ok_helper.1 _ _ _ _ _ ht h.1
    rw [evaluate_decs] at he
    cases he
    cases ht with
    | dtabbrev _ _ _ _ _ h1 h2 h3 =>
      exact Aux.dpost_val h hok (store_type_extension_refl _) h.2.2.2.2 (Nat.le_refl _)
        (Nat.le_refl _) ⟨nsAll2_nsEmpty _, nsAll2_nsEmpty _⟩
  case denv =>
    intro st env n st' r m S tenv tids tenv' he ht h
    have ht := (type_ds_sing _ _ _ _ _).1 ht
    cases ht
  case dexn =>
    intro st env l cn ts st' r m S tenv tids tenv' he ht h
    have ht := (type_ds_sing _ _ _ _ _).1 ht
    rw [evaluate_decs] at he
    cases he
    cases ht with
    | dexn _ _ _ _ h1 h2 => exact Aux.dexn_sound h h1 h2
  case dmod =>
    intro st env mn ds ih st' r m S tenv tids tenv' he ht h
    have ht := (type_ds_sing _ _ _ _ _).1 ht
    have hok := type_d_tenv_ok_helper.1 _ _ _ _ _ ht h.1
    rw [evaluate_decs] at he
    cases ht with
    | dmod _ _ _ _ tenv1 h1 =>
      rcases hev : evaluate_decs st env ds with ⟨st1, r1⟩
      rw [hev] at he
      cases he
      have hsub := ih _ _ m S tenv tids tenv1 hev h1 h
      rcases r1 with env1 | e
      · obtain ⟨m1, S1, a1, a2, a3, a4, a5⟩ := hsub
        have henv' : type_all_env m1 S1 { v := nsLift mn env1.v, c := nsLift mn env1.c }
            (tenvLift mn tenv1) := by
          refine ⟨(nsAll2_nsLift _ _ _ _).2 (nsAll2_mono ?_ a4.1),
            (nsAll2_nsLift _ _ _ _).2 a4.2⟩
          rintro id ⟨n, s⟩ ⟨tvs, ts, ti⟩ hh
          exact hh
        exact ⟨m1, S1, a1, a2, a3, henv', extend_dec_tenv_ok _ _ ⟨hok, h.1⟩, a5.2.1, a5.2.2.1,
          type_all_env_extend _ _ _ _ _ _ ⟨henv', Aux.env_weak h.2.2.2.1 a1 a3⟩, a5.2.2.2.2⟩
      · exact Aux.dpost_sub hsub (fun _ hx => hx)
  case dlocal =>
    intro st env lds ds ih1 ih2 st' r m S tenv tids tenv' he ht h
    have ht := (type_ds_sing _ _ _ _ _).1 ht
    cases ht with
    | dlocal _ _ _ tenv1 _ t1 t2 h1 h2 h3 =>
      rw [Aux.evaluate_decs_Dlocal] at he
      have hsub := fun st1 r1 hev => ih1 st1 r1 m S tenv t1 tenv1 hev h1
        (type_sound_invariant_union _ _ _ _ _ _ _ h)
      rcases hev : evaluate_decs st env lds with ⟨st1, env1 | e⟩
      · rw [hev] at he
        dsimp only at he
        obtain ⟨m1, m2, S1, S2, c1, c2, c3, c4, c5, c6, c7⟩ := Aux.dseq h h3 (hsub _ _ hev)
          (fun m1 S1 ht1 => ih2 _ _ hev st' r m1 S1 _ _ _ he h2 ht1)
        refine ⟨m2, S2, c1, c3, c4, ?_⟩
        have hok1 := type_d_tenv_ok_helper.2 _ _ _ _ _ h1 h.1
        have hok2 := type_d_tenv_ok_helper.2 _ _ _ _ _ h2 (extend_dec_tenv_ok _ _ ⟨hok1, h.1⟩)
        rcases r with env2 | v | _ | _ | _
        · exact ⟨c7.1, extend_dec_tenv_ok _ _ ⟨hok2, h.1⟩, c7.2.2.1, c7.2.2.2.1,
            type_all_env_extend _ _ _ _ _ _ ⟨c7.1, Aux.env_weak h.2.2.2.1 c1 c4⟩, c7.2.2.2.2.2⟩
        · exact ⟨c7.1, h.1, c7.2.2.1, c7.2.2.2.1, Aux.env_weak h.2.2.2.1 c1 c4, c7.2.2.2.2.2⟩
        · exact c7
        · trivial
        · trivial
      · rw [hev] at he
        cases he
        exact Aux.dpost_sub (hsub _ _ hev) (fun _ hx => Or.inl hx)
  all_goals intros; trivial

end decs_sound

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
          | Rerr (Rabort (Rffi_error _)) => True) := by
  rintro st env ds st' r m S tenv tids tenv' ⟨he, ht, h⟩
  obtain ⟨m', S', a1, a2, a3, a4⟩ := Aux.decs_sound.2.2 st env ds st' r m S tenv tids tenv' he ht h
  refine ⟨m', S', a1, a2, a3, ?_⟩
  rcases r with v | v | (_ | _ | _) <;> exact a4

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
          | Rerr (Rabort Rtimeout_error) => True) := by
  rintro st env ds c st' r m S tenv tids tenv' ⟨he, ht, h⟩
  obtain ⟨m', S', a1, a2, a3, a4⟩ := decs_type_sound_no_check st env ds st' r m S tenv tids tenv'
    ⟨he, type_d_check_uniq.2 _ _ _ _ _ ht, h⟩
  refine ⟨m', S', a1, a2, a3, ?_⟩
  rcases r with v | v | (_ | _ | _) <;> exact a4

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
      r ≠ Fail := by
  rintro st env tops r c m S tenv tenv' tids ⟨hs, ht, h⟩ rfl
  obtain ⟨k, hk⟩ := hs
  rcases hev : evaluate_decs { st with clock := k } env tops with ⟨st', r⟩
  have hr : (evaluate_prog_with_clock st env k tops).2 = r := by
    unfold evaluate_prog_with_clock
    rw [hev]
  rw [hr] at hk
  subst hk
  obtain ⟨_, _, _, _, _, h4⟩ := decs_type_sound { st with clock := k } env tops c st' _ m S tenv
    tids tenv' ⟨hev, ht, h⟩
  exact h4

end

end CmlTS
