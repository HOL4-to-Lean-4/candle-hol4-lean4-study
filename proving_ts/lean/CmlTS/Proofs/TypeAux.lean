import CmlTS.Proofs.Lib
import CmlTS.TypeSoundInvariants

/-! Induction principles and basic lemmas for types and the typing relations. -/

namespace CmlTS

open scoped Classical

variable {α β γ : Type}

/-! ### types -/

theorem Aux.typ_ind {P : typ → Prop} (tvar : ∀ tv, P (Tvar tv)) (db : ∀ n, P (Tvar_db n))
    (app : ∀ ts ti, (∀ t, t ∈ ts → P t) → P (Tapp ts ti)) : ∀ t, P t
  | Tvar tv => tvar tv
  | Tvar_db n => db n
  | Tapp ts ti => app ts ti fun t _ => Aux.typ_ind tvar db app t
termination_by t => sizeOf t

theorem Aux.ast_ind {P : ast_t → Prop} (tvar : ∀ tv, P (Atvar tv))
    (fn : ∀ t1 t2, P t1 → P t2 → P (Atfun t1 t2))
    (tup : ∀ ts, (∀ t, t ∈ ts → P t) → P (Attup ts))
    (app : ∀ ts ti, (∀ t, t ∈ ts → P t) → P (Atapp ts ti)) : ∀ t, P t
  | Atvar tv => tvar tv
  | Atfun t1 t2 => fn t1 t2 (Aux.ast_ind tvar fn tup app t1) (Aux.ast_ind tvar fn tup app t2)
  | Attup ts => tup ts fun t _ => Aux.ast_ind tvar fn tup app t
  | Atapp ts ti => app ts ti fun t _ => Aux.ast_ind tvar fn tup app t
termination_by t => sizeOf t

theorem Aux.cf_app {n : Nat} {tvs : List mlstring} {ts : List typ} {ti : type_ident} :
    check_freevars n tvs (Tapp ts ti) ↔ ∀ t, t ∈ ts → check_freevars n tvs t := by
  rw [check_freevars, EVERY_iff_forall]

theorem Aux.cf_var {n : Nat} {tvs : List mlstring} {tv : mlstring} :
    check_freevars n tvs (Tvar tv) ↔ tv ∈ tvs := by
  rw [check_freevars]

theorem Aux.cf_db {n : Nat} {tvs : List mlstring} {m : Nat} :
    check_freevars n tvs (Tvar_db m) ↔ m < n := by
  rw [check_freevars]

theorem Aux.ts_app {s : fmap mlstring typ} {ts : List typ} {ti : type_ident} :
    type_subst s (Tapp ts ti) = Tapp (ts.map (type_subst s)) ti := by
  rw [type_subst]

theorem Aux.inc_app {sk n : Nat} {ts : List typ} {ti : type_ident} :
    deBruijn_inc sk n (Tapp ts ti) = Tapp (ts.map (deBruijn_inc sk n)) ti := by
  rw [deBruijn_inc]

theorem Aux.inc_var {sk n : Nat} {tv : mlstring} : deBruijn_inc sk n (Tvar tv) = Tvar tv := by
  rw [deBruijn_inc]

theorem Aux.inc_db {sk n m : Nat} :
    deBruijn_inc sk n (Tvar_db m) = if m < sk then Tvar_db m else Tvar_db (m + n) := by
  rw [deBruijn_inc]

theorem Aux.inc_db_lt {sk n m : Nat} (h : m < sk) :
    deBruijn_inc sk n (Tvar_db m) = Tvar_db m := by
  rw [deBruijn_inc, if_pos h]

theorem Aux.inc_db_ge {sk n m : Nat} (h : sk ≤ m) :
    deBruijn_inc sk n (Tvar_db m) = Tvar_db (m + n) := by
  rw [deBruijn_inc, if_neg (by omega)]

theorem Aux.sub_app {sk : Nat} {targs ts : List typ} {ti : type_ident} :
    deBruijn_subst sk targs (Tapp ts ti) = Tapp (ts.map (deBruijn_subst sk targs)) ti := by
  rw [deBruijn_subst]

theorem Aux.sub_var {sk : Nat} {targs : List typ} {tv : mlstring} :
    deBruijn_subst sk targs (Tvar tv) = Tvar tv := by
  rw [deBruijn_subst]

theorem Aux.sub_db_lt {sk n : Nat} {targs : List typ} (h : n < sk) :
    deBruijn_subst sk targs (Tvar_db n) = Tvar_db n := by
  rw [deBruijn_subst, if_neg (by omega), if_neg (by omega)]

theorem Aux.sub_db_mid {sk n : Nat} {targs : List typ} (h : sk ≤ n)
    (h2 : n < targs.length + sk) :
    deBruijn_subst sk targs (Tvar_db n) = EL (n - sk) targs := by
  rw [deBruijn_subst, if_pos (by omega)]

theorem Aux.sub_db_ge {sk n : Nat} {targs : List typ} (h2 : targs.length + sk ≤ n) :
    deBruijn_subst sk targs (Tvar_db n) = Tvar_db (n - targs.length) := by
  rw [deBruijn_subst, if_neg (by omega), if_pos (by omega)]

theorem Aux.COUNT_LIST_eq (n : Nat) : COUNT_LIST n = List.range n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [COUNT_LIST, ih, List.range_succ_eq_map]

theorem Aux.ALOOKUP_zip_map (f : β → γ) (l1 : List α) (l2 : List β) (k : α) :
    ALOOKUP (l1.zip (l2.map f)) k = (ALOOKUP (l1.zip l2) k).map f := by
  rw [← Aux.ALOOKUP_map, List.zip_map_right]
  rfl

theorem Aux.ALOOKUP_zip_some {l1 : List α} {l2 : List β} {k : α} (hl : l1.length = l2.length)
    (hk : k ∈ l1) : ∃ x, ALOOKUP (l1.zip l2) k = some x ∧ x ∈ l2 := by
  cases h : ALOOKUP (l1.zip l2) k with
  | none =>
    rw [Aux.ALOOKUP_eq_none, List.map_fst_zip (by omega)] at h
    exact absurd hk h
  | some x => exact ⟨x, rfl, (List.of_mem_zip (Aux.ALOOKUP_mem h)).2⟩

theorem Aux.ts_var_zip {l1 : List mlstring} {l2 : List typ} {k : mlstring} {x : typ}
    (h : ALOOKUP (l1.zip l2) k = some x) :
    type_subst (alist_to_fmap (l1.zip l2)) (Tvar k) = x := by
  rw [type_subst, Aux.FLOOKUP_alist_to_fmap, h]

theorem Aux.type_subst_comm (f : typ → typ) (hf : ∀ ts ti, f (Tapp ts ti) = Tapp (ts.map f) ti)
    {tvs : List mlstring} {ts : List typ} (hl : tvs.length = ts.length) (t : typ)
    (ht : check_freevars 0 tvs t) :
    f (type_subst (alist_to_fmap (tvs.zip ts)) t) =
      type_subst (alist_to_fmap (tvs.zip (ts.map f))) t := by
  induction t using Aux.typ_ind with
  | tvar tv =>
    obtain ⟨x, hx, _⟩ := Aux.ALOOKUP_zip_some hl (Aux.cf_var.1 ht)
    rw [Aux.ts_var_zip hx, Aux.ts_var_zip (x := f x)]
    rw [Aux.ALOOKUP_zip_map, hx]; rfl
  | db n => exact absurd (Aux.cf_db.1 ht) (by omega)
  | app ts' ti ih =>
    rw [Aux.ts_app, Aux.ts_app, hf, List.map_map]
    congr 1
    exact List.map_congr_left fun t h => ih t h (Aux.cf_app.1 ht t h)

theorem Aux.FUPDATE_LIST_reverse (l : List (α × β)) :
    FUPDATE_LIST FEMPTY l.reverse = alist_to_fmap l := by
  refine Aux.fmap_ext fun x => ?_
  rw [Aux.FLOOKUP_FUPDATE_LIST, Aux.FLOOKUP_alist_to_fmap, List.reverse_reverse]
  cases ALOOKUP l x <;> rfl

theorem Aux.EVERY_map {P : β → Prop} {f : α → β} {l : List α} :
    EVERY P (l.map f) ↔ ∀ x, x ∈ l → P (f x) := by
  rw [EVERY_map_aux, EVERY_iff_forall]

/-! ### `LIST_REL` -/

theorem Aux.LIST_REL_length {R : α → β → Prop} {l1 : List α} {l2 : List β}
    (h : LIST_REL R l1 l2) : l1.length = l2.length := (LIST_REL_iff_aux.1 h).1

theorem Aux.LIST_REL_mono {R S : α → β → Prop} {l1 : List α} {l2 : List β}
    (hRS : ∀ a b, a ∈ l1 → b ∈ l2 → R a b → S a b) (h : LIST_REL R l1 l2) : LIST_REL S l1 l2 := by
  rw [LIST_REL_iff_aux] at h ⊢
  refine ⟨h.1, fun i a b ha hb => hRS a b ?_ ?_ (h.2 i a b ha hb)⟩
  · exact List.mem_of_getElem? ha
  · exact List.mem_of_getElem? hb

theorem Aux.LIST_REL_map_right {R : α → γ → Prop} {f : β → γ} {l1 : List α} {l2 : List β} :
    LIST_REL R l1 (l2.map f) ↔ LIST_REL (fun a b => R a (f b)) l1 l2 := by
  induction l1 generalizing l2 with
  | nil => cases l2 <;> simp [LIST_REL]
  | cons a l1 ih => cases l2 <;> simp [LIST_REL, ih]

theorem Aux.LIST_REL_map_left {R : γ → β → Prop} {f : α → γ} {l1 : List α} {l2 : List β} :
    LIST_REL R (l1.map f) l2 ↔ LIST_REL (fun a b => R (f a) b) l1 l2 := by
  induction l1 generalizing l2 with
  | nil => cases l2 <;> simp [LIST_REL]
  | cons a l1 ih => cases l2 <;> simp [LIST_REL, ih]

theorem Aux.LIST_REL_append {R : α → β → Prop} {l1 l1' : List α} {l2 l2' : List β}
    (h : LIST_REL R l1 l2) (h' : LIST_REL R l1' l2') : LIST_REL R (l1 ++ l1') (l2 ++ l2') := by
  induction l1 generalizing l2 with
  | nil =>
    cases l2 with
    | nil => exact h'
    | cons b l2 => exact h.elim
  | cons a l1 ih =>
    cases l2 with
    | nil => exact h.elim
    | cons b l2 => exact ⟨h.1, ih h.2⟩

theorem Aux.LIST_REL_reverse {R : α → β → Prop} {l1 : List α} {l2 : List β}
    (h : LIST_REL R l1 l2) : LIST_REL R l1.reverse l2.reverse := by
  induction l1 generalizing l2 with
  | nil =>
    cases l2 with
    | nil => exact trivial
    | cons b l2 => exact h.elim
  | cons a l1 ih =>
    cases l2 with
    | nil => exact h.elim
    | cons b l2 =>
      rw [List.reverse_cons, List.reverse_cons]
      exact Aux.LIST_REL_append (ih h.2) ⟨h.1, trivial⟩

theorem Aux.LIST_REL_refl_iff {R : α → α → Prop} {l : List α} :
    LIST_REL R l l ↔ ∀ x, x ∈ l → R x x := by
  induction l with
  | nil => simp [LIST_REL]
  | cons a l ih => simp [LIST_REL, ih]

theorem Aux.LIST_REL_mem_left {R : α → β → Prop} {l1 : List α} {l2 : List β} {a : α}
    (h : LIST_REL R l1 l2) (ha : a ∈ l1) : ∃ b, b ∈ l2 ∧ R a b := by
  induction l1 generalizing l2 with
  | nil => cases ha
  | cons x l1 ih =>
    cases l2 with
    | nil => exact h.elim
    | cons y l2 =>
      rcases List.mem_cons.1 ha with rfl | ha
      · exact ⟨y, List.mem_cons_self, h.1⟩
      · obtain ⟨b, hb, hr⟩ := ih h.2 ha
        exact ⟨b, List.mem_cons_of_mem _ hb, hr⟩

theorem Aux.LIST_REL_mem_right {R : α → β → Prop} {l1 : List α} {l2 : List β} {b : β}
    (h : LIST_REL R l1 l2) (hb : b ∈ l2) : ∃ a, a ∈ l1 ∧ R a b := by
  induction l1 generalizing l2 with
  | nil =>
    cases l2 with
    | nil => cases hb
    | cons y l2 => exact h.elim
  | cons x l1 ih =>
    cases l2 with
    | nil => exact h.elim
    | cons y l2 =>
      rcases List.mem_cons.1 hb with rfl | hb
      · exact ⟨x, List.mem_cons_self, h.1⟩
      · obtain ⟨a, ha, hr⟩ := ih h.2 hb
        exact ⟨a, List.mem_cons_of_mem _ ha, hr⟩

/-! ### induction on the typing relations -/

theorem Aux.type_p_ind {P : Nat → type_env → pat → typ → List (varN × typ) → Prop}
    {Q : Nat → type_env → List pat → List typ → List (varN × typ) → Prop}
    (any : ∀ tvs tenv t, check_freevars tvs [] t → P tvs tenv Pany t [])
    (var : ∀ tvs tenv n t, check_freevars tvs [] t → P tvs tenv (Pvar n) t [(n, t)])
    (intLit : ∀ tvs tenv n, P tvs tenv (Plit (lit.IntLit n)) Tint [])
    (char : ∀ tvs tenv c, P tvs tenv (Plit (lit.Char c)) Tchar [])
    (strLit : ∀ tvs tenv s, P tvs tenv (Plit (lit.StrLit s)) Tstring [])
    (word8 : ∀ tvs tenv w, P tvs tenv (Plit (lit.Word8 w)) Tword8 [])
    (word64 : ∀ tvs tenv w, P tvs tenv (Plit (lit.Word64 w)) Tword64 [])
    (con : ∀ (tvs : Nat) (tenv : type_env) (cn : ident modN conN) (ps : List pat) (ts : List typ)
      (tvs' : List tvarN) (tn : type_ident) (ts' : List typ) (bindings : List (varN × typ)),
      EVERY (check_freevars tvs []) ts' → ts'.length = tvs'.length →
      type_ps tvs tenv ps (ts.map (type_subst (alist_to_fmap (tvs'.zip ts')))) bindings →
      Q tvs tenv ps (ts.map (type_subst (alist_to_fmap (tvs'.zip ts')))) bindings →
      nsLookup tenv.c cn = some (tvs', ts, tn) →
      P tvs tenv (Pcon (some cn) ps) (Tapp ts' tn) bindings)
    (tup : ∀ tvs tenv ps ts bindings, type_ps tvs tenv ps ts bindings →
      Q tvs tenv ps ts bindings → P tvs tenv (Pcon none ps) (Ttup ts) bindings)
    (ref : ∀ tvs tenv p t bindings, type_p tvs tenv p t bindings →
      P tvs tenv p t bindings → P tvs tenv (Pref p) (Tref t) bindings)
    (pas : ∀ tvs tenv p v t bindings, type_p tvs tenv p t bindings →
      P tvs tenv p t bindings → P tvs tenv (Pas p v) t (bindings ++ [(v, t)]))
    (tannot : ∀ tvs tenv p t bindings, check_freevars_ast [] t → check_type_names tenv.t t →
      type_p tvs tenv p (type_name_subst tenv.t t) bindings →
      P tvs tenv p (type_name_subst tenv.t t) bindings →
      P tvs tenv (Ptannot p t) (type_name_subst tenv.t t) bindings)
    (nil : ∀ tvs tenv, Q tvs tenv [] [] [])
    (cons : ∀ tvs tenv p ps t ts bindings bindings', type_p tvs tenv p t bindings →
      type_ps tvs tenv ps ts bindings' → P tvs tenv p t bindings →
      Q tvs tenv ps ts bindings' → Q tvs tenv (p :: ps) (t :: ts) (bindings' ++ bindings)) :
    (∀ tvs tenv p t bindings, type_p tvs tenv p t bindings → P tvs tenv p t bindings) ∧
    (∀ tvs tenv ps ts bindings, type_ps tvs tenv ps ts bindings → Q tvs tenv ps ts bindings) := by
  constructor
  · intro tvs tenv p t bindings h
    exact type_p.rec (motive_1 := fun c d e _ => P tvs tenv c d e)
      (motive_2 := fun c d e _ => Q tvs tenv c d e)
      (any tvs tenv) (var tvs tenv) (intLit tvs tenv) (char tvs tenv) (strLit tvs tenv)
      (word8 tvs tenv) (word64 tvs tenv)
      (fun cn ps ts tvs' tn ts' b h1 h2 h3 h4 ih => con tvs tenv cn ps ts tvs' tn ts' b h1 h2 h3 ih h4)
      (tup tvs tenv) (ref tvs tenv) (pas tvs tenv) (tannot tvs tenv)
      (nil tvs tenv) (cons tvs tenv) h
  · intro tvs tenv p t bindings h
    exact type_ps.rec (motive_1 := fun c d e _ => P tvs tenv c d e)
      (motive_2 := fun c d e _ => Q tvs tenv c d e)
      (any tvs tenv) (var tvs tenv) (intLit tvs tenv) (char tvs tenv) (strLit tvs tenv)
      (word8 tvs tenv) (word64 tvs tenv)
      (fun cn ps ts tvs' tn ts' b h1 h2 h3 h4 ih => con tvs tenv cn ps ts tvs' tn ts' b h1 h2 h3 ih h4)
      (tup tvs tenv) (ref tvs tenv) (pas tvs tenv) (tannot tvs tenv)
      (nil tvs tenv) (cons tvs tenv) h

theorem Aux.type_e_ind {P : type_env → tenv_val_exp → exp → typ → Prop}
    {Q : type_env → tenv_val_exp → List exp → List typ → Prop}
    {R : type_env → tenv_val_exp → List (varN × varN × exp) → List (varN × typ) → Prop}
    (intLit : ∀ tenv tenvE n, P tenv tenvE (exp.Lit (lit.IntLit n)) Tint)
    (char : ∀ tenv tenvE c, P tenv tenvE (exp.Lit (lit.Char c)) Tchar)
    (strLit : ∀ tenv tenvE s, P tenv tenvE (exp.Lit (lit.StrLit s)) Tstring)
    (word8 : ∀ tenv tenvE w, P tenv tenvE (exp.Lit (lit.Word8 w)) Tword8)
    (word64 : ∀ tenv tenvE w, P tenv tenvE (exp.Lit (lit.Word64 w)) Tword64)
    (float64 : ∀ tenv tenvE w, P tenv tenvE (exp.Lit (lit.Float64 w)) Tdouble)
    (raise : ∀ tenv tenvE e t, check_freevars (num_tvs tenvE) [] t → type_e tenv tenvE e Texn →
      P tenv tenvE e Texn → P tenv tenvE (exp.Raise e) t)
    (handle : ∀ tenv tenvE e pes t (bs : pat × exp → List (varN × typ)),
      type_e tenv tenvE e t → ¬ pes = [] →
      (∀ pe, pe ∈ pes → ALL_DISTINCT (pat_bindings pe.1 [])) →
      (∀ pe, pe ∈ pes → type_p (num_tvs tenvE) tenv pe.1 Texn (bs pe)) →
      (∀ pe, pe ∈ pes → type_e tenv (bind_var_list 0 (bs pe) tenvE) pe.2 t) →
      P tenv tenvE e t →
      (∀ pe, pe ∈ pes → P tenv (bind_var_list 0 (bs pe) tenvE) pe.2 t) →
      P tenv tenvE (exp.Handle e pes) t)
    (con : ∀ tenv tenvE (cn : ident modN conN) es (tvs : List tvarN) (tn : type_ident)
      (ts' ts : List typ),
      EVERY (check_freevars (num_tvs tenvE) []) ts' → tvs.length = ts'.length →
      type_es tenv tenvE es (ts.map (type_subst (alist_to_fmap (tvs.zip ts')))) →
      nsLookup tenv.c cn = some (tvs, ts, tn) →
      Q tenv tenvE es (ts.map (type_subst (alist_to_fmap (tvs.zip ts')))) →
      P tenv tenvE (exp.Con (some cn) es) (Tapp ts' tn))
    (tup : ∀ tenv tenvE es ts, type_es tenv tenvE es ts → Q tenv tenvE es ts →
      P tenv tenvE (exp.Con none es) (Ttup ts))
    (var : ∀ tenv tenvE n t (targs : List typ) tvs, tvs = targs.length →
      EVERY (check_freevars (num_tvs tenvE) []) targs →
      lookup_var n tenvE tenv = some (tvs, t) →
      P tenv tenvE (exp.Var n) (deBruijn_subst 0 targs t))
    (fn : ∀ tenv tenvE n e t1 t2, check_freevars (num_tvs tenvE) [] t1 →
      type_e tenv (Bind_name n 0 t1 tenvE) e t2 → P tenv (Bind_name n 0 t1 tenvE) e t2 →
      P tenv tenvE (exp.Fun n e) (Tfn t1 t2))
    (app : ∀ tenv tenvE o es ts t, type_es tenv tenvE es ts → type_op o ts t →
      check_freevars (num_tvs tenvE) [] t → Q tenv tenvE es ts → P tenv tenvE (exp.App o es) t)
    (log : ∀ tenv tenvE l e1 e2, type_e tenv tenvE e1 Tbool → type_e tenv tenvE e2 Tbool →
      P tenv tenvE e1 Tbool → P tenv tenvE e2 Tbool → P tenv tenvE (exp.Log l e1 e2) Tbool)
    (ite : ∀ tenv tenvE e1 e2 e3 t, type_e tenv tenvE e1 Tbool → type_e tenv tenvE e2 t →
      type_e tenv tenvE e3 t → P tenv tenvE e1 Tbool → P tenv tenvE e2 t → P tenv tenvE e3 t →
      P tenv tenvE (exp.If e1 e2 e3) t)
    (mat : ∀ tenv tenvE e pes t1 t2 (bs : pat × exp → List (varN × typ)),
      type_e tenv tenvE e t1 → ¬ pes = [] →
      (∀ pe, pe ∈ pes → ALL_DISTINCT (pat_bindings pe.1 [])) →
      (∀ pe, pe ∈ pes → type_p (num_tvs tenvE) tenv pe.1 t1 (bs pe)) →
      (∀ pe, pe ∈ pes → type_e tenv (bind_var_list 0 (bs pe) tenvE) pe.2 t2) →
      P tenv tenvE e t1 →
      (∀ pe, pe ∈ pes → P tenv (bind_var_list 0 (bs pe) tenvE) pe.2 t2) →
      P tenv tenvE (exp.Mat e pes) t2)
    (letc : ∀ tenv tenvE n e1 e2 t1 t2, type_e tenv tenvE e1 t1 →
      type_e tenv (opt_bind_name n 0 t1 tenvE) e2 t2 → P tenv tenvE e1 t1 →
      P tenv (opt_bind_name n 0 t1 tenvE) e2 t2 → P tenv tenvE (exp.Let n e1 e2) t2)
    (letrec : ∀ tenv tenvE funs e t bindings,
      type_funs tenv (bind_var_list 0 bindings tenvE) funs bindings →
      type_e tenv (bind_var_list 0 bindings tenvE) e t →
      R tenv (bind_var_list 0 bindings tenvE) funs bindings →
      P tenv (bind_var_list 0 bindings tenvE) e t → P tenv tenvE (exp.Letrec funs e) t)
    (tannot : ∀ tenv tenvE e t, check_freevars_ast [] t → check_type_names tenv.t t →
      type_e tenv tenvE e (type_name_subst tenv.t t) → P tenv tenvE e (type_name_subst tenv.t t) →
      P tenv tenvE (exp.Tannot e t) (type_name_subst tenv.t t))
    (lannot : ∀ tenv tenvE e l t, type_e tenv tenvE e t → P tenv tenvE e t →
      P tenv tenvE (exp.Lannot e l) t)
    (nil : ∀ tenv tenvE, Q tenv tenvE [] [])
    (cons : ∀ tenv tenvE e es t ts, type_e tenv tenvE e t → type_es tenv tenvE es ts →
      P tenv tenvE e t → Q tenv tenvE es ts → Q tenv tenvE (e :: es) (t :: ts))
    (fnil : ∀ tenv tenvE, R tenv tenvE [] [])
    (fcons : ∀ tenv tenvE fn n e funs bindings t1 t2,
      check_freevars (num_tvs tenvE) [] (Tfn t1 t2) → type_e tenv (Bind_name n 0 t1 tenvE) e t2 →
      type_funs tenv tenvE funs bindings → ALOOKUP bindings fn = none →
      P tenv (Bind_name n 0 t1 tenvE) e t2 → R tenv tenvE funs bindings →
      R tenv tenvE ((fn, n, e) :: funs) ((fn, Tfn t1 t2) :: bindings)) :
    (∀ tenv tenvE e t, type_e tenv tenvE e t → P tenv tenvE e t) ∧
    (∀ tenv tenvE es ts, type_es tenv tenvE es ts → Q tenv tenvE es ts) ∧
    (∀ tenv tenvE funs bindings, type_funs tenv tenvE funs bindings →
      R tenv tenvE funs bindings) := by
  refine ⟨?_, ?_, ?_⟩
  · intro a b c d h
    exact type_e.rec (motive_1 := fun b c d _ => P a b c d)
      (motive_2 := fun b c d _ => Q a b c d) (motive_3 := fun b c d _ => R a b c d)
      (intLit a) (char a) (strLit a) (word8 a) (word64 a) (float64 a) (raise a) (handle a)
      (con a) (tup a) (var a) (fn a) (app a) (log a) (ite a) (mat a) (letc a) (letrec a)
      (tannot a) (lannot a) (nil a) (cons a) (fnil a) (fcons a) h
  · intro a b c d h
    exact type_es.rec (motive_1 := fun b c d _ => P a b c d)
      (motive_2 := fun b c d _ => Q a b c d) (motive_3 := fun b c d _ => R a b c d)
      (intLit a) (char a) (strLit a) (word8 a) (word64 a) (float64 a) (raise a) (handle a)
      (con a) (tup a) (var a) (fn a) (app a) (log a) (ite a) (mat a) (letc a) (letrec a)
      (tannot a) (lannot a) (nil a) (cons a) (fnil a) (fcons a) h
  · intro a b c d h
    exact type_funs.rec (motive_1 := fun b c d _ => P a b c d)
      (motive_2 := fun b c d _ => Q a b c d) (motive_3 := fun b c d _ => R a b c d)
      (intLit a) (char a) (strLit a) (word8 a) (word64 a) (float64 a) (raise a) (handle a)
      (con a) (tup a) (var a) (fn a) (app a) (log a) (ite a) (mat a) (letc a) (letrec a)
      (tannot a) (lannot a) (nil a) (cons a) (fnil a) (fcons a) h

theorem Aux.type_d_ind {P : Bool → type_env → dec → Set type_ident → type_env → Prop}
    {Q : Bool → type_env → List dec → Set type_ident → type_env → Prop}
    (dlet_poly : ∀ (extra_checks : Bool) (tvs : Nat) (tenv : type_env) (p : pat) (e : exp)
      (t : typ) (bindings : List (varN × typ)) (locs : CmlTS.locs),
      is_value e → ALL_DISTINCT (pat_bindings p []) → type_p tvs tenv p t bindings →
      type_e tenv (bind_tvar tvs tenv_val_exp.Empty) e t →
      (extra_checks = true →
        ∀ tvs' bindings' t',
          (type_p tvs' tenv p t' bindings' ∧
            type_e tenv (bind_tvar tvs' tenv_val_exp.Empty) e t') →
          LIST_REL tscheme_inst ((tenv_add_tvs tvs' bindings').map Prod.snd)
            ((tenv_add_tvs tvs bindings).map Prod.snd)) →
      P extra_checks tenv (Dlet locs p e) ∅
        { v := alist_to_ns (tenv_add_tvs tvs bindings), c := nsEmpty, t := nsEmpty })
    (dlet_mono : ∀ (extra_checks : Bool) (tenv : type_env) (p : pat) (e : exp) (t : typ)
      (bindings : List (varN × typ)) (locs : CmlTS.locs),
      (extra_checks = true → ¬ is_value e ∧ type_pe_determ tenv tenv_val_exp.Empty p e) →
      ALL_DISTINCT (pat_bindings p []) → type_p 0 tenv p t bindings →
      type_e tenv tenv_val_exp.Empty e t →
      P extra_checks tenv (Dlet locs p e) ∅
        { v := alist_to_ns (tenv_add_tvs 0 bindings), c := nsEmpty, t := nsEmpty })
    (dletrec : ∀ (extra_checks : Bool) (tenv : type_env) (funs : List (varN × varN × exp))
      (bindings : List (varN × typ)) (tvs : Nat) (locs : CmlTS.locs),
      type_funs tenv (bind_var_list 0 bindings (bind_tvar tvs tenv_val_exp.Empty)) funs bindings →
      (extra_checks = true →
        ∀ tvs' bindings',
          type_funs tenv (bind_var_list 0 bindings' (bind_tvar tvs' tenv_val_exp.Empty)) funs
            bindings' →
          LIST_REL tscheme_inst ((tenv_add_tvs tvs' bindings').map Prod.snd)
            ((tenv_add_tvs tvs bindings).map Prod.snd)) →
      P extra_checks tenv (Dletrec locs funs) ∅
        { v := alist_to_ns (tenv_add_tvs tvs bindings), c := nsEmpty, t := nsEmpty })
    (dtype : ∀ (extra_checks : Bool) (tenv : type_env) (tdefs : type_def)
      (type_identities : List type_ident) (tenvT : tenv_abbrev) (locs : CmlTS.locs),
      ALL_DISTINCT type_identities →
      DISJOINT (LIST_TO_SET type_identities)
        (LIST_TO_SET (Tlist_num :: (Tbool_num :: prim_type_nums))) →
      check_ctor_tenv (nsAppend tenvT tenv.t) tdefs →
      type_identities.length = tdefs.length →
      tenvT = alist_to_ns
        (List.zipWith (fun (tvs, tn, _) i => (tn, (tvs, Tapp (tvs.map Tvar) i)))
          tdefs type_identities) →
      P extra_checks tenv (Dtype locs tdefs) (LIST_TO_SET type_identities)
        { v := nsEmpty
          c := build_ctor_tenv (nsAppend tenvT tenv.t) tdefs type_identities
          t := tenvT })
    (dtabbrev : ∀ (extra_checks : Bool) (tenv : type_env) (tvs : List tvarN) (tn : typeN)
      (t : ast_t) (locs : CmlTS.locs),
      check_freevars_ast tvs t → check_type_names tenv.t t → ALL_DISTINCT tvs →
      P extra_checks tenv (Dtabbrev locs tvs tn t) ∅
        { v := nsEmpty, c := nsEmpty, t := nsSing tn (tvs, type_name_subst tenv.t t) })
    (dexn : ∀ (extra_checks : Bool) (tenv : type_env) (cn : conN) (ts : List ast_t)
      (locs : CmlTS.locs),
      EVERY (check_freevars_ast []) ts → EVERY (check_type_names tenv.t) ts →
      P extra_checks tenv (Dexn locs cn ts) ∅
        { v := nsEmpty
          c := nsSing cn ([], ts.map (type_name_subst tenv.t), Texn_num)
          t := nsEmpty })
    (dmod : ∀ (extra_checks : Bool) (tenv : type_env) (mn : modN) (ds : List dec)
      (decls : Set type_ident) (tenv' : type_env),
      type_ds extra_checks tenv ds decls tenv' → Q extra_checks tenv ds decls tenv' →
      P extra_checks tenv (Dmod mn ds) decls (tenvLift mn tenv'))
    (dlocal : ∀ (extra_checks : Bool) (tenv : type_env) (lds ds : List dec)
      (tenv1 tenv2 : type_env) (decls1 decls2 : Set type_ident),
      type_ds extra_checks tenv lds decls1 tenv1 →
      type_ds extra_checks (extend_dec_tenv tenv1 tenv) ds decls2 tenv2 →
      DISJOINT decls1 decls2 → Q extra_checks tenv lds decls1 tenv1 →
      Q extra_checks (extend_dec_tenv tenv1 tenv) ds decls2 tenv2 →
      P extra_checks tenv (Dlocal lds ds) (decls1 ∪ decls2) tenv2)
    (nil : ∀ extra_checks tenv,
      Q extra_checks tenv [] ∅ { v := nsEmpty, c := nsEmpty, t := nsEmpty })
    (cons : ∀ (extra_checks : Bool) (tenv : type_env) (d : dec) (ds : List dec)
      (tenv1 tenv2 : type_env) (decls1 decls2 : Set type_ident),
      type_d extra_checks tenv d decls1 tenv1 →
      type_ds extra_checks (extend_dec_tenv tenv1 tenv) ds decls2 tenv2 →
      DISJOINT decls1 decls2 → P extra_checks tenv d decls1 tenv1 →
      Q extra_checks (extend_dec_tenv tenv1 tenv) ds decls2 tenv2 →
      Q extra_checks tenv (d :: ds) (decls1 ∪ decls2) (extend_dec_tenv tenv2 tenv1)) :
    (∀ check tenv d decls tenv', type_d check tenv d decls tenv' → P check tenv d decls tenv') ∧
    (∀ check tenv ds decls tenv', type_ds check tenv ds decls tenv' →
      Q check tenv ds decls tenv') := by
  constructor
  · intro a b c d e h
    exact type_d.rec (motive_1 := fun b c d e _ => P a b c d e)
      (motive_2 := fun b c d e _ => Q a b c d e) (dlet_poly a) (dlet_mono a) (dletrec a) (dtype a)
      (dtabbrev a) (dexn a) (dmod a) (dlocal a) (nil a) (cons a) h
  · intro a b c d e h
    exact type_ds.rec (motive_1 := fun b c d e _ => P a b c d e)
      (motive_2 := fun b c d e _ => Q a b c d e) (dlet_poly a) (dlet_mono a) (dletrec a) (dtype a)
      (dtabbrev a) (dexn a) (dmod a) (dlocal a) (nil a) (cons a) h

end CmlTS
