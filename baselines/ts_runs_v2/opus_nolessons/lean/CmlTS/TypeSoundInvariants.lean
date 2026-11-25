import CmlTS.Ast
import CmlTS.Namespace
import CmlTS.SemanticPrimitives
import CmlTS.TypeSystem
import CmlTS.NamespaceProps
/-
  Translation of HOL4 theory `typeSoundInvariants` (typeSoundInvariantsScript.sml).
-/
set_option autoImplicit false

namespace CmlTS
open Classical

/- HOL4:
Datatype:
 store_t =
 | Ref_t t
 | W8array_t
 | Varray_t t
End -/
inductive store_t
  | Ref_t (t : typ)
  | W8array_t
  | Varray_t (t : typ)

export store_t (Ref_t W8array_t Varray_t)

instance : Inhabited store_t := ⟨.W8array_t⟩

/- HOL4:
Type tenv_store = ``:(num, store_t) fmap`` -/
abbrev tenv_store : Type := fmap Nat store_t

/- HOL4:
Definition tenv_abbrev_ok_def:
  tenv_abbrev_ok tenvT ⇔ nsAll (\id (tvs,t). check_freevars 0 tvs t) tenvT
End -/
def tenv_abbrev_ok {m n : Type} (tenvT : Namespace m n (List mlstring × typ)) : Prop :=
  nsAll (fun _ (tvs, t) => check_freevars 0 tvs t) tenvT

/- HOL4:
Definition tenv_ctor_ok_def:
  tenv_ctor_ok tenvC ⇔ nsAll (\id (tvs,ts,tn). EVERY (check_freevars 0 tvs) ts) tenvC
End -/
def tenv_ctor_ok {m n α : Type} (tenvC : Namespace m n (List mlstring × List typ × α)) : Prop :=
  nsAll (fun _ (tvs, ts, _) => EVERY (check_freevars 0 tvs) ts) tenvC

/- HOL4:
Definition tenv_val_ok_def:
  tenv_val_ok tenvV ⇔ nsAll (\id (tvs,t). check_freevars tvs [] t) tenvV
End -/
def tenv_val_ok {m n : Type} (tenvV : Namespace m n (Nat × typ)) : Prop :=
  nsAll (fun _ (tvs, t) => check_freevars tvs [] t) tenvV

/- HOL4:
Definition tenv_ok_def:
  tenv_ok tenv ⇔
    tenv_val_ok tenv.v ∧
    tenv_ctor_ok tenv.c ∧
    tenv_abbrev_ok tenv.t
End -/
def tenv_ok (tenv : type_env) : Prop :=
  tenv_val_ok tenv.v ∧
  tenv_ctor_ok tenv.c ∧
  tenv_abbrev_ok tenv.t

/- HOL4:
Definition tenv_val_exp_ok_def:
  (tenv_val_exp_ok Empty ⇔ T) ∧
  (tenv_val_exp_ok (Bind_tvar n tenv) ⇔ tenv_val_exp_ok tenv) ∧
  (tenv_val_exp_ok (Bind_name x tvs t tenv) ⇔
    check_freevars (tvs + num_tvs tenv) [] t ∧
    tenv_val_exp_ok tenv)
End -/
def tenv_val_exp_ok : tenv_val_exp → Prop
  | .Empty => True
  | .Bind_tvar _ tenv => tenv_val_exp_ok tenv
  | .Bind_name _ tvs t tenv =>
    check_freevars (tvs + num_tvs tenv) [] t ∧
    tenv_val_exp_ok tenv

/- HOL4:
Type ctMap = ``:(stamp, (tvarN list # t list # type_ident)) fmap``
   (Lean name `ctMap_t`, because `ctMap` is the usual variable name) -/
abbrev ctMap_t : Type := fmap stamp (List tvarN × List typ × type_ident)

/- HOL4:
Definition ctMap_ok_def:
  ctMap_ok ctMap ⇔
    (* No free variables in the range *)
    FEVERY (\ (stamp,(tvs,ts, _)). EVERY (check_freevars 0 tvs) ts) ctMap ∧
    (* Exceptions have type exception, and no type variables *)
    (!ex tvs ts ti. FLOOKUP ctMap (ExnStamp ex) = SOME (tvs, ts, ti) ⇒
      tvs = [] ∧ ti = Texn_num) ∧
    (* Primitive, non-constructor types are not mapped *)
    (!cn x tvs ts ti. FLOOKUP ctMap (TypeStamp cn x) = SOME (tvs, ts, ti) ⇒
      ~MEM ti prim_type_nums) ∧
    (* If type identities are equal then the stamps are from the same type *)
    (!stamp1 tvs1 ts1 ti stamp2 tvs2 ts2.
      FLOOKUP ctMap stamp1 = SOME (tvs1, ts1, ti) ∧
      FLOOKUP ctMap stamp2 = SOME (tvs2, ts2, ti) ⇒
      same_type stamp1 stamp2)
End -/
def ctMap_ok (ctMap : ctMap_t) : Prop :=
  FEVERY (fun (_, (tvs, ts, _)) => EVERY (check_freevars 0 tvs) ts) ctMap ∧
  (∀ ex tvs ts ti, FLOOKUP ctMap (.ExnStamp ex) = some (tvs, ts, ti) →
    tvs = [] ∧ ti = Texn_num) ∧
  (∀ cn x tvs ts ti, FLOOKUP ctMap (.TypeStamp cn x) = some (tvs, ts, ti) →
    ¬ ti ∈ prim_type_nums) ∧
  (∀ stamp1 tvs1 ts1 ti stamp2 tvs2 ts2,
    FLOOKUP ctMap stamp1 = some (tvs1, ts1, ti) ∧
    FLOOKUP ctMap stamp2 = some (tvs2, ts2, ti) →
    same_type stamp1 stamp2)

/- HOL4:
Definition type_ctor_def:
  type_ctor ctMap _ (n, stamp) (tvs, ts, ti) ⇔
    FLOOKUP ctMap stamp = SOME (tvs, ts, ti) ∧
    LENGTH ts = n
End -/
def type_ctor {σ ι α β γ : Type} (ctMap : fmap σ (α × List β × γ)) (_ : ι) :
    Nat × σ → α × List β × γ → Prop
  | (n, stamp), (tvs, ts, ti) =>
    FLOOKUP ctMap stamp = some (tvs, ts, ti) ∧
    ts.length = n

/- HOL4:
Definition add_tenvE_def:
  (add_tenvE Empty tenvV = tenvV) ∧
  (add_tenvE (Bind_tvar _ tenvE) tenvV = add_tenvE tenvE tenvV) ∧
  (add_tenvE (Bind_name x tvs t tenvE) tenvV = nsBind x (tvs,t) (add_tenvE tenvE tenvV))
End -/
def add_tenvE {m : Type} :
    tenv_val_exp → Namespace m mlstring (Nat × typ) → Namespace m mlstring (Nat × typ)
  | .Empty, tenvV => tenvV
  | .Bind_tvar _ tenvE, tenvV => add_tenvE tenvE tenvV
  | .Bind_name x tvs t tenvE, tenvV => nsBind x (tvs, t) (add_tenvE tenvE tenvV)

/- HOL4:
Inductive type_v:
  (!tvs ctMap tenvS n.
    type_v tvs ctMap tenvS (Litv (IntLit n)) Tint) ∧
  (!tvs ctMap tenvS c.
    type_v tvs ctMap tenvS (Litv (Char c)) Tchar) ∧
  (!tvs ctMap tenvS s.
    type_v tvs ctMap tenvS (Litv (StrLit s)) Tstring) ∧
  (!tvs ctMap tenvS w.
    type_v tvs ctMap tenvS (Litv (Word8 w)) Tword8) ∧
  (!tvs ctMap tenvS w.
    type_v tvs ctMap tenvS (Litv (Word64 w)) Tword64) ∧
  (!tvs ctMap tenvS w.
    type_v tvs ctMap tenvS (Litv (Float64 w)) Tdouble) ∧
  (!tvs ctMap tenvS vs tvs' stamp ts' ts ti.
    EVERY (check_freevars tvs []) ts' ∧
    LENGTH tvs' = LENGTH ts' ∧
    LIST_REL (type_v tvs ctMap tenvS)
      vs (MAP (type_subst (FUPDATE_LIST FEMPTY (REVERSE (ZIP (tvs', ts'))))) ts) ∧
    FLOOKUP ctMap stamp = SOME (tvs',ts,ti)
    ⇒
    type_v tvs ctMap tenvS (Conv (SOME stamp) vs) (Tapp ts' ti)) ∧
  (!tvs ctMap tenvS vs ts.
    LIST_REL (type_v tvs ctMap tenvS) vs ts
    ⇒
    type_v tvs ctMap tenvS (Conv NONE vs) (Ttup ts)) ∧
  (!tvs ctMap tenvS env tenv tenvE n e t1 t2.
    tenv_ok tenv ∧
    tenv_val_exp_ok tenvE ∧
    num_tvs tenvE = 0 ∧
    nsAll2 (type_ctor ctMap) env.c tenv.c ∧
    nsAll2 (\i v (tvs,t). type_v tvs ctMap tenvS v t) env.v (add_tenvE tenvE tenv.v) ∧
    check_freevars tvs [] t1 ∧
    type_e tenv (Bind_name n 0 t1 (bind_tvar tvs tenvE)) e t2
    ⇒
    type_v tvs ctMap tenvS (Closure env n e) (Tfn t1 t2)) ∧
  (!tvs ctMap tenvS env funs n t tenv tenvE bindings.
    tenv_ok tenv ∧
    tenv_val_exp_ok tenvE ∧
    num_tvs tenvE = 0 ∧
    nsAll2 (type_ctor ctMap) env.c tenv.c ∧
    nsAll2 (\i v (tvs,t). type_v tvs ctMap tenvS v t) env.v (add_tenvE tenvE tenv.v) ∧
    type_funs tenv (bind_var_list 0 bindings (bind_tvar tvs tenvE)) funs bindings ∧
    ALOOKUP bindings n = SOME t ∧
    ALL_DISTINCT (MAP FST funs) ∧
    MEM n (MAP FST funs)
    ⇒
    type_v tvs ctMap tenvS (Recclosure env funs n) t) ∧
  (!tvs ctMap tenvS n t.
    check_freevars 0 [] t ∧
    FLOOKUP tenvS n = SOME (Ref_t t)
    ⇒
    type_v tvs ctMap tenvS (Loc T n) (Tref t)) ∧
  (!tvs ctMap tenvS n.
    FLOOKUP tenvS n = SOME W8array_t
    ⇒
    type_v tvs ctMap tenvS (Loc T n) Tword8array) ∧
  (!tvs ctMap tenvS n t.
    check_freevars 0 [] t ∧
    FLOOKUP tenvS n = SOME (Varray_t t)
    ⇒
    type_v tvs ctMap tenvS (Loc T n) (Tarray t)) ∧
  (!tvs ctMap tenvS vs t.
    check_freevars 0 [] t ∧
    EVERY (\v. type_v tvs ctMap tenvS v t) vs
    ⇒
    type_v tvs ctMap tenvS (Vectorv vs) (Tvector t))
End

   Encoding: Lean does not accept the recursive occurrences of `type_v` as arguments of `LIST_REL`,
   `EVERY` and `nsAll2`.  In the rules concerned the occurrence is an arbitrary relation `R`
   contained in `type_v`.  Because the premises are monotone in `R`, these are the same rules: the
   theorems `type_v.Conv_some'`, `Conv_none'`, `Closure'`, `Recclosure'`, `Vectorv'` below are the
   HOL4 rules (take `R = type_v`), and the theorems `type_v.*_inv` give the converse. -/
inductive type_v : Nat → ctMap_t → tenv_store → val → typ → Prop
  | Litv_IntLit (tvs : Nat) (ctMap : ctMap_t) (tenvS : tenv_store) (n : Int) :
    type_v tvs ctMap tenvS (.Litv (.IntLit n)) Tint
  | Litv_Char (tvs : Nat) (ctMap : ctMap_t) (tenvS : tenv_store) (c : char) :
    type_v tvs ctMap tenvS (.Litv (.Char c)) Tchar
  | Litv_StrLit (tvs : Nat) (ctMap : ctMap_t) (tenvS : tenv_store) (s : mlstring) :
    type_v tvs ctMap tenvS (.Litv (.StrLit s)) Tstring
  | Litv_Word8 (tvs : Nat) (ctMap : ctMap_t) (tenvS : tenv_store) (w : word8) :
    type_v tvs ctMap tenvS (.Litv (.Word8 w)) Tword8
  | Litv_Word64 (tvs : Nat) (ctMap : ctMap_t) (tenvS : tenv_store) (w : word64) :
    type_v tvs ctMap tenvS (.Litv (.Word64 w)) Tword64
  | Litv_Float64 (tvs : Nat) (ctMap : ctMap_t) (tenvS : tenv_store) (w : word64) :
    type_v tvs ctMap tenvS (.Litv (.Float64 w)) Tdouble
  | Conv_some (tvs : Nat) (ctMap : ctMap_t) (tenvS : tenv_store) (vs : List val)
      (tvs' : List tvarN) (stamp : CmlTS.stamp) (ts' ts : List typ) (ti : type_ident)
      (R : Nat → ctMap_t → tenv_store → val → typ → Prop) :
    (∀ tvs ctMap tenvS v t, R tvs ctMap tenvS v t → type_v tvs ctMap tenvS v t) →
    EVERY (check_freevars tvs []) ts' →
    tvs'.length = ts'.length →
    LIST_REL (R tvs ctMap tenvS)
      vs (ts.map (type_subst (FUPDATE_LIST FEMPTY (List.reverse (List.zip tvs' ts'))))) →
    FLOOKUP ctMap stamp = some (tvs', ts, ti) →
    type_v tvs ctMap tenvS (.Conv (some stamp) vs) (.Tapp ts' ti)
  | Conv_none (tvs : Nat) (ctMap : ctMap_t) (tenvS : tenv_store) (vs : List val) (ts : List typ)
      (R : Nat → ctMap_t → tenv_store → val → typ → Prop) :
    (∀ tvs ctMap tenvS v t, R tvs ctMap tenvS v t → type_v tvs ctMap tenvS v t) →
    LIST_REL (R tvs ctMap tenvS) vs ts →
    type_v tvs ctMap tenvS (.Conv none vs) (Ttup ts)
  | Closure (tvs : Nat) (ctMap : ctMap_t) (tenvS : tenv_store) (env : sem_env val)
      (tenv : type_env) (tenvE : tenv_val_exp) (n : varN) (e : exp) (t1 t2 : typ)
      (R : Nat → ctMap_t → tenv_store → val → typ → Prop) :
    (∀ tvs ctMap tenvS v t, R tvs ctMap tenvS v t → type_v tvs ctMap tenvS v t) →
    tenv_ok tenv →
    tenv_val_exp_ok tenvE →
    num_tvs tenvE = 0 →
    nsAll2 (type_ctor ctMap) env.c tenv.c →
    nsAll2 (fun _ v (tvs, t) => R tvs ctMap tenvS v t) env.v (add_tenvE tenvE tenv.v) →
    check_freevars tvs [] t1 →
    type_e tenv (.Bind_name n 0 t1 (bind_tvar tvs tenvE)) e t2 →
    type_v tvs ctMap tenvS (.Closure env n e) (Tfn t1 t2)
  | Recclosure (tvs : Nat) (ctMap : ctMap_t) (tenvS : tenv_store) (env : sem_env val)
      (funs : List (varN × varN × exp)) (n : varN) (t : typ) (tenv : type_env)
      (tenvE : tenv_val_exp) (bindings : List (varN × typ))
      (R : Nat → ctMap_t → tenv_store → val → typ → Prop) :
    (∀ tvs ctMap tenvS v t, R tvs ctMap tenvS v t → type_v tvs ctMap tenvS v t) →
    tenv_ok tenv →
    tenv_val_exp_ok tenvE →
    num_tvs tenvE = 0 →
    nsAll2 (type_ctor ctMap) env.c tenv.c →
    nsAll2 (fun _ v (tvs, t) => R tvs ctMap tenvS v t) env.v (add_tenvE tenvE tenv.v) →
    type_funs tenv (bind_var_list 0 bindings (bind_tvar tvs tenvE)) funs bindings →
    ALOOKUP bindings n = some t →
    ALL_DISTINCT (funs.map Prod.fst) →
    n ∈ funs.map Prod.fst →
    type_v tvs ctMap tenvS (.Recclosure env funs n) t
  | Loc_Ref (tvs : Nat) (ctMap : ctMap_t) (tenvS : tenv_store) (n : Nat) (t : typ) :
    check_freevars 0 [] t →
    FLOOKUP tenvS n = some (.Ref_t t) →
    type_v tvs ctMap tenvS (.Loc true n) (Tref t)
  | Loc_W8array (tvs : Nat) (ctMap : ctMap_t) (tenvS : tenv_store) (n : Nat) :
    FLOOKUP tenvS n = some .W8array_t →
    type_v tvs ctMap tenvS (.Loc true n) Tword8array
  | Loc_Varray (tvs : Nat) (ctMap : ctMap_t) (tenvS : tenv_store) (n : Nat) (t : typ) :
    check_freevars 0 [] t →
    FLOOKUP tenvS n = some (.Varray_t t) →
    type_v tvs ctMap tenvS (.Loc true n) (Tarray t)
  | Vectorv (tvs : Nat) (ctMap : ctMap_t) (tenvS : tenv_store) (vs : List val) (t : typ)
      (R : Nat → ctMap_t → tenv_store → val → typ → Prop) :
    (∀ tvs ctMap tenvS v t, R tvs ctMap tenvS v t → type_v tvs ctMap tenvS v t) →
    check_freevars 0 [] t →
    EVERY (fun v => R tvs ctMap tenvS v t) vs →
    type_v tvs ctMap tenvS (.Vectorv vs) (Tvector t)

/-- The HOL4 rule of `type_v` for `Conv (SOME stamp) vs`. -/
theorem type_v.Conv_some' (tvs : Nat) (ctMap : ctMap_t) (tenvS : tenv_store) (vs : List val)
    (tvs' : List tvarN) (stamp : CmlTS.stamp) (ts' ts : List typ) (ti : type_ident)
    (h1 : EVERY (check_freevars tvs []) ts')
    (h2 : tvs'.length = ts'.length)
    (h3 : LIST_REL (type_v tvs ctMap tenvS)
      vs (ts.map (type_subst (FUPDATE_LIST FEMPTY (List.reverse (List.zip tvs' ts'))))))
    (h4 : FLOOKUP ctMap stamp = some (tvs', ts, ti)) :
    type_v tvs ctMap tenvS (.Conv (some stamp) vs) (.Tapp ts' ti) :=
  .Conv_some tvs ctMap tenvS vs tvs' stamp ts' ts ti type_v (fun _ _ _ _ _ h => h) h1 h2 h3 h4

/-- The HOL4 rule of `type_v` for `Conv NONE vs`. -/
theorem type_v.Conv_none' (tvs : Nat) (ctMap : ctMap_t) (tenvS : tenv_store) (vs : List val)
    (ts : List typ) (h : LIST_REL (type_v tvs ctMap tenvS) vs ts) :
    type_v tvs ctMap tenvS (.Conv none vs) (Ttup ts) :=
  .Conv_none tvs ctMap tenvS vs ts type_v (fun _ _ _ _ _ h => h) h

/-- The HOL4 rule of `type_v` for `Closure`. -/
theorem type_v.Closure' (tvs : Nat) (ctMap : ctMap_t) (tenvS : tenv_store) (env : sem_env val)
    (tenv : type_env) (tenvE : tenv_val_exp) (n : varN) (e : exp) (t1 t2 : typ)
    (h1 : tenv_ok tenv) (h2 : tenv_val_exp_ok tenvE) (h3 : num_tvs tenvE = 0)
    (h4 : nsAll2 (type_ctor ctMap) env.c tenv.c)
    (h5 : nsAll2 (fun _ v (tvs, t) => type_v tvs ctMap tenvS v t) env.v (add_tenvE tenvE tenv.v))
    (h6 : check_freevars tvs [] t1)
    (h7 : type_e tenv (.Bind_name n 0 t1 (bind_tvar tvs tenvE)) e t2) :
    type_v tvs ctMap tenvS (.Closure env n e) (Tfn t1 t2) :=
  .Closure tvs ctMap tenvS env tenv tenvE n e t1 t2 type_v (fun _ _ _ _ _ h => h)
    h1 h2 h3 h4 h5 h6 h7

/-- The HOL4 rule of `type_v` for `Recclosure`. -/
theorem type_v.Recclosure' (tvs : Nat) (ctMap : ctMap_t) (tenvS : tenv_store) (env : sem_env val)
    (funs : List (varN × varN × exp)) (n : varN) (t : typ) (tenv : type_env)
    (tenvE : tenv_val_exp) (bindings : List (varN × typ))
    (h1 : tenv_ok tenv) (h2 : tenv_val_exp_ok tenvE) (h3 : num_tvs tenvE = 0)
    (h4 : nsAll2 (type_ctor ctMap) env.c tenv.c)
    (h5 : nsAll2 (fun _ v (tvs, t) => type_v tvs ctMap tenvS v t) env.v (add_tenvE tenvE tenv.v))
    (h6 : type_funs tenv (bind_var_list 0 bindings (bind_tvar tvs tenvE)) funs bindings)
    (h7 : ALOOKUP bindings n = some t)
    (h8 : ALL_DISTINCT (funs.map Prod.fst))
    (h9 : n ∈ funs.map Prod.fst) :
    type_v tvs ctMap tenvS (.Recclosure env funs n) t :=
  .Recclosure tvs ctMap tenvS env funs n t tenv tenvE bindings type_v (fun _ _ _ _ _ h => h)
    h1 h2 h3 h4 h5 h6 h7 h8 h9

/-- The HOL4 rule of `type_v` for `Vectorv`. -/
theorem type_v.Vectorv' (tvs : Nat) (ctMap : ctMap_t) (tenvS : tenv_store) (vs : List val)
    (t : typ) (h1 : check_freevars 0 [] t)
    (h2 : EVERY (fun v => type_v tvs ctMap tenvS v t) vs) :
    type_v tvs ctMap tenvS (.Vectorv vs) (Tvector t) :=
  .Vectorv tvs ctMap tenvS vs t type_v (fun _ _ _ _ _ h => h) h1 h2

/-! Monotonicity of `LIST_REL`, `EVERY` and `nsAll2` in the relation, for the converse readings. -/

theorem type_v.LIST_REL_imp {α β : Type} {R S : α → β → Prop} (h : ∀ a b, R a b → S a b) :
    ∀ {l1 : List α} {l2 : List β}, LIST_REL R l1 l2 → LIST_REL S l1 l2
  | [], [], _ => trivial
  | _ :: _, _ :: _, ⟨h1, h2⟩ => ⟨h _ _ h1, type_v.LIST_REL_imp h h2⟩

theorem type_v.nsAll2_imp {m n v1 v2 : Type} {R S : ident m n → v1 → v2 → Prop}
    (h : ∀ i a b, R i a b → S i a b) {e1 : Namespace m n v1} {e2 : Namespace m n v2}
    (hh : nsAll2 R e1 e2) : nsAll2 S e1 e2 := by
  obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := hh
  refine ⟨⟨fun id a ha => ?_, h2⟩, ⟨fun id a ha => ?_, h4⟩⟩
  · obtain ⟨b, hb, hr⟩ := h1 id a ha
    exact ⟨b, hb, h _ _ _ hr⟩
  · obtain ⟨b, hb, hr⟩ := h3 id a ha
    exact ⟨b, hb, h _ _ _ hr⟩

/-- HOL4 `type_v_cases` for `Conv NONE vs`. -/
theorem type_v.Conv_none_inv {tvs : Nat} {ctMap : ctMap_t} {tenvS : tenv_store} {vs : List val}
    {t : typ} (h : type_v tvs ctMap tenvS (.Conv none vs) t) :
    ∃ ts, t = Ttup ts ∧ LIST_REL (type_v tvs ctMap tenvS) vs ts := by
  generalize hv : val.Conv none vs = v at h
  cases h with
  | Conv_none _ _ _ _ ts R hR h1 =>
    cases hv
    exact ⟨ts, rfl, type_v.LIST_REL_imp (fun _ _ => hR _ _ _ _ _) h1⟩
  | _ => cases hv

/-- HOL4 `type_v_cases` for `Conv (SOME stamp) vs`. -/
theorem type_v.Conv_some_inv {tvs : Nat} {ctMap : ctMap_t} {tenvS : tenv_store}
    {stamp : CmlTS.stamp} {vs : List val} {t : typ}
    (h : type_v tvs ctMap tenvS (.Conv (some stamp) vs) t) :
    ∃ tvs' ts' ts ti, t = .Tapp ts' ti ∧
      EVERY (check_freevars tvs []) ts' ∧
      tvs'.length = ts'.length ∧
      LIST_REL (type_v tvs ctMap tenvS)
        vs (ts.map (type_subst (FUPDATE_LIST FEMPTY (List.reverse (List.zip tvs' ts'))))) ∧
      FLOOKUP ctMap stamp = some (tvs', ts, ti) := by
  generalize hv : val.Conv (some stamp) vs = v at h
  cases h with
  | Conv_some _ _ _ _ tvs' st ts' ts ti R hR h1 h2 h3 h4 =>
    cases hv
    exact ⟨tvs', ts', ts, ti, rfl, h1, h2,
      type_v.LIST_REL_imp (fun _ _ => hR _ _ _ _ _) h3, h4⟩
  | _ => cases hv

/-- HOL4 `type_v_cases` for `Closure`. -/
theorem type_v.Closure_inv {tvs : Nat} {ctMap : ctMap_t} {tenvS : tenv_store} {env : sem_env val}
    {n : varN} {e : exp} {t : typ} (h : type_v tvs ctMap tenvS (.Closure env n e) t) :
    ∃ tenv tenvE t1 t2, t = Tfn t1 t2 ∧
      tenv_ok tenv ∧ tenv_val_exp_ok tenvE ∧ num_tvs tenvE = 0 ∧
      nsAll2 (type_ctor ctMap) env.c tenv.c ∧
      nsAll2 (fun _ v (tvs, t) => type_v tvs ctMap tenvS v t) env.v (add_tenvE tenvE tenv.v) ∧
      check_freevars tvs [] t1 ∧
      type_e tenv (.Bind_name n 0 t1 (bind_tvar tvs tenvE)) e t2 := by
  generalize hv : val.Closure env n e = v at h
  cases h with
  | Closure _ _ _ env' tenv tenvE n' e' t1 t2 R hR h1 h2 h3 h4 h5 h6 h7 =>
    cases hv
    exact ⟨tenv, tenvE, t1, t2, rfl, h1, h2, h3, h4,
      type_v.nsAll2_imp (fun _ _ _ => hR _ _ _ _ _) h5, h6, h7⟩
  | _ => cases hv

/-- HOL4 `type_v_cases` for `Recclosure`. -/
theorem type_v.Recclosure_inv {tvs : Nat} {ctMap : ctMap_t} {tenvS : tenv_store}
    {env : sem_env val} {funs : List (varN × varN × exp)} {n : varN} {t : typ}
    (h : type_v tvs ctMap tenvS (.Recclosure env funs n) t) :
    ∃ tenv tenvE bindings,
      tenv_ok tenv ∧ tenv_val_exp_ok tenvE ∧ num_tvs tenvE = 0 ∧
      nsAll2 (type_ctor ctMap) env.c tenv.c ∧
      nsAll2 (fun _ v (tvs, t) => type_v tvs ctMap tenvS v t) env.v (add_tenvE tenvE tenv.v) ∧
      type_funs tenv (bind_var_list 0 bindings (bind_tvar tvs tenvE)) funs bindings ∧
      ALOOKUP bindings n = some t ∧
      ALL_DISTINCT (funs.map Prod.fst) ∧
      n ∈ funs.map Prod.fst := by
  generalize hv : val.Recclosure env funs n = v at h
  cases h with
  | Recclosure _ _ _ env' funs' n' t' tenv tenvE bindings R hR h1 h2 h3 h4 h5 h6 h7 h8 h9 =>
    cases hv
    exact ⟨tenv, tenvE, bindings, h1, h2, h3, h4,
      type_v.nsAll2_imp (fun _ _ _ => hR _ _ _ _ _) h5, h6, h7, h8, h9⟩
  | _ => cases hv

/-- HOL4 `type_v_cases` for `Vectorv`. -/
theorem type_v.Vectorv_inv {tvs : Nat} {ctMap : ctMap_t} {tenvS : tenv_store} {vs : List val}
    {t : typ} (h : type_v tvs ctMap tenvS (.Vectorv vs) t) :
    ∃ t', t = Tvector t' ∧ check_freevars 0 [] t' ∧
      EVERY (fun v => type_v tvs ctMap tenvS v t') vs := by
  generalize hv : val.Vectorv vs = v at h
  cases h with
  | Vectorv _ _ _ _ t' R hR h1 h2 =>
    cases hv
    exact ⟨t', rfl, h1, EVERY_iff.mpr fun x hx => hR _ _ _ _ _ (EVERY_iff.mp h2 x hx)⟩
  | _ => cases hv

/- HOL4:
Definition type_sv_def:
  (type_sv ctMap tenvS (Refv v) (Ref_t t) ⇔ type_v 0 ctMap tenvS v t) ∧
  (type_sv ctMap tenvS (W8array v) W8array_t ⇔ T) ∧
  (type_sv ctMap tenvS (Varray vs) (Varray_t t) ⇔
    EVERY (\v. type_v 0 ctMap tenvS v t) vs) ∧
  (type_sv _ _ _ _ ⇔ F)
End -/
def type_sv (ctMap : ctMap_t) (tenvS : tenv_store) : store_v val → store_t → Prop
  | .Refv v, .Ref_t t => type_v 0 ctMap tenvS v t
  | .W8array _, .W8array_t => True
  | .Varray vs, .Varray_t t => EVERY (fun v => type_v 0 ctMap tenvS v t) vs
  | _, _ => False

/- HOL4:
Definition type_s_def:
  type_s ctMap envS tenvS ⇔
    (!l.
      ((?st. FLOOKUP tenvS l = SOME st) ⇔ (?v. store_lookup l envS = SOME v)) ∧
      (!st sv.
        FLOOKUP tenvS l = SOME st ∧ store_lookup l envS = SOME sv
        ⇒
        type_sv ctMap tenvS sv st))
End -/
def type_s (ctMap : ctMap_t) (envS : List (store_v val)) (tenvS : tenv_store) : Prop :=
  ∀ l,
    ((∃ st, FLOOKUP tenvS l = some st) ↔ (∃ v, store_lookup l envS = some v)) ∧
    (∀ st sv,
      FLOOKUP tenvS l = some st ∧ store_lookup l envS = some sv →
      type_sv ctMap tenvS sv st)

/- HOL4:
Definition ctMap_has_exns_def:
  ctMap_has_exns ctMap ⇔
    FLOOKUP ctMap bind_stamp = SOME ([],[],Texn_num) ∧
    FLOOKUP ctMap chr_stamp = SOME ([],[],Texn_num) ∧
    FLOOKUP ctMap div_stamp = SOME ([],[],Texn_num) ∧
    FLOOKUP ctMap subscript_stamp = SOME ([],[],Texn_num)
End -/
def ctMap_has_exns {α β : Type} (ctMap : fmap stamp (List α × List β × Nat)) : Prop :=
  FLOOKUP ctMap bind_stamp = some ([], [], Texn_num) ∧
  FLOOKUP ctMap chr_stamp = some ([], [], Texn_num) ∧
  FLOOKUP ctMap div_stamp = some ([], [], Texn_num) ∧
  FLOOKUP ctMap subscript_stamp = some ([], [], Texn_num)

/- HOL4:
Definition ctMap_has_lists_def:
  ctMap_has_lists ctMap ⇔
    FLOOKUP ctMap (TypeStamp «[]» list_type_num) = SOME ([«'a»],[],Tlist_num) ∧
    FLOOKUP ctMap (TypeStamp «::» list_type_num) =
      SOME ([«'a»],[Tvar «'a»; Tlist (Tvar «'a»)],Tlist_num) ∧
    (!cn. cn ≠ «::» ∧ cn ≠ «[]» ⇒ FLOOKUP ctMap (TypeStamp cn list_type_num) = NONE)
End -/
def ctMap_has_lists (ctMap : ctMap_t) : Prop :=
  FLOOKUP ctMap (.TypeStamp (mls "[]") list_type_num) = some ([mls "'a"], [], Tlist_num) ∧
  FLOOKUP ctMap (.TypeStamp (mls "::") list_type_num) =
    some ([mls "'a"], [.Tvar (mls "'a"), Tlist (.Tvar (mls "'a"))], Tlist_num) ∧
  (∀ cn, cn ≠ mls "::" ∧ cn ≠ mls "[]" → FLOOKUP ctMap (.TypeStamp cn list_type_num) = none)

/- HOL4:
Definition ctMap_has_bools_def:
  ctMap_has_bools ctMap ⇔
    FLOOKUP ctMap (TypeStamp «True» bool_type_num) = SOME ([],[],Tbool_num) ∧
    FLOOKUP ctMap (TypeStamp «False» bool_type_num) = SOME ([],[],Tbool_num) ∧
    (!cn. cn ≠ «True» ∧ cn ≠ «False» ⇒ FLOOKUP ctMap (TypeStamp cn bool_type_num) = NONE)
End -/
def ctMap_has_bools {α β : Type} (ctMap : fmap stamp (List α × List β × Nat)) : Prop :=
  FLOOKUP ctMap (.TypeStamp (mls "True") bool_type_num) = some ([], [], Tbool_num) ∧
  FLOOKUP ctMap (.TypeStamp (mls "False") bool_type_num) = some ([], [], Tbool_num) ∧
  (∀ cn, cn ≠ mls "True" ∧ cn ≠ mls "False" →
    FLOOKUP ctMap (.TypeStamp cn bool_type_num) = none)

/- HOL4:
Definition good_ctMap_def:
  good_ctMap ctMap ⇔
    ctMap_ok ctMap ∧
    ctMap_has_bools ctMap ∧
    ctMap_has_exns ctMap ∧
    ctMap_has_lists ctMap
End -/
def good_ctMap (ctMap : ctMap_t) : Prop :=
  ctMap_ok ctMap ∧
  ctMap_has_bools ctMap ∧
  ctMap_has_exns ctMap ∧
  ctMap_has_lists ctMap

/- HOL4:
Definition consistent_ctMap_def:
  consistent_ctMap st type_ids ctMap ⇔
    (DISJOINT type_ids (FRANGE ((SND o SND) o_f ctMap))) ∧
    !cn id.
      (TypeStamp cn id ∈ FDOM ctMap ⇒ id < st.next_type_stamp) ∧
      (ExnStamp id ∈ FDOM ctMap ⇒ id < st.next_exn_stamp)
End -/
def consistent_ctMap {ffiT α β γ : Type} (st : state ffiT) (type_ids : Set γ)
    (ctMap : fmap stamp (α × β × γ)) : Prop :=
  DISJOINT type_ids (FRANGE (o_f (Prod.snd ∘ Prod.snd) ctMap)) ∧
  ∀ cn id,
    (stamp.TypeStamp cn id ∈ FDOM ctMap → id < st.next_type_stamp) ∧
    (stamp.ExnStamp id ∈ FDOM ctMap → id < st.next_exn_stamp)

/- HOL4:
Definition type_all_env_def:
  type_all_env ctMap tenvS env tenv ⇔
    nsAll2 (type_ctor ctMap) (sem_env_c env) tenv.c ∧
    nsAll2 (\i v (tvs,t). type_v tvs ctMap tenvS v t) (sem_env_v env) tenv.v
End -/
def type_all_env (ctMap : ctMap_t) (tenvS : tenv_store) (env : sem_env val) (tenv : type_env) :
    Prop :=
  nsAll2 (type_ctor ctMap) env.c tenv.c ∧
  nsAll2 (fun _ v (tvs, t) => type_v tvs ctMap tenvS v t) env.v tenv.v

/- HOL4:
Definition type_sound_invariant_def:
type_sound_invariant st env ctMap tenvS type_idents tenv ⇔
  tenv_ok tenv ∧
  good_ctMap ctMap ∧
  consistent_ctMap st type_idents ctMap ∧
  type_all_env ctMap tenvS env tenv ∧
  type_s ctMap st.refs tenvS
End -/
def type_sound_invariant {ffiT : Type} (st : state ffiT) (env : sem_env val) (ctMap : ctMap_t)
    (tenvS : tenv_store) (type_idents : Set type_ident) (tenv : type_env) : Prop :=
  tenv_ok tenv ∧
  good_ctMap ctMap ∧
  consistent_ctMap st type_idents ctMap ∧
  type_all_env ctMap tenvS env tenv ∧
  type_s ctMap st.refs tenvS

end CmlTS
