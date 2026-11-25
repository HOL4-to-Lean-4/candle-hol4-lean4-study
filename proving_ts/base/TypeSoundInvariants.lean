import CmlTS.Ast
import CmlTS.Namespace
import CmlTS.SemanticPrimitives
import CmlTS.TypeSystem
import CmlTS.NamespaceProps

/-
HOL4 theory `typeSoundInvariants` (typeSoundInvariantsScript.sml).
The type abbreviation `ctMap` is `ctMap_ty` here.
-/

namespace CmlTS

noncomputable section

open scoped Classical

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

/- HOL4: Type tenv_store = ``:(num, store_t) fmap`` -/
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
  tenv_val_ok tenv.v ∧ tenv_ctor_ok tenv.c ∧ tenv_abbrev_ok tenv.t

/- HOL4:
Definition tenv_val_exp_ok_def:
  (tenv_val_exp_ok Empty ⇔ T) ∧
  (tenv_val_exp_ok (Bind_tvar n tenv) ⇔ tenv_val_exp_ok tenv) ∧
  (tenv_val_exp_ok (Bind_name x tvs t tenv) ⇔
    check_freevars (tvs + num_tvs tenv) [] t ∧
    tenv_val_exp_ok tenv)
End -/
def tenv_val_exp_ok : tenv_val_exp → Prop
  | tenv_val_exp.Empty => True
  | Bind_tvar _ tenv => tenv_val_exp_ok tenv
  | Bind_name _ tvs t tenv => check_freevars (tvs + num_tvs tenv) [] t ∧ tenv_val_exp_ok tenv

/- HOL4: Type ctMap = ``:(stamp, (tvarN list # t list # type_ident)) fmap`` -/
abbrev ctMap_ty : Type := fmap stamp (List tvarN × List typ × type_ident)

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
def ctMap_ok (ctMap : ctMap_ty) : Prop :=
  FEVERY (fun (_, (tvs, ts, _)) => EVERY (check_freevars 0 tvs) ts) ctMap ∧
  (∀ ex tvs ts ti, FLOOKUP ctMap (ExnStamp ex) = some (tvs, ts, ti) →
    tvs = [] ∧ ti = Texn_num) ∧
  (∀ cn x tvs ts ti, FLOOKUP ctMap (TypeStamp cn x) = some (tvs, ts, ti) →
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
End
(as polymorphic as in HOL4) -/
def type_ctor {σ α β γ δ : Type} (ctMap : fmap σ (α × List β × γ)) (_ : δ) :
    Nat × σ → α × List β × γ → Prop
  | (n, stamp), (tvs, ts, ti) => FLOOKUP ctMap stamp = some (tvs, ts, ti) ∧ ts.length = n

/- HOL4:
Definition add_tenvE_def:
  (add_tenvE Empty tenvV = tenvV) ∧
  (add_tenvE (Bind_tvar _ tenvE) tenvV = add_tenvE tenvE tenvV) ∧
  (add_tenvE (Bind_name x tvs t tenvE) tenvV = nsBind x (tvs,t) (add_tenvE tenvE tenvV))
End -/
def add_tenvE {m : Type} : tenv_val_exp → Namespace m varN (Nat × typ) →
    Namespace m varN (Nat × typ)
  | tenv_val_exp.Empty, tenvV => tenvV
  | Bind_tvar _ tenvE, tenvV => add_tenvE tenvE tenvV
  | Bind_name x tvs t tenvE, tenvV => nsBind x (tvs, t) (add_tenvE tenvE tenvV)

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
Lean does not allow the recursive occurrences under `LIST_REL`, `EVERY` and
`nsAll2`, so these premises are spelled out pointwise:
* `LIST_REL R vs ts` as equal lengths and `R` on the elements at each index;
* `EVERY P vs` as `P` on all members;
* `nsAll2 R e1 e2` as `nsAll2 (λ_ _ _. T) e1 e2` and `R` on the values found at
  each identifier.
The HOL4 forms are proved below: `type_v_*_aux` (rules), `type_v_*_inv_aux`
(inversions). -/
inductive type_v : Nat → ctMap_ty → tenv_store → value → typ → Prop
  | intLit (tvs : Nat) (ctMap : ctMap_ty) (tenvS : tenv_store) (n : Int) :
      type_v tvs ctMap tenvS (Litv (lit.IntLit n)) Tint
  | char (tvs : Nat) (ctMap : ctMap_ty) (tenvS : tenv_store) (c : CmlTS.char) :
      type_v tvs ctMap tenvS (Litv (lit.Char c)) Tchar
  | strLit (tvs : Nat) (ctMap : ctMap_ty) (tenvS : tenv_store) (s : mlstring) :
      type_v tvs ctMap tenvS (Litv (lit.StrLit s)) Tstring
  | word8 (tvs : Nat) (ctMap : ctMap_ty) (tenvS : tenv_store) (w : CmlTS.word8) :
      type_v tvs ctMap tenvS (Litv (lit.Word8 w)) Tword8
  | word64 (tvs : Nat) (ctMap : ctMap_ty) (tenvS : tenv_store) (w : CmlTS.word64) :
      type_v tvs ctMap tenvS (Litv (lit.Word64 w)) Tword64
  | float64 (tvs : Nat) (ctMap : ctMap_ty) (tenvS : tenv_store) (w : CmlTS.word64) :
      type_v tvs ctMap tenvS (Litv (lit.Float64 w)) Tdouble
  | conv (tvs : Nat) (ctMap : ctMap_ty) (tenvS : tenv_store) (vs : List value)
      (tvs' : List tvarN) (stamp : CmlTS.stamp) (ts' ts : List typ) (ti : type_ident) :
      EVERY (check_freevars tvs []) ts' →
      tvs'.length = ts'.length →
      vs.length =
        (ts.map (type_subst (FUPDATE_LIST FEMPTY (tvs'.zip ts').reverse))).length →
      (∀ (i : Nat) (v : value) (t : typ), vs[i]? = some v →
        (ts.map (type_subst (FUPDATE_LIST FEMPTY (tvs'.zip ts').reverse)))[i]? = some t →
        type_v tvs ctMap tenvS v t) →
      FLOOKUP ctMap stamp = some (tvs', ts, ti) →
      type_v tvs ctMap tenvS (Conv (some stamp) vs) (Tapp ts' ti)
  | tup (tvs : Nat) (ctMap : ctMap_ty) (tenvS : tenv_store) (vs : List value) (ts : List typ) :
      vs.length = ts.length →
      (∀ (i : Nat) (v : value) (t : typ), vs[i]? = some v → ts[i]? = some t →
        type_v tvs ctMap tenvS v t) →
      type_v tvs ctMap tenvS (Conv none vs) (Ttup ts)
  | closure (tvs : Nat) (ctMap : ctMap_ty) (tenvS : tenv_store) (env : sem_env value)
      (tenv : type_env) (tenvE : tenv_val_exp) (n : varN) (e : exp) (t1 t2 : typ) :
      tenv_ok tenv →
      tenv_val_exp_ok tenvE →
      num_tvs tenvE = 0 →
      nsAll2 (type_ctor ctMap) env.c tenv.c →
      nsAll2 (fun _ _ _ => True) env.v (add_tenvE tenvE tenv.v) →
      (∀ (i : ident modN varN) (v : value) (tvs_t : Nat × typ),
        nsLookup env.v i = some v →
        nsLookup (add_tenvE tenvE tenv.v) i = some tvs_t →
        type_v tvs_t.1 ctMap tenvS v tvs_t.2) →
      check_freevars tvs [] t1 →
      type_e tenv (Bind_name n 0 t1 (bind_tvar tvs tenvE)) e t2 →
      type_v tvs ctMap tenvS (Closure env n e) (Tfn t1 t2)
  | recclosure (tvs : Nat) (ctMap : ctMap_ty) (tenvS : tenv_store) (env : sem_env value)
      (funs : List (varN × varN × exp)) (n : varN) (t : typ) (tenv : type_env)
      (tenvE : tenv_val_exp) (bindings : List (varN × typ)) :
      tenv_ok tenv →
      tenv_val_exp_ok tenvE →
      num_tvs tenvE = 0 →
      nsAll2 (type_ctor ctMap) env.c tenv.c →
      nsAll2 (fun _ _ _ => True) env.v (add_tenvE tenvE tenv.v) →
      (∀ (i : ident modN varN) (v : value) (tvs_t : Nat × typ),
        nsLookup env.v i = some v →
        nsLookup (add_tenvE tenvE tenv.v) i = some tvs_t →
        type_v tvs_t.1 ctMap tenvS v tvs_t.2) →
      type_funs tenv (bind_var_list 0 bindings (bind_tvar tvs tenvE)) funs bindings →
      ALOOKUP bindings n = some t →
      ALL_DISTINCT (funs.map Prod.fst) →
      n ∈ funs.map Prod.fst →
      type_v tvs ctMap tenvS (Recclosure env funs n) t
  | ref (tvs : Nat) (ctMap : ctMap_ty) (tenvS : tenv_store) (n : Nat) (t : typ) :
      check_freevars 0 [] t →
      FLOOKUP tenvS n = some (Ref_t t) →
      type_v tvs ctMap tenvS (Loc true n) (Tref t)
  | w8array (tvs : Nat) (ctMap : ctMap_ty) (tenvS : tenv_store) (n : Nat) :
      FLOOKUP tenvS n = some W8array_t →
      type_v tvs ctMap tenvS (Loc true n) Tword8array
  | varray (tvs : Nat) (ctMap : ctMap_ty) (tenvS : tenv_store) (n : Nat) (t : typ) :
      check_freevars 0 [] t →
      FLOOKUP tenvS n = some (Varray_t t) →
      type_v tvs ctMap tenvS (Loc true n) (Tarray t)
  | vector (tvs : Nat) (ctMap : ctMap_ty) (tenvS : tenv_store) (vs : List value) (t : typ) :
      check_freevars 0 [] t →
      (∀ v, v ∈ vs → type_v tvs ctMap tenvS v t) →
      type_v tvs ctMap tenvS (Vectorv vs) (Tvector t)

/-! The HOL4 forms of the rules of `type_v` whose premises were spelled out. -/

theorem type_v_conv_aux (tvs : Nat) (ctMap : ctMap_ty) (tenvS : tenv_store) (vs : List value)
    (tvs' : List tvarN) (stamp : CmlTS.stamp) (ts' ts : List typ) (ti : type_ident)
    (h1 : EVERY (check_freevars tvs []) ts')
    (h2 : tvs'.length = ts'.length)
    (h3 : LIST_REL (type_v tvs ctMap tenvS) vs
      (ts.map (type_subst (FUPDATE_LIST FEMPTY (tvs'.zip ts').reverse))))
    (h4 : FLOOKUP ctMap stamp = some (tvs', ts, ti)) :
    type_v tvs ctMap tenvS (Conv (some stamp) vs) (Tapp ts' ti) := by
  rw [LIST_REL_iff_aux] at h3
  exact type_v.conv tvs ctMap tenvS vs tvs' stamp ts' ts ti h1 h2 h3.1 h3.2 h4

theorem type_v_tup_aux (tvs : Nat) (ctMap : ctMap_ty) (tenvS : tenv_store) (vs : List value)
    (ts : List typ) (h : LIST_REL (type_v tvs ctMap tenvS) vs ts) :
    type_v tvs ctMap tenvS (Conv none vs) (Ttup ts) := by
  rw [LIST_REL_iff_aux] at h
  exact type_v.tup tvs ctMap tenvS vs ts h.1 h.2

theorem type_v_closure_aux (tvs : Nat) (ctMap : ctMap_ty) (tenvS : tenv_store)
    (env : sem_env value) (tenv : type_env) (tenvE : tenv_val_exp) (n : varN) (e : exp)
    (t1 t2 : typ)
    (h1 : tenv_ok tenv) (h2 : tenv_val_exp_ok tenvE) (h3 : num_tvs tenvE = 0)
    (h4 : nsAll2 (type_ctor ctMap) env.c tenv.c)
    (h5 : nsAll2 (fun _ v (tvs, t) => type_v tvs ctMap tenvS v t) env.v
      (add_tenvE tenvE tenv.v))
    (h6 : check_freevars tvs [] t1)
    (h7 : type_e tenv (Bind_name n 0 t1 (bind_tvar tvs tenvE)) e t2) :
    type_v tvs ctMap tenvS (Closure env n e) (Tfn t1 t2) := by
  rw [nsAll2_iff_aux] at h5
  exact type_v.closure tvs ctMap tenvS env tenv tenvE n e t1 t2 h1 h2 h3 h4 h5.1 h5.2 h6 h7

theorem type_v_recclosure_aux (tvs : Nat) (ctMap : ctMap_ty) (tenvS : tenv_store)
    (env : sem_env value) (funs : List (varN × varN × exp)) (n : varN) (t : typ)
    (tenv : type_env) (tenvE : tenv_val_exp) (bindings : List (varN × typ))
    (h1 : tenv_ok tenv) (h2 : tenv_val_exp_ok tenvE) (h3 : num_tvs tenvE = 0)
    (h4 : nsAll2 (type_ctor ctMap) env.c tenv.c)
    (h5 : nsAll2 (fun _ v (tvs, t) => type_v tvs ctMap tenvS v t) env.v
      (add_tenvE tenvE tenv.v))
    (h6 : type_funs tenv (bind_var_list 0 bindings (bind_tvar tvs tenvE)) funs bindings)
    (h7 : ALOOKUP bindings n = some t) (h8 : ALL_DISTINCT (funs.map Prod.fst))
    (h9 : n ∈ funs.map Prod.fst) :
    type_v tvs ctMap tenvS (Recclosure env funs n) t := by
  rw [nsAll2_iff_aux] at h5
  exact type_v.recclosure tvs ctMap tenvS env funs n t tenv tenvE bindings h1 h2 h3 h4
    h5.1 h5.2 h6 h7 h8 h9

theorem type_v_vector_aux (tvs : Nat) (ctMap : ctMap_ty) (tenvS : tenv_store) (vs : List value)
    (t : typ) (h1 : check_freevars 0 [] t)
    (h2 : EVERY (fun v => type_v tvs ctMap tenvS v t) vs) :
    type_v tvs ctMap tenvS (Vectorv vs) (Tvector t) :=
  type_v.vector tvs ctMap tenvS vs t h1 (EVERY_iff_forall.mp h2)

theorem type_v_conv_inv_aux (tvs : Nat) (ctMap : ctMap_ty) (tenvS : tenv_store)
    (vs : List value) (stamp : CmlTS.stamp) (t : typ)
    (h : type_v tvs ctMap tenvS (Conv (some stamp) vs) t) :
    ∃ tvs' ts' ts ti, t = Tapp ts' ti ∧
      EVERY (check_freevars tvs []) ts' ∧
      tvs'.length = ts'.length ∧
      LIST_REL (type_v tvs ctMap tenvS) vs
        (ts.map (type_subst (FUPDATE_LIST FEMPTY (tvs'.zip ts').reverse))) ∧
      FLOOKUP ctMap stamp = some (tvs', ts, ti) := by
  cases h with
  | conv _ _ _ _ tvs' _ ts' ts ti h1 h2 h3 h4 h5 =>
    exact ⟨tvs', ts', ts, ti, rfl, h1, h2, LIST_REL_iff_aux.mpr ⟨h3, h4⟩, h5⟩

theorem type_v_tup_inv_aux (tvs : Nat) (ctMap : ctMap_ty) (tenvS : tenv_store)
    (vs : List value) (t : typ) (h : type_v tvs ctMap tenvS (Conv none vs) t) :
    ∃ ts, t = Ttup ts ∧ LIST_REL (type_v tvs ctMap tenvS) vs ts := by
  cases h with
  | tup _ _ _ _ ts h1 h2 => exact ⟨ts, rfl, LIST_REL_iff_aux.mpr ⟨h1, h2⟩⟩

theorem type_v_closure_inv_aux (tvs : Nat) (ctMap : ctMap_ty) (tenvS : tenv_store)
    (env : sem_env value) (n : varN) (e : exp) (t : typ)
    (h : type_v tvs ctMap tenvS (Closure env n e) t) :
    ∃ tenv tenvE t1 t2, t = Tfn t1 t2 ∧
      tenv_ok tenv ∧ tenv_val_exp_ok tenvE ∧ num_tvs tenvE = 0 ∧
      nsAll2 (type_ctor ctMap) env.c tenv.c ∧
      nsAll2 (fun _ v (tvs, t) => type_v tvs ctMap tenvS v t) env.v (add_tenvE tenvE tenv.v) ∧
      check_freevars tvs [] t1 ∧
      type_e tenv (Bind_name n 0 t1 (bind_tvar tvs tenvE)) e t2 := by
  cases h with
  | closure _ _ _ _ tenv tenvE _ _ t1 t2 h1 h2 h3 h4 h5 h6 h7 h8 =>
    exact ⟨tenv, tenvE, t1, t2, rfl, h1, h2, h3, h4, nsAll2_iff_aux.mpr ⟨h5, h6⟩, h7, h8⟩

theorem type_v_recclosure_inv_aux (tvs : Nat) (ctMap : ctMap_ty) (tenvS : tenv_store)
    (env : sem_env value) (funs : List (varN × varN × exp)) (n : varN) (t : typ)
    (h : type_v tvs ctMap tenvS (Recclosure env funs n) t) :
    ∃ tenv tenvE bindings,
      tenv_ok tenv ∧ tenv_val_exp_ok tenvE ∧ num_tvs tenvE = 0 ∧
      nsAll2 (type_ctor ctMap) env.c tenv.c ∧
      nsAll2 (fun _ v (tvs, t) => type_v tvs ctMap tenvS v t) env.v (add_tenvE tenvE tenv.v) ∧
      type_funs tenv (bind_var_list 0 bindings (bind_tvar tvs tenvE)) funs bindings ∧
      ALOOKUP bindings n = some t ∧
      ALL_DISTINCT (funs.map Prod.fst) ∧
      n ∈ funs.map Prod.fst := by
  cases h with
  | recclosure _ _ _ _ _ _ _ tenv tenvE bindings h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 =>
    exact ⟨tenv, tenvE, bindings, h1, h2, h3, h4, nsAll2_iff_aux.mpr ⟨h5, h6⟩, h7, h8, h9, h10⟩

theorem type_v_vector_inv_aux (tvs : Nat) (ctMap : ctMap_ty) (tenvS : tenv_store)
    (vs : List value) (t : typ) (h : type_v tvs ctMap tenvS (Vectorv vs) t) :
    ∃ t', t = Tvector t' ∧ check_freevars 0 [] t' ∧
      EVERY (fun v => type_v tvs ctMap tenvS v t') vs := by
  cases h with
  | vector _ _ _ _ t' h1 h2 => exact ⟨t', rfl, h1, EVERY_iff_forall.mpr h2⟩

/- HOL4:
Definition type_sv_def:
  (type_sv ctMap tenvS (Refv v) (Ref_t t) ⇔ type_v 0 ctMap tenvS v t) ∧
  (type_sv ctMap tenvS (W8array v) W8array_t ⇔ T) ∧
  (type_sv ctMap tenvS (Varray vs) (Varray_t t) ⇔
    EVERY (\v. type_v 0 ctMap tenvS v t) vs) ∧
  (type_sv _ _ _ _ ⇔ F)
End -/
def type_sv (ctMap : ctMap_ty) (tenvS : tenv_store) : store_v value → store_t → Prop
  | Refv v, Ref_t t => type_v 0 ctMap tenvS v t
  | W8array _, W8array_t => True
  | Varray vs, Varray_t t => EVERY (fun v => type_v 0 ctMap tenvS v t) vs
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
def type_s (ctMap : ctMap_ty) (envS : List (store_v value)) (tenvS : tenv_store) : Prop :=
  ∀ l : Nat,
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
def ctMap_has_lists (ctMap : ctMap_ty) : Prop :=
  FLOOKUP ctMap (TypeStamp ml!"[]" list_type_num) = some ([ml!"'a"], [], Tlist_num) ∧
  FLOOKUP ctMap (TypeStamp ml!"::" list_type_num) =
    some ([ml!"'a"], [Tvar ml!"'a", Tlist (Tvar ml!"'a")], Tlist_num) ∧
  (∀ cn, cn ≠ ml!"::" ∧ cn ≠ ml!"[]" → FLOOKUP ctMap (TypeStamp cn list_type_num) = none)

/- HOL4:
Definition ctMap_has_bools_def:
  ctMap_has_bools ctMap ⇔
    FLOOKUP ctMap (TypeStamp «True» bool_type_num) = SOME ([],[],Tbool_num) ∧
    FLOOKUP ctMap (TypeStamp «False» bool_type_num) = SOME ([],[],Tbool_num) ∧
    (!cn. cn ≠ «True» ∧ cn ≠ «False» ⇒ FLOOKUP ctMap (TypeStamp cn bool_type_num) = NONE)
End -/
def ctMap_has_bools {α β : Type} (ctMap : fmap stamp (List α × List β × Nat)) : Prop :=
  FLOOKUP ctMap (TypeStamp ml!"True" bool_type_num) = some ([], [], Tbool_num) ∧
  FLOOKUP ctMap (TypeStamp ml!"False" bool_type_num) = some ([], [], Tbool_num) ∧
  (∀ cn, cn ≠ ml!"True" ∧ cn ≠ ml!"False" →
    FLOOKUP ctMap (TypeStamp cn bool_type_num) = none)

/- HOL4:
Definition good_ctMap_def:
  good_ctMap ctMap ⇔
    ctMap_ok ctMap ∧
    ctMap_has_bools ctMap ∧
    ctMap_has_exns ctMap ∧
    ctMap_has_lists ctMap
End -/
def good_ctMap (ctMap : ctMap_ty) : Prop :=
  ctMap_ok ctMap ∧ ctMap_has_bools ctMap ∧ ctMap_has_exns ctMap ∧ ctMap_has_lists ctMap

/- HOL4:
Definition consistent_ctMap_def:
  consistent_ctMap st type_ids ctMap ⇔
    (DISJOINT type_ids (FRANGE ((SND o SND) o_f ctMap))) ∧
    !cn id.
      (TypeStamp cn id ∈ FDOM ctMap ⇒ id < st.next_type_stamp) ∧
      (ExnStamp id ∈ FDOM ctMap ⇒ id < st.next_exn_stamp)
End -/
def consistent_ctMap {ffi α β γ : Type} (st : state ffi) (type_ids : Set γ)
    (ctMap : fmap stamp (α × β × γ)) : Prop :=
  DISJOINT type_ids (FRANGE (o_f (Prod.snd ∘ Prod.snd) ctMap)) ∧
  ∀ cn id,
    (TypeStamp cn id ∈ FDOM ctMap → id < st.next_type_stamp) ∧
    (ExnStamp id ∈ FDOM ctMap → id < st.next_exn_stamp)

/- HOL4:
Definition type_all_env_def:
  type_all_env ctMap tenvS env tenv ⇔
    nsAll2 (type_ctor ctMap) (sem_env_c env) tenv.c ∧
    nsAll2 (\i v (tvs,t). type_v tvs ctMap tenvS v t) (sem_env_v env) tenv.v
End -/
def type_all_env (ctMap : ctMap_ty) (tenvS : tenv_store) (env : sem_env value)
    (tenv : type_env) : Prop :=
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
def type_sound_invariant {ffi : Type} (st : state ffi) (env : sem_env value) (ctMap : ctMap_ty)
    (tenvS : tenv_store) (type_idents : Set type_ident) (tenv : type_env) : Prop :=
  tenv_ok tenv ∧
  good_ctMap ctMap ∧
  consistent_ctMap st type_idents ctMap ∧
  type_all_env ctMap tenvS env tenv ∧
  type_s ctMap st.refs tenvS

end

end CmlTS
