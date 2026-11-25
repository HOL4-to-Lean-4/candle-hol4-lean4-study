import CmlTS.Ast
import CmlTS.Namespace
import CmlTS.SemanticPrimitives
import CmlTS.TypeSystem
import CmlTS.NamespaceProps

/-!
# typeSoundInvariants (HOL4 theory `typeSoundInvariants`)

A type system for values, and the invariants that are used for type soundness.
-/

universe u v w

noncomputable section

open Classical

/- HOL4:
   Datatype:
    store_t =
    | Ref_t t
    | W8array_t
    | Varray_t t
   End -/
inductive store_t : Type where
  | Ref_t (t : Ty) : store_t
  | W8array_t : store_t
  | Varray_t (t : Ty) : store_t

/- HOL4:
   (* Store typing *)
   Type tenv_store = ``:(num, store_t) fmap`` -/
abbrev tenv_store : Type := FMap Nat store_t

/- HOL4:
   (* Check that the type names map to valid types *)
   Definition tenv_abbrev_ok_def:
     tenv_abbrev_ok tenvT ⇔ nsAll (\id (tvs,t). check_freevars 0 tvs t) tenvT
   End -/
def tenv_abbrev_ok (tenvT : tenv_abbrev) : Prop :=
  nsAll (fun _ p => check_freevars 0 p.1 p.2) tenvT

/- HOL4:
   Definition tenv_ctor_ok_def:
     tenv_ctor_ok tenvC ⇔ nsAll (\id (tvs,ts,tn). EVERY (check_freevars 0 tvs) ts) tenvC
   End -/
def tenv_ctor_ok (tenvC : tenv_ctor) : Prop :=
  nsAll (fun _ p => EVERY (check_freevars 0 p.1) p.2.1) tenvC

/- HOL4:
   Definition tenv_val_ok_def:
     tenv_val_ok tenvV ⇔ nsAll (\id (tvs,t). check_freevars tvs [] t) tenvV
   End -/
def tenv_val_ok (tenvV : tenv_val) : Prop :=
  nsAll (fun _ p => check_freevars p.1 [] p.2) tenvV

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
  | .Empty => True
  | .Bind_tvar _ tenv => tenv_val_exp_ok tenv
  | .Bind_name _ tvs t tenv => check_freevars (tvs + num_tvs tenv) [] t ∧ tenv_val_exp_ok tenv

/- HOL4:
   (* Global constructor type environments keyed by constructor name and type
    * stamp. Contains the type variables, the type of the arguments, and
    * the identity of the type. *)
   Type ctMap = ``:(stamp, (tvarN list # t list # type_ident)) fmap`` -/
abbrev ctMap : Type := FMap stamp (List tvarN × List Ty × type_ident)

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
def ctMap_ok (ctMap : ctMap) : Prop :=
  FEVERY (fun sp => EVERY (check_freevars 0 sp.2.1) sp.2.2.1) ctMap ∧
  (∀ ex tvs ts ti, FLOOKUP ctMap (.ExnStamp ex) = some (tvs, ts, ti) →
    tvs = [] ∧ ti = Texn_num) ∧
  (∀ cn x tvs ts ti, FLOOKUP ctMap (.TypeStamp cn x) = some (tvs, ts, ti) →
    ¬ MEM ti prim_type_nums) ∧
  (∀ stamp1 tvs1 ts1 ti stamp2 tvs2 ts2,
    FLOOKUP ctMap stamp1 = some (tvs1, ts1, ti) ∧
    FLOOKUP ctMap stamp2 = some (tvs2, ts2, ti) →
    same_type stamp1 stamp2)

/- HOL4:
   (* Check that a constructor type environment is consistent with a runtime type
    * enviroment, using the full type keyed constructor type environment to ensure
    * that the correct types are used. *)
   Definition type_ctor_def:
     type_ctor ctMap _ (n, stamp) (tvs, ts, ti) ⇔
       FLOOKUP ctMap stamp = SOME (tvs, ts, ti) ∧
       LENGTH ts = n
   End -/
def type_ctor (ctMap : ctMap) (_ : Ident modN conN) (ns : Nat × stamp)
    (tti : List tvarN × List Ty × type_ident) : Prop :=
  FLOOKUP ctMap ns.2 = some (tti.1, tti.2.1, tti.2.2) ∧ LENGTH tti.2.1 = ns.1

/- HOL4:
   Definition add_tenvE_def:
     (add_tenvE Empty tenvV = tenvV) ∧
     (add_tenvE (Bind_tvar _ tenvE) tenvV = add_tenvE tenvE tenvV) ∧
     (add_tenvE (Bind_name x tvs t tenvE) tenvV = nsBind x (tvs,t) (add_tenvE tenvE tenvV))
   End -/
def add_tenvE : tenv_val_exp → tenv_val → tenv_val
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
   (Lean: premises are separate constructor arguments.  Lean cannot accept the recursive
   occurrences of `type_v` inside the *definitions* `LIST_REL`, `EVERY`, `nsAll2`, so those are
   expanded (equivalently):
   * `LIST_REL (type_v ..) vs us` is `LENGTH vs = LENGTH us` together with
     `∀ i v t, vs[i]? = some v → us[i]? = some t → type_v .. v t`;
   * `EVERY (λv. type_v .. v t) vs` is `∀ v, MEM v vs → type_v .. v t`;
   * `nsAll2 (λi v (tvs,t). type_v tvs ctMap tenvS v t) env.v V` is
     `nsAll2 (λ_ _ _. T) env.v V` (same shape of the two namespaces: every identifier/module
     path of one is in the other) together with
     `∀ i v1 p, nsLookup env.v i = some v1 → nsLookup V i = some p → type_v p.1 ctMap tenvS v1 p.2`
     (this is equivalent to `nsAll2 ..` because `nsLookup` is a function).) -/
inductive type_v : Nat → ctMap → tenv_store → Value → Ty → Prop where
  | int (tvs : Nat) (ctMap : ctMap) (tenvS : tenv_store) (n : Int) :
    type_v tvs ctMap tenvS (.Litv (.IntLit n)) Tint
  | char (tvs : Nat) (ctMap : ctMap) (tenvS : tenv_store) (c : char) :
    type_v tvs ctMap tenvS (.Litv (.Char c)) Tchar
  | str (tvs : Nat) (ctMap : ctMap) (tenvS : tenv_store) (s : mlstring) :
    type_v tvs ctMap tenvS (.Litv (.StrLit s)) Tstring
  | word8 (tvs : Nat) (ctMap : ctMap) (tenvS : tenv_store) (w : word8) :
    type_v tvs ctMap tenvS (.Litv (.Word8 w)) Tword8
  | word64 (tvs : Nat) (ctMap : ctMap) (tenvS : tenv_store) (w : word64) :
    type_v tvs ctMap tenvS (.Litv (.Word64 w)) Tword64
  | float64 (tvs : Nat) (ctMap : ctMap) (tenvS : tenv_store) (w : word64) :
    type_v tvs ctMap tenvS (.Litv (.Float64 w)) Tdouble
  | conv_some (tvs : Nat) (ctMap : ctMap) (tenvS : tenv_store) (vs : List Value)
      (tvs' : List tvarN) (stamp : stamp) (ts' ts : List Ty) (ti : type_ident) :
    EVERY (check_freevars tvs []) ts' →
    LENGTH tvs' = LENGTH ts' →
    LENGTH vs = LENGTH (MAP (type_subst (FUPDATE_LIST FEMPTY (REVERSE (ZIP (tvs', ts'))))) ts) →
    (∀ (i : Nat) v t, vs[i]? = some v →
      (MAP (type_subst (FUPDATE_LIST FEMPTY (REVERSE (ZIP (tvs', ts'))))) ts)[i]? = some t →
      type_v tvs ctMap tenvS v t) →
    FLOOKUP ctMap stamp = some (tvs', ts, ti) →
    type_v tvs ctMap tenvS (.Conv (some stamp) vs) (.Tapp ts' ti)
  | conv_none (tvs : Nat) (ctMap : ctMap) (tenvS : tenv_store) (vs : List Value) (ts : List Ty) :
    LENGTH vs = LENGTH ts →
    (∀ (i : Nat) v t, vs[i]? = some v → ts[i]? = some t → type_v tvs ctMap tenvS v t) →
    type_v tvs ctMap tenvS (.Conv none vs) (Ttup ts)
  | closure (tvs : Nat) (ctMap : ctMap) (tenvS : tenv_store) (env : sem_env Value)
      (tenv : type_env) (tenvE : tenv_val_exp) (n : varN) (e : exp) (t1 t2 : Ty) :
    tenv_ok tenv →
    tenv_val_exp_ok tenvE →
    num_tvs tenvE = 0 →
    nsAll2 (type_ctor ctMap) env.c tenv.c →
    nsAll2 (fun _ _ _ => True) env.v (add_tenvE tenvE tenv.v) →
    (∀ i v1 p, nsLookup env.v i = some v1 → nsLookup (add_tenvE tenvE tenv.v) i = some p →
      type_v p.1 ctMap tenvS v1 p.2) →
    check_freevars tvs [] t1 →
    type_e tenv (.Bind_name n 0 t1 (bind_tvar tvs tenvE)) e t2 →
    type_v tvs ctMap tenvS (.Closure env n e) (Tfn t1 t2)
  | recclosure (tvs : Nat) (ctMap : ctMap) (tenvS : tenv_store) (env : sem_env Value)
      (funs : List (varN × varN × exp)) (n : varN) (t : Ty) (tenv : type_env)
      (tenvE : tenv_val_exp) (bindings : List (varN × Ty)) :
    tenv_ok tenv →
    tenv_val_exp_ok tenvE →
    num_tvs tenvE = 0 →
    nsAll2 (type_ctor ctMap) env.c tenv.c →
    nsAll2 (fun _ _ _ => True) env.v (add_tenvE tenvE tenv.v) →
    (∀ i v1 p, nsLookup env.v i = some v1 → nsLookup (add_tenvE tenvE tenv.v) i = some p →
      type_v p.1 ctMap tenvS v1 p.2) →
    type_funs tenv (bind_var_list 0 bindings (bind_tvar tvs tenvE)) funs bindings →
    ALOOKUP bindings n = some t →
    ALL_DISTINCT (MAP FST funs) →
    MEM n (MAP FST funs) →
    type_v tvs ctMap tenvS (.Recclosure env funs n) t
  | loc_ref (tvs : Nat) (ctMap : ctMap) (tenvS : tenv_store) (n : Nat) (t : Ty) :
    check_freevars 0 [] t →
    FLOOKUP tenvS n = some (.Ref_t t) →
    type_v tvs ctMap tenvS (.Loc True n) (Tref t)
  | loc_w8array (tvs : Nat) (ctMap : ctMap) (tenvS : tenv_store) (n : Nat) :
    FLOOKUP tenvS n = some .W8array_t →
    type_v tvs ctMap tenvS (.Loc True n) Tword8array
  | loc_varray (tvs : Nat) (ctMap : ctMap) (tenvS : tenv_store) (n : Nat) (t : Ty) :
    check_freevars 0 [] t →
    FLOOKUP tenvS n = some (.Varray_t t) →
    type_v tvs ctMap tenvS (.Loc True n) (Tarray t)
  | vectorv (tvs : Nat) (ctMap : ctMap) (tenvS : tenv_store) (vs : List Value) (t : Ty) :
    check_freevars 0 [] t →
    (∀ v, MEM v vs → type_v tvs ctMap tenvS v t) →
    type_v tvs ctMap tenvS (.Vectorv vs) (Tvector t)

/- HOL4:
   Definition type_sv_def:
     (type_sv ctMap tenvS (Refv v) (Ref_t t) ⇔ type_v 0 ctMap tenvS v t) ∧
     (type_sv ctMap tenvS (W8array v) W8array_t ⇔ T) ∧
     (type_sv ctMap tenvS (Varray vs) (Varray_t t) ⇔
       EVERY (\v. type_v 0 ctMap tenvS v t) vs) ∧
     (type_sv _ _ _ _ ⇔ F)
   End -/
def type_sv (ctMap : ctMap) (tenvS : tenv_store) : store_v Value → store_t → Prop
  | .Refv v, .Ref_t t => type_v 0 ctMap tenvS v t
  | .W8array _, .W8array_t => True
  | .Varray vs, .Varray_t t => EVERY (fun v => type_v 0 ctMap tenvS v t) vs
  | _, _ => False

/- HOL4:
   (* The type of the store *)
   Definition type_s_def:
     type_s ctMap envS tenvS ⇔
       (!l.
         ((?st. FLOOKUP tenvS l = SOME st) ⇔ (?v. store_lookup l envS = SOME v)) ∧
         (!st sv.
           FLOOKUP tenvS l = SOME st ∧ store_lookup l envS = SOME sv
           ⇒
           type_sv ctMap tenvS sv st))
   End -/
def type_s (ctMap : ctMap) (envS : List (store_v Value)) (tenvS : tenv_store) : Prop :=
  ∀ l,
    ((∃ st, FLOOKUP tenvS l = some st) ↔ (∃ v, store_lookup l envS = some v)) ∧
    (∀ st sv, FLOOKUP tenvS l = some st ∧ store_lookup l envS = some sv →
      type_sv ctMap tenvS sv st)

/- HOL4:
   (* The global constructor type environment has the primitive exceptions in it *)
   Definition ctMap_has_exns_def:
     ctMap_has_exns ctMap ⇔
       FLOOKUP ctMap bind_stamp = SOME ([],[],Texn_num) ∧
       FLOOKUP ctMap chr_stamp = SOME ([],[],Texn_num) ∧
       FLOOKUP ctMap div_stamp = SOME ([],[],Texn_num) ∧
       FLOOKUP ctMap subscript_stamp = SOME ([],[],Texn_num)
   End -/
def ctMap_has_exns (ctMap : ctMap) : Prop :=
  FLOOKUP ctMap bind_stamp = some ([], [], Texn_num) ∧
  FLOOKUP ctMap chr_stamp = some ([], [], Texn_num) ∧
  FLOOKUP ctMap div_stamp = some ([], [], Texn_num) ∧
  FLOOKUP ctMap subscript_stamp = some ([], [], Texn_num)

/- HOL4:
   (* The global constructor type environment has the list primitives in it *)
   Definition ctMap_has_lists_def:
     ctMap_has_lists ctMap ⇔
       FLOOKUP ctMap (TypeStamp «[]» list_type_num) = SOME ([«'a»],[],Tlist_num) ∧
       FLOOKUP ctMap (TypeStamp «::» list_type_num) =
         SOME ([«'a»],[Tvar «'a»; Tlist (Tvar «'a»)],Tlist_num) ∧
       (!cn. cn ≠ «::» ∧ cn ≠ «[]» ⇒ FLOOKUP ctMap (TypeStamp cn list_type_num) = NONE)
   End -/
def ctMap_has_lists (ctMap : ctMap) : Prop :=
  FLOOKUP ctMap (.TypeStamp (mlstr "[]") list_type_num) = some ([mlstr "'a"], [], Tlist_num) ∧
  FLOOKUP ctMap (.TypeStamp (mlstr "::") list_type_num) =
    some ([mlstr "'a"], [.Tvar (mlstr "'a"), Tlist (.Tvar (mlstr "'a"))], Tlist_num) ∧
  (∀ cn, cn ≠ mlstr "::" ∧ cn ≠ mlstr "[]" →
    FLOOKUP ctMap (.TypeStamp cn list_type_num) = none)

/- HOL4:
   (* The global constructor type environment has the bool primitives in it *)
   Definition ctMap_has_bools_def:
     ctMap_has_bools ctMap ⇔
       FLOOKUP ctMap (TypeStamp «True» bool_type_num) = SOME ([],[],Tbool_num) ∧
       FLOOKUP ctMap (TypeStamp «False» bool_type_num) = SOME ([],[],Tbool_num) ∧
       (!cn. cn ≠ «True» ∧ cn ≠ «False» ⇒ FLOOKUP ctMap (TypeStamp cn bool_type_num) = NONE)
   End -/
def ctMap_has_bools (ctMap : ctMap) : Prop :=
  FLOOKUP ctMap (.TypeStamp (mlstr "True") bool_type_num) = some ([], [], Tbool_num) ∧
  FLOOKUP ctMap (.TypeStamp (mlstr "False") bool_type_num) = some ([], [], Tbool_num) ∧
  (∀ cn, cn ≠ mlstr "True" ∧ cn ≠ mlstr "False" →
    FLOOKUP ctMap (.TypeStamp cn bool_type_num) = none)

/- HOL4:
   Definition good_ctMap_def:
     good_ctMap ctMap ⇔
       ctMap_ok ctMap ∧
       ctMap_has_bools ctMap ∧
       ctMap_has_exns ctMap ∧
       ctMap_has_lists ctMap
   End -/
def good_ctMap (ctMap : ctMap) : Prop :=
  ctMap_ok ctMap ∧ ctMap_has_bools ctMap ∧ ctMap_has_exns ctMap ∧ ctMap_has_lists ctMap

/- HOL4:
   Definition consistent_ctMap_def:
     consistent_ctMap st type_ids ctMap ⇔
       (DISJOINT type_ids (FRANGE ((SND o SND) o_f ctMap))) ∧
       !cn id.
         (TypeStamp cn id ∈ FDOM ctMap ⇒ id < st.next_type_stamp) ∧
         (ExnStamp id ∈ FDOM ctMap ⇒ id < st.next_exn_stamp)
   End -/
def consistent_ctMap {α : Type u} (st : state α) (type_ids : Set type_ident) (ctMap : ctMap) :
    Prop :=
  DISJOINT type_ids (FRANGE (o_f (SND ∘ SND) ctMap)) ∧
  ∀ cn id,
    (stamp.TypeStamp cn id ∈ FDOM ctMap → id < st.next_type_stamp) ∧
    (stamp.ExnStamp id ∈ FDOM ctMap → id < st.next_exn_stamp)

/- HOL4:
   Definition type_all_env_def:
     type_all_env ctMap tenvS env tenv ⇔
       nsAll2 (type_ctor ctMap) (sem_env_c env) tenv.c ∧
       nsAll2 (\i v (tvs,t). type_v tvs ctMap tenvS v t) (sem_env_v env) tenv.v
   End -/
def type_all_env (ctMap : ctMap) (tenvS : tenv_store) (env : sem_env Value) (tenv : type_env) :
    Prop :=
  nsAll2 (type_ctor ctMap) env.c tenv.c ∧
  nsAll2 (fun _ v p => type_v p.1 ctMap tenvS v p.2) env.v tenv.v

/- HOL4:
   Definition type_sound_invariant_def:
   type_sound_invariant st env ctMap tenvS type_idents tenv ⇔
     tenv_ok tenv ∧
     good_ctMap ctMap ∧
     consistent_ctMap st type_idents ctMap ∧
     type_all_env ctMap tenvS env tenv ∧
     type_s ctMap st.refs tenvS
   End -/
def type_sound_invariant {α : Type u} (st : state α) (env : sem_env Value) (ctMap : ctMap)
    (tenvS : tenv_store) (type_idents : Set type_ident) (tenv : type_env) : Prop :=
  tenv_ok tenv ∧
  good_ctMap ctMap ∧
  consistent_ctMap st type_idents ctMap ∧
  type_all_env ctMap tenvS env tenv ∧
  type_s ctMap st.refs tenvS

end
