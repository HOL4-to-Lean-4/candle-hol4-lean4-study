import CmlTS.Ast
import CmlTS.Namespace
import CmlTS.TypeSystem
import CmlTS.TypeSoundInvariants
import CmlTS.NamespaceProps
import CmlTS.SemanticPrimitivesProps
/-
  Translation of HOL4 theory `typeSysProps` (typeSysPropsScript.sml): definitions.
-/
set_option autoImplicit false

namespace CmlTS
open Classical

/- HOL4:
Definition type_pes_def:
  type_pes tvs tvs' tenv tenvE pes t1 t2 ⇔
    (∀(p,e)::set pes.
      ∃bindings.
        ALL_DISTINCT (pat_bindings p []) ∧
        type_p tvs tenv p t1 bindings ∧
        type_e tenv (bind_var_list tvs' bindings tenvE) e t2)
End -/
def type_pes (tvs tvs' : Nat) (tenv : type_env) (tenvE : tenv_val_exp)
    (pes : List (pat × exp)) (t1 t2 : typ) : Prop :=
  RES_FORALL (LIST_TO_SET pes) (fun (p, e) =>
    ∃ bindings,
      ALL_DISTINCT (pat_bindings p []) ∧
      type_p tvs tenv p t1 bindings ∧
      type_e tenv (bind_var_list tvs' bindings tenvE) e t2)

/- HOL4:
Definition deBruijn_subst_tenvE_def:
(deBruijn_subst_tenvE targs Empty = Empty) ∧
(deBruijn_subst_tenvE targs (Bind_tvar tvs env) =
  Bind_tvar tvs (deBruijn_subst_tenvE targs env)) ∧
(deBruijn_subst_tenvE targs (Bind_name x tvs t env) =
  Bind_name x tvs (deBruijn_subst (tvs + num_tvs env)
                                  (MAP (deBruijn_inc 0 (tvs + num_tvs env)) targs)
                                  t)
       (deBruijn_subst_tenvE targs env))
End -/
noncomputable def deBruijn_subst_tenvE (targs : List typ) : tenv_val_exp → tenv_val_exp
  | .Empty => .Empty
  | .Bind_tvar tvs env => .Bind_tvar tvs (deBruijn_subst_tenvE targs env)
  | .Bind_name x tvs t env =>
    .Bind_name x tvs
      (deBruijn_subst (tvs + num_tvs env)
        (targs.map (deBruijn_inc 0 (tvs + num_tvs env)))
        t)
      (deBruijn_subst_tenvE targs env)

/- HOL4:
Definition db_merge_def:
(db_merge Empty e = e) ∧
(db_merge (Bind_tvar tvs e1) e2 = Bind_tvar tvs (db_merge e1 e2)) ∧
(db_merge (Bind_name x tvs t e1) e2 = Bind_name x tvs t (db_merge e1 e2))
End -/
def db_merge : tenv_val_exp → tenv_val_exp → tenv_val_exp
  | .Empty, e => e
  | .Bind_tvar tvs e1, e2 => .Bind_tvar tvs (db_merge e1 e2)
  | .Bind_name x tvs t e1, e2 => .Bind_name x tvs t (db_merge e1 e2)

/- HOL4:
Definition type_def_to_ctMap_def:
  (type_def_to_ctMap tenvT next_stamp [] [] = []) ∧
  (type_def_to_ctMap tenvT next_stamp ((tvs,tn,ctors)::tds) (id::ids) =
    type_def_to_ctMap tenvT (next_stamp + 1) tds ids ++
    REVERSE
      (MAP (\(cn,ts).
        (TypeStamp cn next_stamp, (tvs, MAP (type_name_subst tenvT) ts, id)))
        ctors))
End
   (ARB when the two lists have different lengths.  As in HOL4, the types of `tvs`, `tn` and `id`
   are arbitrary.) -/
noncomputable def type_def_to_ctMap {α β γ : Type}
    (tenvT : Namespace mlstring mlstring (List mlstring × typ)) :
    Nat → List (α × β × List (mlstring × List ast_t)) → List γ →
      List (stamp × α × List typ × γ)
  | _, [], [] => []
  | next_stamp, (tvs, _, ctors) :: tds, id :: ids =>
    type_def_to_ctMap tenvT (next_stamp + 1) tds ids ++
    List.reverse
      (ctors.map fun (cn, ts) =>
        (.TypeStamp cn next_stamp, (tvs, ts.map (type_name_subst tenvT), id)))
  | _, _, _ => ARB

/-! ## Theorem statements (stage 2), in HOL4 source order -/

/- HOL4:
Theorem unchanged_tenv[simp]:
  !(tenv : type_env).
  <| v := tenv.v; c := tenv.c; t := tenv.t |> = tenv -/
theorem unchanged_tenv :
    ∀ (tenv : type_env),
      ({ v := tenv.v, c := tenv.c, t := tenv.t } : type_env) = tenv := by sorry

/- HOL4:
Theorem extend_dec_tenv_assoc[simp]:
   !tenv1 tenv2 tenv3.
    extend_dec_tenv tenv1 (extend_dec_tenv tenv2 tenv3)
    =
    extend_dec_tenv (extend_dec_tenv tenv1 tenv2) tenv3 -/
theorem extend_dec_tenv_assoc :
    ∀ (tenv1 tenv2 tenv3 : type_env),
      extend_dec_tenv tenv1 (extend_dec_tenv tenv2 tenv3)
      =
      extend_dec_tenv (extend_dec_tenv tenv1 tenv2) tenv3 := by sorry

/- HOL4:
Theorem tenv_val_ok_nsEmpty[simp]:
   tenv_val_ok nsEmpty -/
theorem tenv_val_ok_nsEmpty {m n : Type} :
    tenv_val_ok (nsEmpty : Namespace m n (Nat × typ)) := by sorry

/- HOL4:
Theorem tenv_ctor_ok_nsEmpty[simp]:
   tenv_ctor_ok nsEmpty -/
theorem tenv_ctor_ok_nsEmpty {m n α : Type} :
    tenv_ctor_ok (nsEmpty : Namespace m n (List mlstring × List typ × α)) := by sorry

/- HOL4:
Theorem tenv_abbrev_ok_nsEmpty[simp]:
   tenv_abbrev_ok nsEmpty -/
theorem tenv_abbrev_ok_nsEmpty {m n : Type} :
    tenv_abbrev_ok (nsEmpty : Namespace m n (List mlstring × typ)) := by sorry

/- HOL4:
Theorem tenv_ok_empty[simp]:
   tenv_ok <| v := nsEmpty; c := nsEmpty; t := nsEmpty |> -/
theorem tenv_ok_empty :
    tenv_ok { v := nsEmpty, c := nsEmpty, t := nsEmpty } := by sorry

/- HOL4:
Theorem check_freevars_add:
 (!tvs tvs' t. check_freevars tvs tvs' t ⇒
  !tvs''. tvs'' ≥ tvs ⇒ check_freevars tvs'' tvs' t) -/
theorem check_freevars_add :
    ∀ (tvs : Nat) (tvs' : List mlstring) (t : typ), check_freevars tvs tvs' t →
      ∀ (tvs'' : Nat), tvs'' ≥ tvs → check_freevars tvs'' tvs' t := by sorry

/- HOL4:
Theorem check_freevars_subst_single:
 !dbmax tvs t tvs' ts.
  LENGTH tvs = LENGTH ts ∧
  check_freevars dbmax tvs t ∧
  EVERY (check_freevars dbmax tvs') ts
  ⇒
  check_freevars dbmax tvs' (type_subst (alist_to_fmap (ZIP (tvs,ts))) t) -/
theorem check_freevars_subst_single :
    ∀ (dbmax : Nat) (tvs : List mlstring) (t : typ) (tvs' : List mlstring) (ts : List typ),
      tvs.length = ts.length ∧
      check_freevars dbmax tvs t ∧
      EVERY (check_freevars dbmax tvs') ts
      →
      check_freevars dbmax tvs' (type_subst (alist_to_fmap (List.zip tvs ts)) t) := by sorry

/- HOL4:
Theorem deBruijn_inc0:
 (!t sk. deBruijn_inc sk 0 t = t) ∧
 (!ts sk. MAP (deBruijn_inc sk 0) ts = ts) -/
theorem deBruijn_inc0 :
    (∀ (t : typ) (sk : Nat), deBruijn_inc sk 0 t = t) ∧
    (∀ (ts : List typ) (sk : Nat), ts.map (deBruijn_inc sk 0) = ts) := by sorry

/- HOL4:
Theorem deBruijn_inc_deBruijn_inc:
 !sk i2 t i1.
  deBruijn_inc sk i1 (deBruijn_inc sk i2 t) = deBruijn_inc sk (i1 + i2) t -/
theorem deBruijn_inc_deBruijn_inc :
    ∀ (sk i2 : Nat) (t : typ) (i1 : Nat),
      deBruijn_inc sk i1 (deBruijn_inc sk i2 t) = deBruijn_inc sk (i1 + i2) t := by sorry

/- HOL4:
Theorem deBuijn_inc_lem1[local]:
  !sk i2 t i1.
  deBruijn_inc sk i1 (deBruijn_inc 0 (sk + i2) t) = deBruijn_inc 0 (i1 + (sk + i2)) t -/
theorem deBuijn_inc_lem1 :
    ∀ (sk i2 : Nat) (t : typ) (i1 : Nat),
      deBruijn_inc sk i1 (deBruijn_inc 0 (sk + i2) t) =
        deBruijn_inc 0 (i1 + (sk + i2)) t := by sorry

/- HOL4:
Theorem type_subst_deBruijn_inc_single[local]:
  !s t ts tvs inc sk.
  (LENGTH tvs = LENGTH ts) ∧
  (s = alist_to_fmap (ZIP (tvs,ts))) ∧
  check_freevars 0 tvs t ⇒
  (deBruijn_inc sk inc (type_subst s t) =
   type_subst (alist_to_fmap (ZIP (tvs, MAP (\t. deBruijn_inc sk inc t) ts))) t) -/
theorem type_subst_deBruijn_inc_single :
    ∀ (s : fmap mlstring typ) (t : typ) (ts : List typ) (tvs : List mlstring) (inc sk : Nat),
      tvs.length = ts.length ∧
      s = alist_to_fmap (List.zip tvs ts) ∧
      check_freevars 0 tvs t →
      deBruijn_inc sk inc (type_subst s t) =
        type_subst (alist_to_fmap (List.zip tvs (ts.map (fun t => deBruijn_inc sk inc t)))) t := by
  sorry

/- HOL4:
Theorem type_subst_deBruijn_inc_list:
 !ts' ts tvs inc sk.
  (LENGTH tvs = LENGTH ts) ∧
  EVERY (check_freevars 0 tvs) ts' ⇒
  (MAP (deBruijn_inc sk inc) (MAP (type_subst (alist_to_fmap (ZIP (tvs,ts)))) ts') =
   MAP (type_subst (alist_to_fmap (ZIP (tvs, MAP (\t. deBruijn_inc sk inc t) ts)))) ts') -/
theorem type_subst_deBruijn_inc_list :
    ∀ (ts' ts : List typ) (tvs : List mlstring) (inc sk : Nat),
      tvs.length = ts.length ∧
      EVERY (check_freevars 0 tvs) ts' →
      (ts'.map (type_subst (alist_to_fmap (List.zip tvs ts)))).map (deBruijn_inc sk inc) =
        ts'.map (type_subst
          (alist_to_fmap (List.zip tvs (ts.map (fun t => deBruijn_inc sk inc t))))) := by sorry

/- HOL4:
Theorem check_freevars_deBruijn_inc[local]:
  !tvs tvs' t. check_freevars tvs tvs' t ⇒
  !n n'. check_freevars (n+tvs) tvs' (deBruijn_inc n' n t) -/
theorem check_freevars_deBruijn_inc :
    ∀ (tvs : Nat) (tvs' : List mlstring) (t : typ), check_freevars tvs tvs' t →
      ∀ (n n' : Nat), check_freevars (n + tvs) tvs' (deBruijn_inc n' n t) := by sorry

/- HOL4:
Theorem nil_deBruijn_inc:
 ∀skip tvs t.
  (check_freevars skip [] t ∨ check_freevars skip [] (deBruijn_inc skip tvs t))
  ⇒
  (deBruijn_inc skip tvs t = t) -/
theorem nil_deBruijn_inc :
    ∀ (skip tvs : Nat) (t : typ),
      (check_freevars skip [] t ∨ check_freevars skip [] (deBruijn_inc skip tvs t))
      →
      deBruijn_inc skip tvs t = t := by sorry

/- HOL4:
Theorem deBruijn_subst_check_freevars:
 !tvs tvs' t ts n.
  check_freevars tvs tvs' t ∧
  EVERY (check_freevars tvs tvs') ts
  ⇒
  check_freevars tvs tvs' (deBruijn_subst 0 ts t)
   (`n` is unused, its HOL4 type is a type variable) -/
theorem deBruijn_subst_check_freevars {α : Type} :
    ∀ (tvs : Nat) (tvs' : List mlstring) (t : typ) (ts : List typ) (_n : α),
      check_freevars tvs tvs' t ∧
      EVERY (check_freevars tvs tvs') ts
      →
      check_freevars tvs tvs' (deBruijn_subst 0 ts t) := by sorry

/- HOL4:
Theorem deBruijn_subst_check_freevars2:
 !tvs tvs' t ts n tvs''.
  check_freevars (LENGTH ts) tvs' t ∧
  EVERY (check_freevars tvs tvs') ts
  ⇒
  check_freevars tvs tvs' (deBruijn_subst 0 ts t)
   (`n` and `tvs''` are unused, their HOL4 types are type variables) -/
theorem deBruijn_subst_check_freevars2 {α β : Type} :
    ∀ (tvs : Nat) (tvs' : List mlstring) (t : typ) (ts : List typ) (_n : α) (_tvs'' : β),
      check_freevars ts.length tvs' t ∧
      EVERY (check_freevars tvs tvs') ts
      →
      check_freevars tvs tvs' (deBruijn_subst 0 ts t) := by sorry

/- HOL4:
Theorem check_freevars_subst_inc:
 ∀tvs tvs2 t.
  check_freevars tvs tvs2 t ⇒
  ∀tvs' targs tvs1.
  tvs = LENGTH targs + tvs' ∧
  EVERY (check_freevars (tvs1 + tvs') tvs2) targs
  ⇒
  check_freevars (tvs1 + tvs') tvs2
     (deBruijn_subst 0 targs (deBruijn_inc (LENGTH targs) tvs1 t)) -/
theorem check_freevars_subst_inc :
    ∀ (tvs : Nat) (tvs2 : List mlstring) (t : typ),
      check_freevars tvs tvs2 t →
      ∀ (tvs' : Nat) (targs : List typ) (tvs1 : Nat),
        tvs = targs.length + tvs' ∧
        EVERY (check_freevars (tvs1 + tvs') tvs2) targs
        →
        check_freevars (tvs1 + tvs') tvs2
          (deBruijn_subst 0 targs (deBruijn_inc targs.length tvs1 t)) := by sorry

/- HOL4:
Theorem check_freevars_subst:
 ∀tvs tvs2 t.
  check_freevars tvs tvs2 t ⇒
  ∀tvs' targs tvs1.
  tvs = LENGTH targs + tvs' ∧
  EVERY (check_freevars (tvs1 + tvs') tvs2) targs
  ⇒
  check_freevars (tvs1 + tvs') tvs2 (deBruijn_subst 0 targs t) -/
theorem check_freevars_subst :
    ∀ (tvs : Nat) (tvs2 : List mlstring) (t : typ),
      check_freevars tvs tvs2 t →
      ∀ (tvs' : Nat) (targs : List typ) (tvs1 : Nat),
        tvs = targs.length + tvs' ∧
        EVERY (check_freevars (tvs1 + tvs') tvs2) targs
        →
        check_freevars (tvs1 + tvs') tvs2 (deBruijn_subst 0 targs t) := by sorry

/- HOL4:
Theorem type_subst_deBruijn_subst_single[local]:
  !s t tvs tvs' ts ts' inc.
  (LENGTH tvs = LENGTH ts) ∧
  check_freevars 0 tvs t ∧
  (s = alist_to_fmap (ZIP (tvs,ts))) ⇒
  (deBruijn_subst inc ts' (type_subst (alist_to_fmap (ZIP (tvs,ts))) t) =
   type_subst (alist_to_fmap (ZIP (tvs,MAP (\t. deBruijn_subst inc ts' t) ts))) t)
   (`tvs'` is unused, its HOL4 type is a type variable) -/
theorem type_subst_deBruijn_subst_single {α : Type} :
    ∀ (s : fmap mlstring typ) (t : typ) (tvs : List mlstring) (_tvs' : α) (ts ts' : List typ)
      (inc : Nat),
      tvs.length = ts.length ∧
      check_freevars 0 tvs t ∧
      s = alist_to_fmap (List.zip tvs ts) →
      deBruijn_subst inc ts' (type_subst (alist_to_fmap (List.zip tvs ts)) t) =
        type_subst
          (alist_to_fmap (List.zip tvs (ts.map (fun t => deBruijn_subst inc ts' t)))) t := by
  sorry

/- HOL4:
Theorem type_subst_deBruijn_subst_list:
 !t tvs tvs' ts ts' ts'' inc.
  (LENGTH tvs = LENGTH ts) ∧
  EVERY (check_freevars 0 tvs) ts'' ⇒
  (MAP (deBruijn_subst inc ts') (MAP (type_subst (alist_to_fmap (ZIP (tvs,ts)))) ts'') =
   MAP (type_subst (alist_to_fmap (ZIP (tvs,MAP (\t. deBruijn_subst inc ts' t) ts)))) ts'')
   (the outer `t` and `tvs'` are unused, their HOL4 types are type variables) -/
theorem type_subst_deBruijn_subst_list {α β : Type} :
    ∀ (_t : α) (tvs : List mlstring) (_tvs' : β) (ts ts' ts'' : List typ) (inc : Nat),
      tvs.length = ts.length ∧
      EVERY (check_freevars 0 tvs) ts'' →
      (ts''.map (type_subst (alist_to_fmap (List.zip tvs ts)))).map (deBruijn_subst inc ts') =
        ts''.map (type_subst
          (alist_to_fmap (List.zip tvs (ts.map (fun t => deBruijn_subst inc ts' t))))) := by sorry

/- HOL4:
Theorem check_freevars_lem[local]:
  !l tvs' t.
  check_freevars l tvs' t ⇒
  !targs n1 tvs.
    (l = n1 + (LENGTH targs)) ∧
    EVERY (check_freevars tvs tvs') targs
     ⇒
     check_freevars (n1 + tvs) tvs'
       (deBruijn_subst n1 (MAP (deBruijn_inc 0 n1) targs) t) -/
theorem check_freevars_lem :
    ∀ (l : Nat) (tvs' : List mlstring) (t : typ),
      check_freevars l tvs' t →
      ∀ (targs : List typ) (n1 tvs : Nat),
        l = n1 + targs.length ∧
        EVERY (check_freevars tvs tvs') targs
        →
        check_freevars (n1 + tvs) tvs'
          (deBruijn_subst n1 (targs.map (deBruijn_inc 0 n1)) t) := by sorry

/- HOL4:
Theorem nil_deBruijn_subst:
 ∀skip tvs t. check_freevars skip [] t ⇒ (deBruijn_subst skip tvs t = t) -/
theorem nil_deBruijn_subst :
    ∀ (skip : Nat) (tvs : List typ) (t : typ),
      check_freevars skip [] t → deBruijn_subst skip tvs t = t := by sorry

/- HOL4:
Theorem deBruijn_subst2:
 (!t sk targs targs' tvs'.
  check_freevars (LENGTH targs) [] t ⇒
  (deBruijn_subst sk (MAP (deBruijn_inc 0 sk) targs') (deBruijn_subst 0 targs t) =
   deBruijn_subst 0 (MAP (deBruijn_subst sk (MAP (deBruijn_inc 0 sk) targs')) targs) t)) ∧
 (!ts sk targs targs' tvs'.
  EVERY (check_freevars (LENGTH targs) []) ts ⇒
  (MAP (deBruijn_subst sk (MAP (deBruijn_inc 0 sk) targs')) (MAP (deBruijn_subst 0 targs) ts) =
  (MAP (deBruijn_subst 0 (MAP (deBruijn_subst sk (MAP (deBruijn_inc 0 sk) targs')) targs)) ts)))
   (both `tvs'` are unused, their HOL4 types are type variables) -/
theorem deBruijn_subst2 {α β : Type} :
    (∀ (t : typ) (sk : Nat) (targs targs' : List typ) (_tvs' : α),
      check_freevars targs.length [] t →
      deBruijn_subst sk (targs'.map (deBruijn_inc 0 sk)) (deBruijn_subst 0 targs t) =
        deBruijn_subst 0
          (targs.map (deBruijn_subst sk (targs'.map (deBruijn_inc 0 sk)))) t) ∧
    (∀ (ts : List typ) (sk : Nat) (targs targs' : List typ) (_tvs' : β),
      EVERY (check_freevars targs.length []) ts →
      (ts.map (deBruijn_subst 0 targs)).map
          (deBruijn_subst sk (targs'.map (deBruijn_inc 0 sk))) =
        ts.map (deBruijn_subst 0
          (targs.map (deBruijn_subst sk (targs'.map (deBruijn_inc 0 sk)))))) := by sorry

/- HOL4:
Theorem type_e_subst_lem3:
 ∀tvs tvs2 t.
  check_freevars tvs tvs2 t ⇒
  ∀tvs' targs n.
  (tvs = n + LENGTH targs) ∧
  EVERY (check_freevars tvs' tvs2) targs
  ⇒
  check_freevars (n + tvs') tvs2
     (deBruijn_subst n (MAP (deBruijn_inc 0 n) targs) t) -/
theorem type_e_subst_lem3 :
    ∀ (tvs : Nat) (tvs2 : List mlstring) (t : typ),
      check_freevars tvs tvs2 t →
      ∀ (tvs' : Nat) (targs : List typ) (n : Nat),
        tvs = n + targs.length ∧
        EVERY (check_freevars tvs' tvs2) targs
        →
        check_freevars (n + tvs') tvs2
          (deBruijn_subst n (targs.map (deBruijn_inc 0 n)) t) := by sorry

/- HOL4:
Theorem type_e_subst_lem5[local]:
  (!t n inc n' targs.
   deBruijn_inc n inc
         (deBruijn_subst (n + n') (MAP (deBruijn_inc 0 (n + n')) targs) t) =
   deBruijn_subst (n + inc + n') (MAP (deBruijn_inc 0 (n + inc + n')) targs)
         (deBruijn_inc n inc t)) ∧
 (!ts n inc n' targs.
   MAP (deBruijn_inc n inc)
         (MAP (deBruijn_subst (n + n') (MAP (deBruijn_inc 0 (n + n')) targs)) ts) =
   MAP (deBruijn_subst (n + inc + n') (MAP (deBruijn_inc 0 (n + inc + n')) targs))
         (MAP (deBruijn_inc n inc) ts)) -/
theorem type_e_subst_lem5 :
    (∀ (t : typ) (n inc n' : Nat) (targs : List typ),
      deBruijn_inc n inc
          (deBruijn_subst (n + n') (targs.map (deBruijn_inc 0 (n + n'))) t) =
        deBruijn_subst (n + inc + n') (targs.map (deBruijn_inc 0 (n + inc + n')))
          (deBruijn_inc n inc t)) ∧
    (∀ (ts : List typ) (n inc n' : Nat) (targs : List typ),
      (ts.map (deBruijn_subst (n + n') (targs.map (deBruijn_inc 0 (n + n'))))).map
          (deBruijn_inc n inc) =
        (ts.map (deBruijn_inc n inc)).map
          (deBruijn_subst (n + inc + n') (targs.map (deBruijn_inc 0 (n + inc + n'))))) := by
  sorry

/- HOL4:
Theorem subst_inc_cancel:
 (!t ts inc.
  deBruijn_subst 0 ts (deBruijn_inc 0 (inc + LENGTH ts) t)
  =
  deBruijn_inc 0 inc t) ∧
 (!ts' ts inc.
  MAP (deBruijn_subst 0 ts) (MAP (deBruijn_inc 0 (inc + LENGTH ts)) ts')
  =
  MAP (deBruijn_inc 0 inc) ts') -/
theorem subst_inc_cancel :
    (∀ (t : typ) (ts : List typ) (inc : Nat),
      deBruijn_subst 0 ts (deBruijn_inc 0 (inc + ts.length) t)
      =
      deBruijn_inc 0 inc t) ∧
    (∀ (ts' ts : List typ) (inc : Nat),
      (ts'.map (deBruijn_inc 0 (inc + ts.length))).map (deBruijn_subst 0 ts)
      =
      ts'.map (deBruijn_inc 0 inc)) := by sorry

/- HOL4:
Theorem type_e_subst_lem7[local]:
  (!t sk targs targs' tvs' tvs''.
  (deBruijn_subst sk (MAP (deBruijn_inc 0 sk) targs') (deBruijn_subst 0 targs t) =
   deBruijn_subst 0 (MAP (deBruijn_subst sk (MAP (deBruijn_inc 0 sk) targs')) targs)
     (deBruijn_subst (LENGTH targs + sk) (MAP (deBruijn_inc 0 (LENGTH targs + sk)) targs') t))) ∧
 (!ts sk targs targs' tvs' tvs''.
  (MAP (deBruijn_subst sk (MAP (deBruijn_inc 0 sk) targs')) (MAP (deBruijn_subst 0 targs) ts) =
  (MAP (deBruijn_subst 0 (MAP (deBruijn_subst sk (MAP (deBruijn_inc 0 sk) targs')) targs))
       (MAP (deBruijn_subst (LENGTH targs + sk) (MAP (deBruijn_inc 0 (LENGTH targs + sk)) targs')) ts))))
   (all `tvs'` and `tvs''` are unused, their HOL4 types are type variables) -/
theorem type_e_subst_lem7 {α β γ δ : Type} :
    (∀ (t : typ) (sk : Nat) (targs targs' : List typ) (_tvs' : α) (_tvs'' : β),
      deBruijn_subst sk (targs'.map (deBruijn_inc 0 sk)) (deBruijn_subst 0 targs t) =
        deBruijn_subst 0 (targs.map (deBruijn_subst sk (targs'.map (deBruijn_inc 0 sk))))
          (deBruijn_subst (targs.length + sk)
            (targs'.map (deBruijn_inc 0 (targs.length + sk))) t)) ∧
    (∀ (ts : List typ) (sk : Nat) (targs targs' : List typ) (_tvs' : γ) (_tvs'' : δ),
      (ts.map (deBruijn_subst 0 targs)).map
          (deBruijn_subst sk (targs'.map (deBruijn_inc 0 sk))) =
        (ts.map (deBruijn_subst (targs.length + sk)
            (targs'.map (deBruijn_inc 0 (targs.length + sk))))).map
          (deBruijn_subst 0
            (targs.map (deBruijn_subst sk (targs'.map (deBruijn_inc 0 sk)))))) := by sorry

/- HOL4:
Theorem deBruijn_subst_id:
 (!t n. check_freevars n [] t ⇒ (deBruijn_subst 0 (MAP Tvar_db (COUNT_LIST n)) t = t)) ∧
 (!ts n. EVERY (check_freevars n []) ts ⇒ (MAP (deBruijn_subst 0 (MAP Tvar_db (COUNT_LIST n))) ts = ts)) -/
theorem deBruijn_subst_id :
    (∀ (t : typ) (n : Nat), check_freevars n [] t →
      deBruijn_subst 0 ((COUNT_LIST n).map Tvar_db) t = t) ∧
    (∀ (ts : List typ) (n : Nat), EVERY (check_freevars n []) ts →
      ts.map (deBruijn_subst 0 ((COUNT_LIST n).map Tvar_db)) = ts) := by sorry

/- HOL4:
Theorem deBruijn_subst_freevars:
 !skip targs t tvs.
  skip = 0 ∧
  EVERY (check_freevars tvs []) targs ∧
  check_freevars (LENGTH targs) [] t
  ⇒
  check_freevars tvs [] (deBruijn_subst skip targs t) -/
theorem deBruijn_subst_freevars :
    ∀ (skip : Nat) (targs : List typ) (t : typ) (tvs : Nat),
      skip = 0 ∧
      EVERY (check_freevars tvs []) targs ∧
      check_freevars targs.length [] t
      →
      check_freevars tvs [] (deBruijn_subst skip targs t) := by sorry

/- HOL4:
Theorem tenv_abbrev_ok_lookup:
 !tenvT tn tvs t.
  tenv_abbrev_ok tenvT ∧
  nsLookup tenvT tn = SOME (tvs,t)
  ⇒
  check_freevars 0 tvs t -/
theorem tenv_abbrev_ok_lookup {m n : Type} :
    ∀ (tenvT : Namespace m n (List mlstring × typ)) (tn : ident m n) (tvs : List mlstring)
      (t : typ),
      tenv_abbrev_ok tenvT ∧
      nsLookup tenvT tn = some (tvs, t)
      →
      check_freevars 0 tvs t := by sorry

/- HOL4:
Theorem check_freevars_type_name_subst:
 !tvs t dbmax tenvT.
  tenv_abbrev_ok tenvT ∧
  check_type_names tenvT t ∧
  check_freevars_ast tvs t
  ⇒
  check_freevars dbmax tvs (type_name_subst tenvT t) -/
theorem check_freevars_type_name_subst :
    ∀ (tvs : List mlstring) (t : ast_t) (dbmax : Nat)
      (tenvT : Namespace mlstring mlstring (List mlstring × typ)),
      tenv_abbrev_ok tenvT ∧
      check_type_names tenvT t ∧
      check_freevars_ast tvs t
      →
      check_freevars dbmax tvs (type_name_subst tenvT t) := by sorry

/- HOL4:
Theorem tenv_ctor_ok_merge[simp]:
   !tenvC1 tenvC2.
    tenv_ctor_ok tenvC1 ∧ tenv_ctor_ok tenvC2
    ⇒
    tenv_ctor_ok (nsAppend tenvC1 tenvC2) -/
theorem tenv_ctor_ok_merge {m n α : Type} :
    ∀ (tenvC1 tenvC2 : Namespace m n (List mlstring × List typ × α)),
      tenv_ctor_ok tenvC1 ∧ tenv_ctor_ok tenvC2
      →
      tenv_ctor_ok (nsAppend tenvC1 tenvC2) := by sorry

/- HOL4:
Theorem tenv_ctor_ok_lookup:
   !tenvC cn tvs ts tn.
    tenv_ctor_ok tenvC ∧ nsLookup tenvC cn = SOME (tvs,ts,tn)
    ⇒
    EVERY (check_freevars 0 tvs) ts -/
theorem tenv_ctor_ok_lookup {m n α : Type} :
    ∀ (tenvC : Namespace m n (List mlstring × List typ × α)) (cn : ident m n)
      (tvs : List mlstring) (ts : List typ) (tn : α),
      tenv_ctor_ok tenvC ∧ nsLookup tenvC cn = some (tvs, ts, tn)
      →
      EVERY (check_freevars 0 tvs) ts := by sorry

/- HOL4:
Theorem bind_tvar_rewrites[simp]:
   (!tvs e1 e2. db_merge (bind_tvar tvs e1) e2 = bind_tvar tvs (db_merge e1 e2)) ∧
   (!tvs e. num_tvs (bind_tvar tvs e) = tvs + num_tvs e) ∧
   (!tvs e. num_tvs (Bind_tvar tvs e) = tvs + num_tvs e) ∧
   (!tvs n t e. num_tvs (Bind_name n tvs t e) = num_tvs e) ∧
   (!tvs e. num_tvs Empty = 0) ∧
   (!n inc tvs e. tveLookup n inc (bind_tvar tvs e) = tveLookup n (inc+tvs) e) ∧
   (!tvs e. tenv_val_exp_ok (bind_tvar tvs e) ⇔ tenv_val_exp_ok e) ∧
   (!targs tvs e.
     deBruijn_subst_tenvE targs (bind_tvar tvs e) =
     bind_tvar tvs (deBruijn_subst_tenvE targs e))
   (in the fifth conjunct `tvs` and `e` are unused, their HOL4 types are type variables) -/
theorem bind_tvar_rewrites {α β : Type} :
    (∀ (tvs : Nat) (e1 e2 : tenv_val_exp),
      db_merge (bind_tvar tvs e1) e2 = bind_tvar tvs (db_merge e1 e2)) ∧
    (∀ (tvs : Nat) (e : tenv_val_exp), num_tvs (bind_tvar tvs e) = tvs + num_tvs e) ∧
    (∀ (tvs : Nat) (e : tenv_val_exp), num_tvs (.Bind_tvar tvs e) = tvs + num_tvs e) ∧
    (∀ (tvs : Nat) (n : varN) (t : typ) (e : tenv_val_exp),
      num_tvs (.Bind_name n tvs t e) = num_tvs e) ∧
    (∀ (_tvs : α) (_e : β), num_tvs .Empty = 0) ∧
    (∀ (n : mlstring) (inc tvs : Nat) (e : tenv_val_exp),
      tveLookup n inc (bind_tvar tvs e) = tveLookup n (inc + tvs) e) ∧
    (∀ (tvs : Nat) (e : tenv_val_exp),
      tenv_val_exp_ok (bind_tvar tvs e) ↔ tenv_val_exp_ok e) ∧
    (∀ (targs : List typ) (tvs : Nat) (e : tenv_val_exp),
      deBruijn_subst_tenvE targs (bind_tvar tvs e) =
        bind_tvar tvs (deBruijn_subst_tenvE targs e)) := by sorry

/- HOL4:
Theorem bind_tvar0[simp]:
 !x. bind_tvar 0 x = x -/
theorem bind_tvar0 :
    ∀ (x : tenv_val_exp), bind_tvar 0 x = x := by sorry

/- HOL4:
Theorem tveLookup_subst_none:
 !n inc e.
 tveLookup n inc (deBruijn_subst_tenvE targs e) = NONE ⇔
 tveLookup n inc e = NONE -/
theorem tveLookup_subst_none (targs : List typ) :
    ∀ (n : mlstring) (inc : Nat) (e : tenv_val_exp),
      tveLookup n inc (deBruijn_subst_tenvE targs e) = none ↔
      tveLookup n inc e = none := by sorry

/- HOL4:
Theorem tveLookup_db_merge_none:
 !n inc e1 e2.
  tveLookup n inc (db_merge e1 e2) = NONE
  ⇔
  tveLookup n inc e1 = NONE ∧ tveLookup n (num_tvs e1 + inc) e2 = NONE -/
theorem tveLookup_db_merge_none :
    ∀ (n : mlstring) (inc : Nat) (e1 e2 : tenv_val_exp),
      tveLookup n inc (db_merge e1 e2) = none
      ↔
      tveLookup n inc e1 = none ∧ tveLookup n (num_tvs e1 + inc) e2 = none := by sorry

/- HOL4:
Theorem tveLookup_inc_none:
 !n inc e.
  tveLookup n inc e = NONE
  ⇔
  tveLookup n 0 e = NONE -/
theorem tveLookup_inc_none :
    ∀ (n : mlstring) (inc : Nat) (e : tenv_val_exp),
      tveLookup n inc e = none
      ↔
      tveLookup n 0 e = none := by sorry

/- HOL4:
Theorem tveLookup_freevars:
   !n tvs tenvE tvs' t.
    tenv_val_exp_ok tenvE ∧
    num_tvs tenvE = 0 ∧
    tveLookup n tvs tenvE = SOME (tvs',t)
    ⇒
    check_freevars tvs' [] t -/
theorem tveLookup_freevars :
    ∀ (n : mlstring) (tvs : Nat) (tenvE : tenv_val_exp) (tvs' : Nat) (t : typ),
      tenv_val_exp_ok tenvE ∧
      num_tvs tenvE = 0 ∧
      tveLookup n tvs tenvE = some (tvs', t)
      →
      check_freevars tvs' [] t := by sorry

/- HOL4:
Theorem bind_var_list_append:
 !n te1 te2 te3.
  bind_var_list n (te1++te2) te3 = bind_var_list n te1 (bind_var_list n te2 te3) -/
theorem bind_var_list_append :
    ∀ (n : Nat) (te1 te2 : List (mlstring × typ)) (te3 : tenv_val_exp),
      bind_var_list n (te1 ++ te2) te3 =
        bind_var_list n te1 (bind_var_list n te2 te3) := by sorry

/- HOL4:
Theorem num_tvs_bind_var_list[simp]:
 !tvs env tenvE. num_tvs (bind_var_list tvs env tenvE) = num_tvs tenvE -/
theorem num_tvs_bind_var_list :
    ∀ (tvs : Nat) (env : List (mlstring × typ)) (tenvE : tenv_val_exp),
      num_tvs (bind_var_list tvs env tenvE) = num_tvs tenvE := by sorry

/- HOL4:
Theorem tenv_val_exp_ok_bvl:
 !tenvE env.
  tenv_val_exp_ok tenvE ∧ EVERY (check_freevars (num_tvs tenvE) []) (MAP SND env)
  ⇒
  tenv_val_exp_ok (bind_var_list 0 env tenvE) -/
theorem tenv_val_exp_ok_bvl :
    ∀ (tenvE : tenv_val_exp) (env : List (mlstring × typ)),
      tenv_val_exp_ok tenvE ∧ EVERY (check_freevars (num_tvs tenvE) []) (env.map Prod.snd)
      →
      tenv_val_exp_ok (bind_var_list 0 env tenvE) := by sorry

/- HOL4:
Theorem tveLookup_subst_some:
   ∀n e targs tvs t inc.
    tveLookup n inc e = SOME (tvs,t)
    ⇒
    tveLookup n inc (deBruijn_subst_tenvE targs e) =
      SOME (tvs, deBruijn_subst (tvs+inc+num_tvs e) (MAP (deBruijn_inc 0 (tvs+inc+num_tvs e)) targs) t) -/
theorem tveLookup_subst_some :
    ∀ (n : mlstring) (e : tenv_val_exp) (targs : List typ) (tvs : Nat) (t : typ) (inc : Nat),
      tveLookup n inc e = some (tvs, t)
      →
      tveLookup n inc (deBruijn_subst_tenvE targs e) =
        some (tvs, deBruijn_subst (tvs + inc + num_tvs e)
          (targs.map (deBruijn_inc 0 (tvs + inc + num_tvs e))) t) := by sorry

/- HOL4:
Theorem num_tvs_db_merge[simp]:
 !e1 e2. num_tvs (db_merge e1 e2) = num_tvs e1 + num_tvs e2 -/
theorem num_tvs_db_merge :
    ∀ (e1 e2 : tenv_val_exp), num_tvs (db_merge e1 e2) = num_tvs e1 + num_tvs e2 := by sorry

/- HOL4:
Theorem num_tvs_deBruijn_subst_tenvE[simp]:
 !targs tenvE. num_tvs (deBruijn_subst_tenvE targs tenvE) = num_tvs tenvE -/
theorem num_tvs_deBruijn_subst_tenvE :
    ∀ (targs : List typ) (tenvE : tenv_val_exp),
      num_tvs (deBruijn_subst_tenvE targs tenvE) = num_tvs tenvE := by sorry

/- HOL4:
Theorem tveLookup_inc_some:
 !n inc e tvs t inc2.
   tveLookup n inc e = SOME (tvs, t)
   ⇒
   ?t'. (t = deBruijn_inc tvs inc t') ∧
        (tveLookup n inc2 e = SOME (tvs, deBruijn_inc tvs inc2 t')) -/
theorem tveLookup_inc_some :
    ∀ (n : mlstring) (inc : Nat) (e : tenv_val_exp) (tvs : Nat) (t : typ) (inc2 : Nat),
      tveLookup n inc e = some (tvs, t)
      →
      ∃ (t' : typ), t = deBruijn_inc tvs inc t' ∧
        tveLookup n inc2 e = some (tvs, deBruijn_inc tvs inc2 t') := by sorry

/- HOL4:
Theorem tveLookup_freevars_subst:
   !tenvE targs n t inc.
    EVERY (check_freevars (inc + num_tvs tenvE) []) targs ∧
    tveLookup n inc tenvE = SOME (LENGTH targs,t) ∧
    tenv_val_exp_ok tenvE
    ⇒
    check_freevars (inc + num_tvs tenvE) [] (deBruijn_subst 0 targs t) -/
theorem tveLookup_freevars_subst :
    ∀ (tenvE : tenv_val_exp) (targs : List typ) (n : mlstring) (t : typ) (inc : Nat),
      EVERY (check_freevars (inc + num_tvs tenvE) []) targs ∧
      tveLookup n inc tenvE = some (targs.length, t) ∧
      tenv_val_exp_ok tenvE
      →
      check_freevars (inc + num_tvs tenvE) [] (deBruijn_subst 0 targs t) := by sorry

/- HOL4:
Theorem tenv_val_exp_ok_db_merge:
 !e1 e2. tenv_val_exp_ok (db_merge e1 e2) ⇒ tenv_val_exp_ok e2 -/
theorem tenv_val_exp_ok_db_merge :
    ∀ (e1 e2 : tenv_val_exp), tenv_val_exp_ok (db_merge e1 e2) → tenv_val_exp_ok e2 := by sorry

/- HOL4:
Theorem tveLookup_freevars[local]:
  !e n inc t tvs.
  tenv_val_exp_ok e ∧
  tveLookup n inc e = SOME (tvs, t)
  ⇒
  check_freevars (tvs+inc+num_tvs e) [] t
   (the second, local, theorem of this name; Lean name `tveLookup_freevars_lem`) -/
theorem tveLookup_freevars_lem :
    ∀ (e : tenv_val_exp) (n : mlstring) (inc : Nat) (t : typ) (tvs : Nat),
      tenv_val_exp_ok e ∧
      tveLookup n inc e = some (tvs, t)
      →
      check_freevars (tvs + inc + num_tvs e) [] t := by sorry

/- HOL4:
Theorem tveLookup_no_tvs:
 !tvs l tenv n t.
  tenv_val_exp_ok tenv ∧
  num_tvs tenv = 0
  ⇒
  (tveLookup n tvs tenv = SOME (l,t)
   ⇔
   tveLookup n 0 tenv = SOME (l,t)) -/
theorem tveLookup_no_tvs :
    ∀ (tvs l : Nat) (tenv : tenv_val_exp) (n : mlstring) (t : typ),
      tenv_val_exp_ok tenv ∧
      num_tvs tenv = 0
      →
      (tveLookup n tvs tenv = some (l, t)
       ↔
       tveLookup n 0 tenv = some (l, t)) := by sorry

/- HOL4:
Theorem deBruijn_subst_E_bvl:
 !tenv1 tenv2 tvs.
  deBruijn_subst_tenvE targs (bind_var_list tvs tenv1 tenv2)
  =
  bind_var_list tvs
          (MAP (\(x,t). (x, deBruijn_subst (tvs + num_tvs tenv2) (MAP (deBruijn_inc 0 (tvs + num_tvs tenv2)) targs) t)) tenv1)
          (deBruijn_subst_tenvE targs tenv2) -/
theorem deBruijn_subst_E_bvl (targs : List typ) :
    ∀ (tenv1 : List (mlstring × typ)) (tenv2 : tenv_val_exp) (tvs : Nat),
      deBruijn_subst_tenvE targs (bind_var_list tvs tenv1 tenv2)
      =
      bind_var_list tvs
        (tenv1.map (fun (x, t) => (x, deBruijn_subst (tvs + num_tvs tenv2)
          (targs.map (deBruijn_inc 0 (tvs + num_tvs tenv2))) t)))
        (deBruijn_subst_tenvE targs tenv2) := by sorry

/- HOL4:
Theorem db_merge_bvl:
 !tenv1 tenv2 tenv3 tvs.
  db_merge (bind_var_list tvs tenv1 tenv2) tenv3
  =
  bind_var_list tvs tenv1 (db_merge tenv2 tenv3) -/
theorem db_merge_bvl :
    ∀ (tenv1 : List (mlstring × typ)) (tenv2 tenv3 : tenv_val_exp) (tvs : Nat),
      db_merge (bind_var_list tvs tenv1 tenv2) tenv3
      =
      bind_var_list tvs tenv1 (db_merge tenv2 tenv3) := by sorry

/- HOL4:
Theorem tveLookup_db_merge_some:
   !n inc tenvE1 tenvE2 tvs t.
    tveLookup n inc (db_merge tenvE1 tenvE2) = SOME (tvs,t)
    ⇔
    tveLookup n inc tenvE1 = SOME (tvs,t) ∨
    (tveLookup n inc tenvE1 = NONE ∧
     tveLookup n (num_tvs tenvE1 + inc) tenvE2 = SOME (tvs, t)) -/
theorem tveLookup_db_merge_some :
    ∀ (n : mlstring) (inc : Nat) (tenvE1 tenvE2 : tenv_val_exp) (tvs : Nat) (t : typ),
      tveLookup n inc (db_merge tenvE1 tenvE2) = some (tvs, t)
      ↔
      tveLookup n inc tenvE1 = some (tvs, t) ∨
      (tveLookup n inc tenvE1 = none ∧
       tveLookup n (num_tvs tenvE1 + inc) tenvE2 = some (tvs, t)) := by sorry

/- HOL4:
Theorem type_op_cases =
  ``type_op op ts t3``
  |> (SIMP_CONV(srw_ss())(type_op_def::eqs@elims) THENC
      SIMP_CONV (bool_ss++DNF_ss) [
        PULL_EXISTS])
   (The HOL4 statement is computed: `type_op op ts t3` is rewritten with `type_op_def` and the
   case-elimination theorems of `op`, lists, `t` and `word_size` into a disjunctive normal form, one
   disjunct per typing rule in the order of the constructors of `op`, with the abbreviations
   `Tarray`, ..., `Tdouble` unfolded (they are in `srw_ss()`) and equated variables eliminated.
   The right-hand side below is that normal form, worked out by hand.) -/
theorem type_op_cases (op : CmlTS.op) (ts : List typ) (t3 : typ) :
    type_op op ts t3 ↔
      (∃ a ty, op = .Arith a ty ∧ EVERY (fun arg => arg = t_of ty) ts ∧ t3 = t_of ty ∧
        supported_arith a ty = some ts.length) ∨
      (∃ ty1 ty2, op = .FromTo ty1 ty2 ∧ ts = [t_of ty1] ∧ t3 = t_of ty2 ∧
        supported_conversion ty1 ty2) ∨
      (∃ sh n, op = .Shift .W8 sh n ∧ ts = [.Tapp [] Tword8_num] ∧ t3 = .Tapp [] Tword8_num) ∨
      (∃ sh n, op = .Shift .W64 sh n ∧ ts = [.Tapp [] Tword64_num] ∧
        t3 = .Tapp [] Tword64_num) ∨
      (∃ t2, op = .Equality ∧ ts = [t2, t2] ∧ t3 = .Tapp [] Tbool_num) ∨
      (∃ test ty, op = .Test test ty ∧ ts = [t_of ty, t_of ty] ∧ t3 = .Tapp [] Tbool_num ∧
        supported_test test ty) ∨
      (∃ t2, op = .Opapp ∧ ts = [.Tapp [t2, t3] Tfn_num, t2]) ∨
      (∃ t2, op = .Opassign ∧ ts = [.Tapp [t2] Tref_num, t2] ∧ t3 = .Tapp [] Ttup_num) ∨
      (∃ t1, op = .Opref ∧ ts = [t1] ∧ t3 = .Tapp [t1] Tref_num) ∨
      (op = .Opderef ∧ ts = [.Tapp [t3] Tref_num]) ∨
      (op = .Aw8alloc ∧ ts = [.Tapp [] Tint_num, .Tapp [] Tword8_num] ∧
        t3 = .Tapp [] Tword8array_num) ∨
      (op = .Aw8sub ∧ ts = [.Tapp [] Tword8array_num, .Tapp [] Tint_num] ∧
        t3 = .Tapp [] Tword8_num) ∨
      (op = .Aw8length ∧ ts = [.Tapp [] Tword8array_num] ∧ t3 = .Tapp [] Tint_num) ∨
      (op = .Aw8update ∧
        ts = [.Tapp [] Tword8array_num, .Tapp [] Tint_num, .Tapp [] Tword8_num] ∧
        t3 = .Tapp [] Ttup_num) ∨
      (op = .CopyStrStr ∧
        ts = [.Tapp [] Tstring_num, .Tapp [] Tint_num, .Tapp [] Tint_num] ∧
        t3 = .Tapp [] Tstring_num) ∨
      (op = .CopyStrAw8 ∧
        ts = [.Tapp [] Tstring_num, .Tapp [] Tint_num, .Tapp [] Tint_num,
          .Tapp [] Tword8array_num, .Tapp [] Tint_num] ∧
        t3 = .Tapp [] Ttup_num) ∨
      (op = .CopyAw8Str ∧
        ts = [.Tapp [] Tword8array_num, .Tapp [] Tint_num, .Tapp [] Tint_num] ∧
        t3 = .Tapp [] Tstring_num) ∨
      (op = .CopyAw8Aw8 ∧
        ts = [.Tapp [] Tword8array_num, .Tapp [] Tint_num, .Tapp [] Tint_num,
          .Tapp [] Tword8array_num, .Tapp [] Tint_num] ∧
        t3 = .Tapp [] Ttup_num) ∨
      (op = .Implode ∧ ts = [.Tapp [.Tapp [] Tchar_num] Tlist_num] ∧
        t3 = .Tapp [] Tstring_num) ∨
      (op = .Explode ∧ ts = [.Tapp [] Tstring_num] ∧
        t3 = .Tapp [.Tapp [] Tchar_num] Tlist_num) ∨
      (op = .Strsub ∧ ts = [.Tapp [] Tstring_num, .Tapp [] Tint_num] ∧
        t3 = .Tapp [] Tchar_num) ∨
      (op = .Strlen ∧ ts = [.Tapp [] Tstring_num] ∧ t3 = .Tapp [] Tint_num) ∨
      (op = .Strcat ∧ ts = [.Tapp [.Tapp [] Tstring_num] Tlist_num] ∧
        t3 = .Tapp [] Tstring_num) ∨
      (∃ t1, op = .VfromList ∧ ts = [.Tapp [t1] Tlist_num] ∧ t3 = .Tapp [t1] Tvector_num) ∨
      (op = .Vsub ∧ ts = [.Tapp [t3] Tvector_num, .Tapp [] Tint_num]) ∨
      (∃ t1, op = .Vlength ∧ ts = [.Tapp [t1] Tvector_num] ∧ t3 = .Tapp [] Tint_num) ∨
      (∃ t2, op = .Aalloc ∧ ts = [.Tapp [] Tint_num, t2] ∧ t3 = .Tapp [t2] Tarray_num) ∨
      (∃ t2, op = .AallocEmpty ∧ ts = [.Tapp [] Ttup_num] ∧ t3 = .Tapp [t2] Tarray_num) ∨
      (op = .Asub ∧ ts = [.Tapp [t3] Tarray_num, .Tapp [] Tint_num]) ∨
      (∃ t1, op = .Alength ∧ ts = [.Tapp [t1] Tarray_num] ∧ t3 = .Tapp [] Tint_num) ∨
      (∃ t3', op = .Aupdate ∧ ts = [.Tapp [t3'] Tarray_num, .Tapp [] Tint_num, t3'] ∧
        t3 = .Tapp [] Ttup_num) ∨
      (∃ t1, op = .ListAppend ∧ ts = [.Tapp [t1] Tlist_num, .Tapp [t1] Tlist_num] ∧
        t3 = .Tapp [t1] Tlist_num) ∨
      (op = .ConfigGC ∧ ts = [.Tapp [] Tint_num, .Tapp [] Tint_num] ∧ t3 = .Tapp [] Ttup_num) ∨
      (∃ n, op = .FFI n ∧ ts = [.Tapp [] Tstring_num, .Tapp [] Tword8array_num] ∧
        t3 = .Tapp [] Ttup_num) := by sorry

/- HOL4:
Theorem type_ps_length:
 ∀tvs tenvC ps ts tenv.
  type_ps tvs tenvC ps ts tenv ⇒ (LENGTH ps = LENGTH ts) -/
theorem type_ps_length :
    ∀ (tvs : Nat) (tenvC : type_env) (ps : List pat) (ts : List typ)
      (tenv : List (varN × typ)),
      type_ps tvs tenvC ps ts tenv → ps.length = ts.length := by sorry

/- HOL4:
Theorem type_p_freevars:
 (!tvs tenvC p t env'.
   type_p tvs tenvC p t env' ⇒
   check_freevars tvs [] t ∧
   EVERY (check_freevars tvs []) (MAP SND env')) ∧
 (!tvs tenvC ps ts env'.
   type_ps tvs tenvC ps ts env' ⇒
   EVERY (check_freevars tvs []) ts ∧
   EVERY (check_freevars tvs []) (MAP SND env')) -/
theorem type_p_freevars :
    (∀ (tvs : Nat) (tenvC : type_env) (p : pat) (t : typ) (env' : List (varN × typ)),
      type_p tvs tenvC p t env' →
      check_freevars tvs [] t ∧
      EVERY (check_freevars tvs []) (env'.map Prod.snd)) ∧
    (∀ (tvs : Nat) (tenvC : type_env) (ps : List pat) (ts : List typ)
      (env' : List (varN × typ)),
      type_ps tvs tenvC ps ts env' →
      EVERY (check_freevars tvs []) ts ∧
      EVERY (check_freevars tvs []) (env'.map Prod.snd)) := by sorry

/- HOL4:
Theorem type_p_subst:
 (!n tenv p t new_bindings. type_p n tenv p t new_bindings ⇒
    !targs' inc tvs targs.
    tenv_abbrev_ok tenv.t ∧
    tenv_ctor_ok tenv.c ∧
    (n = inc + LENGTH targs) ∧
    EVERY (check_freevars tvs []) targs ∧
    (targs' = MAP (deBruijn_inc 0 inc) targs)
    ⇒
    type_p (inc + tvs) tenv
           p
           (deBruijn_subst inc targs' t)
           (MAP (\(x,t). (x, deBruijn_subst inc targs' t)) new_bindings)) ∧
 (!n tenv ps ts new_bindings. type_ps n tenv ps ts new_bindings ⇒
    !targs' inc targs tvs.
    tenv_abbrev_ok tenv.t ∧
    tenv_ctor_ok tenv.c ∧
    (n = inc + LENGTH targs) ∧
    EVERY (check_freevars tvs []) targs ∧
    (targs' = MAP (deBruijn_inc 0 inc) targs)
    ⇒
    type_ps (inc +  tvs) tenv
           ps
           (MAP (deBruijn_subst inc targs') ts)
           (MAP (\(x,t). (x, deBruijn_subst inc targs' t)) new_bindings)) -/
theorem type_p_subst :
    (∀ (n : Nat) (tenv : type_env) (p : pat) (t : typ) (new_bindings : List (varN × typ)),
      type_p n tenv p t new_bindings →
      ∀ (targs' : List typ) (inc tvs : Nat) (targs : List typ),
        tenv_abbrev_ok tenv.t ∧
        tenv_ctor_ok tenv.c ∧
        n = inc + targs.length ∧
        EVERY (check_freevars tvs []) targs ∧
        targs' = targs.map (deBruijn_inc 0 inc)
        →
        type_p (inc + tvs) tenv
          p
          (deBruijn_subst inc targs' t)
          (new_bindings.map (fun (x, t) => (x, deBruijn_subst inc targs' t)))) ∧
    (∀ (n : Nat) (tenv : type_env) (ps : List pat) (ts : List typ)
      (new_bindings : List (varN × typ)),
      type_ps n tenv ps ts new_bindings →
      ∀ (targs' : List typ) (inc : Nat) (targs : List typ) (tvs : Nat),
        tenv_abbrev_ok tenv.t ∧
        tenv_ctor_ok tenv.c ∧
        n = inc + targs.length ∧
        EVERY (check_freevars tvs []) targs ∧
        targs' = targs.map (deBruijn_inc 0 inc)
        →
        type_ps (inc + tvs) tenv
          ps
          (ts.map (deBruijn_subst inc targs'))
          (new_bindings.map (fun (x, t) => (x, deBruijn_subst inc targs' t)))) := by sorry

/- HOL4:
Theorem type_p_bvl:
   (!tvs tenvC p t bindings. type_p tvs tenvC p t bindings ⇒
    !tenv'. tenv_val_exp_ok tenv' ⇒ tenv_val_exp_ok (bind_var_list tvs bindings tenv')) ∧
   (!tvs tenvC ps ts bindings. type_ps tvs tenvC ps ts bindings ⇒
    !tenv'. tenv_val_exp_ok tenv' ⇒ tenv_val_exp_ok (bind_var_list tvs bindings tenv')) -/
theorem type_p_bvl :
    (∀ (tvs : Nat) (tenvC : type_env) (p : pat) (t : typ) (bindings : List (varN × typ)),
      type_p tvs tenvC p t bindings →
      ∀ (tenv' : tenv_val_exp), tenv_val_exp_ok tenv' →
        tenv_val_exp_ok (bind_var_list tvs bindings tenv')) ∧
    (∀ (tvs : Nat) (tenvC : type_env) (ps : List pat) (ts : List typ)
      (bindings : List (varN × typ)),
      type_ps tvs tenvC ps ts bindings →
      ∀ (tenv' : tenv_val_exp), tenv_val_exp_ok tenv' →
        tenv_val_exp_ok (bind_var_list tvs bindings tenv')) := by sorry

/- HOL4:
Theorem type_p_tenvV_indep:
 (!p tvs tenv t bindings tenvV.
  type_p tvs tenv p t bindings = type_p tvs (tenv with v := tenvV) p t bindings) ∧
 (!ps tvs tenv t bindings tenvV.
  type_ps tvs tenv ps t bindings = type_ps tvs (tenv with v := tenvV) ps t bindings) -/
theorem type_p_tenvV_indep :
    (∀ (p : pat) (tvs : Nat) (tenv : type_env) (t : typ) (bindings : List (varN × typ))
      (tenvV : tenv_val),
      type_p tvs tenv p t bindings ↔ type_p tvs { tenv with v := tenvV } p t bindings) ∧
    (∀ (ps : List pat) (tvs : Nat) (tenv : type_env) (t : List typ)
      (bindings : List (varN × typ)) (tenvV : tenv_val),
      type_ps tvs tenv ps t bindings ↔
        type_ps tvs { tenv with v := tenvV } ps t bindings) := by sorry

/- HOL4:
Theorem type_es_list_rel:
 !es ts tenv tenvE. type_es tenv tenvE es ts = LIST_REL (type_e tenv tenvE) es ts -/
theorem type_es_list_rel :
    ∀ (es : List exp) (ts : List typ) (tenv : type_env) (tenvE : tenv_val_exp),
      type_es tenv tenvE es ts ↔ LIST_REL (type_e tenv tenvE) es ts := by sorry

/- HOL4:
Theorem type_es_length:
 ∀tenv tenvE es ts.
  type_es tenv tenvE es ts ⇒ (LENGTH es = LENGTH ts) -/
theorem type_es_length :
    ∀ (tenv : type_env) (tenvE : tenv_val_exp) (es : List exp) (ts : List typ),
      type_es tenv tenvE es ts → es.length = ts.length := by sorry

/- HOL4:
Theorem tenv_val_exp_ok_bvl_funs:
   !funs env tenv bindings tenv_val tenvE.
    type_funs tenv (bind_var_list 0 bindings tenvE) funs env ∧
    tenv_val_exp_ok tenvE
    ⇒
    tenv_val_exp_ok (bind_var_list 0 env tenvE)
   (`tenv_val` is unused, its HOL4 type is a type variable) -/
theorem tenv_val_exp_ok_bvl_funs {α : Type} :
    ∀ (funs : List (varN × varN × exp)) (env : List (varN × typ)) (tenv : type_env)
      (bindings : List (varN × typ)) (_tenv_val : α) (tenvE : tenv_val_exp),
      type_funs tenv (bind_var_list 0 bindings tenvE) funs env ∧
      tenv_val_exp_ok tenvE
      →
      tenv_val_exp_ok (bind_var_list 0 env tenvE) := by sorry

/- HOL4:
Theorem type_e_freevars:
 (!tenv tenvE e t.
   type_e tenv tenvE e t ⇒
   tenv_val_exp_ok tenvE ∧ tenv_val_ok tenv.v ⇒
   check_freevars (num_tvs tenvE) [] t) ∧
 (!tenv tenvE es ts.
   type_es tenv tenvE es ts ⇒
   tenv_val_exp_ok tenvE ∧ tenv_val_ok tenv.v ⇒
   EVERY (check_freevars (num_tvs tenvE) []) ts) ∧
 (!tenv tenvE funs env.
   type_funs tenv tenvE funs env ⇒
   tenv_val_exp_ok tenvE ∧ tenv_val_ok tenv.v ⇒
   EVERY (check_freevars (num_tvs tenvE) []) (MAP SND env)) -/
theorem type_e_freevars :
    (∀ (tenv : type_env) (tenvE : tenv_val_exp) (e : exp) (t : typ),
      type_e tenv tenvE e t →
      tenv_val_exp_ok tenvE ∧ tenv_val_ok tenv.v →
      check_freevars (num_tvs tenvE) [] t) ∧
    (∀ (tenv : type_env) (tenvE : tenv_val_exp) (es : List exp) (ts : List typ),
      type_es tenv tenvE es ts →
      tenv_val_exp_ok tenvE ∧ tenv_val_ok tenv.v →
      EVERY (check_freevars (num_tvs tenvE) []) ts) ∧
    (∀ (tenv : type_env) (tenvE : tenv_val_exp) (funs : List (varN × varN × exp))
      (env : List (varN × typ)),
      type_funs tenv tenvE funs env →
      tenv_val_exp_ok tenvE ∧ tenv_val_ok tenv.v →
      EVERY (check_freevars (num_tvs tenvE) []) (env.map Prod.snd)) := by sorry

/- HOL4:
Theorem type_e_subst:
 (!tenv tenvE e t. type_e tenv tenvE e t ⇒
    !tenvE1 targs tvs targs'.
      num_tvs tenvE2 = 0 ∧
      tenv_abbrev_ok tenv.t ∧
      tenv_ctor_ok tenv.c ∧
      tenv_val_ok tenv.v ∧
      tenv_val_exp_ok tenvE ∧
      EVERY (check_freevars tvs []) targs ∧
      tenvE = db_merge tenvE1 (bind_tvar (LENGTH targs) tenvE2) ∧
      targs' = MAP (deBruijn_inc 0 (num_tvs tenvE1)) targs
      ⇒
      type_e tenv (db_merge (deBruijn_subst_tenvE targs tenvE1) (bind_tvar tvs tenvE2))
                   e
                   (deBruijn_subst (num_tvs tenvE1) targs' t)) ∧
 (!tenv tenvE es ts. type_es tenv tenvE es ts ⇒
    !tenvE1 targs tvs targs'.
      num_tvs tenvE2 = 0 ∧
      tenv_abbrev_ok tenv.t ∧
      tenv_ctor_ok tenv.c ∧
      tenv_val_ok tenv.v ∧
      tenv_val_exp_ok tenvE ∧
      EVERY (check_freevars tvs []) targs ∧
      tenvE = db_merge tenvE1 (bind_tvar (LENGTH targs) tenvE2) ∧
      targs' = MAP (deBruijn_inc 0 (num_tvs tenvE1)) targs
      ⇒
      type_es tenv (db_merge (deBruijn_subst_tenvE targs tenvE1) (bind_tvar tvs tenvE2))
                  es
                  (MAP (deBruijn_subst (num_tvs tenvE1) targs') ts)) ∧
 (!tenv tenvE funs env. type_funs tenv tenvE funs env ⇒
    !tenvE1 targs tvs targs'.
      num_tvs tenvE2 = 0 ∧
      tenv_abbrev_ok tenv.t ∧
      tenv_ctor_ok tenv.c ∧
      tenv_val_ok tenv.v ∧
      tenv_val_exp_ok tenvE ∧
      EVERY (check_freevars tvs []) targs ∧
      tenvE = db_merge tenvE1 (bind_tvar (LENGTH targs) tenvE2) ∧
      targs' = MAP (deBruijn_inc 0 (num_tvs tenvE1)) targs
      ⇒
      type_funs tenv (db_merge (deBruijn_subst_tenvE targs tenvE1) (bind_tvar tvs tenvE2))
                      funs
                      (MAP (\(x,t). (x, deBruijn_subst (num_tvs tenvE1) targs' t)) env)) -/
theorem type_e_subst (tenvE2 : tenv_val_exp) :
    (∀ (tenv : type_env) (tenvE : tenv_val_exp) (e : exp) (t : typ),
      type_e tenv tenvE e t →
      ∀ (tenvE1 : tenv_val_exp) (targs : List typ) (tvs : Nat) (targs' : List typ),
        num_tvs tenvE2 = 0 ∧
        tenv_abbrev_ok tenv.t ∧
        tenv_ctor_ok tenv.c ∧
        tenv_val_ok tenv.v ∧
        tenv_val_exp_ok tenvE ∧
        EVERY (check_freevars tvs []) targs ∧
        tenvE = db_merge tenvE1 (bind_tvar targs.length tenvE2) ∧
        targs' = targs.map (deBruijn_inc 0 (num_tvs tenvE1))
        →
        type_e tenv (db_merge (deBruijn_subst_tenvE targs tenvE1) (bind_tvar tvs tenvE2))
          e
          (deBruijn_subst (num_tvs tenvE1) targs' t)) ∧
    (∀ (tenv : type_env) (tenvE : tenv_val_exp) (es : List exp) (ts : List typ),
      type_es tenv tenvE es ts →
      ∀ (tenvE1 : tenv_val_exp) (targs : List typ) (tvs : Nat) (targs' : List typ),
        num_tvs tenvE2 = 0 ∧
        tenv_abbrev_ok tenv.t ∧
        tenv_ctor_ok tenv.c ∧
        tenv_val_ok tenv.v ∧
        tenv_val_exp_ok tenvE ∧
        EVERY (check_freevars tvs []) targs ∧
        tenvE = db_merge tenvE1 (bind_tvar targs.length tenvE2) ∧
        targs' = targs.map (deBruijn_inc 0 (num_tvs tenvE1))
        →
        type_es tenv (db_merge (deBruijn_subst_tenvE targs tenvE1) (bind_tvar tvs tenvE2))
          es
          (ts.map (deBruijn_subst (num_tvs tenvE1) targs'))) ∧
    (∀ (tenv : type_env) (tenvE : tenv_val_exp) (funs : List (varN × varN × exp))
      (env : List (varN × typ)),
      type_funs tenv tenvE funs env →
      ∀ (tenvE1 : tenv_val_exp) (targs : List typ) (tvs : Nat) (targs' : List typ),
        num_tvs tenvE2 = 0 ∧
        tenv_abbrev_ok tenv.t ∧
        tenv_ctor_ok tenv.c ∧
        tenv_val_ok tenv.v ∧
        tenv_val_exp_ok tenvE ∧
        EVERY (check_freevars tvs []) targs ∧
        tenvE = db_merge tenvE1 (bind_tvar targs.length tenvE2) ∧
        targs' = targs.map (deBruijn_inc 0 (num_tvs tenvE1))
        →
        type_funs tenv (db_merge (deBruijn_subst_tenvE targs tenvE1) (bind_tvar tvs tenvE2))
          funs
          (env.map (fun (x, t) => (x, deBruijn_subst (num_tvs tenvE1) targs' t)))) := by sorry

/- HOL4:
Theorem type_funs_Tfn:
   ∀tenv tenvE funs bindings tvs t n.
    type_funs tenv tenvE funs bindings ∧
    ALOOKUP bindings n = SOME t
    ⇒
    ∃t1 t2. (t = Tfn t1 t2) ∧ check_freevars (num_tvs tenvE) [] (Tfn t1 t2)
   (`tvs` is unused, its HOL4 type is a type variable) -/
theorem type_funs_Tfn {α : Type} :
    ∀ (tenv : type_env) (tenvE : tenv_val_exp) (funs : List (varN × varN × exp))
      (bindings : List (varN × typ)) (_tvs : α) (t : typ) (n : varN),
      type_funs tenv tenvE funs bindings ∧
      ALOOKUP bindings n = some t
      →
      ∃ (t1 t2 : typ), t = Tfn t1 t2 ∧ check_freevars (num_tvs tenvE) [] (Tfn t1 t2) := by sorry

/- HOL4:
Theorem type_funs_lookup:
 ∀fn tenvE funs bindings n e tenv.
  MEM (fn,n,e) funs ∧
  type_funs tenv tenvE funs bindings
  ⇒
  (∃t. ALOOKUP bindings fn = SOME t) -/
theorem type_funs_lookup :
    ∀ (fn : varN) (tenvE : tenv_val_exp) (funs : List (varN × varN × exp))
      (bindings : List (varN × typ)) (n : varN) (e : exp) (tenv : type_env),
      (fn, n, e) ∈ funs ∧
      type_funs tenv tenvE funs bindings
      →
      ∃ (t : typ), ALOOKUP bindings fn = some t := by sorry

/- HOL4:
Theorem type_funs_find_recfun:
 ∀fn env funs bindings e tenv tenvE t.
  ALOOKUP bindings fn = SOME t ∧
  type_funs tenv tenvE funs bindings
  ⇒
  (∃n e. find_recfun fn funs = SOME (n,e))
   (`env` and the outer `e` are unused, their HOL4 types are type variables) -/
theorem type_funs_find_recfun {α β : Type} :
    ∀ (fn : varN) (_env : α) (funs : List (varN × varN × exp)) (bindings : List (varN × typ))
      (_e : β) (tenv : type_env) (tenvE : tenv_val_exp) (t : typ),
      ALOOKUP bindings fn = some t ∧
      type_funs tenv tenvE funs bindings
      →
      ∃ (n : varN) (e : exp), find_recfun fn funs = some (n, e) := by sorry

/- HOL4:
Theorem type_recfun_lookup:
   ∀fn funs n e tenv tenvE bindings tvs t1 t2.
    find_recfun fn funs = SOME (n,e) ∧
    type_funs tenv tenvE funs bindings ∧
    ALOOKUP bindings fn = SOME (Tfn t1 t2)
    ⇒
    type_e tenv (Bind_name n 0 t1 tenvE) e t2 ∧
    check_freevars (num_tvs tenvE) [] (Tfn t1 t2)
   (`tvs` is unused, its HOL4 type is a type variable) -/
theorem type_recfun_lookup {α : Type} :
    ∀ (fn : varN) (funs : List (varN × varN × exp)) (n : varN) (e : exp) (tenv : type_env)
      (tenvE : tenv_val_exp) (bindings : List (varN × typ)) (_tvs : α) (t1 t2 : typ),
      find_recfun fn funs = some (n, e) ∧
      type_funs tenv tenvE funs bindings ∧
      ALOOKUP bindings fn = some (Tfn t1 t2)
      →
      type_e tenv (.Bind_name n 0 t1 tenvE) e t2 ∧
      check_freevars (num_tvs tenvE) [] (Tfn t1 t2) := by sorry

/- HOL4:
Theorem type_funs_distinct:
 ∀tenv tenvE funs bindings .
  type_funs tenv tenvE funs bindings
  ⇒
  ALL_DISTINCT (MAP (λ(x,y,z). x) funs) -/
theorem type_funs_distinct :
    ∀ (tenv : type_env) (tenvE : tenv_val_exp) (funs : List (varN × varN × exp))
      (bindings : List (varN × typ)),
      type_funs tenv tenvE funs bindings
      →
      ALL_DISTINCT (funs.map (fun (x, _y, _z) => x)) := by sorry

/- HOL4:
Theorem type_e_subst_lem[local]:
  ∀tenv tenvE e t targs tvs targs'.
  type_e tenv (Bind_name x 0 t1 (bind_tvar (LENGTH targs) tenvE)) e t ∧
  num_tvs tenvE = 0 ∧
  tenv_abbrev_ok tenv.t ∧
  tenv_ctor_ok tenv.c ∧
  tenv_val_ok tenv.v ∧
  tenv_val_exp_ok (bind_tvar (LENGTH targs) tenvE) ∧
  EVERY (check_freevars tvs []) targs ∧
  check_freevars (LENGTH targs) [] t1
  ⇒
  type_e tenv (Bind_name x 0 (deBruijn_subst 0 targs t1) (bind_tvar tvs tenvE)) e (deBruijn_subst 0 targs t)
   (`targs'` is unused, its HOL4 type is a type variable) -/
theorem type_e_subst_lem {α : Type} (x : varN) (t1 : typ) :
    ∀ (tenv : type_env) (tenvE : tenv_val_exp) (e : exp) (t : typ) (targs : List typ) (tvs : Nat)
      (_targs' : α),
      type_e tenv (.Bind_name x 0 t1 (bind_tvar targs.length tenvE)) e t ∧
      num_tvs tenvE = 0 ∧
      tenv_abbrev_ok tenv.t ∧
      tenv_ctor_ok tenv.c ∧
      tenv_val_ok tenv.v ∧
      tenv_val_exp_ok (bind_tvar targs.length tenvE) ∧
      EVERY (check_freevars tvs []) targs ∧
      check_freevars targs.length [] t1
      →
      type_e tenv (.Bind_name x 0 (deBruijn_subst 0 targs t1) (bind_tvar tvs tenvE)) e
        (deBruijn_subst 0 targs t) := by sorry

/- HOL4:
Theorem mem_type_def_to_ctMap:
   !tenvT next tds ids stamp x.
    MEM (stamp,x) (type_def_to_ctMap tenvT next tds ids) ∧
    LENGTH tds = LENGTH ids
    ⇒
    ?cn i. stamp = TypeStamp cn i ∧ next ≤ i ∧ i < next + LENGTH tds -/
theorem mem_type_def_to_ctMap {α β γ : Type} :
    ∀ (tenvT : Namespace mlstring mlstring (List mlstring × typ)) (next : Nat)
      (tds : List (α × β × List (mlstring × List ast_t))) (ids : List γ) (stamp : CmlTS.stamp)
      (x : α × List typ × γ),
      (stamp, x) ∈ type_def_to_ctMap tenvT next tds ids ∧
      tds.length = ids.length
      →
      ∃ (cn : conN) (i : Nat),
        stamp = .TypeStamp cn i ∧ next ≤ i ∧ i < next + tds.length := by sorry

/- HOL4:
Theorem ctMap_ok_merge_imp:
   !ctMap1 ctMap2.
    DISJOINT (FRANGE ((SND o SND) o_f ctMap1)) (FRANGE ((SND o SND) o_f ctMap2)) ∧
    ctMap_ok ctMap1 ∧ ctMap_ok ctMap2 ⇒
    ctMap_ok (FUNION ctMap1 ctMap2) -/
theorem ctMap_ok_merge_imp :
    ∀ (ctMap1 ctMap2 : ctMap_t),
      DISJOINT (FRANGE (o_f (Prod.snd ∘ Prod.snd) ctMap1))
        (FRANGE (o_f (Prod.snd ∘ Prod.snd) ctMap2)) ∧
      ctMap_ok ctMap1 ∧ ctMap_ok ctMap2 →
      ctMap_ok (FUNION ctMap1 ctMap2) := by sorry

/- HOL4:
Theorem ctMap_ok_lookup:
 !ctMap cn tvs ts ti tn.
  ctMap_ok ctMap ∧ (FLOOKUP ctMap tn = SOME (tvs,ts,ti))
  ⇒
  EVERY (check_freevars 0 tvs) ts
   (`cn` is unused, its HOL4 type is a type variable) -/
theorem ctMap_ok_lookup {α : Type} :
    ∀ (ctMap : ctMap_t) (_cn : α) (tvs : List tvarN) (ts : List typ) (ti : type_ident)
      (tn : stamp),
      ctMap_ok ctMap ∧ FLOOKUP ctMap tn = some (tvs, ts, ti)
      →
      EVERY (check_freevars 0 tvs) ts := by sorry

/- HOL4:
Theorem type_def_to_ctMap_mem:
   !tenvT next tds tids.
    ALOOKUP (type_def_to_ctMap tenvT next tds tids) k = SOME x ∧
    LENGTH tds = LENGTH tids
    ⇒
    MEM (SND (SND x)) tids -/
theorem type_def_to_ctMap_mem {α β γ : Type} (k : stamp) (x : α × List typ × γ) :
    ∀ (tenvT : Namespace mlstring mlstring (List mlstring × typ)) (next : Nat)
      (tds : List (α × β × List (mlstring × List ast_t))) (tids : List γ),
      ALOOKUP (type_def_to_ctMap tenvT next tds tids) k = some x ∧
      tds.length = tids.length
      →
      x.2.2 ∈ tids := by sorry

/- HOL4:
Theorem fupdate2_union[local]:
  !m a1 a2. m |++ a1 |++ a2 = FEMPTY |++ a2 ⊌ (m |++ a1) -/
theorem fupdate2_union {α β : Type} :
    ∀ (m : fmap α β) (a1 a2 : List (α × β)),
      (m |++ a1) |++ a2 = (FEMPTY |++ a2) ⊌ (m |++ a1) := by sorry

/- HOL4:
Theorem ctMap_ok_type_defs:
   !tenvT next tds tids.
    ALL_DISTINCT tids ∧
    DISJOINT (set tids) (set prim_type_nums) ∧
    LENGTH tds = LENGTH tids ∧
    check_ctor_tenv tenvT tds ∧
    tenv_abbrev_ok tenvT
    ⇒
    ctMap_ok
      (FEMPTY |++
        REVERSE (type_def_to_ctMap tenvT next tds tids)) -/
theorem ctMap_ok_type_defs :
    ∀ (tenvT : Namespace modN typeN (List tvarN × typ)) (next : Nat)
      (tds : List (List tvarN × mlstring × List (conN × List ast_t))) (tids : List type_ident),
      ALL_DISTINCT tids ∧
      DISJOINT (LIST_TO_SET tids) (LIST_TO_SET prim_type_nums) ∧
      tds.length = tids.length ∧
      check_ctor_tenv tenvT tds ∧
      tenv_abbrev_ok tenvT
      →
      ctMap_ok
        (FEMPTY |++
          List.reverse (type_def_to_ctMap tenvT next tds tids)) := by sorry

/- HOL4:
Theorem nsLookup_add_tenvE1:
   !tenvE tenvV n tvs t tvs2.
    check_freevars tvs2 [] t ∧
    tveLookup n tvs tenvE = SOME (tvs2,t) ⇒
    nsLookup (add_tenvE tenvE tenvV) (Short n) = SOME (tvs2,t) -/
theorem nsLookup_add_tenvE1 {m : Type} :
    ∀ (tenvE : tenv_val_exp) (tenvV : Namespace m mlstring (Nat × typ)) (n : mlstring) (tvs : Nat)
      (t : typ) (tvs2 : Nat),
      check_freevars tvs2 [] t ∧
      tveLookup n tvs tenvE = some (tvs2, t) →
      nsLookup (add_tenvE tenvE tenvV) (.Short n) = some (tvs2, t) := by sorry

/- HOL4:
Theorem nsLookup_add_tenvE2:
   !tenvE tenvV n tvs t tvs2.
    tveLookup n tvs tenvE = NONE ∧
    nsLookup tenvV (Short n) = SOME (tvs2,t) ⇒
    nsLookup (add_tenvE tenvE tenvV) (Short n) = SOME (tvs2,t) -/
theorem nsLookup_add_tenvE2 {m : Type} :
    ∀ (tenvE : tenv_val_exp) (tenvV : Namespace m mlstring (Nat × typ)) (n : mlstring) (tvs : Nat)
      (t : typ) (tvs2 : Nat),
      tveLookup n tvs tenvE = none ∧
      nsLookup tenvV (.Short n) = some (tvs2, t) →
      nsLookup (add_tenvE tenvE tenvV) (.Short n) = some (tvs2, t) := by sorry

/- HOL4:
Theorem nsLookup_add_tenvE3:
   !tenvE tenvV n t tvs2 mn.
    nsLookup tenvV (Long mn n) = SOME (tvs2,t) ⇒
    nsLookup (add_tenvE tenvE tenvV) (Long mn n) = SOME (tvs2,t) -/
theorem nsLookup_add_tenvE3 {m : Type} :
    ∀ (tenvE : tenv_val_exp) (tenvV : Namespace m mlstring (Nat × typ)) (n : ident m mlstring)
      (t : typ) (tvs2 : Nat) (mn : m),
      nsLookup tenvV (.Long mn n) = some (tvs2, t) →
      nsLookup (add_tenvE tenvE tenvV) (.Long mn n) = some (tvs2, t) := by sorry

/- HOL4:
Theorem add_tenvE_bvl:
   !n bindings tenvE tenvV.
    add_tenvE (bind_var_list n bindings tenvE) tenvV =
    nsBindList (MAP (\(x,t). (x, (n, t))) bindings) (add_tenvE tenvE tenvV) -/
theorem add_tenvE_bvl {m : Type} :
    ∀ (n : Nat) (bindings : List (mlstring × typ)) (tenvE : tenv_val_exp)
      (tenvV : Namespace m mlstring (Nat × typ)),
      add_tenvE (bind_var_list n bindings tenvE) tenvV =
        nsBindList (bindings.map (fun (x, t) => (x, (n, t)))) (add_tenvE tenvE tenvV) := by sorry

/- HOL4:
Theorem type_v_freevars:
 !tvs tenvC tenvS v t. type_v tvs tenvC tenvS v t ⇒ check_freevars tvs [] t -/
theorem type_v_freevars :
    ∀ (tvs : Nat) (tenvC : ctMap_t) (tenvS : tenv_store) (v : val) (t : typ),
      type_v tvs tenvC tenvS v t → check_freevars tvs [] t := by sorry

/- HOL4:
Theorem type_subst:
   !tvs ctMap tenvS v t.
     type_v tvs ctMap tenvS v t ⇒
     tvs = LENGTH targs ∧
     ctMap_ok ctMap ∧
     EVERY (check_freevars tvs' []) targs ∧
     check_freevars (LENGTH targs) [] t
     ⇒
     type_v tvs' ctMap tenvS v (deBruijn_subst 0 targs t)
   (Lean name `type_subst_thm`, because `type_subst` is the function) -/
theorem type_subst_thm (targs : List typ) (tvs' : Nat) :
    ∀ (tvs : Nat) (ctMap : ctMap_t) (tenvS : tenv_store) (v : val) (t : typ),
      type_v tvs ctMap tenvS v t →
      tvs = targs.length ∧
      ctMap_ok ctMap ∧
      EVERY (check_freevars tvs' []) targs ∧
      check_freevars targs.length [] t
      →
      type_v tvs' ctMap tenvS v (deBruijn_subst 0 targs t) := by sorry

/- HOL4:
Theorem check_ctor_tenv_ok:
 !tenvT tds tis.
 LENGTH tds = LENGTH tis ∧
 check_ctor_tenv tenvT tds ∧
 tenv_abbrev_ok tenvT
 ⇒
 tenv_ctor_ok (build_ctor_tenv tenvT tds tis) -/
theorem check_ctor_tenv_ok {m γ : Type} :
    ∀ (tenvT : Namespace modN typeN (List tvarN × typ))
      (tds : List (List tvarN × mlstring × List (conN × List ast_t))) (tis : List γ),
      tds.length = tis.length ∧
      check_ctor_tenv tenvT tds ∧
      tenv_abbrev_ok tenvT
      →
      tenv_ctor_ok
        (build_ctor_tenv tenvT tds tis : Namespace m conN (List tvarN × List typ × γ)) := by
  sorry

/- HOL4:
Theorem type_d_check_uniq:
 (!check tenv d tdecs new_tenv.
  type_d check tenv d tdecs new_tenv
  ⇒
  type_d F tenv d tdecs new_tenv) ∧
 (!check tenv d tdecs new_tenv.
  type_ds check tenv d tdecs new_tenv
  ⇒
  type_ds F tenv d tdecs new_tenv) -/
theorem type_d_check_uniq :
    (∀ (check : Prop) (tenv : type_env) (d : dec) (tdecs : Set type_ident) (new_tenv : type_env),
      type_d check tenv d tdecs new_tenv
      →
      type_d False tenv d tdecs new_tenv) ∧
    (∀ (check : Prop) (tenv : type_env) (d : List dec) (tdecs : Set type_ident)
      (new_tenv : type_env),
      type_ds check tenv d tdecs new_tenv
      →
      type_ds False tenv d tdecs new_tenv) := by sorry

/- HOL4:
Theorem extend_dec_tenv_ok:
   !tenv tenv'. tenv_ok tenv ∧ tenv_ok tenv' ⇒ tenv_ok (extend_dec_tenv tenv tenv') -/
theorem extend_dec_tenv_ok :
    ∀ (tenv tenv' : type_env),
      tenv_ok tenv ∧ tenv_ok tenv' → tenv_ok (extend_dec_tenv tenv tenv') := by sorry

/- HOL4:
Theorem type_d_tenv_ok_helper:
  (∀check tenv d tdecs tenv'.
   type_d check tenv d tdecs tenv' ⇒
   tenv_ok tenv
   ⇒
   tenv_ok tenv') ∧
  (∀check tenv d tdecs tenv'.
   type_ds check tenv d tdecs tenv' ⇒
   tenv_ok tenv
   ⇒
   tenv_ok tenv') -/
theorem type_d_tenv_ok_helper :
    (∀ (check : Prop) (tenv : type_env) (d : dec) (tdecs : Set type_ident) (tenv' : type_env),
      type_d check tenv d tdecs tenv' →
      tenv_ok tenv
      →
      tenv_ok tenv') ∧
    (∀ (check : Prop) (tenv : type_env) (d : List dec) (tdecs : Set type_ident)
      (tenv' : type_env),
      type_ds check tenv d tdecs tenv' →
      tenv_ok tenv
      →
      tenv_ok tenv') := by sorry

/- HOL4:
Theorem type_d_tenv_ok:
  ∀check tenv d tdecs tenv'.
   type_d check tenv d tdecs tenv' ∧
   tenv_ok tenv
   ⇒
   tenv_ok (extend_dec_tenv tenv' tenv) -/
theorem type_d_tenv_ok :
    ∀ (check : Prop) (tenv : type_env) (d : dec) (tdecs : Set type_ident) (tenv' : type_env),
      type_d check tenv d tdecs tenv' ∧
      tenv_ok tenv
      →
      tenv_ok (extend_dec_tenv tenv' tenv) := by sorry

/- HOL4:
Theorem type_ds_empty[simp]:
  !check tenv decls r.
  type_ds check tenv [] decls r ⇔
  decls = {} ∧ r = <| v := nsEmpty; c:= nsEmpty; t := nsEmpty |> -/
theorem type_ds_empty :
    ∀ (check : Prop) (tenv : type_env) (decls : Set type_ident) (r : type_env),
      type_ds check tenv [] decls r ↔
      decls = ∅ ∧ r = { v := nsEmpty, c := nsEmpty, t := nsEmpty } := by sorry

/- HOL4:
Theorem type_ds_sing[simp]:
  !check tenv d decls r.
  type_ds check tenv [d] decls r ⇔ type_d check tenv d decls r -/
theorem type_ds_sing :
    ∀ (check : Prop) (tenv : type_env) (d : dec) (decls : Set type_ident) (r : type_env),
      type_ds check tenv [d] decls r ↔ type_d check tenv d decls r := by sorry

end CmlTS
