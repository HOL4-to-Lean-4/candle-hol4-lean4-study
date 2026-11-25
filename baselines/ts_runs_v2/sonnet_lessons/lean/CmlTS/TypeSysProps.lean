import CmlTS.Ast
import CmlTS.Namespace
import CmlTS.TypeSystem
import CmlTS.TypeSoundInvariants
import CmlTS.NamespaceProps
import CmlTS.SemanticPrimitivesProps

/-!
# typeSysProps (HOL4 theory `typeSysProps`): theorems about the type system

Definitions of this theory (the theorems are for stage 2).
-/

universe u v w

noncomputable section

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
def type_pes (tvs tvs' : Nat) (tenv : type_env) (tenvE : tenv_val_exp) (pes : List (pat × exp))
    (t1 t2 : Ty) : Prop :=
  ∀ pe, pe ∈ LIST_TO_SET pes →
    ∃ bindings,
      ALL_DISTINCT (pat_bindings pe.1 []) ∧
      type_p tvs tenv pe.1 t1 bindings ∧
      type_e tenv (bind_var_list tvs' bindings tenvE) pe.2 t2

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
def deBruijn_subst_tenvE (targs : List Ty) : tenv_val_exp → tenv_val_exp
  | .Empty => .Empty
  | .Bind_tvar tvs env => .Bind_tvar tvs (deBruijn_subst_tenvE targs env)
  | .Bind_name x tvs t env =>
    .Bind_name x tvs
      (deBruijn_subst (tvs + num_tvs env) (MAP (deBruijn_inc 0 (tvs + num_tvs env)) targs) t)
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
   (the two cases with lists of different shapes are unspecified: `ARB`) -/
def type_def_to_ctMap (tenvT : Namespace modN typeN (List tvarN × Ty)) :
    Nat → List (List tvarN × mlstring × List (conN × List ast_t)) → List type_ident →
      List (stamp × (List tvarN × List Ty × type_ident))
  | _, [], [] => []
  | next_stamp, (tvs, _, ctors) :: tds, i :: ids =>
    type_def_to_ctMap tenvT (next_stamp + 1) tds ids ++
    REVERSE (MAP (fun cnts =>
      (.TypeStamp cnts.1 next_stamp, (tvs, MAP (type_name_subst tenvT) cnts.2, i))) ctors)
  | _, _, _ => ARB

/- HOL4:
   Theorem unchanged_tenv[simp]:
     !(tenv : type_env).
     <| v := tenv.v; c := tenv.c; t := tenv.t |> = tenv -/
theorem unchanged_tenv : ∀ (tenv : type_env),
    (⟨tenv.v, tenv.c, tenv.t⟩ : type_env) = tenv := by
  sorry

/- HOL4:
   Theorem extend_dec_tenv_assoc[simp]:
      !tenv1 tenv2 tenv3.
       extend_dec_tenv tenv1 (extend_dec_tenv tenv2 tenv3)
       =
       extend_dec_tenv (extend_dec_tenv tenv1 tenv2) tenv3 -/
theorem extend_dec_tenv_assoc : ∀ (tenv1 tenv2 tenv3 : type_env),
    extend_dec_tenv tenv1 (extend_dec_tenv tenv2 tenv3)
    =
    extend_dec_tenv (extend_dec_tenv tenv1 tenv2) tenv3 := by
  sorry

/- HOL4:
   Theorem tenv_val_ok_nsEmpty[simp]:
      tenv_val_ok nsEmpty -/
theorem tenv_val_ok_nsEmpty : tenv_val_ok nsEmpty := by
  sorry

/- HOL4:
   Theorem tenv_ctor_ok_nsEmpty[simp]:
      tenv_ctor_ok nsEmpty -/
theorem tenv_ctor_ok_nsEmpty : tenv_ctor_ok nsEmpty := by
  sorry

/- HOL4:
   Theorem tenv_abbrev_ok_nsEmpty[simp]:
      tenv_abbrev_ok nsEmpty -/
theorem tenv_abbrev_ok_nsEmpty : tenv_abbrev_ok nsEmpty := by
  sorry

/- HOL4:
   Theorem tenv_ok_empty[simp]:
      tenv_ok <| v := nsEmpty; c := nsEmpty; t := nsEmpty |> -/
theorem tenv_ok_empty : tenv_ok ⟨nsEmpty, nsEmpty, nsEmpty⟩ := by
  sorry

/- HOL4:
   Theorem check_freevars_add:
    (!tvs tvs' t. check_freevars tvs tvs' t ⇒
     !tvs''. tvs'' ≥ tvs ⇒ check_freevars tvs'' tvs' t) -/
theorem check_freevars_add :
    (∀ (tvs : Nat) (tvs' : List mlstring) (t : Ty), check_freevars tvs tvs' t →
      ∀ (tvs'' : Nat), tvs'' ≥ tvs → check_freevars tvs'' tvs' t) := by
  sorry

/- HOL4:
   Theorem check_freevars_subst_single:
    !dbmax tvs t tvs' ts.
     LENGTH tvs = LENGTH ts ∧
     check_freevars dbmax tvs t ∧
     EVERY (check_freevars dbmax tvs') ts
     ⇒
     check_freevars dbmax tvs' (type_subst (alist_to_fmap (ZIP (tvs,ts))) t) -/
theorem check_freevars_subst_single :
    ∀ (dbmax : Nat) (tvs : List mlstring) (t : Ty) (tvs' : List mlstring) (ts : List Ty),
     LENGTH tvs = LENGTH ts ∧
     check_freevars dbmax tvs t ∧
     EVERY (check_freevars dbmax tvs') ts
     →
     check_freevars dbmax tvs' (type_subst (alist_to_fmap (ZIP (tvs, ts))) t) := by
  sorry

/- HOL4:
   Theorem deBruijn_inc0:
    (!t sk. deBruijn_inc sk 0 t = t) ∧
    (!ts sk. MAP (deBruijn_inc sk 0) ts = ts) -/
theorem deBruijn_inc0 :
    (∀ (t : Ty) (sk : Nat), deBruijn_inc sk 0 t = t) ∧
    (∀ (ts : List Ty) (sk : Nat), MAP (deBruijn_inc sk 0) ts = ts) := by
  sorry

/- HOL4:
   Theorem deBruijn_inc_deBruijn_inc:
    !sk i2 t i1.
     deBruijn_inc sk i1 (deBruijn_inc sk i2 t) = deBruijn_inc sk (i1 + i2) t -/
theorem deBruijn_inc_deBruijn_inc :
    ∀ (sk i2 : Nat) (t : Ty) (i1 : Nat),
     deBruijn_inc sk i1 (deBruijn_inc sk i2 t) = deBruijn_inc sk (i1 + i2) t := by
  sorry

/- HOL4:
   Theorem deBuijn_inc_lem1[local]:
     !sk i2 t i1.
     deBruijn_inc sk i1 (deBruijn_inc 0 (sk + i2) t) = deBruijn_inc 0 (i1 + (sk + i2)) t -/
theorem deBuijn_inc_lem1 :
    ∀ (sk i2 : Nat) (t : Ty) (i1 : Nat),
    deBruijn_inc sk i1 (deBruijn_inc 0 (sk + i2) t) = deBruijn_inc 0 (i1 + (sk + i2)) t := by
  sorry

/- HOL4:
   Theorem type_subst_deBruijn_inc_single[local]:
     !s t ts tvs inc sk.
     (LENGTH tvs = LENGTH ts) ∧
     (s = alist_to_fmap (ZIP (tvs,ts))) ∧
     check_freevars 0 tvs t ⇒
     (deBruijn_inc sk inc (type_subst s t) =
      type_subst (alist_to_fmap (ZIP (tvs, MAP (\t. deBruijn_inc sk inc t) ts))) t) -/
theorem type_subst_deBruijn_inc_single :
    ∀ (s : FMap mlstring Ty) (t : Ty) (ts : List Ty) (tvs : List mlstring) (inc sk : Nat),
     (LENGTH tvs = LENGTH ts) ∧
     (s = alist_to_fmap (ZIP (tvs, ts))) ∧
     check_freevars 0 tvs t →
     (deBruijn_inc sk inc (type_subst s t) =
      type_subst (alist_to_fmap (ZIP (tvs, MAP (fun t => deBruijn_inc sk inc t) ts))) t) := by
  sorry

/- HOL4:
   Theorem type_subst_deBruijn_inc_list:
    !ts' ts tvs inc sk.
     (LENGTH tvs = LENGTH ts) ∧
     EVERY (check_freevars 0 tvs) ts' ⇒
     (MAP (deBruijn_inc sk inc) (MAP (type_subst (alist_to_fmap (ZIP (tvs,ts)))) ts') =
      MAP (type_subst (alist_to_fmap (ZIP (tvs, MAP (\t. deBruijn_inc sk inc t) ts)))) ts') -/
theorem type_subst_deBruijn_inc_list :
    ∀ (ts' ts : List Ty) (tvs : List mlstring) (inc sk : Nat),
     (LENGTH tvs = LENGTH ts) ∧
     EVERY (check_freevars 0 tvs) ts' →
     (MAP (deBruijn_inc sk inc) (MAP (type_subst (alist_to_fmap (ZIP (tvs, ts)))) ts') =
      MAP (type_subst (alist_to_fmap (ZIP (tvs, MAP (fun t => deBruijn_inc sk inc t) ts)))) ts') := by
  sorry

/- HOL4:
   Theorem check_freevars_deBruijn_inc[local]:
     !tvs tvs' t. check_freevars tvs tvs' t ⇒
     !n n'. check_freevars (n+tvs) tvs' (deBruijn_inc n' n t) -/
theorem check_freevars_deBruijn_inc :
    ∀ (tvs : Nat) (tvs' : List mlstring) (t : Ty), check_freevars tvs tvs' t →
    ∀ (n n' : Nat), check_freevars (n + tvs) tvs' (deBruijn_inc n' n t) := by
  sorry

/- HOL4:
   Theorem nil_deBruijn_inc:
    ∀skip tvs t.
     (check_freevars skip [] t ∨ check_freevars skip [] (deBruijn_inc skip tvs t))
     ⇒
     (deBruijn_inc skip tvs t = t) -/
theorem nil_deBruijn_inc :
    ∀ (skip tvs : Nat) (t : Ty),
     (check_freevars skip [] t ∨ check_freevars skip [] (deBruijn_inc skip tvs t))
     →
     (deBruijn_inc skip tvs t = t) := by
  sorry

/- HOL4:
   Theorem deBruijn_subst_check_freevars:
    !tvs tvs' t ts n.
     check_freevars tvs tvs' t ∧
     EVERY (check_freevars tvs tvs') ts
     ⇒
     check_freevars tvs tvs' (deBruijn_subst 0 ts t)
   (`n` is unused, so in HOL4 it has an arbitrary type variable `'a`) -/
theorem deBruijn_subst_check_freevars {α : Type u} :
    ∀ (tvs : Nat) (tvs' : List mlstring) (t : Ty) (ts : List Ty) (n : α),
     check_freevars tvs tvs' t ∧
     EVERY (check_freevars tvs tvs') ts
     →
     check_freevars tvs tvs' (deBruijn_subst 0 ts t) := by
  sorry

/- HOL4:
   Theorem deBruijn_subst_check_freevars2:
    !tvs tvs' t ts n tvs''.
     check_freevars (LENGTH ts) tvs' t ∧
     EVERY (check_freevars tvs tvs') ts
     ⇒
     check_freevars tvs tvs' (deBruijn_subst 0 ts t)
   (`n` and `tvs''` are unused, so in HOL4 they have arbitrary type variables `'a`, `'b`) -/
theorem deBruijn_subst_check_freevars2 {α : Type u} {β : Type v} :
    ∀ (tvs : Nat) (tvs' : List mlstring) (t : Ty) (ts : List Ty) (n : α) (tvs'' : β),
     check_freevars (LENGTH ts) tvs' t ∧
     EVERY (check_freevars tvs tvs') ts
     →
     check_freevars tvs tvs' (deBruijn_subst 0 ts t) := by
  sorry

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
    ∀ (tvs : Nat) (tvs2 : List mlstring) (t : Ty),
     check_freevars tvs tvs2 t →
     ∀ (tvs' : Nat) (targs : List Ty) (tvs1 : Nat),
     tvs = LENGTH targs + tvs' ∧
     EVERY (check_freevars (tvs1 + tvs') tvs2) targs
     →
     check_freevars (tvs1 + tvs') tvs2
        (deBruijn_subst 0 targs (deBruijn_inc (LENGTH targs) tvs1 t)) := by
  sorry

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
    ∀ (tvs : Nat) (tvs2 : List mlstring) (t : Ty),
     check_freevars tvs tvs2 t →
     ∀ (tvs' : Nat) (targs : List Ty) (tvs1 : Nat),
     tvs = LENGTH targs + tvs' ∧
     EVERY (check_freevars (tvs1 + tvs') tvs2) targs
     →
     check_freevars (tvs1 + tvs') tvs2 (deBruijn_subst 0 targs t) := by
  sorry

/- HOL4:
   Theorem type_subst_deBruijn_subst_single[local]:
     !s t tvs tvs' ts ts' inc.
     (LENGTH tvs = LENGTH ts) ∧
     check_freevars 0 tvs t ∧
     (s = alist_to_fmap (ZIP (tvs,ts))) ⇒
     (deBruijn_subst inc ts' (type_subst (alist_to_fmap (ZIP (tvs,ts))) t) =
      type_subst (alist_to_fmap (ZIP (tvs,MAP (\t. deBruijn_subst inc ts' t) ts))) t)
   (`tvs'` is unused, so in HOL4 it has an arbitrary type variable `'a`) -/
theorem type_subst_deBruijn_subst_single {α : Type u} :
    ∀ (s : FMap mlstring Ty) (t : Ty) (tvs : List mlstring) (tvs' : α) (ts ts' : List Ty)
      (inc : Nat),
     (LENGTH tvs = LENGTH ts) ∧
     check_freevars 0 tvs t ∧
     (s = alist_to_fmap (ZIP (tvs, ts))) →
     (deBruijn_subst inc ts' (type_subst (alist_to_fmap (ZIP (tvs, ts))) t) =
      type_subst (alist_to_fmap (ZIP (tvs, MAP (fun t => deBruijn_subst inc ts' t) ts))) t) := by
  sorry

/- HOL4:
   Theorem type_subst_deBruijn_subst_list:
    !t tvs tvs' ts ts' ts'' inc.
     (LENGTH tvs = LENGTH ts) ∧
     EVERY (check_freevars 0 tvs) ts'' ⇒
     (MAP (deBruijn_subst inc ts') (MAP (type_subst (alist_to_fmap (ZIP (tvs,ts)))) ts'') =
      MAP (type_subst (alist_to_fmap (ZIP (tvs,MAP (\t. deBruijn_subst inc ts' t) ts)))) ts'')
   (`t` and `tvs'` are unused, so in HOL4 they have arbitrary type variables `'a`, `'b`) -/
theorem type_subst_deBruijn_subst_list {α : Type u} {β : Type v} :
    ∀ (t : α) (tvs : List mlstring) (tvs' : β) (ts ts' ts'' : List Ty) (inc : Nat),
     (LENGTH tvs = LENGTH ts) ∧
     EVERY (check_freevars 0 tvs) ts'' →
     (MAP (deBruijn_subst inc ts') (MAP (type_subst (alist_to_fmap (ZIP (tvs, ts)))) ts'') =
      MAP (type_subst (alist_to_fmap (ZIP (tvs, MAP (fun t => deBruijn_subst inc ts' t) ts))))
        ts'') := by
  sorry

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
    ∀ (l : Nat) (tvs' : List mlstring) (t : Ty),
     check_freevars l tvs' t →
     ∀ (targs : List Ty) (n1 tvs : Nat),
       (l = n1 + (LENGTH targs)) ∧
       EVERY (check_freevars tvs tvs') targs
        →
        check_freevars (n1 + tvs) tvs'
          (deBruijn_subst n1 (MAP (deBruijn_inc 0 n1) targs) t) := by
  sorry

/- HOL4:
   Theorem nil_deBruijn_subst:
    ∀skip tvs t. check_freevars skip [] t ⇒ (deBruijn_subst skip tvs t = t) -/
theorem nil_deBruijn_subst :
    ∀ (skip : Nat) (tvs : List Ty) (t : Ty),
      check_freevars skip [] t → (deBruijn_subst skip tvs t = t) := by
  sorry

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
   (`tvs'` is unused in both conjuncts, so in HOL4 it has an arbitrary type variable in each
   (`'a` resp. `'b`)) -/
theorem deBruijn_subst2 {α : Type u} {β : Type v} :
    (∀ (t : Ty) (sk : Nat) (targs targs' : List Ty) (tvs' : α),
     check_freevars (LENGTH targs) [] t →
     (deBruijn_subst sk (MAP (deBruijn_inc 0 sk) targs') (deBruijn_subst 0 targs t) =
      deBruijn_subst 0 (MAP (deBruijn_subst sk (MAP (deBruijn_inc 0 sk) targs')) targs) t)) ∧
    (∀ (ts : List Ty) (sk : Nat) (targs targs' : List Ty) (tvs' : β),
     EVERY (check_freevars (LENGTH targs) []) ts →
     (MAP (deBruijn_subst sk (MAP (deBruijn_inc 0 sk) targs')) (MAP (deBruijn_subst 0 targs) ts) =
     (MAP (deBruijn_subst 0 (MAP (deBruijn_subst sk (MAP (deBruijn_inc 0 sk) targs')) targs)) ts))) := by
  sorry

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
    ∀ (tvs : Nat) (tvs2 : List mlstring) (t : Ty),
     check_freevars tvs tvs2 t →
     ∀ (tvs' : Nat) (targs : List Ty) (n : Nat),
     (tvs = n + LENGTH targs) ∧
     EVERY (check_freevars tvs' tvs2) targs
     →
     check_freevars (n + tvs') tvs2
        (deBruijn_subst n (MAP (deBruijn_inc 0 n) targs) t) := by
  sorry

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
    (∀ (t : Ty) (n inc n' : Nat) (targs : List Ty),
      deBruijn_inc n inc
            (deBruijn_subst (n + n') (MAP (deBruijn_inc 0 (n + n')) targs) t) =
      deBruijn_subst (n + inc + n') (MAP (deBruijn_inc 0 (n + inc + n')) targs)
            (deBruijn_inc n inc t)) ∧
    (∀ (ts : List Ty) (n inc n' : Nat) (targs : List Ty),
      MAP (deBruijn_inc n inc)
            (MAP (deBruijn_subst (n + n') (MAP (deBruijn_inc 0 (n + n')) targs)) ts) =
      MAP (deBruijn_subst (n + inc + n') (MAP (deBruijn_inc 0 (n + inc + n')) targs))
            (MAP (deBruijn_inc n inc) ts)) := by
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
    (∀ (t : Ty) (ts : List Ty) (inc : Nat),
     deBruijn_subst 0 ts (deBruijn_inc 0 (inc + LENGTH ts) t)
     =
     deBruijn_inc 0 inc t) ∧
    (∀ (ts' ts : List Ty) (inc : Nat),
     MAP (deBruijn_subst 0 ts) (MAP (deBruijn_inc 0 (inc + LENGTH ts)) ts')
     =
     MAP (deBruijn_inc 0 inc) ts') := by
  sorry

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
   (`tvs'` and `tvs''` are unused in both conjuncts, so in HOL4 they have arbitrary type variables
   (`'a`, `'b` in the first conjunct, `'c`, `'d` in the second)) -/
theorem type_e_subst_lem7 {α : Type u} {β : Type v} {γ : Type w} {δ : Type u} :
    (∀ (t : Ty) (sk : Nat) (targs targs' : List Ty) (tvs' : α) (tvs'' : β),
     (deBruijn_subst sk (MAP (deBruijn_inc 0 sk) targs') (deBruijn_subst 0 targs t) =
      deBruijn_subst 0 (MAP (deBruijn_subst sk (MAP (deBruijn_inc 0 sk) targs')) targs)
        (deBruijn_subst (LENGTH targs + sk) (MAP (deBruijn_inc 0 (LENGTH targs + sk)) targs') t))) ∧
    (∀ (ts : List Ty) (sk : Nat) (targs targs' : List Ty) (tvs' : γ) (tvs'' : δ),
     (MAP (deBruijn_subst sk (MAP (deBruijn_inc 0 sk) targs')) (MAP (deBruijn_subst 0 targs) ts) =
     (MAP (deBruijn_subst 0 (MAP (deBruijn_subst sk (MAP (deBruijn_inc 0 sk) targs')) targs))
          (MAP (deBruijn_subst (LENGTH targs + sk) (MAP (deBruijn_inc 0 (LENGTH targs + sk)) targs')) ts)))) := by
  sorry

/- HOL4:
   Theorem deBruijn_subst_id:
    (!t n. check_freevars n [] t ⇒ (deBruijn_subst 0 (MAP Tvar_db (COUNT_LIST n)) t = t)) ∧
    (!ts n. EVERY (check_freevars n []) ts ⇒ (MAP (deBruijn_subst 0 (MAP Tvar_db (COUNT_LIST n))) ts = ts)) -/
theorem deBruijn_subst_id :
    (∀ (t : Ty) (n : Nat), check_freevars n [] t →
      (deBruijn_subst 0 (MAP Ty.Tvar_db (COUNT_LIST n)) t = t)) ∧
    (∀ (ts : List Ty) (n : Nat), EVERY (check_freevars n []) ts →
      (MAP (deBruijn_subst 0 (MAP Ty.Tvar_db (COUNT_LIST n))) ts = ts)) := by
  sorry

/- HOL4:
   Theorem deBruijn_subst_freevars:
    !skip targs t tvs.
     skip = 0 ∧
     EVERY (check_freevars tvs []) targs ∧
     check_freevars (LENGTH targs) [] t
     ⇒
     check_freevars tvs [] (deBruijn_subst skip targs t) -/
theorem deBruijn_subst_freevars :
    ∀ (skip : Nat) (targs : List Ty) (t : Ty) (tvs : Nat),
     skip = 0 ∧
     EVERY (check_freevars tvs []) targs ∧
     check_freevars (LENGTH targs) [] t
     →
     check_freevars tvs [] (deBruijn_subst skip targs t) := by
  sorry

/- HOL4:
   Theorem tenv_abbrev_ok_lookup:
    !tenvT tn tvs t.
     tenv_abbrev_ok tenvT ∧
     nsLookup tenvT tn = SOME (tvs,t)
     ⇒
     check_freevars 0 tvs t -/
theorem tenv_abbrev_ok_lookup :
    ∀ (tenvT : tenv_abbrev) (tn : Ident modN typeN) (tvs : List tvarN) (t : Ty),
     tenv_abbrev_ok tenvT ∧
     nsLookup tenvT tn = some (tvs, t)
     →
     check_freevars 0 tvs t := by
  sorry

/- HOL4:
   Theorem check_freevars_type_name_subst:
    !tvs t dbmax tenvT.
     tenv_abbrev_ok tenvT ∧
     check_type_names tenvT t ∧
     check_freevars_ast tvs t
     ⇒
     check_freevars dbmax tvs (type_name_subst tenvT t) -/
theorem check_freevars_type_name_subst :
    ∀ (tvs : List mlstring) (t : ast_t) (dbmax : Nat) (tenvT : tenv_abbrev),
     tenv_abbrev_ok tenvT ∧
     check_type_names tenvT t ∧
     check_freevars_ast tvs t
     →
     check_freevars dbmax tvs (type_name_subst tenvT t) := by
  sorry

/- HOL4:
   Theorem tenv_ctor_ok_merge[simp]:
      !tenvC1 tenvC2.
       tenv_ctor_ok tenvC1 ∧ tenv_ctor_ok tenvC2
       ⇒
       tenv_ctor_ok (nsAppend tenvC1 tenvC2) -/
theorem tenv_ctor_ok_merge :
    ∀ (tenvC1 tenvC2 : tenv_ctor),
     tenv_ctor_ok tenvC1 ∧ tenv_ctor_ok tenvC2
     →
     tenv_ctor_ok (nsAppend tenvC1 tenvC2) := by
  sorry

/- HOL4:
   Theorem tenv_ctor_ok_lookup:
      !tenvC cn tvs ts tn.
       tenv_ctor_ok tenvC ∧ nsLookup tenvC cn = SOME (tvs,ts,tn)
       ⇒
       EVERY (check_freevars 0 tvs) ts -/
theorem tenv_ctor_ok_lookup :
    ∀ (tenvC : tenv_ctor) (cn : Ident modN conN) (tvs : List tvarN) (ts : List Ty)
      (tn : type_ident),
     tenv_ctor_ok tenvC ∧ nsLookup tenvC cn = some (tvs, ts, tn)
     →
     EVERY (check_freevars 0 tvs) ts := by
  sorry

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
   (in the fifth conjunct `tvs` and `e` are unused, so in HOL4 they have arbitrary type variables
   `'a`, `'b`) -/
theorem bind_tvar_rewrites {α : Type u} {β : Type v} :
    (∀ (tvs : Nat) (e1 e2 : tenv_val_exp),
      db_merge (bind_tvar tvs e1) e2 = bind_tvar tvs (db_merge e1 e2)) ∧
    (∀ (tvs : Nat) (e : tenv_val_exp), num_tvs (bind_tvar tvs e) = tvs + num_tvs e) ∧
    (∀ (tvs : Nat) (e : tenv_val_exp), num_tvs (.Bind_tvar tvs e) = tvs + num_tvs e) ∧
    (∀ (tvs : Nat) (n : varN) (t : Ty) (e : tenv_val_exp),
      num_tvs (.Bind_name n tvs t e) = num_tvs e) ∧
    (∀ (tvs : α) (e : β), num_tvs tenv_val_exp.Empty = 0) ∧
    (∀ (n : mlstring) (inc tvs : Nat) (e : tenv_val_exp),
      tveLookup n inc (bind_tvar tvs e) = tveLookup n (inc + tvs) e) ∧
    (∀ (tvs : Nat) (e : tenv_val_exp), tenv_val_exp_ok (bind_tvar tvs e) ↔ tenv_val_exp_ok e) ∧
    (∀ (targs : List Ty) (tvs : Nat) (e : tenv_val_exp),
      deBruijn_subst_tenvE targs (bind_tvar tvs e) =
      bind_tvar tvs (deBruijn_subst_tenvE targs e)) := by
  sorry

/- HOL4:
   Theorem bind_tvar0[simp]:
    !x. bind_tvar 0 x = x -/
theorem bind_tvar0 : ∀ (x : tenv_val_exp), bind_tvar 0 x = x := by
  sorry

/- HOL4:
   Theorem tveLookup_subst_none:
    !n inc e.
    tveLookup n inc (deBruijn_subst_tenvE targs e) = NONE ⇔
    tveLookup n inc e = NONE
   (`targs` is a free variable, hence universally quantified) -/
theorem tveLookup_subst_none :
    ∀ (targs : List Ty) (n : mlstring) (inc : Nat) (e : tenv_val_exp),
    tveLookup n inc (deBruijn_subst_tenvE targs e) = none ↔
    tveLookup n inc e = none := by
  sorry

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
     tveLookup n inc e1 = none ∧ tveLookup n (num_tvs e1 + inc) e2 = none := by
  sorry

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
     tveLookup n 0 e = none := by
  sorry

/- HOL4:
   Theorem tveLookup_freevars:
      !n tvs tenvE tvs' t.
       tenv_val_exp_ok tenvE ∧
       num_tvs tenvE = 0 ∧
       tveLookup n tvs tenvE = SOME (tvs',t)
       ⇒
       check_freevars tvs' [] t -/
theorem tveLookup_freevars :
    ∀ (n : mlstring) (tvs : Nat) (tenvE : tenv_val_exp) (tvs' : Nat) (t : Ty),
     tenv_val_exp_ok tenvE ∧
     num_tvs tenvE = 0 ∧
     tveLookup n tvs tenvE = some (tvs', t)
     →
     check_freevars tvs' [] t := by
  sorry

/- HOL4:
   Theorem bind_var_list_append:
    !n te1 te2 te3.
     bind_var_list n (te1++te2) te3 = bind_var_list n te1 (bind_var_list n te2 te3) -/
theorem bind_var_list_append :
    ∀ (n : Nat) (te1 te2 : List (varN × Ty)) (te3 : tenv_val_exp),
     bind_var_list n (te1 ++ te2) te3 = bind_var_list n te1 (bind_var_list n te2 te3) := by
  sorry

/- HOL4:
   Theorem num_tvs_bind_var_list[simp]:
    !tvs env tenvE. num_tvs (bind_var_list tvs env tenvE) = num_tvs tenvE -/
theorem num_tvs_bind_var_list :
    ∀ (tvs : Nat) (env : List (varN × Ty)) (tenvE : tenv_val_exp),
      num_tvs (bind_var_list tvs env tenvE) = num_tvs tenvE := by
  sorry

/- HOL4:
   Theorem tenv_val_exp_ok_bvl:
    !tenvE env.
     tenv_val_exp_ok tenvE ∧ EVERY (check_freevars (num_tvs tenvE) []) (MAP SND env)
     ⇒
     tenv_val_exp_ok (bind_var_list 0 env tenvE) -/
theorem tenv_val_exp_ok_bvl :
    ∀ (tenvE : tenv_val_exp) (env : List (varN × Ty)),
     tenv_val_exp_ok tenvE ∧ EVERY (check_freevars (num_tvs tenvE) []) (MAP SND env)
     →
     tenv_val_exp_ok (bind_var_list 0 env tenvE) := by
  sorry

/- HOL4:
   Theorem tveLookup_subst_some:
      ∀n e targs tvs t inc.
       tveLookup n inc e = SOME (tvs,t)
       ⇒
       tveLookup n inc (deBruijn_subst_tenvE targs e) =
         SOME (tvs, deBruijn_subst (tvs+inc+num_tvs e) (MAP (deBruijn_inc 0 (tvs+inc+num_tvs e)) targs) t) -/
theorem tveLookup_subst_some :
    ∀ (n : mlstring) (e : tenv_val_exp) (targs : List Ty) (tvs : Nat) (t : Ty) (inc : Nat),
     tveLookup n inc e = some (tvs, t)
     →
     tveLookup n inc (deBruijn_subst_tenvE targs e) =
       some (tvs, deBruijn_subst (tvs + inc + num_tvs e)
         (MAP (deBruijn_inc 0 (tvs + inc + num_tvs e)) targs) t) := by
  sorry

/- HOL4:
   Theorem num_tvs_db_merge[simp]:
    !e1 e2. num_tvs (db_merge e1 e2) = num_tvs e1 + num_tvs e2 -/
theorem num_tvs_db_merge :
    ∀ (e1 e2 : tenv_val_exp), num_tvs (db_merge e1 e2) = num_tvs e1 + num_tvs e2 := by
  sorry

/- HOL4:
   Theorem num_tvs_deBruijn_subst_tenvE[simp]:
    !targs tenvE. num_tvs (deBruijn_subst_tenvE targs tenvE) = num_tvs tenvE -/
theorem num_tvs_deBruijn_subst_tenvE :
    ∀ (targs : List Ty) (tenvE : tenv_val_exp),
      num_tvs (deBruijn_subst_tenvE targs tenvE) = num_tvs tenvE := by
  sorry

/- HOL4:
   Theorem tveLookup_inc_some:
    !n inc e tvs t inc2.
      tveLookup n inc e = SOME (tvs, t)
      ⇒
      ?t'. (t = deBruijn_inc tvs inc t') ∧
           (tveLookup n inc2 e = SOME (tvs, deBruijn_inc tvs inc2 t')) -/
theorem tveLookup_inc_some :
    ∀ (n : mlstring) (inc : Nat) (e : tenv_val_exp) (tvs : Nat) (t : Ty) (inc2 : Nat),
      tveLookup n inc e = some (tvs, t)
      →
      ∃ t', (t = deBruijn_inc tvs inc t') ∧
           (tveLookup n inc2 e = some (tvs, deBruijn_inc tvs inc2 t')) := by
  sorry

/- HOL4:
   Theorem tveLookup_freevars_subst:
      !tenvE targs n t inc.
       EVERY (check_freevars (inc + num_tvs tenvE) []) targs ∧
       tveLookup n inc tenvE = SOME (LENGTH targs,t) ∧
       tenv_val_exp_ok tenvE
       ⇒
       check_freevars (inc + num_tvs tenvE) [] (deBruijn_subst 0 targs t) -/
theorem tveLookup_freevars_subst :
    ∀ (tenvE : tenv_val_exp) (targs : List Ty) (n : mlstring) (t : Ty) (inc : Nat),
     EVERY (check_freevars (inc + num_tvs tenvE) []) targs ∧
     tveLookup n inc tenvE = some (LENGTH targs, t) ∧
     tenv_val_exp_ok tenvE
     →
     check_freevars (inc + num_tvs tenvE) [] (deBruijn_subst 0 targs t) := by
  sorry

/- HOL4:
   Theorem tenv_val_exp_ok_db_merge:
    !e1 e2. tenv_val_exp_ok (db_merge e1 e2) ⇒ tenv_val_exp_ok e2 -/
theorem tenv_val_exp_ok_db_merge :
    ∀ (e1 e2 : tenv_val_exp), tenv_val_exp_ok (db_merge e1 e2) → tenv_val_exp_ok e2 := by
  sorry

/- HOL4:
   Theorem tveLookup_freevars[local]:
     !e n inc t tvs.
     tenv_val_exp_ok e ∧
     tveLookup n inc e = SOME (tvs, t)
     ⇒
     check_freevars (tvs+inc+num_tvs e) [] t
   (second theorem of that name in the HOL4 script; Lean name: `tveLookup_freevars'`) -/
theorem tveLookup_freevars' :
    ∀ (e : tenv_val_exp) (n : mlstring) (inc : Nat) (t : Ty) (tvs : Nat),
     tenv_val_exp_ok e ∧
     tveLookup n inc e = some (tvs, t)
     →
     check_freevars (tvs + inc + num_tvs e) [] t := by
  sorry

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
    ∀ (tvs l : Nat) (tenv : tenv_val_exp) (n : mlstring) (t : Ty),
     tenv_val_exp_ok tenv ∧
     num_tvs tenv = 0
     →
     (tveLookup n tvs tenv = some (l, t)
      ↔
      tveLookup n 0 tenv = some (l, t)) := by
  sorry

/- HOL4:
   Theorem deBruijn_subst_E_bvl:
    !tenv1 tenv2 tvs.
     deBruijn_subst_tenvE targs (bind_var_list tvs tenv1 tenv2)
     =
     bind_var_list tvs
             (MAP (\(x,t). (x, deBruijn_subst (tvs + num_tvs tenv2) (MAP (deBruijn_inc 0 (tvs + num_tvs tenv2)) targs) t)) tenv1)
             (deBruijn_subst_tenvE targs tenv2)
   (`targs` is a free variable, hence universally quantified) -/
theorem deBruijn_subst_E_bvl :
    ∀ (targs : List Ty) (tenv1 : List (varN × Ty)) (tenv2 : tenv_val_exp) (tvs : Nat),
     deBruijn_subst_tenvE targs (bind_var_list tvs tenv1 tenv2)
     =
     bind_var_list tvs
             (MAP (fun p => (p.1, deBruijn_subst (tvs + num_tvs tenv2)
               (MAP (deBruijn_inc 0 (tvs + num_tvs tenv2)) targs) p.2)) tenv1)
             (deBruijn_subst_tenvE targs tenv2) := by
  sorry

/- HOL4:
   Theorem db_merge_bvl:
    !tenv1 tenv2 tenv3 tvs.
     db_merge (bind_var_list tvs tenv1 tenv2) tenv3
     =
     bind_var_list tvs tenv1 (db_merge tenv2 tenv3) -/
theorem db_merge_bvl :
    ∀ (tenv1 : List (varN × Ty)) (tenv2 tenv3 : tenv_val_exp) (tvs : Nat),
     db_merge (bind_var_list tvs tenv1 tenv2) tenv3
     =
     bind_var_list tvs tenv1 (db_merge tenv2 tenv3) := by
  sorry

/- HOL4:
   Theorem tveLookup_db_merge_some:
      !n inc tenvE1 tenvE2 tvs t.
       tveLookup n inc (db_merge tenvE1 tenvE2) = SOME (tvs,t)
       ⇔
       tveLookup n inc tenvE1 = SOME (tvs,t) ∨
       (tveLookup n inc tenvE1 = NONE ∧
        tveLookup n (num_tvs tenvE1 + inc) tenvE2 = SOME (tvs, t)) -/
theorem tveLookup_db_merge_some :
    ∀ (n : mlstring) (inc : Nat) (tenvE1 tenvE2 : tenv_val_exp) (tvs : Nat) (t : Ty),
     tveLookup n inc (db_merge tenvE1 tenvE2) = some (tvs, t)
     ↔
     tveLookup n inc tenvE1 = some (tvs, t) ∨
     (tveLookup n inc tenvE1 = none ∧
      tveLookup n (num_tvs tenvE1 + inc) tenvE2 = some (tvs, t)) := by
  sorry

/- HOL4:
   Theorem type_op_cases =
     ``type_op op ts t3``
     |> (SIMP_CONV(srw_ss())(type_op_def::eqs@elims) THENC
         SIMP_CONV (bool_ss++DNF_ss) [
           PULL_EXISTS])
   (the HOL4 theorem is `⊢ type_op op ts t3 ⇔ <case analysis>`; stated here in the natural
   expanded form, one disjunct per clause of `type_op`; free variables `op ts t3` are universally
   quantified) -/
theorem type_op_cases : ∀ (op : op) (ts : List Ty) (t3 : Ty),
    type_op op ts t3 ↔
    (op = .Opapp ∧ ∃ a1 a2, ts = [a1, a2] ∧ a1 = Tfn a2 t3) ∨
    (∃ s n, op = .Shift .W8 s n ∧ ∃ a1, ts = [a1] ∧ a1 = Tword8 ∧ t3 = Tword8) ∨
    (∃ s n, op = .Shift .W64 s n ∧ ∃ a1, ts = [a1] ∧ a1 = Tword64 ∧ t3 = Tword64) ∨
    (op = .Equality ∧ ∃ a1 a2, ts = [a1, a2] ∧ a1 = a2 ∧ t3 = Tbool) ∨
    (∃ a ty, op = .Arith a ty ∧
      EVERY (fun arg => arg = t_of ty) ts ∧ t3 = t_of ty ∧
      supported_arith a ty = some (LENGTH ts)) ∨
    (∃ ty1 ty2, op = .FromTo ty1 ty2 ∧ ∃ a1, ts = [a1] ∧ a1 = t_of ty1 ∧ t3 = t_of ty2 ∧
      supported_conversion ty1 ty2) ∨
    (∃ tst ty, op = .Test tst ty ∧ ∃ a1 a2, ts = [a1, a2] ∧ a1 = a2 ∧ t3 = Tbool ∧
      a1 = t_of ty ∧ supported_test tst ty) ∨
    (op = .Opassign ∧ ∃ a1 a2, ts = [a1, a2] ∧ a1 = Tref a2 ∧ t3 = Ttup []) ∨
    (op = .Opref ∧ ∃ a1, ts = [a1] ∧ t3 = Tref a1) ∨
    (op = .Opderef ∧ ∃ a1, ts = [a1] ∧ a1 = Tref t3) ∨
    (op = .Aw8alloc ∧ ∃ a1 a2, ts = [a1, a2] ∧ a1 = Tint ∧ a2 = Tword8 ∧ t3 = Tword8array) ∨
    (op = .Aw8sub ∧ ∃ a1 a2, ts = [a1, a2] ∧ a1 = Tword8array ∧ a2 = Tint ∧ t3 = Tword8) ∨
    (op = .Aw8length ∧ ∃ a1, ts = [a1] ∧ a1 = Tword8array ∧ t3 = Tint) ∨
    (op = .Aw8update ∧ ∃ a1 a2 a3, ts = [a1, a2, a3] ∧ a1 = Tword8array ∧ a2 = Tint ∧
      a3 = Tword8 ∧ t3 = Ttup []) ∨
    (op = .CopyStrStr ∧ ∃ a1 a2 a3, ts = [a1, a2, a3] ∧ a1 = Tstring ∧ a2 = Tint ∧
      a3 = Tint ∧ t3 = Tstring) ∨
    (op = .CopyStrAw8 ∧ ∃ a1 a2 a3 a4 a5, ts = [a1, a2, a3, a4, a5] ∧ a1 = Tstring ∧
      a2 = Tint ∧ a3 = Tint ∧ a4 = Tword8array ∧ a5 = Tint ∧ t3 = Ttup []) ∨
    (op = .CopyAw8Str ∧ ∃ a1 a2 a3, ts = [a1, a2, a3] ∧ a1 = Tword8array ∧ a2 = Tint ∧
      a3 = Tint ∧ t3 = Tstring) ∨
    (op = .CopyAw8Aw8 ∧ ∃ a1 a2 a3 a4 a5, ts = [a1, a2, a3, a4, a5] ∧ a1 = Tword8array ∧
      a2 = Tint ∧ a3 = Tint ∧ a4 = Tword8array ∧ a5 = Tint ∧ t3 = Ttup []) ∨
    (op = .Implode ∧ ∃ a1, ts = [a1] ∧ a1 = Tlist Tchar ∧ t3 = Tstring) ∨
    (op = .Explode ∧ ∃ a1, ts = [a1] ∧ a1 = Tstring ∧ t3 = Tlist Tchar) ∨
    (op = .Strsub ∧ ∃ a1 a2, ts = [a1, a2] ∧ a1 = Tstring ∧ a2 = Tint ∧ t3 = Tchar) ∨
    (op = .Strlen ∧ ∃ a1, ts = [a1] ∧ a1 = Tstring ∧ t3 = Tint) ∨
    (op = .Strcat ∧ ∃ a1, ts = [a1] ∧ a1 = Tlist Tstring ∧ t3 = Tstring) ∨
    (op = .VfromList ∧ ∃ a1 ctor, ts = [.Tapp [a1] ctor] ∧ ctor = Tlist_num ∧
      t3 = Tvector a1) ∨
    (op = .Vsub ∧ ∃ a1 a2, ts = [a1, a2] ∧ a2 = Tint ∧ Tvector t3 = a1) ∨
    (op = .Vlength ∧ ∃ a1 ctor, ts = [.Tapp [a1] ctor] ∧ ctor = Tvector_num ∧ t3 = Tint) ∨
    (op = .Aalloc ∧ ∃ a1 a2, ts = [a1, a2] ∧ a1 = Tint ∧ t3 = Tarray a2) ∨
    (op = .AallocEmpty ∧ ∃ a1, ts = [a1] ∧ a1 = Ttup [] ∧ ∃ a2, t3 = Tarray a2) ∨
    (op = .Asub ∧ ∃ a1 a2, ts = [a1, a2] ∧ a2 = Tint ∧ Tarray t3 = a1) ∨
    (op = .Alength ∧ ∃ a1 ctor, ts = [.Tapp [a1] ctor] ∧ ctor = Tarray_num ∧ t3 = Tint) ∨
    (op = .Aupdate ∧ ∃ a1 a2 a3, ts = [a1, a2, a3] ∧ a1 = Tarray a3 ∧ a2 = Tint ∧
      t3 = Ttup []) ∨
    (op = .ConfigGC ∧ ∃ a1 a2, ts = [a1, a2] ∧ a1 = Tint ∧ a2 = Tint ∧ t3 = Ttup []) ∨
    (∃ n, op = .FFI n ∧ ∃ a1 a2, ts = [a1, a2] ∧ a1 = Tstring ∧ a2 = Tword8array ∧
      t3 = Ttup []) ∨
    (op = .ListAppend ∧ ∃ a1 ctor a2, ts = [.Tapp [a1] ctor, a2] ∧ ctor = Tlist_num ∧
      a2 = .Tapp [a1] ctor ∧ t3 = a2) := by
  sorry

/- HOL4:
   Theorem type_ps_length:
    ∀tvs tenvC ps ts tenv.
     type_ps tvs tenvC ps ts tenv ⇒ (LENGTH ps = LENGTH ts) -/
theorem type_ps_length :
    ∀ (tvs : Nat) (tenvC : type_env) (ps : List pat) (ts : List Ty)
      (tenv : List (varN × Ty)),
     type_ps tvs tenvC ps ts tenv → (LENGTH ps = LENGTH ts) := by
  sorry

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
    (∀ (tvs : Nat) (tenvC : type_env) (p : pat) (t : Ty) (env' : List (varN × Ty)),
      type_p tvs tenvC p t env' →
      check_freevars tvs [] t ∧
      EVERY (check_freevars tvs []) (MAP SND env')) ∧
    (∀ (tvs : Nat) (tenvC : type_env) (ps : List pat) (ts : List Ty) (env' : List (varN × Ty)),
      type_ps tvs tenvC ps ts env' →
      EVERY (check_freevars tvs []) ts ∧
      EVERY (check_freevars tvs []) (MAP SND env')) := by
  sorry

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
    (∀ (n : Nat) (tenv : type_env) (p : pat) (t : Ty) (new_bindings : List (varN × Ty)),
       type_p n tenv p t new_bindings →
       ∀ (targs' : List Ty) (inc tvs : Nat) (targs : List Ty),
       tenv_abbrev_ok tenv.t ∧
       tenv_ctor_ok tenv.c ∧
       (n = inc + LENGTH targs) ∧
       EVERY (check_freevars tvs []) targs ∧
       (targs' = MAP (deBruijn_inc 0 inc) targs)
       →
       type_p (inc + tvs) tenv
              p
              (deBruijn_subst inc targs' t)
              (MAP (fun p => (p.1, deBruijn_subst inc targs' p.2)) new_bindings)) ∧
    (∀ (n : Nat) (tenv : type_env) (ps : List pat) (ts : List Ty)
       (new_bindings : List (varN × Ty)),
       type_ps n tenv ps ts new_bindings →
       ∀ (targs' : List Ty) (inc : Nat) (targs : List Ty) (tvs : Nat),
       tenv_abbrev_ok tenv.t ∧
       tenv_ctor_ok tenv.c ∧
       (n = inc + LENGTH targs) ∧
       EVERY (check_freevars tvs []) targs ∧
       (targs' = MAP (deBruijn_inc 0 inc) targs)
       →
       type_ps (inc + tvs) tenv
              ps
              (MAP (deBruijn_subst inc targs') ts)
              (MAP (fun p => (p.1, deBruijn_subst inc targs' p.2)) new_bindings)) := by
  sorry

/- HOL4:
   Theorem type_p_bvl:
      (!tvs tenvC p t bindings. type_p tvs tenvC p t bindings ⇒
       !tenv'. tenv_val_exp_ok tenv' ⇒ tenv_val_exp_ok (bind_var_list tvs bindings tenv')) ∧
      (!tvs tenvC ps ts bindings. type_ps tvs tenvC ps ts bindings ⇒
       !tenv'. tenv_val_exp_ok tenv' ⇒ tenv_val_exp_ok (bind_var_list tvs bindings tenv')) -/
theorem type_p_bvl :
    (∀ (tvs : Nat) (tenvC : type_env) (p : pat) (t : Ty) (bindings : List (varN × Ty)),
       type_p tvs tenvC p t bindings →
       ∀ (tenv' : tenv_val_exp),
         tenv_val_exp_ok tenv' → tenv_val_exp_ok (bind_var_list tvs bindings tenv')) ∧
    (∀ (tvs : Nat) (tenvC : type_env) (ps : List pat) (ts : List Ty)
       (bindings : List (varN × Ty)),
       type_ps tvs tenvC ps ts bindings →
       ∀ (tenv' : tenv_val_exp),
         tenv_val_exp_ok tenv' → tenv_val_exp_ok (bind_var_list tvs bindings tenv')) := by
  sorry

/- HOL4:
   Theorem type_p_tenvV_indep:
    (!p tvs tenv t bindings tenvV.
     type_p tvs tenv p t bindings = type_p tvs (tenv with v := tenvV) p t bindings) ∧
    (!ps tvs tenv t bindings tenvV.
     type_ps tvs tenv ps t bindings = type_ps tvs (tenv with v := tenvV) ps t bindings) -/
theorem type_p_tenvV_indep :
    (∀ (p : pat) (tvs : Nat) (tenv : type_env) (t : Ty) (bindings : List (varN × Ty))
       (tenvV : tenv_val),
     type_p tvs tenv p t bindings ↔ type_p tvs { tenv with v := tenvV } p t bindings) ∧
    (∀ (ps : List pat) (tvs : Nat) (tenv : type_env) (t : List Ty)
       (bindings : List (varN × Ty)) (tenvV : tenv_val),
     type_ps tvs tenv ps t bindings ↔ type_ps tvs { tenv with v := tenvV } ps t bindings) := by
  sorry

/- HOL4:
   Theorem type_es_list_rel:
    !es ts tenv tenvE. type_es tenv tenvE es ts = LIST_REL (type_e tenv tenvE) es ts -/
theorem type_es_list_rel :
    ∀ (es : List exp) (ts : List Ty) (tenv : type_env) (tenvE : tenv_val_exp),
      type_es tenv tenvE es ts ↔ LIST_REL (type_e tenv tenvE) es ts := by
  sorry

/- HOL4:
   Theorem type_es_length:
    ∀tenv tenvE es ts.
     type_es tenv tenvE es ts ⇒ (LENGTH es = LENGTH ts) -/
theorem type_es_length :
    ∀ (tenv : type_env) (tenvE : tenv_val_exp) (es : List exp) (ts : List Ty),
     type_es tenv tenvE es ts → (LENGTH es = LENGTH ts) := by
  sorry

/- HOL4:
   Theorem tenv_val_exp_ok_bvl_funs:
      !funs env tenv bindings tenv_val tenvE.
       type_funs tenv (bind_var_list 0 bindings tenvE) funs env ∧
       tenv_val_exp_ok tenvE
       ⇒
       tenv_val_exp_ok (bind_var_list 0 env tenvE)
   (`tenv_val` is unused, so in HOL4 it has an arbitrary type variable `'a`) -/
theorem tenv_val_exp_ok_bvl_funs {α : Type u} :
    ∀ (funs : List (varN × varN × exp)) (env : List (varN × Ty)) (tenv : type_env)
      (bindings : List (varN × Ty)) (tenv_val : α) (tenvE : tenv_val_exp),
     type_funs tenv (bind_var_list 0 bindings tenvE) funs env ∧
     tenv_val_exp_ok tenvE
     →
     tenv_val_exp_ok (bind_var_list 0 env tenvE) := by
  sorry

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
    (∀ (tenv : type_env) (tenvE : tenv_val_exp) (e : exp) (t : Ty),
      type_e tenv tenvE e t →
      tenv_val_exp_ok tenvE ∧ tenv_val_ok tenv.v →
      check_freevars (num_tvs tenvE) [] t) ∧
    (∀ (tenv : type_env) (tenvE : tenv_val_exp) (es : List exp) (ts : List Ty),
      type_es tenv tenvE es ts →
      tenv_val_exp_ok tenvE ∧ tenv_val_ok tenv.v →
      EVERY (check_freevars (num_tvs tenvE) []) ts) ∧
    (∀ (tenv : type_env) (tenvE : tenv_val_exp) (funs : List (varN × varN × exp))
       (env : List (varN × Ty)),
      type_funs tenv tenvE funs env →
      tenv_val_exp_ok tenvE ∧ tenv_val_ok tenv.v →
      EVERY (check_freevars (num_tvs tenvE) []) (MAP SND env)) := by
  sorry

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
                         (MAP (\(x,t). (x, deBruijn_subst (num_tvs tenvE1) targs' t)) env))
   (`tenvE2` is a free variable, hence universally quantified, shared by the three conjuncts) -/
theorem type_e_subst : ∀ (tenvE2 : tenv_val_exp),
    (∀ (tenv : type_env) (tenvE : tenv_val_exp) (e : exp) (t : Ty),
       type_e tenv tenvE e t →
       ∀ (tenvE1 : tenv_val_exp) (targs : List Ty) (tvs : Nat) (targs' : List Ty),
         num_tvs tenvE2 = 0 ∧
         tenv_abbrev_ok tenv.t ∧
         tenv_ctor_ok tenv.c ∧
         tenv_val_ok tenv.v ∧
         tenv_val_exp_ok tenvE ∧
         EVERY (check_freevars tvs []) targs ∧
         tenvE = db_merge tenvE1 (bind_tvar (LENGTH targs) tenvE2) ∧
         targs' = MAP (deBruijn_inc 0 (num_tvs tenvE1)) targs
         →
         type_e tenv (db_merge (deBruijn_subst_tenvE targs tenvE1) (bind_tvar tvs tenvE2))
                      e
                      (deBruijn_subst (num_tvs tenvE1) targs' t)) ∧
    (∀ (tenv : type_env) (tenvE : tenv_val_exp) (es : List exp) (ts : List Ty),
       type_es tenv tenvE es ts →
       ∀ (tenvE1 : tenv_val_exp) (targs : List Ty) (tvs : Nat) (targs' : List Ty),
         num_tvs tenvE2 = 0 ∧
         tenv_abbrev_ok tenv.t ∧
         tenv_ctor_ok tenv.c ∧
         tenv_val_ok tenv.v ∧
         tenv_val_exp_ok tenvE ∧
         EVERY (check_freevars tvs []) targs ∧
         tenvE = db_merge tenvE1 (bind_tvar (LENGTH targs) tenvE2) ∧
         targs' = MAP (deBruijn_inc 0 (num_tvs tenvE1)) targs
         →
         type_es tenv (db_merge (deBruijn_subst_tenvE targs tenvE1) (bind_tvar tvs tenvE2))
                     es
                     (MAP (deBruijn_subst (num_tvs tenvE1) targs') ts)) ∧
    (∀ (tenv : type_env) (tenvE : tenv_val_exp) (funs : List (varN × varN × exp))
       (env : List (varN × Ty)),
       type_funs tenv tenvE funs env →
       ∀ (tenvE1 : tenv_val_exp) (targs : List Ty) (tvs : Nat) (targs' : List Ty),
         num_tvs tenvE2 = 0 ∧
         tenv_abbrev_ok tenv.t ∧
         tenv_ctor_ok tenv.c ∧
         tenv_val_ok tenv.v ∧
         tenv_val_exp_ok tenvE ∧
         EVERY (check_freevars tvs []) targs ∧
         tenvE = db_merge tenvE1 (bind_tvar (LENGTH targs) tenvE2) ∧
         targs' = MAP (deBruijn_inc 0 (num_tvs tenvE1)) targs
         →
         type_funs tenv (db_merge (deBruijn_subst_tenvE targs tenvE1) (bind_tvar tvs tenvE2))
                         funs
                         (MAP (fun p => (p.1, deBruijn_subst (num_tvs tenvE1) targs' p.2)) env)) := by
  sorry

/- HOL4:
   Theorem type_funs_Tfn:
      ∀tenv tenvE funs bindings tvs t n.
       type_funs tenv tenvE funs bindings ∧
       ALOOKUP bindings n = SOME t
       ⇒
       ∃t1 t2. (t = Tfn t1 t2) ∧ check_freevars (num_tvs tenvE) [] (Tfn t1 t2)
   (`tvs` is unused, so in HOL4 it has an arbitrary type variable `'a`) -/
theorem type_funs_Tfn {α : Type u} :
    ∀ (tenv : type_env) (tenvE : tenv_val_exp) (funs : List (varN × varN × exp))
      (bindings : List (varN × Ty)) (tvs : α) (t : Ty) (n : varN),
     type_funs tenv tenvE funs bindings ∧
     ALOOKUP bindings n = some t
     →
     ∃ t1 t2, (t = Tfn t1 t2) ∧ check_freevars (num_tvs tenvE) [] (Tfn t1 t2) := by
  sorry

/- HOL4:
   Theorem type_funs_lookup:
    ∀fn tenvE funs bindings n e tenv.
     MEM (fn,n,e) funs ∧
     type_funs tenv tenvE funs bindings
     ⇒
     (∃t. ALOOKUP bindings fn = SOME t) -/
theorem type_funs_lookup :
    ∀ (fn : varN) (tenvE : tenv_val_exp) (funs : List (varN × varN × exp))
      (bindings : List (varN × Ty)) (n : varN) (e : exp) (tenv : type_env),
     MEM (fn, n, e) funs ∧
     type_funs tenv tenvE funs bindings
     →
     (∃ t, ALOOKUP bindings fn = some t) := by
  sorry

/- HOL4:
   Theorem type_funs_find_recfun:
    ∀fn env funs bindings e tenv tenvE t.
     ALOOKUP bindings fn = SOME t ∧
     type_funs tenv tenvE funs bindings
     ⇒
     (∃n e. find_recfun fn funs = SOME (n,e))
   (`env` and the outer `e` are unused, so in HOL4 they have arbitrary type variables `'a`, `'b`) -/
theorem type_funs_find_recfun {α : Type u} {β : Type v} :
    ∀ (fn : varN) (env : α) (funs : List (varN × varN × exp)) (bindings : List (varN × Ty))
      (e : β) (tenv : type_env) (tenvE : tenv_val_exp) (t : Ty),
     ALOOKUP bindings fn = some t ∧
     type_funs tenv tenvE funs bindings
     →
     (∃ (n : varN) (e : exp), find_recfun fn funs = some (n, e)) := by
  sorry

/- HOL4:
   Theorem type_recfun_lookup:
      ∀fn funs n e tenv tenvE bindings tvs t1 t2.
       find_recfun fn funs = SOME (n,e) ∧
       type_funs tenv tenvE funs bindings ∧
       ALOOKUP bindings fn = SOME (Tfn t1 t2)
       ⇒
       type_e tenv (Bind_name n 0 t1 tenvE) e t2 ∧
       check_freevars (num_tvs tenvE) [] (Tfn t1 t2)
   (`tvs` is unused, so in HOL4 it has an arbitrary type variable `'a`) -/
theorem type_recfun_lookup {α : Type u} :
    ∀ (fn : varN) (funs : List (varN × varN × exp)) (n : varN) (e : exp) (tenv : type_env)
      (tenvE : tenv_val_exp) (bindings : List (varN × Ty)) (tvs : α) (t1 t2 : Ty),
     find_recfun fn funs = some (n, e) ∧
     type_funs tenv tenvE funs bindings ∧
     ALOOKUP bindings fn = some (Tfn t1 t2)
     →
     type_e tenv (.Bind_name n 0 t1 tenvE) e t2 ∧
     check_freevars (num_tvs tenvE) [] (Tfn t1 t2) := by
  sorry

/- HOL4:
   Theorem type_funs_distinct:
    ∀tenv tenvE funs bindings .
     type_funs tenv tenvE funs bindings
     ⇒
     ALL_DISTINCT (MAP (λ(x,y,z). x) funs) -/
theorem type_funs_distinct :
    ∀ (tenv : type_env) (tenvE : tenv_val_exp) (funs : List (varN × varN × exp))
      (bindings : List (varN × Ty)),
     type_funs tenv tenvE funs bindings
     →
     ALL_DISTINCT (MAP (fun p => p.1) funs) := by
  sorry

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
   (`x` and `t1` are free variables, hence universally quantified; `targs'` is unused, so in HOL4
   it has an arbitrary type variable `'a`) -/
theorem type_e_subst_lem {α : Type u} : ∀ (x : varN) (t1 : Ty),
    ∀ (tenv : type_env) (tenvE : tenv_val_exp) (e : exp) (t : Ty) (targs : List Ty) (tvs : Nat)
      (targs' : α),
     type_e tenv (.Bind_name x 0 t1 (bind_tvar (LENGTH targs) tenvE)) e t ∧
     num_tvs tenvE = 0 ∧
     tenv_abbrev_ok tenv.t ∧
     tenv_ctor_ok tenv.c ∧
     tenv_val_ok tenv.v ∧
     tenv_val_exp_ok (bind_tvar (LENGTH targs) tenvE) ∧
     EVERY (check_freevars tvs []) targs ∧
     check_freevars (LENGTH targs) [] t1
     →
     type_e tenv (.Bind_name x 0 (deBruijn_subst 0 targs t1) (bind_tvar tvs tenvE)) e
       (deBruijn_subst 0 targs t) := by
  sorry

/- HOL4:
   Theorem mem_type_def_to_ctMap:
      !tenvT next tds ids stamp x.
       MEM (stamp,x) (type_def_to_ctMap tenvT next tds ids) ∧
       LENGTH tds = LENGTH ids
       ⇒
       ?cn i. stamp = TypeStamp cn i ∧ next ≤ i ∧ i < next + LENGTH tds -/
theorem mem_type_def_to_ctMap :
    ∀ (tenvT : Namespace modN typeN (List tvarN × Ty)) (next : Nat)
      (tds : List (List tvarN × mlstring × List (conN × List ast_t))) (ids : List type_ident)
      (stmp : stamp) (x : List tvarN × List Ty × type_ident),
     MEM (stmp, x) (type_def_to_ctMap tenvT next tds ids) ∧
     LENGTH tds = LENGTH ids
     →
     ∃ cn i, stmp = .TypeStamp cn i ∧ next ≤ i ∧ i < next + LENGTH tds := by
  sorry

/- HOL4:
   Theorem ctMap_ok_merge_imp:
      !ctMap1 ctMap2.
       DISJOINT (FRANGE ((SND o SND) o_f ctMap1)) (FRANGE ((SND o SND) o_f ctMap2)) ∧
       ctMap_ok ctMap1 ∧ ctMap_ok ctMap2 ⇒
       ctMap_ok (FUNION ctMap1 ctMap2) -/
theorem ctMap_ok_merge_imp :
    ∀ (ctMap1 ctMap2 : ctMap),
     DISJOINT (FRANGE (o_f (SND ∘ SND) ctMap1)) (FRANGE (o_f (SND ∘ SND) ctMap2)) ∧
     ctMap_ok ctMap1 ∧ ctMap_ok ctMap2 →
     ctMap_ok (FUNION ctMap1 ctMap2) := by
  sorry

/- HOL4:
   Theorem ctMap_ok_lookup:
    !ctMap cn tvs ts ti tn.
     ctMap_ok ctMap ∧ (FLOOKUP ctMap tn = SOME (tvs,ts,ti))
     ⇒
     EVERY (check_freevars 0 tvs) ts
   (`cn` is unused, so in HOL4 it has an arbitrary type variable `'a`) -/
theorem ctMap_ok_lookup {α : Type u} :
    ∀ (ctMap : ctMap) (cn : α) (tvs : List tvarN) (ts : List Ty) (ti : type_ident)
      (tn : stamp),
     ctMap_ok ctMap ∧ (FLOOKUP ctMap tn = some (tvs, ts, ti))
     →
     EVERY (check_freevars 0 tvs) ts := by
  sorry

/- HOL4:
   Theorem type_def_to_ctMap_mem:
      !tenvT next tds tids.
       ALOOKUP (type_def_to_ctMap tenvT next tds tids) k = SOME x ∧
       LENGTH tds = LENGTH tids
       ⇒
       MEM (SND (SND x)) tids
   (`k` and `x` are free variables, hence universally quantified) -/
theorem type_def_to_ctMap_mem :
    ∀ (k : stamp) (x : List tvarN × List Ty × type_ident),
    ∀ (tenvT : Namespace modN typeN (List tvarN × Ty)) (next : Nat)
      (tds : List (List tvarN × mlstring × List (conN × List ast_t))) (tids : List type_ident),
     ALOOKUP (type_def_to_ctMap tenvT next tds tids) k = some x ∧
     LENGTH tds = LENGTH tids
     →
     MEM (SND (SND x)) tids := by
  sorry

/- HOL4:
   Theorem fupdate2_union[local]:
     !m a1 a2. m |++ a1 |++ a2 = FEMPTY |++ a2 ⊌ (m |++ a1)
   (type variables `'a`, `'b` of the finite maps are the Lean variables `α`, `β`) -/
theorem fupdate2_union {α : Type u} {β : Type v} :
    ∀ (m : FMap α β) (a1 a2 : List (α × β)),
      ((m |++ a1) |++ a2) = ((FEMPTY |++ a2) ⊌ (m |++ a1)) := by
  sorry

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
    ∀ (tenvT : tenv_abbrev) (next : Nat)
      (tds : List (List tvarN × mlstring × List (conN × List ast_t))) (tids : List type_ident),
     ALL_DISTINCT tids ∧
     DISJOINT (LIST_TO_SET tids) (LIST_TO_SET prim_type_nums) ∧
     LENGTH tds = LENGTH tids ∧
     check_ctor_tenv tenvT tds ∧
     tenv_abbrev_ok tenvT
     →
     ctMap_ok
       (FEMPTY |++
         REVERSE (type_def_to_ctMap tenvT next tds tids)) := by
  sorry

/- HOL4:
   Theorem nsLookup_add_tenvE1:
      !tenvE tenvV n tvs t tvs2.
       check_freevars tvs2 [] t ∧
       tveLookup n tvs tenvE = SOME (tvs2,t) ⇒
       nsLookup (add_tenvE tenvE tenvV) (Short n) = SOME (tvs2,t) -/
theorem nsLookup_add_tenvE1 :
    ∀ (tenvE : tenv_val_exp) (tenvV : tenv_val) (n : varN) (tvs : Nat) (t : Ty) (tvs2 : Nat),
     check_freevars tvs2 [] t ∧
     tveLookup n tvs tenvE = some (tvs2, t) →
     nsLookup (add_tenvE tenvE tenvV) (.Short n) = some (tvs2, t) := by
  sorry

/- HOL4:
   Theorem nsLookup_add_tenvE2:
      !tenvE tenvV n tvs t tvs2.
       tveLookup n tvs tenvE = NONE ∧
       nsLookup tenvV (Short n) = SOME (tvs2,t) ⇒
       nsLookup (add_tenvE tenvE tenvV) (Short n) = SOME (tvs2,t) -/
theorem nsLookup_add_tenvE2 :
    ∀ (tenvE : tenv_val_exp) (tenvV : tenv_val) (n : varN) (tvs : Nat) (t : Ty) (tvs2 : Nat),
     tveLookup n tvs tenvE = none ∧
     nsLookup tenvV (.Short n) = some (tvs2, t) →
     nsLookup (add_tenvE tenvE tenvV) (.Short n) = some (tvs2, t) := by
  sorry

/- HOL4:
   Theorem nsLookup_add_tenvE3:
      !tenvE tenvV n t tvs2 mn.
       nsLookup tenvV (Long mn n) = SOME (tvs2,t) ⇒
       nsLookup (add_tenvE tenvE tenvV) (Long mn n) = SOME (tvs2,t) -/
theorem nsLookup_add_tenvE3 :
    ∀ (tenvE : tenv_val_exp) (tenvV : tenv_val) (n : Ident modN varN) (t : Ty) (tvs2 : Nat)
      (mn : modN),
     nsLookup tenvV (.Long mn n) = some (tvs2, t) →
     nsLookup (add_tenvE tenvE tenvV) (.Long mn n) = some (tvs2, t) := by
  sorry

/- HOL4:
   Theorem add_tenvE_bvl:
      !n bindings tenvE tenvV.
       add_tenvE (bind_var_list n bindings tenvE) tenvV =
       nsBindList (MAP (\(x,t). (x, (n, t))) bindings) (add_tenvE tenvE tenvV) -/
theorem add_tenvE_bvl :
    ∀ (n : Nat) (bindings : List (varN × Ty)) (tenvE : tenv_val_exp) (tenvV : tenv_val),
     add_tenvE (bind_var_list n bindings tenvE) tenvV =
     nsBindList (MAP (fun p => (p.1, (n, p.2))) bindings) (add_tenvE tenvE tenvV) := by
  sorry

/- HOL4:
   Theorem type_v_freevars:
    !tvs tenvC tenvS v t. type_v tvs tenvC tenvS v t ⇒ check_freevars tvs [] t -/
theorem type_v_freevars :
    ∀ (tvs : Nat) (tenvC : ctMap) (tenvS : tenv_store) (v : Value) (t : Ty),
      type_v tvs tenvC tenvS v t → check_freevars tvs [] t := by
  sorry

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
   (`targs` and `tvs'` are free variables, hence universally quantified; the Lean name is
   `type_subst_thm` because `type_subst` is the function of `typeSystem`) -/
theorem type_subst_thm : ∀ (targs : List Ty) (tvs' : Nat),
    ∀ (tvs : Nat) (ctMap : ctMap) (tenvS : tenv_store) (v : Value) (t : Ty),
      type_v tvs ctMap tenvS v t →
      tvs = LENGTH targs ∧
      ctMap_ok ctMap ∧
      EVERY (check_freevars tvs' []) targs ∧
      check_freevars (LENGTH targs) [] t
      →
      type_v tvs' ctMap tenvS v (deBruijn_subst 0 targs t) := by
  sorry

/- HOL4:
   Theorem check_ctor_tenv_ok:
    !tenvT tds tis.
    LENGTH tds = LENGTH tis ∧
    check_ctor_tenv tenvT tds ∧
    tenv_abbrev_ok tenvT
    ⇒
    tenv_ctor_ok (build_ctor_tenv tenvT tds tis) -/
theorem check_ctor_tenv_ok :
    ∀ (tenvT : tenv_abbrev)
      (tds : List (List tvarN × mlstring × List (conN × List ast_t))) (tis : List type_ident),
    LENGTH tds = LENGTH tis ∧
    check_ctor_tenv tenvT tds ∧
    tenv_abbrev_ok tenvT
    →
    tenv_ctor_ok (build_ctor_tenv tenvT tds tis) := by
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
    (∀ (check : Prop) (tenv : type_env) (d : dec) (tdecs : Set type_ident)
       (new_tenv : type_env),
     type_d check tenv d tdecs new_tenv
     →
     type_d False tenv d tdecs new_tenv) ∧
    (∀ (check : Prop) (tenv : type_env) (d : List dec) (tdecs : Set type_ident)
       (new_tenv : type_env),
     type_ds check tenv d tdecs new_tenv
     →
     type_ds False tenv d tdecs new_tenv) := by
  sorry

/- HOL4:
   Theorem extend_dec_tenv_ok:
      !tenv tenv'. tenv_ok tenv ∧ tenv_ok tenv' ⇒ tenv_ok (extend_dec_tenv tenv tenv') -/
theorem extend_dec_tenv_ok :
    ∀ (tenv tenv' : type_env),
      tenv_ok tenv ∧ tenv_ok tenv' → tenv_ok (extend_dec_tenv tenv tenv') := by
  sorry

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
     tenv_ok tenv') := by
  sorry

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
     tenv_ok (extend_dec_tenv tenv' tenv) := by
  sorry

/- HOL4:
   Theorem type_ds_empty[simp]:
     !check tenv decls r.
     type_ds check tenv [] decls r ⇔
     decls = {} ∧ r = <| v := nsEmpty; c:= nsEmpty; t := nsEmpty |> -/
theorem type_ds_empty :
    ∀ (check : Prop) (tenv : type_env) (decls : Set type_ident) (r : type_env),
     type_ds check tenv [] decls r ↔
     decls = ∅ ∧ r = ⟨nsEmpty, nsEmpty, nsEmpty⟩ := by
  sorry

/- HOL4:
   Theorem type_ds_sing[simp]:
     !check tenv d decls r.
     type_ds check tenv [d] decls r ⇔ type_d check tenv d decls r -/
theorem type_ds_sing :
    ∀ (check : Prop) (tenv : type_env) (d : dec) (decls : Set type_ident) (r : type_env),
     type_ds check tenv [d] decls r ↔ type_d check tenv d decls r := by
  sorry

end
