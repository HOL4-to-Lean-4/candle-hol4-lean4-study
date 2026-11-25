import CmlTS.Ast
import CmlTS.Namespace
import CmlTS.TypeSystem
import CmlTS.TypeSoundInvariants
import CmlTS.NamespaceProps
import CmlTS.SemanticPrimitivesProps
import CmlTS.Proofs.TypeAux

/-
HOL4 theory `typeSysProps` (typeSysPropsScript.sml).
-/

namespace CmlTS

noncomputable section

open scoped Classical

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
  ∀ p e, (p, e) ∈ pes →
    ∃ bindings,
      ALL_DISTINCT (pat_bindings p []) ∧
      type_p tvs tenv p t1 bindings ∧
      type_e tenv (bind_var_list tvs' bindings tenvE) e t2

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
def deBruijn_subst_tenvE (targs : List typ) : tenv_val_exp → tenv_val_exp
  | tenv_val_exp.Empty => tenv_val_exp.Empty
  | Bind_tvar tvs env => Bind_tvar tvs (deBruijn_subst_tenvE targs env)
  | Bind_name x tvs t env =>
    Bind_name x tvs
      (deBruijn_subst (tvs + num_tvs env) (targs.map (deBruijn_inc 0 (tvs + num_tvs env))) t)
      (deBruijn_subst_tenvE targs env)

/- HOL4:
Definition db_merge_def:
(db_merge Empty e = e) ∧
(db_merge (Bind_tvar tvs e1) e2 = Bind_tvar tvs (db_merge e1 e2)) ∧
(db_merge (Bind_name x tvs t e1) e2 = Bind_name x tvs t (db_merge e1 e2))
End -/
def db_merge : tenv_val_exp → tenv_val_exp → tenv_val_exp
  | tenv_val_exp.Empty, e => e
  | Bind_tvar tvs e1, e2 => Bind_tvar tvs (db_merge e1 e2)
  | Bind_name x tvs t e1, e2 => Bind_name x tvs t (db_merge e1 e2)

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
(unspecified on lists of different lengths) -/
def type_def_to_ctMap {α β γ : Type}
    (tenvT : Namespace mlstring mlstring (List mlstring × typ)) :
    Nat → List (α × β × List (conN × List ast_t)) → List γ →
      List (stamp × (α × List typ × γ))
  | _, [], [] => []
  | next_stamp, (tvs, _, ctors) :: tds, id :: ids =>
    type_def_to_ctMap tenvT (next_stamp + 1) tds ids ++
      (ctors.map (fun (cn, ts) =>
        (TypeStamp cn next_stamp, (tvs, ts.map (type_name_subst tenvT), id)))).reverse
  | _, _, _ => ARB

set_option linter.unusedVariables false

/-! Theorems, in HOL4 source order. -/

/- HOL4:
Theorem unchanged_tenv[simp]:
  !(tenv : type_env).
  <| v := tenv.v; c := tenv.c; t := tenv.t |> = tenv -/
theorem unchanged_tenv :
    ∀ (tenv : type_env), ({ v := tenv.v, c := tenv.c, t := tenv.t } : type_env) = tenv := by
  intro tenv; rfl

/- HOL4:
Theorem extend_dec_tenv_assoc[simp]:
   !tenv1 tenv2 tenv3.
    extend_dec_tenv tenv1 (extend_dec_tenv tenv2 tenv3)
    =
    extend_dec_tenv (extend_dec_tenv tenv1 tenv2) tenv3 -/
theorem extend_dec_tenv_assoc :
    ∀ (tenv1 tenv2 tenv3 : type_env),
      extend_dec_tenv tenv1 (extend_dec_tenv tenv2 tenv3) =
      extend_dec_tenv (extend_dec_tenv tenv1 tenv2) tenv3 := by
  intro tenv1 tenv2 tenv3
  simp [extend_dec_tenv, nsAppend_assoc]

/- HOL4:
Theorem tenv_val_ok_nsEmpty[simp]:
   tenv_val_ok nsEmpty -/
theorem tenv_val_ok_nsEmpty {m n : Type} :
    tenv_val_ok (nsEmpty : Namespace m n (Nat × typ)) := by
  exact nsAll_nsEmpty _

/- HOL4:
Theorem tenv_ctor_ok_nsEmpty[simp]:
   tenv_ctor_ok nsEmpty -/
theorem tenv_ctor_ok_nsEmpty {m n α : Type} :
    tenv_ctor_ok (nsEmpty : Namespace m n (List mlstring × List typ × α)) := by
  exact nsAll_nsEmpty _

/- HOL4:
Theorem tenv_abbrev_ok_nsEmpty[simp]:
   tenv_abbrev_ok nsEmpty -/
theorem tenv_abbrev_ok_nsEmpty {m n : Type} :
    tenv_abbrev_ok (nsEmpty : Namespace m n (List mlstring × typ)) := by
  exact nsAll_nsEmpty _

/- HOL4:
Theorem tenv_ok_empty[simp]:
   tenv_ok <| v := nsEmpty; c := nsEmpty; t := nsEmpty |> -/
theorem tenv_ok_empty :
    tenv_ok { v := nsEmpty, c := nsEmpty, t := nsEmpty } := by
  exact ⟨tenv_val_ok_nsEmpty, tenv_ctor_ok_nsEmpty, tenv_abbrev_ok_nsEmpty⟩

/- HOL4:
Theorem check_freevars_add:
 (!tvs tvs' t. check_freevars tvs tvs' t ⇒
  !tvs''. tvs'' ≥ tvs ⇒ check_freevars tvs'' tvs' t) -/
theorem check_freevars_add :
    ∀ (tvs : Nat) (tvs' : List mlstring) (t : typ), check_freevars tvs tvs' t →
      ∀ (tvs'' : Nat), tvs'' ≥ tvs → check_freevars tvs'' tvs' t := by
  intro tvs tvs' t h tvs'' hge
  induction t using Aux.typ_ind with
  | tvar tv => exact Aux.cf_var.2 (Aux.cf_var.1 h)
  | db n => have := Aux.cf_db.1 h; exact Aux.cf_db.2 (by omega)
  | app ts ti ih => exact Aux.cf_app.2 fun t ht => ih t ht (Aux.cf_app.1 h t ht)

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
      EVERY (check_freevars dbmax tvs') ts →
      check_freevars dbmax tvs' (type_subst (alist_to_fmap (tvs.zip ts)) t) := by
  rintro dbmax tvs t tvs' ts ⟨hl, h, hts⟩
  rw [EVERY_iff_forall] at hts
  induction t using Aux.typ_ind with
  | tvar tv =>
    obtain ⟨x, hx, hm⟩ := Aux.ALOOKUP_zip_some hl (Aux.cf_var.1 h)
    rw [Aux.ts_var_zip hx]
    exact hts x hm
  | db n => rw [type_subst]; exact Aux.cf_db.2 (Aux.cf_db.1 h)
  | app ts' ti ih =>
    rw [Aux.ts_app, Aux.cf_app]
    intro t ht
    obtain ⟨t', ht', rfl⟩ := List.mem_map.1 ht
    exact ih t' ht' (Aux.cf_app.1 h t' ht')

/- HOL4:
Theorem deBruijn_inc0:
 (!t sk. deBruijn_inc sk 0 t = t) ∧
 (!ts sk. MAP (deBruijn_inc sk 0) ts = ts) -/
theorem deBruijn_inc0 :
    (∀ (t : typ) (sk : Nat), deBruijn_inc sk 0 t = t) ∧
    (∀ (ts : List typ) (sk : Nat), ts.map (deBruijn_inc sk 0) = ts) := by
  have key : ∀ (t : typ) (sk : Nat), deBruijn_inc sk 0 t = t := by
    intro t sk
    induction t using Aux.typ_ind with
    | tvar tv => exact Aux.inc_var
    | db n => rw [Aux.inc_db]; split <;> rfl
    | app ts ti ih =>
      rw [Aux.inc_app]
      congr 1
      exact (List.map_congr_left ih).trans (List.map_id ts)
  exact ⟨key, fun ts sk => (List.map_congr_left fun t _ => key t sk).trans (List.map_id ts)⟩

/- HOL4:
Theorem deBruijn_inc_deBruijn_inc:
 !sk i2 t i1.
  deBruijn_inc sk i1 (deBruijn_inc sk i2 t) = deBruijn_inc sk (i1 + i2) t -/
theorem deBruijn_inc_deBruijn_inc :
    ∀ (sk i2 : Nat) (t : typ) (i1 : Nat),
      deBruijn_inc sk i1 (deBruijn_inc sk i2 t) = deBruijn_inc sk (i1 + i2) t := by
  intro sk i2 t i1
  induction t using Aux.typ_ind with
  | tvar tv => rw [Aux.inc_var, Aux.inc_var, Aux.inc_var]
  | db n =>
    by_cases h : n < sk
    · rw [Aux.inc_db_lt h, Aux.inc_db_lt h, Aux.inc_db_lt h]
    · rw [Aux.inc_db_ge (by omega), Aux.inc_db_ge (by omega), Aux.inc_db_ge (by omega)]
      congr 1; omega
  | app ts ti ih =>
    rw [Aux.inc_app, Aux.inc_app, Aux.inc_app, List.map_map]
    congr 1
    exact List.map_congr_left ih

/- HOL4:
Theorem deBuijn_inc_lem1[local]:
  !sk i2 t i1.
  deBruijn_inc sk i1 (deBruijn_inc 0 (sk + i2) t) = deBruijn_inc 0 (i1 + (sk + i2)) t -/
theorem deBuijn_inc_lem1 :
    ∀ (sk i2 : Nat) (t : typ) (i1 : Nat),
      deBruijn_inc sk i1 (deBruijn_inc 0 (sk + i2) t) = deBruijn_inc 0 (i1 + (sk + i2)) t := by
  intro sk i2 t i1
  induction t using Aux.typ_ind with
  | tvar tv => rw [Aux.inc_var, Aux.inc_var, Aux.inc_var]
  | db n =>
    rw [Aux.inc_db_ge (by omega), Aux.inc_db_ge (by omega), Aux.inc_db_ge (by omega)]
    congr 1; omega
  | app ts ti ih =>
    rw [Aux.inc_app, Aux.inc_app, Aux.inc_app, List.map_map]
    congr 1
    exact List.map_congr_left ih

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
      s = alist_to_fmap (tvs.zip ts) ∧
      check_freevars 0 tvs t →
      deBruijn_inc sk inc (type_subst s t) =
        type_subst (alist_to_fmap (tvs.zip (ts.map (fun t => deBruijn_inc sk inc t)))) t := by
  rintro s t ts tvs inc sk ⟨hl, rfl, h⟩
  exact Aux.type_subst_comm (deBruijn_inc sk inc) (fun _ _ => Aux.inc_app) hl t h

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
      (ts'.map (type_subst (alist_to_fmap (tvs.zip ts)))).map (deBruijn_inc sk inc) =
        ts'.map
          (type_subst (alist_to_fmap (tvs.zip (ts.map (fun t => deBruijn_inc sk inc t))))) := by
  rintro ts' ts tvs inc sk ⟨hl, h⟩
  rw [EVERY_iff_forall] at h
  rw [List.map_map]
  exact List.map_congr_left fun t ht =>
    Aux.type_subst_comm (deBruijn_inc sk inc) (fun _ _ => Aux.inc_app) hl t (h t ht)

/- HOL4:
Theorem check_freevars_deBruijn_inc[local]:
  !tvs tvs' t. check_freevars tvs tvs' t ⇒
  !n n'. check_freevars (n+tvs) tvs' (deBruijn_inc n' n t) -/
theorem check_freevars_deBruijn_inc :
    ∀ (tvs : Nat) (tvs' : List mlstring) (t : typ), check_freevars tvs tvs' t →
      ∀ (n n' : Nat), check_freevars (n + tvs) tvs' (deBruijn_inc n' n t) := by
  intro tvs tvs' t h n n'
  induction t using Aux.typ_ind with
  | tvar tv => rw [Aux.inc_var]; exact Aux.cf_var.2 (Aux.cf_var.1 h)
  | db m =>
    have := Aux.cf_db.1 h
    rw [Aux.inc_db]
    split <;> exact Aux.cf_db.2 (by omega)
  | app ts ti ih =>
    rw [Aux.inc_app, Aux.cf_app]
    intro t ht
    obtain ⟨t', ht', rfl⟩ := List.mem_map.1 ht
    exact ih t' ht' (Aux.cf_app.1 h t' ht')

/- HOL4:
Theorem nil_deBruijn_inc:
 ∀skip tvs t.
  (check_freevars skip [] t ∨ check_freevars skip [] (deBruijn_inc skip tvs t))
  ⇒
  (deBruijn_inc skip tvs t = t) -/
theorem nil_deBruijn_inc :
    ∀ (skip tvs : Nat) (t : typ),
      (check_freevars skip [] t ∨ check_freevars skip [] (deBruijn_inc skip tvs t)) →
      deBruijn_inc skip tvs t = t := by
  intro skip tvs t h
  induction t using Aux.typ_ind with
  | tvar tv => exact Aux.inc_var
  | db n =>
    by_cases hn : n < skip
    · exact Aux.inc_db_lt hn
    · rw [Aux.inc_db_ge (by omega), Aux.cf_db, Aux.cf_db] at h
      omega
  | app ts ti ih =>
    rw [Aux.inc_app]
    congr 1
    refine (List.map_congr_left fun t ht => ih t ht ?_).trans (List.map_id ts)
    rcases h with h | h
    · exact Or.inl (Aux.cf_app.1 h t ht)
    · rw [Aux.inc_app] at h
      exact Or.inr (Aux.cf_app.1 h _ (List.mem_map.2 ⟨t, ht, rfl⟩))

/- HOL4:
Theorem deBruijn_subst_check_freevars:
 !tvs tvs' t ts n.
  check_freevars tvs tvs' t ∧
  EVERY (check_freevars tvs tvs') ts
  ⇒
  check_freevars tvs tvs' (deBruijn_subst 0 ts t) -/
theorem deBruijn_subst_check_freevars {α : Type} :
    ∀ (tvs : Nat) (tvs' : List mlstring) (t : typ) (ts : List typ) (n : α),
      check_freevars tvs tvs' t ∧
      EVERY (check_freevars tvs tvs') ts →
      check_freevars tvs tvs' (deBruijn_subst 0 ts t) := by
  rintro tvs tvs' t ts _ ⟨h, hts⟩
  rw [EVERY_iff_forall] at hts
  induction t using Aux.typ_ind with
  | tvar tv => rw [Aux.sub_var]; exact h
  | db n =>
    have := Aux.cf_db.1 h
    by_cases hn : n < ts.length
    · rw [Aux.sub_db_mid (by omega) (by omega)]
      exact hts _ (Aux.EL_mem (by omega))
    · rw [Aux.sub_db_ge (by omega)]
      exact Aux.cf_db.2 (by omega)
  | app ts' ti ih =>
    rw [Aux.sub_app, Aux.cf_app]
    intro t ht
    obtain ⟨t', ht', rfl⟩ := List.mem_map.1 ht
    exact ih t' ht' (Aux.cf_app.1 h t' ht')

/- HOL4:
Theorem deBruijn_subst_check_freevars2:
 !tvs tvs' t ts n tvs''.
  check_freevars (LENGTH ts) tvs' t ∧
  EVERY (check_freevars tvs tvs') ts
  ⇒
  check_freevars tvs tvs' (deBruijn_subst 0 ts t) -/
theorem deBruijn_subst_check_freevars2 {α β : Type} :
    ∀ (tvs : Nat) (tvs' : List mlstring) (t : typ) (ts : List typ) (n : α) (tvs'' : β),
      check_freevars ts.length tvs' t ∧
      EVERY (check_freevars tvs tvs') ts →
      check_freevars tvs tvs' (deBruijn_subst 0 ts t) := by
  rintro tvs tvs' t ts _ _ ⟨h, hts⟩
  rw [EVERY_iff_forall] at hts
  induction t using Aux.typ_ind with
  | tvar tv => rw [Aux.sub_var]; exact Aux.cf_var.2 (Aux.cf_var.1 h)
  | db n =>
    have := Aux.cf_db.1 h
    rw [Aux.sub_db_mid (by omega) (by omega)]
    exact hts _ (Aux.EL_mem (by omega))
  | app ts' ti ih =>
    rw [Aux.sub_app, Aux.cf_app]
    intro t ht
    obtain ⟨t', ht', rfl⟩ := List.mem_map.1 ht
    exact ih t' ht' (Aux.cf_app.1 h t' ht')

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
        EVERY (check_freevars (tvs1 + tvs') tvs2) targs →
        check_freevars (tvs1 + tvs') tvs2
          (deBruijn_subst 0 targs (deBruijn_inc targs.length tvs1 t)) := by
  rintro tvs tvs2 t h tvs' targs tvs1 ⟨rfl, hts⟩
  rw [EVERY_iff_forall] at hts
  induction t using Aux.typ_ind with
  | tvar tv => rw [Aux.inc_var, Aux.sub_var]; exact Aux.cf_var.2 (Aux.cf_var.1 h)
  | db n =>
    have := Aux.cf_db.1 h
    by_cases hn : n < targs.length
    · rw [Aux.inc_db_lt hn, Aux.sub_db_mid (by omega) (by omega)]
      exact hts _ (Aux.EL_mem (by omega))
    · rw [Aux.inc_db_ge (by omega), Aux.sub_db_ge (by omega)]
      exact Aux.cf_db.2 (by omega)
  | app ts' ti ih =>
    rw [Aux.inc_app, Aux.sub_app, Aux.cf_app, List.map_map]
    intro t ht
    obtain ⟨t', ht', rfl⟩ := List.mem_map.1 ht
    exact ih t' ht' (Aux.cf_app.1 h t' ht')

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
        EVERY (check_freevars (tvs1 + tvs') tvs2) targs →
        check_freevars (tvs1 + tvs') tvs2 (deBruijn_subst 0 targs t) := by
  rintro tvs tvs2 t h tvs' targs tvs1 ⟨rfl, hts⟩
  rw [EVERY_iff_forall] at hts
  induction t using Aux.typ_ind with
  | tvar tv => rw [Aux.sub_var]; exact Aux.cf_var.2 (Aux.cf_var.1 h)
  | db n =>
    have := Aux.cf_db.1 h
    by_cases hn : n < targs.length
    · rw [Aux.sub_db_mid (by omega) (by omega)]
      exact hts _ (Aux.EL_mem (by omega))
    · rw [Aux.sub_db_ge (by omega)]
      exact Aux.cf_db.2 (by omega)
  | app ts' ti ih =>
    rw [Aux.sub_app, Aux.cf_app]
    intro t ht
    obtain ⟨t', ht', rfl⟩ := List.mem_map.1 ht
    exact ih t' ht' (Aux.cf_app.1 h t' ht')

/- HOL4:
Theorem type_subst_deBruijn_subst_single[local]:
  !s t tvs tvs' ts ts' inc.
  (LENGTH tvs = LENGTH ts) ∧
  check_freevars 0 tvs t ∧
  (s = alist_to_fmap (ZIP (tvs,ts))) ⇒
  (deBruijn_subst inc ts' (type_subst (alist_to_fmap (ZIP (tvs,ts))) t) =
   type_subst (alist_to_fmap (ZIP (tvs,MAP (\t. deBruijn_subst inc ts' t) ts))) t) -/
theorem type_subst_deBruijn_subst_single {α : Type} :
    ∀ (s : fmap mlstring typ) (t : typ) (tvs : List mlstring) (tvs' : α) (ts ts' : List typ)
      (inc : Nat),
      tvs.length = ts.length ∧
      check_freevars 0 tvs t ∧
      s = alist_to_fmap (tvs.zip ts) →
      deBruijn_subst inc ts' (type_subst (alist_to_fmap (tvs.zip ts)) t) =
        type_subst (alist_to_fmap (tvs.zip (ts.map (fun t => deBruijn_subst inc ts' t)))) t := by
  rintro s t tvs _ ts ts' inc ⟨hl, h, rfl⟩
  exact Aux.type_subst_comm (deBruijn_subst inc ts') (fun _ _ => Aux.sub_app) hl t h

/- HOL4:
Theorem type_subst_deBruijn_subst_list:
 !t tvs tvs' ts ts' ts'' inc.
  (LENGTH tvs = LENGTH ts) ∧
  EVERY (check_freevars 0 tvs) ts'' ⇒
  (MAP (deBruijn_subst inc ts') (MAP (type_subst (alist_to_fmap (ZIP (tvs,ts)))) ts'') =
   MAP (type_subst (alist_to_fmap (ZIP (tvs,MAP (\t. deBruijn_subst inc ts' t) ts)))) ts'') -/
theorem type_subst_deBruijn_subst_list {α β : Type} :
    ∀ (t : α) (tvs : List mlstring) (tvs' : β) (ts ts' ts'' : List typ) (inc : Nat),
      tvs.length = ts.length ∧
      EVERY (check_freevars 0 tvs) ts'' →
      (ts''.map (type_subst (alist_to_fmap (tvs.zip ts)))).map (deBruijn_subst inc ts') =
        ts''.map
          (type_subst (alist_to_fmap (tvs.zip (ts.map (fun t => deBruijn_subst inc ts' t))))) := by
  rintro _ tvs _ ts ts' ts'' inc ⟨hl, h⟩
  rw [EVERY_iff_forall] at h
  rw [List.map_map]
  exact List.map_congr_left fun t ht =>
    Aux.type_subst_comm (deBruijn_subst inc ts') (fun _ _ => Aux.sub_app) hl t (h t ht)

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
        EVERY (check_freevars tvs tvs') targs →
        check_freevars (n1 + tvs) tvs'
          (deBruijn_subst n1 (targs.map (deBruijn_inc 0 n1)) t) := by
  rintro l tvs' t h targs n1 tvs ⟨rfl, hts⟩
  rw [EVERY_iff_forall] at hts
  induction t using Aux.typ_ind with
  | tvar tv => rw [Aux.sub_var]; exact Aux.cf_var.2 (Aux.cf_var.1 h)
  | db n =>
    have := Aux.cf_db.1 h
    by_cases hn : n < n1
    · rw [Aux.sub_db_lt hn]
      exact Aux.cf_db.2 (by omega)
    · rw [Aux.sub_db_mid (by omega) (by simp; omega), Aux.EL_map (by omega)]
      exact check_freevars_deBruijn_inc _ _ _ (hts _ (Aux.EL_mem (by omega))) _ _
  | app ts' ti ih =>
    rw [Aux.sub_app, Aux.cf_app]
    intro t ht
    obtain ⟨t', ht', rfl⟩ := List.mem_map.1 ht
    exact ih t' ht' (Aux.cf_app.1 h t' ht')

/- HOL4:
Theorem nil_deBruijn_subst:
 ∀skip tvs t. check_freevars skip [] t ⇒ (deBruijn_subst skip tvs t = t) -/
theorem nil_deBruijn_subst :
    ∀ (skip : Nat) (tvs : List typ) (t : typ),
      check_freevars skip [] t → deBruijn_subst skip tvs t = t := by
  intro skip tvs t h
  induction t using Aux.typ_ind with
  | tvar tv => exact Aux.sub_var
  | db n => exact Aux.sub_db_lt (Aux.cf_db.1 h)
  | app ts ti ih =>
    rw [Aux.sub_app]
    congr 1
    exact (List.map_congr_left fun t ht => ih t ht (Aux.cf_app.1 h t ht)).trans (List.map_id ts)

/- HOL4:
Theorem deBruijn_subst2:
 (!t sk targs targs' tvs'.
  check_freevars (LENGTH targs) [] t ⇒
  (deBruijn_subst sk (MAP (deBruijn_inc 0 sk) targs') (deBruijn_subst 0 targs t) =
   deBruijn_subst 0 (MAP (deBruijn_subst sk (MAP (deBruijn_inc 0 sk) targs')) targs) t)) ∧
 (!ts sk targs targs' tvs'.
  EVERY (check_freevars (LENGTH targs) []) ts ⇒
  (MAP (deBruijn_subst sk (MAP (deBruijn_inc 0 sk) targs')) (MAP (deBruijn_subst 0 targs) ts) =
  (MAP (deBruijn_subst 0 (MAP (deBruijn_subst sk (MAP (deBruijn_inc 0 sk) targs')) targs)) ts))) -/
theorem deBruijn_subst2 {α β : Type} :
    (∀ (t : typ) (sk : Nat) (targs targs' : List typ) (tvs' : α),
      check_freevars targs.length [] t →
      deBruijn_subst sk (targs'.map (deBruijn_inc 0 sk)) (deBruijn_subst 0 targs t) =
        deBruijn_subst 0
          (targs.map (deBruijn_subst sk (targs'.map (deBruijn_inc 0 sk)))) t) ∧
    (∀ (ts : List typ) (sk : Nat) (targs targs' : List typ) (tvs' : β),
      EVERY (check_freevars targs.length []) ts →
      (ts.map (deBruijn_subst 0 targs)).map
          (deBruijn_subst sk (targs'.map (deBruijn_inc 0 sk))) =
        ts.map (deBruijn_subst 0
          (targs.map (deBruijn_subst sk (targs'.map (deBruijn_inc 0 sk)))))) := by
  have key : ∀ (t : typ) (sk : Nat) (targs targs' : List typ),
      check_freevars targs.length [] t →
      deBruijn_subst sk (targs'.map (deBruijn_inc 0 sk)) (deBruijn_subst 0 targs t) =
        deBruijn_subst 0
          (targs.map (deBruijn_subst sk (targs'.map (deBruijn_inc 0 sk)))) t := by
    intro t sk targs targs' h
    induction t using Aux.typ_ind with
    | tvar tv => exact absurd (Aux.cf_var.1 h) (by simp)
    | db n =>
      have := Aux.cf_db.1 h
      rw [Aux.sub_db_mid (by omega) (by omega), Aux.sub_db_mid (by omega) (by simp; omega),
        Aux.EL_map (by omega)]
    | app ts ti ih =>
      rw [Aux.sub_app, Aux.sub_app, Aux.sub_app, List.map_map]
      congr 1
      exact List.map_congr_left fun t ht => ih t ht (Aux.cf_app.1 h t ht)
  refine ⟨fun t sk targs targs' _ h => key t sk targs targs' h,
    fun ts sk targs targs' _ h => ?_⟩
  rw [EVERY_iff_forall] at h
  rw [List.map_map]
  exact List.map_congr_left fun t ht => key t sk targs targs' (h t ht)

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
        EVERY (check_freevars tvs' tvs2) targs →
        check_freevars (n + tvs') tvs2
          (deBruijn_subst n (targs.map (deBruijn_inc 0 n)) t) := by
  intro tvs tvs2 t h tvs' targs n hh
  exact check_freevars_lem tvs tvs2 t h targs n tvs' hh

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
  have key : ∀ (t : typ) (n inc n' : Nat) (targs : List typ),
      deBruijn_inc n inc
          (deBruijn_subst (n + n') (targs.map (deBruijn_inc 0 (n + n'))) t) =
        deBruijn_subst (n + inc + n') (targs.map (deBruijn_inc 0 (n + inc + n')))
          (deBruijn_inc n inc t) := by
    intro t n inc n' targs
    induction t using Aux.typ_ind with
    | tvar tv => rw [Aux.sub_var, Aux.inc_var, Aux.sub_var]
    | db m =>
      by_cases h1 : m < n + n'
      · rw [Aux.sub_db_lt h1]
        by_cases h2 : m < n
        · rw [Aux.inc_db_lt h2, Aux.sub_db_lt (by omega)]
        · rw [Aux.inc_db_ge (by omega), Aux.sub_db_lt (by omega)]
      · by_cases h2 : m < targs.length + (n + n')
        · rw [Aux.sub_db_mid (by omega) (by simpa using h2), Aux.EL_map (by omega),
            deBuijn_inc_lem1, Aux.inc_db_ge (by omega),
            Aux.sub_db_mid (by omega) (by simp; omega), Aux.EL_map (by omega)]
          have e1 : inc + (n + n') = n + inc + n' := by omega
          have e2 : m + inc - (n + inc + n') = m - (n + n') := by omega
          rw [e1, e2]
        · rw [Aux.sub_db_ge (by simp; omega), Aux.inc_db_ge (by simp; omega),
            Aux.inc_db_ge (by omega), Aux.sub_db_ge (by simp; omega)]
          congr 1
          simp; omega
    | app ts ti ih =>
      rw [Aux.sub_app, Aux.inc_app, Aux.inc_app, Aux.sub_app, List.map_map, List.map_map]
      congr 1
      exact List.map_congr_left ih
  refine ⟨key, fun ts n inc n' targs => ?_⟩
  rw [List.map_map, List.map_map]
  exact List.map_congr_left fun t _ => key t n inc n' targs

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
      deBruijn_subst 0 ts (deBruijn_inc 0 (inc + ts.length) t) = deBruijn_inc 0 inc t) ∧
    (∀ (ts' ts : List typ) (inc : Nat),
      (ts'.map (deBruijn_inc 0 (inc + ts.length))).map (deBruijn_subst 0 ts) =
        ts'.map (deBruijn_inc 0 inc)) := by
  have key : ∀ (t : typ) (ts : List typ) (inc : Nat),
      deBruijn_subst 0 ts (deBruijn_inc 0 (inc + ts.length) t) = deBruijn_inc 0 inc t := by
    intro t ts inc
    induction t using Aux.typ_ind with
    | tvar tv => rw [Aux.inc_var, Aux.sub_var, Aux.inc_var]
    | db m =>
      rw [Aux.inc_db_ge (by omega), Aux.sub_db_ge (by omega), Aux.inc_db_ge (by omega)]
      congr 1; omega
    | app ts' ti ih =>
      rw [Aux.inc_app, Aux.sub_app, Aux.inc_app, List.map_map]
      congr 1
      exact List.map_congr_left ih
  refine ⟨key, fun ts' ts inc => ?_⟩
  rw [List.map_map]
  exact List.map_congr_left fun t _ => key t ts inc

/- HOL4:
Theorem type_e_subst_lem7[local]:
  (!t sk targs targs' tvs' tvs''.
  (deBruijn_subst sk (MAP (deBruijn_inc 0 sk) targs') (deBruijn_subst 0 targs t) =
   deBruijn_subst 0 (MAP (deBruijn_subst sk (MAP (deBruijn_inc 0 sk) targs')) targs)
     (deBruijn_subst (LENGTH targs + sk) (MAP (deBruijn_inc 0 (LENGTH targs + sk)) targs') t))) ∧
 (!ts sk targs targs' tvs' tvs''.
  (MAP (deBruijn_subst sk (MAP (deBruijn_inc 0 sk) targs')) (MAP (deBruijn_subst 0 targs) ts) =
  (MAP (deBruijn_subst 0 (MAP (deBruijn_subst sk (MAP (deBruijn_inc 0 sk) targs')) targs))
       (MAP (deBruijn_subst (LENGTH targs + sk) (MAP (deBruijn_inc 0 (LENGTH targs + sk)) targs')) ts)))) -/
theorem type_e_subst_lem7 {α β γ δ : Type} :
    (∀ (t : typ) (sk : Nat) (targs targs' : List typ) (tvs' : α) (tvs'' : β),
      deBruijn_subst sk (targs'.map (deBruijn_inc 0 sk)) (deBruijn_subst 0 targs t) =
        deBruijn_subst 0 (targs.map (deBruijn_subst sk (targs'.map (deBruijn_inc 0 sk))))
          (deBruijn_subst (targs.length + sk)
            (targs'.map (deBruijn_inc 0 (targs.length + sk))) t)) ∧
    (∀ (ts : List typ) (sk : Nat) (targs targs' : List typ) (tvs' : γ) (tvs'' : δ),
      (ts.map (deBruijn_subst 0 targs)).map
          (deBruijn_subst sk (targs'.map (deBruijn_inc 0 sk))) =
        (ts.map (deBruijn_subst (targs.length + sk)
            (targs'.map (deBruijn_inc 0 (targs.length + sk))))).map
          (deBruijn_subst 0
            (targs.map (deBruijn_subst sk (targs'.map (deBruijn_inc 0 sk)))))) := by
  have key : ∀ (t : typ) (sk : Nat) (targs targs' : List typ),
      deBruijn_subst sk (targs'.map (deBruijn_inc 0 sk)) (deBruijn_subst 0 targs t) =
        deBruijn_subst 0 (targs.map (deBruijn_subst sk (targs'.map (deBruijn_inc 0 sk))))
          (deBruijn_subst (targs.length + sk)
            (targs'.map (deBruijn_inc 0 (targs.length + sk))) t) := by
    intro t sk targs targs'
    induction t using Aux.typ_ind with
    | tvar tv => rw [Aux.sub_var, Aux.sub_var, Aux.sub_var, Aux.sub_var]
    | db m =>
      by_cases h1 : m < targs.length
      · rw [Aux.sub_db_mid (by omega) (by omega), Aux.sub_db_lt (by omega),
          Aux.sub_db_mid (by omega) (by simp; omega), Aux.EL_map (by omega)]
      · rw [Aux.sub_db_ge (sk := 0) (by omega)]
        by_cases h2 : m < targs.length + sk
        · rw [Aux.sub_db_lt (by omega), Aux.sub_db_lt (by omega),
            Aux.sub_db_ge (by simp; omega)]
          simp
        · by_cases h3 : m < targs'.length + (targs.length + sk)
          · rw [Aux.sub_db_mid (sk := sk) (by omega) (by simp; omega), Aux.EL_map (by omega),
              Aux.sub_db_mid (sk := targs.length + sk) (by omega) (by simp; omega),
              Aux.EL_map (by omega)]
            have hc := (subst_inc_cancel).1 (EL (m - (targs.length + sk)) targs')
              (targs.map (deBruijn_subst sk (targs'.map (deBruijn_inc 0 sk)))) sk
            rw [List.length_map, Nat.add_comm sk] at hc
            rw [hc]
            congr 2; omega
          · rw [Aux.sub_db_ge (sk := sk) (by simp; omega),
              Aux.sub_db_ge (sk := targs.length + sk) (by simp; omega),
              Aux.sub_db_ge (by simp; omega)]
            congr 1
            simp; omega
    | app ts ti ih =>
      rw [Aux.sub_app, Aux.sub_app, Aux.sub_app, Aux.sub_app, List.map_map, List.map_map]
      congr 1
      exact List.map_congr_left ih
  refine ⟨fun t sk targs targs' _ _ => key t sk targs targs', fun ts sk targs targs' _ _ => ?_⟩
  rw [List.map_map, List.map_map]
  exact List.map_congr_left fun t _ => key t sk targs targs'

/- HOL4:
Theorem deBruijn_subst_id:
 (!t n. check_freevars n [] t ⇒ (deBruijn_subst 0 (MAP Tvar_db (COUNT_LIST n)) t = t)) ∧
 (!ts n. EVERY (check_freevars n []) ts ⇒ (MAP (deBruijn_subst 0 (MAP Tvar_db (COUNT_LIST n))) ts = ts)) -/
theorem deBruijn_subst_id :
    (∀ (t : typ) (n : Nat), check_freevars n [] t →
      deBruijn_subst 0 ((COUNT_LIST n).map Tvar_db) t = t) ∧
    (∀ (ts : List typ) (n : Nat), EVERY (check_freevars n []) ts →
      ts.map (deBruijn_subst 0 ((COUNT_LIST n).map Tvar_db)) = ts) := by
  have key : ∀ (t : typ) (n : Nat), check_freevars n [] t →
      deBruijn_subst 0 ((COUNT_LIST n).map Tvar_db) t = t := by
    intro t n h
    rw [Aux.COUNT_LIST_eq]
    induction t using Aux.typ_ind with
    | tvar tv => exact Aux.sub_var
    | db m =>
      have := Aux.cf_db.1 h
      rw [Aux.sub_db_mid (by omega) (by simpa using this), Aux.EL_map (by simpa using this),
        Aux.EL_getElem (by simpa using this)]
      simp
    | app ts ti ih =>
      rw [Aux.sub_app]
      congr 1
      exact (List.map_congr_left fun t ht => ih t ht (Aux.cf_app.1 h t ht)).trans
        (List.map_id ts)
  refine ⟨key, fun ts n h => ?_⟩
  rw [EVERY_iff_forall] at h
  exact (List.map_congr_left fun t ht => key t n (h t ht)).trans (List.map_id ts)

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
      check_freevars targs.length [] t →
      check_freevars tvs [] (deBruijn_subst skip targs t) := by
  rintro skip targs t tvs ⟨rfl, h1, h2⟩
  exact deBruijn_subst_check_freevars2 tvs [] t targs () () ⟨h2, h1⟩

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
      nsLookup tenvT tn = some (tvs, t) →
      check_freevars 0 tvs t := by
  rintro tenvT tn tvs t ⟨h, hl⟩
  exact h tn (tvs, t) hl

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
      check_freevars_ast tvs t →
      check_freevars dbmax tvs (type_name_subst tenvT t) := by
  rintro tvs t dbmax tenvT ⟨hok, hn, hf⟩
  induction t using Aux.ast_ind with
  | tvar tv =>
    rw [type_name_subst]
    rw [check_freevars_ast] at hf
    exact Aux.cf_var.2 hf
  | fn t1 t2 ih1 ih2 =>
    rw [type_name_subst]
    rw [check_freevars_ast] at hf
    rw [check_type_names] at hn
    refine Aux.cf_app.2 fun t ht => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · exact ih1 hn.1 hf.1
    · exact ih2 hn.2 hf.2
  | tup ts ih =>
    rw [type_name_subst]
    rw [check_freevars_ast, EVERY_iff_forall] at hf
    rw [check_type_names, EVERY_iff_forall] at hn
    refine Aux.cf_app.2 fun t ht => ?_
    obtain ⟨t', ht', rfl⟩ := List.mem_map.1 ht
    exact ih t' ht' (hn t' ht') (hf t' ht')
  | app ts tn ih =>
    rw [type_name_subst]
    rw [check_freevars_ast, EVERY_iff_forall] at hf
    rw [check_type_names, EVERY_iff_forall] at hn
    obtain ⟨hl, hn⟩ := hn
    cases h : nsLookup tenvT tn with
    | none => rw [h] at hl; exact hl.elim
    | some p =>
      obtain ⟨tvs', t'⟩ := p
      rw [h] at hl
      refine check_freevars_subst_single dbmax tvs' t' tvs _ ⟨by simpa using hl, ?_, ?_⟩
      · exact check_freevars_add _ _ _ (tenv_abbrev_ok_lookup _ _ _ _ ⟨hok, h⟩) _ (by omega)
      · rw [Aux.EVERY_map]
        exact fun t ht => ih t ht (hn t ht) (hf t ht)

/- HOL4:
Theorem tenv_ctor_ok_merge[simp]:
   !tenvC1 tenvC2.
    tenv_ctor_ok tenvC1 ∧ tenv_ctor_ok tenvC2
    ⇒
    tenv_ctor_ok (nsAppend tenvC1 tenvC2) -/
theorem tenv_ctor_ok_merge {m n α : Type} :
    ∀ (tenvC1 tenvC2 : Namespace m n (List mlstring × List typ × α)),
      tenv_ctor_ok tenvC1 ∧ tenv_ctor_ok tenvC2 →
      tenv_ctor_ok (nsAppend tenvC1 tenvC2) := by
  rintro tenvC1 tenvC2 h
  exact nsAll_nsAppend _ _ _ h

/- HOL4:
Theorem tenv_ctor_ok_lookup:
   !tenvC cn tvs ts tn.
    tenv_ctor_ok tenvC ∧ nsLookup tenvC cn = SOME (tvs,ts,tn)
    ⇒
    EVERY (check_freevars 0 tvs) ts -/
theorem tenv_ctor_ok_lookup {m n α : Type} :
    ∀ (tenvC : Namespace m n (List mlstring × List typ × α)) (cn : ident m n)
      (tvs : List mlstring) (ts : List typ) (tn : α),
      tenv_ctor_ok tenvC ∧ nsLookup tenvC cn = some (tvs, ts, tn) →
      EVERY (check_freevars 0 tvs) ts := by
  rintro tenvC cn tvs ts tn ⟨h, hl⟩
  exact h cn (tvs, ts, tn) hl

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
(in the fifth conjunct `tvs` and `e` are unused, so of arbitrary types) -/
theorem bind_tvar_rewrites {α β : Type} :
    (∀ (tvs : Nat) (e1 e2 : tenv_val_exp),
      db_merge (bind_tvar tvs e1) e2 = bind_tvar tvs (db_merge e1 e2)) ∧
    (∀ (tvs : Nat) (e : tenv_val_exp), num_tvs (bind_tvar tvs e) = tvs + num_tvs e) ∧
    (∀ (tvs : Nat) (e : tenv_val_exp), num_tvs (Bind_tvar tvs e) = tvs + num_tvs e) ∧
    (∀ (tvs : Nat) (n : varN) (t : typ) (e : tenv_val_exp),
      num_tvs (Bind_name n tvs t e) = num_tvs e) ∧
    (∀ (tvs : α) (e : β), num_tvs tenv_val_exp.Empty = 0) ∧
    (∀ (n : mlstring) (inc tvs : Nat) (e : tenv_val_exp),
      tveLookup n inc (bind_tvar tvs e) = tveLookup n (inc + tvs) e) ∧
    (∀ (tvs : Nat) (e : tenv_val_exp),
      tenv_val_exp_ok (bind_tvar tvs e) ↔ tenv_val_exp_ok e) ∧
    (∀ (targs : List typ) (tvs : Nat) (e : tenv_val_exp),
      deBruijn_subst_tenvE targs (bind_tvar tvs e) =
        bind_tvar tvs (deBruijn_subst_tenvE targs e)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro tvs e1 e2; unfold bind_tvar; split <;> simp [db_merge]
  · intro tvs e; unfold bind_tvar; split <;> simp [num_tvs, *]
  · intro tvs e; simp [num_tvs]
  · intro tvs n t e; simp [num_tvs]
  · intro _ _; simp [num_tvs]
  · intro n inc tvs e; unfold bind_tvar; split <;> simp [tveLookup, *]
  · intro tvs e; unfold bind_tvar; split <;> simp [tenv_val_exp_ok]
  · intro targs tvs e; unfold bind_tvar; split <;> simp [deBruijn_subst_tenvE]

theorem Aux.num_tvs_bt (tvs : Nat) (e : tenv_val_exp) :
    num_tvs (bind_tvar tvs e) = tvs + num_tvs e :=
  (bind_tvar_rewrites (α := Unit) (β := Unit)).2.1 tvs e

theorem Aux.db_merge_bt (tvs : Nat) (e1 e2 : tenv_val_exp) :
    db_merge (bind_tvar tvs e1) e2 = bind_tvar tvs (db_merge e1 e2) :=
  (bind_tvar_rewrites (α := Unit) (β := Unit)).1 tvs e1 e2

theorem Aux.tveLookup_bt (n : mlstring) (inc tvs : Nat) (e : tenv_val_exp) :
    tveLookup n inc (bind_tvar tvs e) = tveLookup n (inc + tvs) e :=
  (bind_tvar_rewrites (α := Unit) (β := Unit)).2.2.2.2.2.1 n inc tvs e

theorem Aux.ok_bt (tvs : Nat) (e : tenv_val_exp) :
    tenv_val_exp_ok (bind_tvar tvs e) ↔ tenv_val_exp_ok e :=
  (bind_tvar_rewrites (α := Unit) (β := Unit)).2.2.2.2.2.2.1 tvs e

theorem Aux.subst_bt (targs : List typ) (tvs : Nat) (e : tenv_val_exp) :
    deBruijn_subst_tenvE targs (bind_tvar tvs e) =
      bind_tvar tvs (deBruijn_subst_tenvE targs e) :=
  (bind_tvar_rewrites (α := Unit) (β := Unit)).2.2.2.2.2.2.2 targs tvs e

/- HOL4:
Theorem bind_tvar0[simp]:
 !x. bind_tvar 0 x = x -/
theorem bind_tvar0 :
    ∀ (x : tenv_val_exp), bind_tvar 0 x = x := by
  intro x; simp [bind_tvar]

/- HOL4:
Theorem tveLookup_subst_none:
 !n inc e.
 tveLookup n inc (deBruijn_subst_tenvE targs e) = NONE ⇔
 tveLookup n inc e = NONE -/
theorem tveLookup_subst_none (targs : List typ) :
    ∀ (n : mlstring) (inc : Nat) (e : tenv_val_exp),
      tveLookup n inc (deBruijn_subst_tenvE targs e) = none ↔
      tveLookup n inc e = none := by
  intro n inc e
  induction e generalizing inc with
  | Empty => simp [deBruijn_subst_tenvE]
  | Bind_tvar tvs e ih => simp only [deBruijn_subst_tenvE, tveLookup]; exact ih _
  | Bind_name x tvs t e ih =>
    simp only [deBruijn_subst_tenvE, tveLookup]
    split
    · simp
    · exact ih _

/- HOL4:
Theorem tveLookup_db_merge_none:
 !n inc e1 e2.
  tveLookup n inc (db_merge e1 e2) = NONE
  ⇔
  tveLookup n inc e1 = NONE ∧ tveLookup n (num_tvs e1 + inc) e2 = NONE -/
theorem tveLookup_db_merge_none :
    ∀ (n : mlstring) (inc : Nat) (e1 e2 : tenv_val_exp),
      tveLookup n inc (db_merge e1 e2) = none ↔
      (tveLookup n inc e1 = none ∧ tveLookup n (num_tvs e1 + inc) e2 = none) := by
  intro n inc e1 e2
  induction e1 generalizing inc with
  | Empty => simp [db_merge, tveLookup, num_tvs]
  | Bind_tvar tvs e ih =>
    simp only [db_merge, tveLookup, num_tvs]
    rw [ih]
    have : num_tvs e + (inc + tvs) = tvs + num_tvs e + inc := by omega
    rw [this]
  | Bind_name x tvs t e ih =>
    simp only [db_merge, tveLookup, num_tvs]
    split
    · simp
    · exact ih _

/- HOL4:
Theorem tveLookup_inc_none:
 !n inc e.
  tveLookup n inc e = NONE
  ⇔
  tveLookup n 0 e = NONE -/
theorem tveLookup_inc_none :
    ∀ (n : mlstring) (inc : Nat) (e : tenv_val_exp),
      tveLookup n inc e = none ↔ tveLookup n 0 e = none := by
  intro n inc e
  have key : ∀ i j, tveLookup n i e = none → tveLookup n j e = none := by
    induction e with
    | Empty => simp [tveLookup]
    | Bind_tvar tvs e ih => simp only [tveLookup]; exact fun i j => ih _ _
    | Bind_name x tvs t e ih =>
      simp only [tveLookup]
      intro i j
      split
      · simp
      · exact ih _ _
  exact ⟨key _ _, key _ _⟩

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
      tveLookup n tvs tenvE = some (tvs', t) →
      check_freevars tvs' [] t := by
  rintro n tvs tenvE tvs' t ⟨hok, hn, hl⟩
  induction tenvE generalizing tvs with
  | Empty => simp [tveLookup] at hl
  | Bind_tvar k e ih =>
    simp only [tveLookup] at hl
    simp only [num_tvs] at hn
    exact ih _ hok (by omega) hl
  | Bind_name x k t0 e ih =>
    simp only [tveLookup] at hl
    simp only [num_tvs] at hn
    split at hl
    · cases hl
      have h := hok.1
      rw [hn, Nat.add_zero] at h
      rw [nil_deBruijn_inc _ _ _ (Or.inl h)]
      exact h
    · exact ih _ hok.2 hn hl

/- HOL4:
Theorem bind_var_list_append:
 !n te1 te2 te3.
  bind_var_list n (te1++te2) te3 = bind_var_list n te1 (bind_var_list n te2 te3) -/
theorem bind_var_list_append :
    ∀ (n : Nat) (te1 te2 : List (mlstring × typ)) (te3 : tenv_val_exp),
      bind_var_list n (te1 ++ te2) te3 = bind_var_list n te1 (bind_var_list n te2 te3) := by
  intro n te1 te2 te3
  induction te1 with
  | nil => rfl
  | cons p te1 ih =>
    obtain ⟨x, t⟩ := p
    simp only [List.cons_append, bind_var_list, ih]

/- HOL4:
Theorem num_tvs_bind_var_list[simp]:
 !tvs env tenvE. num_tvs (bind_var_list tvs env tenvE) = num_tvs tenvE -/
theorem num_tvs_bind_var_list :
    ∀ (tvs : Nat) (env : List (mlstring × typ)) (tenvE : tenv_val_exp),
      num_tvs (bind_var_list tvs env tenvE) = num_tvs tenvE := by
  intro tvs env tenvE
  induction env with
  | nil => rfl
  | cons p env ih =>
    obtain ⟨x, t⟩ := p
    simp only [bind_var_list, num_tvs, ih]

/- HOL4:
Theorem tenv_val_exp_ok_bvl:
 !tenvE env.
  tenv_val_exp_ok tenvE ∧ EVERY (check_freevars (num_tvs tenvE) []) (MAP SND env)
  ⇒
  tenv_val_exp_ok (bind_var_list 0 env tenvE) -/
theorem tenv_val_exp_ok_bvl :
    ∀ (tenvE : tenv_val_exp) (env : List (mlstring × typ)),
      tenv_val_exp_ok tenvE ∧ EVERY (check_freevars (num_tvs tenvE) []) (env.map Prod.snd) →
      tenv_val_exp_ok (bind_var_list 0 env tenvE) := by
  rintro tenvE env ⟨hok, h⟩
  induction env with
  | nil => exact hok
  | cons p env ih =>
    obtain ⟨x, t⟩ := p
    refine ⟨?_, ih h.2⟩
    rw [num_tvs_bind_var_list, Nat.zero_add]
    exact h.1

/- HOL4:
Theorem tveLookup_subst_some:
   ∀n e targs tvs t inc.
    tveLookup n inc e = SOME (tvs,t)
    ⇒
    tveLookup n inc (deBruijn_subst_tenvE targs e) =
      SOME (tvs, deBruijn_subst (tvs+inc+num_tvs e) (MAP (deBruijn_inc 0 (tvs+inc+num_tvs e)) targs) t) -/
theorem tveLookup_subst_some :
    ∀ (n : mlstring) (e : tenv_val_exp) (targs : List typ) (tvs : Nat) (t : typ) (inc : Nat),
      tveLookup n inc e = some (tvs, t) →
      tveLookup n inc (deBruijn_subst_tenvE targs e) =
        some (tvs, deBruijn_subst (tvs + inc + num_tvs e)
          (targs.map (deBruijn_inc 0 (tvs + inc + num_tvs e))) t) := by
  intro n e targs tvs t inc h
  induction e generalizing inc with
  | Empty => simp [tveLookup] at h
  | Bind_tvar k e ih =>
    simp only [tveLookup] at h
    simp only [deBruijn_subst_tenvE, tveLookup, num_tvs]
    rw [ih _ h]
    have : tvs + (inc + k) + num_tvs e = tvs + inc + (k + num_tvs e) := by omega
    rw [this]
  | Bind_name x k t0 e ih =>
    simp only [tveLookup] at h
    simp only [deBruijn_subst_tenvE, tveLookup, num_tvs]
    split
    · rename_i hx
      rw [if_pos hx] at h
      cases h
      rw [type_e_subst_lem5.1]
    · rename_i hx
      rw [if_neg hx] at h
      exact ih _ h

/- HOL4:
Theorem num_tvs_db_merge[simp]:
 !e1 e2. num_tvs (db_merge e1 e2) = num_tvs e1 + num_tvs e2 -/
theorem num_tvs_db_merge :
    ∀ (e1 e2 : tenv_val_exp), num_tvs (db_merge e1 e2) = num_tvs e1 + num_tvs e2 := by
  intro e1 e2
  induction e1 with
  | Empty => simp [db_merge, num_tvs]
  | Bind_tvar k e ih => simp only [db_merge, num_tvs, ih]; omega
  | Bind_name x k t0 e ih => simp only [db_merge, num_tvs, ih]

/- HOL4:
Theorem num_tvs_deBruijn_subst_tenvE[simp]:
 !targs tenvE. num_tvs (deBruijn_subst_tenvE targs tenvE) = num_tvs tenvE -/
theorem num_tvs_deBruijn_subst_tenvE :
    ∀ (targs : List typ) (tenvE : tenv_val_exp),
      num_tvs (deBruijn_subst_tenvE targs tenvE) = num_tvs tenvE := by
  intro targs tenvE
  induction tenvE with
  | Empty => rfl
  | Bind_tvar k e ih => simp only [deBruijn_subst_tenvE, num_tvs, ih]
  | Bind_name x k t0 e ih => simp only [deBruijn_subst_tenvE, num_tvs, ih]

/- HOL4:
Theorem tveLookup_inc_some:
 !n inc e tvs t inc2.
   tveLookup n inc e = SOME (tvs, t)
   ⇒
   ?t'. (t = deBruijn_inc tvs inc t') ∧
        (tveLookup n inc2 e = SOME (tvs, deBruijn_inc tvs inc2 t')) -/
theorem tveLookup_inc_some :
    ∀ (n : mlstring) (inc : Nat) (e : tenv_val_exp) (tvs : Nat) (t : typ) (inc2 : Nat),
      tveLookup n inc e = some (tvs, t) →
      ∃ t' : typ, t = deBruijn_inc tvs inc t' ∧
        tveLookup n inc2 e = some (tvs, deBruijn_inc tvs inc2 t') := by
  intro n inc e tvs t inc2 h
  induction e generalizing inc inc2 t with
  | Empty => simp [tveLookup] at h
  | Bind_tvar k e ih =>
    simp only [tveLookup] at h ⊢
    obtain ⟨t', rfl, h2⟩ := ih _ _ (inc2 + k) h
    refine ⟨deBruijn_inc tvs k t', ?_, ?_⟩
    · rw [deBruijn_inc_deBruijn_inc]
    · rw [h2, deBruijn_inc_deBruijn_inc]
  | Bind_name x k t0 e ih =>
    simp only [tveLookup] at h ⊢
    split at h
    · rename_i hx
      cases h
      exact ⟨t0, rfl, by rw [if_pos hx]⟩
    · rename_i hx
      obtain ⟨t', h1, h2⟩ := ih _ _ inc2 h
      exact ⟨t', h1, by rw [if_neg hx, h2]⟩

theorem Aux.tveLookup_freevars_gen {e : tenv_val_exp} {n : mlstring} {inc : Nat} {t : typ}
    {tvs : Nat} (hok : tenv_val_exp_ok e) (h : tveLookup n inc e = some (tvs, t)) :
    check_freevars (tvs + inc + num_tvs e) [] t := by
  induction e generalizing inc with
  | Empty => simp [tveLookup] at h
  | Bind_tvar k e ih =>
    simp only [tveLookup] at h
    have := ih hok h
    simp only [num_tvs]
    have e1 : tvs + (inc + k) + num_tvs e = tvs + inc + (k + num_tvs e) := by omega
    rw [← e1]; exact this
  | Bind_name x k t0 e ih =>
    simp only [tveLookup] at h
    split at h
    · cases h
      have := check_freevars_deBruijn_inc _ _ _ hok.1 inc tvs
      simp only [num_tvs]
      have e1 : inc + (tvs + num_tvs e) = tvs + inc + num_tvs e := by omega
      rw [← e1]; exact this
    · exact ih hok.2 h

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
      tenv_val_exp_ok tenvE →
      check_freevars (inc + num_tvs tenvE) [] (deBruijn_subst 0 targs t) := by
  rintro tenvE targs n t inc ⟨h1, h2, h3⟩
  have := Aux.tveLookup_freevars_gen h3 h2
  have h4 := check_freevars_subst _ _ _ this (inc + num_tvs tenvE) targs 0
    ⟨by omega, by rw [Nat.zero_add]; exact h1⟩
  rw [Nat.zero_add] at h4
  exact h4

/- HOL4:
Theorem tenv_val_exp_ok_db_merge:
 !e1 e2. tenv_val_exp_ok (db_merge e1 e2) ⇒ tenv_val_exp_ok e2 -/
theorem tenv_val_exp_ok_db_merge :
    ∀ (e1 e2 : tenv_val_exp), tenv_val_exp_ok (db_merge e1 e2) → tenv_val_exp_ok e2 := by
  intro e1 e2
  induction e1 with
  | Empty => exact id
  | Bind_tvar k e ih => exact ih
  | Bind_name x k t0 e ih => exact fun h => ih h.2

/- HOL4:
Theorem tveLookup_freevars[local]:
  !e n inc t tvs.
  tenv_val_exp_ok e ∧
  tveLookup n inc e = SOME (tvs, t)
  ⇒
  check_freevars (tvs+inc+num_tvs e) [] t
(the second theorem of this name in the theory, line 731) -/
theorem tveLookup_freevars_2 :
    ∀ (e : tenv_val_exp) (n : mlstring) (inc : Nat) (t : typ) (tvs : Nat),
      tenv_val_exp_ok e ∧
      tveLookup n inc e = some (tvs, t) →
      check_freevars (tvs + inc + num_tvs e) [] t := by
  rintro e n inc t tvs ⟨h1, h2⟩
  exact Aux.tveLookup_freevars_gen h1 h2

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
      num_tvs tenv = 0 →
      (tveLookup n tvs tenv = some (l, t) ↔ tveLookup n 0 tenv = some (l, t)) := by
  rintro tvs l tenv n t ⟨hok, hn⟩
  have key : ∀ i j, tveLookup n i tenv = some (l, t) → tveLookup n j tenv = some (l, t) := by
    intro i j h
    have hf := tveLookup_freevars _ _ _ _ _ ⟨hok, hn, h⟩
    obtain ⟨t', rfl, h2⟩ := tveLookup_inc_some _ _ _ _ _ j h
    have h3 := nil_deBruijn_inc l i t' (Or.inr hf)
    rw [h3] at hf ⊢
    rw [h2, nil_deBruijn_inc l j t' (Or.inl hf)]
  exact ⟨key _ _, key _ _⟩

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
      deBruijn_subst_tenvE targs (bind_var_list tvs tenv1 tenv2) =
        bind_var_list tvs
          (tenv1.map (fun (x, t) => (x, deBruijn_subst (tvs + num_tvs tenv2)
            (targs.map (deBruijn_inc 0 (tvs + num_tvs tenv2))) t)))
          (deBruijn_subst_tenvE targs tenv2) := by
  intro tenv1 tenv2 tvs
  induction tenv1 with
  | nil => rfl
  | cons p tenv1 ih =>
    obtain ⟨x, t⟩ := p
    simp only [bind_var_list, deBruijn_subst_tenvE, List.map_cons, ih, num_tvs_bind_var_list]

/- HOL4:
Theorem db_merge_bvl:
 !tenv1 tenv2 tenv3 tvs.
  db_merge (bind_var_list tvs tenv1 tenv2) tenv3
  =
  bind_var_list tvs tenv1 (db_merge tenv2 tenv3) -/
theorem db_merge_bvl :
    ∀ (tenv1 : List (mlstring × typ)) (tenv2 tenv3 : tenv_val_exp) (tvs : Nat),
      db_merge (bind_var_list tvs tenv1 tenv2) tenv3 =
        bind_var_list tvs tenv1 (db_merge tenv2 tenv3) := by
  intro tenv1 tenv2 tenv3 tvs
  induction tenv1 with
  | nil => rfl
  | cons p tenv1 ih =>
    obtain ⟨x, t⟩ := p
    simp only [bind_var_list, db_merge, ih]

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
      tveLookup n inc (db_merge tenvE1 tenvE2) = some (tvs, t) ↔
      (tveLookup n inc tenvE1 = some (tvs, t) ∨
        (tveLookup n inc tenvE1 = none ∧
          tveLookup n (num_tvs tenvE1 + inc) tenvE2 = some (tvs, t))) := by
  intro n inc e1 e2 tvs t
  induction e1 generalizing inc with
  | Empty => simp [db_merge, tveLookup, num_tvs]
  | Bind_tvar k e ih =>
    simp only [db_merge, tveLookup, num_tvs]
    rw [ih]
    have : num_tvs e + (inc + k) = k + num_tvs e + inc := by omega
    rw [this]
  | Bind_name x k t0 e ih =>
    simp only [db_merge, tveLookup, num_tvs]
    split
    · simp
    · exact ih _

/- HOL4:
Theorem type_op_cases =
  ``type_op op ts t3``
  |> (SIMP_CONV(srw_ss())(type_op_def::eqs@elims) THENC
      SIMP_CONV (bool_ss++DNF_ss) [
        PULL_EXISTS])
(no written statement: the equivalence of `type_op op ts t3` with the disjunction
of the cases of `type_op_def`) -/
theorem type_op_cases (op : CmlTS.op) (ts : List typ) (t3 : typ) :
    type_op op ts t3 ↔
      ((∃ t1 t2, op = Opapp ∧ ts = [t1, t2] ∧ t1 = Tfn t2 t3) ∨
       (∃ sh n t1, op = Shift W8 sh n ∧ ts = [t1] ∧ t1 = Tword8 ∧ t3 = Tword8) ∨
       (∃ sh n t1, op = Shift W64 sh n ∧ ts = [t1] ∧ t1 = Tword64 ∧ t3 = Tword64) ∨
       (∃ t1 t2, op = Equality ∧ ts = [t1, t2] ∧ t1 = t2 ∧ t3 = Tbool) ∨
       (∃ a ty, op = Arith a ty ∧ EVERY (fun arg => arg = t_of ty) ts ∧ t3 = t_of ty ∧
         supported_arith a ty = some ts.length) ∨
       (∃ ty1 ty2 t1, op = FromTo ty1 ty2 ∧ ts = [t1] ∧ t1 = t_of ty1 ∧ t3 = t_of ty2 ∧
         supported_conversion ty1 ty2) ∨
       (∃ test ty t1 t2, op = Test test ty ∧ ts = [t1, t2] ∧ t1 = t2 ∧ t3 = Tbool ∧
         t1 = t_of ty ∧ supported_test test ty) ∨
       (∃ t1 t2, op = Opassign ∧ ts = [t1, t2] ∧ t1 = Tref t2 ∧ t3 = Ttup []) ∨
       (∃ t1, op = Opref ∧ ts = [t1] ∧ t3 = Tref t1) ∨
       (∃ t1, op = Opderef ∧ ts = [t1] ∧ t1 = Tref t3) ∨
       (∃ t1 t2, op = Aw8alloc ∧ ts = [t1, t2] ∧ t1 = Tint ∧ t2 = Tword8 ∧ t3 = Tword8array) ∨
       (∃ t1 t2, op = Aw8sub ∧ ts = [t1, t2] ∧ t1 = Tword8array ∧ t2 = Tint ∧ t3 = Tword8) ∨
       (∃ t1, op = Aw8length ∧ ts = [t1] ∧ t1 = Tword8array ∧ t3 = Tint) ∨
       (∃ t1 t2 t3', op = Aw8update ∧ ts = [t1, t2, t3'] ∧ t1 = Tword8array ∧ t2 = Tint ∧
         t3' = Tword8 ∧ t3 = Ttup []) ∨
       (∃ t1 t2 t3', op = CopyStrStr ∧ ts = [t1, t2, t3'] ∧ t1 = Tstring ∧ t2 = Tint ∧
         t3' = Tint ∧ t3 = Tstring) ∨
       (∃ t1 t2 t3' t4 t5, op = CopyStrAw8 ∧ ts = [t1, t2, t3', t4, t5] ∧ t1 = Tstring ∧
         t2 = Tint ∧ t3' = Tint ∧ t4 = Tword8array ∧ t5 = Tint ∧ t3 = Ttup []) ∨
       (∃ t1 t2 t3', op = CopyAw8Str ∧ ts = [t1, t2, t3'] ∧ t1 = Tword8array ∧ t2 = Tint ∧
         t3' = Tint ∧ t3 = Tstring) ∨
       (∃ t1 t2 t3' t4 t5, op = CopyAw8Aw8 ∧ ts = [t1, t2, t3', t4, t5] ∧ t1 = Tword8array ∧
         t2 = Tint ∧ t3' = Tint ∧ t4 = Tword8array ∧ t5 = Tint ∧ t3 = Ttup []) ∨
       (∃ t1, op = Implode ∧ ts = [t1] ∧ t1 = Tlist Tchar ∧ t3 = Tstring) ∨
       (∃ t1, op = Explode ∧ ts = [t1] ∧ t1 = Tstring ∧ t3 = Tlist Tchar) ∨
       (∃ t1 t2, op = Strsub ∧ ts = [t1, t2] ∧ t1 = Tstring ∧ t2 = Tint ∧ t3 = Tchar) ∨
       (∃ t1, op = Strlen ∧ ts = [t1] ∧ t1 = Tstring ∧ t3 = Tint) ∨
       (∃ t1, op = Strcat ∧ ts = [t1] ∧ t1 = Tlist Tstring ∧ t3 = Tstring) ∨
       (∃ t1 ctor, op = VfromList ∧ ts = [Tapp [t1] ctor] ∧ ctor = Tlist_num ∧
         t3 = Tvector t1) ∨
       (∃ t1 t2, op = Vsub ∧ ts = [t1, t2] ∧ t2 = Tint ∧ Tvector t3 = t1) ∨
       (∃ t1 ctor, op = Vlength ∧ ts = [Tapp [t1] ctor] ∧ ctor = Tvector_num ∧ t3 = Tint) ∨
       (∃ t1 t2, op = Aalloc ∧ ts = [t1, t2] ∧ t1 = Tint ∧ t3 = Tarray t2) ∨
       (∃ t1 t2, op = AallocEmpty ∧ ts = [t1] ∧ t1 = Ttup [] ∧ t3 = Tarray t2) ∨
       (∃ t1 t2, op = Asub ∧ ts = [t1, t2] ∧ t2 = Tint ∧ Tarray t3 = t1) ∨
       (∃ t1 ctor, op = Alength ∧ ts = [Tapp [t1] ctor] ∧ ctor = Tarray_num ∧ t3 = Tint) ∨
       (∃ t1 t2 t3', op = Aupdate ∧ ts = [t1, t2, t3'] ∧ t1 = Tarray t3' ∧ t2 = Tint ∧
         t3 = Ttup []) ∨
       (∃ t1 t2, op = ConfigGC ∧ ts = [t1, t2] ∧ t1 = Tint ∧ t2 = Tint ∧ t3 = Ttup []) ∨
       (∃ n t1 t2, op = FFI n ∧ ts = [t1, t2] ∧ t1 = Tstring ∧ t2 = Tword8array ∧
         t3 = Ttup []) ∨
       (∃ t1 ctor t2, op = ListAppend ∧ ts = [Tapp [t1] ctor, t2] ∧ ctor = Tlist_num ∧
         t2 = Tapp [t1] ctor ∧ t3 = t2)) := by
  constructor
  · intro h
    unfold type_op at h
    split at h
    all_goals first
      | exact h.elim
      | (simp_all [and_assoc]; done)
      | (obtain ⟨rfl, rfl, rfl, h⟩ := h; simp [h, and_assoc]; done)
  · intro h
    repeat' first
      | (cases h with
         | inl h => ?_
         | inr h => ?_)
      | (obtain ⟨_, h⟩ := h)
    all_goals subst_vars
    all_goals unfold type_op
    all_goals first
      | (simp [*]; done)
      | (simp [*]; exact ⟨_, rfl⟩)

/- HOL4:
Theorem type_ps_length:
 ∀tvs tenvC ps ts tenv.
  type_ps tvs tenvC ps ts tenv ⇒ (LENGTH ps = LENGTH ts) -/
theorem type_ps_length :
    ∀ (tvs : Nat) (tenvC : type_env) (ps : List pat) (ts : List typ)
      (tenv : List (varN × typ)),
      type_ps tvs tenvC ps ts tenv → ps.length = ts.length := by
  intro tvs tenvC ps
  induction ps with
  | nil => intro ts tenv h; cases h; rfl
  | cons p ps ih =>
    intro ts tenv h
    cases h with
    | cons _ _ t ts b b' h1 h2 => simp only [List.length_cons, ih _ _ h2]

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
      EVERY (check_freevars tvs []) (env'.map Prod.snd)) := by
  have hc : ∀ tvs ti, check_freevars tvs [] (Tapp [] ti) := fun tvs ti =>
    Aux.cf_app.2 (by simp)
  apply Aux.type_p_ind
  case any => intro tvs tenv t h; exact ⟨h, trivial⟩
  case var => intro tvs tenv n t h; exact ⟨h, h, trivial⟩
  case intLit => intro tvs tenv n; exact ⟨hc _ _, trivial⟩
  case char => intro tvs tenv n; exact ⟨hc _ _, trivial⟩
  case strLit => intro tvs tenv n; exact ⟨hc _ _, trivial⟩
  case word8 => intro tvs tenv n; exact ⟨hc _ _, trivial⟩
  case word64 => intro tvs tenv n; exact ⟨hc _ _, trivial⟩
  case con =>
    intro tvs tenv cn ps ts tvs' tn ts' b h1 _ _ ih _
    exact ⟨Aux.cf_app.2 (EVERY_iff_forall.1 h1), ih.2⟩
  case tup =>
    intro tvs tenv ps ts b _ ih
    exact ⟨Aux.cf_app.2 (EVERY_iff_forall.1 ih.1), ih.2⟩
  case ref =>
    intro tvs tenv p t b _ ih
    refine ⟨Aux.cf_app.2 fun t' ht => ?_, ih.2⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rw [ht]; exact ih.1
  case pas =>
    intro tvs tenv p v t b _ ih
    refine ⟨ih.1, ?_⟩
    rw [Aux.EVERY_map]
    have h2 := Aux.EVERY_map.1 ih.2
    intro x hx
    rcases List.mem_append.1 hx with hx | hx
    · exact h2 x hx
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rw [hx]; exact ih.1
  case tannot => intro tvs tenv p t b _ _ _ ih; exact ih
  case nil => intro tvs tenv; exact ⟨trivial, trivial⟩
  case cons =>
    intro tvs tenv p ps t ts b b' _ _ ih1 ih2
    refine ⟨⟨ih1.1, ih2.1⟩, ?_⟩
    rw [Aux.EVERY_map]
    intro x hx
    rcases List.mem_append.1 hx with hx | hx
    · exact Aux.EVERY_map.1 ih2.2 x hx
    · exact Aux.EVERY_map.1 ih1.2 x hx

theorem Aux.sub_const {sk : Nat} {targs : List typ} {ti : type_ident} :
    deBruijn_subst sk targs (Tapp [] ti) = Tapp [] ti := by
  rw [Aux.sub_app]; rfl

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
        targs' = targs.map (deBruijn_inc 0 inc) →
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
        targs' = targs.map (deBruijn_inc 0 inc) →
        type_ps (inc + tvs) tenv
          ps
          (ts.map (deBruijn_subst inc targs'))
          (new_bindings.map (fun (x, t) => (x, deBruijn_subst inc targs' t)))) := by
  apply Aux.type_p_ind
  case any =>
    rintro n tenv t h targs' inc tvs targs ⟨ha, hc, rfl, he, rfl⟩
    exact type_p.any _ _ _ (check_freevars_lem _ _ _ h _ _ _ ⟨rfl, he⟩)
  case var =>
    rintro n tenv x t h targs' inc tvs targs ⟨ha, hc, rfl, he, rfl⟩
    exact type_p.var _ _ _ _ (check_freevars_lem _ _ _ h _ _ _ ⟨rfl, he⟩)
  case intLit =>
    rintro n tenv x targs' inc tvs targs -
    rw [show deBruijn_subst inc targs' Tint = Tint from Aux.sub_const]
    exact type_p.intLit _ _ _
  case char =>
    rintro n tenv x targs' inc tvs targs -
    rw [show deBruijn_subst inc targs' Tchar = Tchar from Aux.sub_const]
    exact type_p.char _ _ _
  case strLit =>
    rintro n tenv x targs' inc tvs targs -
    rw [show deBruijn_subst inc targs' Tstring = Tstring from Aux.sub_const]
    exact type_p.strLit _ _ _
  case word8 =>
    rintro n tenv x targs' inc tvs targs -
    rw [show deBruijn_subst inc targs' Tword8 = Tword8 from Aux.sub_const]
    exact type_p.word8 _ _ _
  case word64 =>
    rintro n tenv x targs' inc tvs targs -
    rw [show deBruijn_subst inc targs' Tword64 = Tword64 from Aux.sub_const]
    exact type_p.word64 _ _ _
  case con =>
    rintro n tenv cn ps ts tvs' tn ts' b h1 h2 _ ih h3 targs' inc tvs targs ⟨ha, hc, rfl, he, rfl⟩
    rw [Aux.sub_app]
    refine type_p.con _ _ cn ps ts tvs' tn _ _ ?_ (by simpa using h2) ?_ h3
    · rw [Aux.EVERY_map]
      rw [EVERY_iff_forall] at h1
      exact fun t ht => check_freevars_lem _ _ _ (h1 t ht) _ _ _ ⟨rfl, he⟩
    · have := ih _ inc targs tvs ⟨ha, hc, rfl, he, rfl⟩
      rw [type_subst_deBruijn_subst_list () tvs' () ts' _ ts inc
        ⟨h2.symm, tenv_ctor_ok_lookup _ _ _ _ _ ⟨hc, h3⟩⟩] at this
      exact this
  case tup =>
    rintro n tenv ps ts b _ ih targs' inc tvs targs hh
    rw [show deBruijn_subst inc targs' (Ttup ts) = Ttup (ts.map (deBruijn_subst inc targs'))
      from Aux.sub_app]
    exact type_p.tup _ _ _ _ _ (ih _ inc targs tvs hh)
  case ref =>
    rintro n tenv p t b _ ih targs' inc tvs targs hh
    rw [show deBruijn_subst inc targs' (Tref t) = Tref (deBruijn_subst inc targs' t)
      from Aux.sub_app]
    exact type_p.ref _ _ _ _ _ (ih _ inc tvs targs hh)
  case pas =>
    rintro n tenv p v t b _ ih targs' inc tvs targs hh
    rw [List.map_append]
    exact type_p.pas _ _ _ _ _ _ (ih _ inc tvs targs hh)
  case tannot =>
    rintro n tenv p t b h1 h2 _ ih targs' inc tvs targs hh
    have hcl := nil_deBruijn_subst inc targs' _
      (check_freevars_type_name_subst [] t inc tenv.t ⟨hh.1, h2, h1⟩)
    have := ih _ inc tvs targs hh
    rw [hcl] at this ⊢
    exact type_p.tannot _ _ _ _ _ h1 h2 this
  case nil => rintro n tenv targs' inc tvs targs -; exact type_ps.nil _ _
  case cons =>
    rintro n tenv p ps t ts b b' _ _ ih1 ih2 targs' inc targs tvs hh
    rw [List.map_append]
    exact type_ps.cons _ _ _ _ _ _ _ _ (ih1 _ inc tvs targs hh) (ih2 _ inc targs tvs hh)

theorem Aux.ok_bvl_gen {k : Nat} {b : List (mlstring × typ)} {E : tenv_val_exp}
    (hE : tenv_val_exp_ok E)
    (h : EVERY (check_freevars (k + num_tvs E) []) (b.map Prod.snd)) :
    tenv_val_exp_ok (bind_var_list k b E) := by
  induction b with
  | nil => exact hE
  | cons p b ih =>
    obtain ⟨x, t⟩ := p
    refine ⟨?_, ih h.2⟩
    rw [num_tvs_bind_var_list]
    exact h.1

/- HOL4:
Theorem type_p_bvl:
   (!tvs tenvC p t bindings. type_p tvs tenvC p t bindings ⇒
    !tenv'. tenv_val_exp_ok tenv' ⇒ tenv_val_exp_ok (bind_var_list tvs bindings tenv')) ∧
   (!tvs tenvC ps ts bindings. type_ps tvs tenvC ps ts bindings ⇒
    !tenv'. tenv_val_exp_ok tenv' ⇒ tenv_val_exp_ok (bind_var_list tvs bindings tenv')) -/
theorem type_p_bvl :
    (∀ (tvs : Nat) (tenvC : type_env) (p : pat) (t : typ) (bindings : List (varN × typ)),
      type_p tvs tenvC p t bindings →
      ∀ (tenv' : tenv_val_exp),
        tenv_val_exp_ok tenv' → tenv_val_exp_ok (bind_var_list tvs bindings tenv')) ∧
    (∀ (tvs : Nat) (tenvC : type_env) (ps : List pat) (ts : List typ)
      (bindings : List (varN × typ)),
      type_ps tvs tenvC ps ts bindings →
      ∀ (tenv' : tenv_val_exp),
        tenv_val_exp_ok tenv' → tenv_val_exp_ok (bind_var_list tvs bindings tenv')) := by
  have key : ∀ (tvs : Nat) (bindings : List (varN × typ)) (tenv' : tenv_val_exp),
      EVERY (check_freevars tvs []) (bindings.map Prod.snd) → tenv_val_exp_ok tenv' →
      tenv_val_exp_ok (bind_var_list tvs bindings tenv') := by
    intro tvs b tenv' h hE
    refine Aux.ok_bvl_gen hE ?_
    rw [EVERY_iff_forall] at h ⊢
    exact fun t ht => check_freevars_add _ _ _ (h t ht) _ (by omega)
  exact ⟨fun tvs tenvC p t b h tenv' => key _ _ _ (type_p_freevars.1 _ _ _ _ _ h).2,
    fun tvs tenvC p t b h tenv' => key _ _ _ (type_p_freevars.2 _ _ _ _ _ h).2⟩

theorem Aux.type_p_change :
    (∀ (tvs : Nat) (tenv : type_env) (p : pat) (t : typ) (b : List (varN × typ)),
      type_p tvs tenv p t b → ∀ tenv' : type_env, tenv'.c = tenv.c → tenv'.t = tenv.t →
      type_p tvs tenv' p t b) ∧
    (∀ (tvs : Nat) (tenv : type_env) (p : List pat) (t : List typ) (b : List (varN × typ)),
      type_ps tvs tenv p t b → ∀ tenv' : type_env, tenv'.c = tenv.c → tenv'.t = tenv.t →
      type_ps tvs tenv' p t b) := by
  apply Aux.type_p_ind
  case any => intro tvs tenv t h tenv' _ _; exact type_p.any _ _ _ h
  case var => intro tvs tenv n t h tenv' _ _; exact type_p.var _ _ _ _ h
  case intLit => intros; exact type_p.intLit _ _ _
  case char => intros; exact type_p.char _ _ _
  case strLit => intros; exact type_p.strLit _ _ _
  case word8 => intros; exact type_p.word8 _ _ _
  case word64 => intros; exact type_p.word64 _ _ _
  case con =>
    intro tvs tenv cn ps ts tvs' tn ts' b h1 h2 _ ih h3 tenv' hc ht
    exact type_p.con _ _ _ _ _ _ _ _ _ h1 h2 (ih _ hc ht) (by rw [hc]; exact h3)
  case tup => intro tvs tenv ps ts b _ ih tenv' hc ht; exact type_p.tup _ _ _ _ _ (ih _ hc ht)
  case ref => intro tvs tenv ps ts b _ ih tenv' hc ht; exact type_p.ref _ _ _ _ _ (ih _ hc ht)
  case pas => intro tvs tenv p v t b _ ih tenv' hc ht; exact type_p.pas _ _ _ _ _ _ (ih _ hc ht)
  case tannot =>
    intro tvs tenv p t b h1 h2 _ ih tenv' hc ht
    have := ih _ hc ht
    rw [← ht] at h2 this ⊢
    exact type_p.tannot _ _ _ _ _ h1 h2 this
  case nil => intros; exact type_ps.nil _ _
  case cons =>
    intro tvs tenv p ps t ts b b' _ _ ih1 ih2 tenv' hc ht
    exact type_ps.cons _ _ _ _ _ _ _ _ (ih1 _ hc ht) (ih2 _ hc ht)

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
      type_ps tvs tenv ps t bindings ↔ type_ps tvs { tenv with v := tenvV } ps t bindings) := by
  exact ⟨fun p tvs tenv t b tenvV =>
      ⟨fun h => Aux.type_p_change.1 _ _ _ _ _ h _ rfl rfl,
        fun h => Aux.type_p_change.1 _ _ _ _ _ h _ rfl rfl⟩,
    fun p tvs tenv t b tenvV =>
      ⟨fun h => Aux.type_p_change.2 _ _ _ _ _ h _ rfl rfl,
        fun h => Aux.type_p_change.2 _ _ _ _ _ h _ rfl rfl⟩⟩

/- HOL4:
Theorem type_es_list_rel:
 !es ts tenv tenvE. type_es tenv tenvE es ts = LIST_REL (type_e tenv tenvE) es ts -/
theorem type_es_list_rel :
    ∀ (es : List exp) (ts : List typ) (tenv : type_env) (tenvE : tenv_val_exp),
      type_es tenv tenvE es ts ↔ LIST_REL (type_e tenv tenvE) es ts := by
  intro es
  induction es with
  | nil =>
    intro ts tenv tenvE
    constructor
    · intro h; cases h; trivial
    · intro h
      cases ts with
      | nil => exact type_es.nil _ _
      | cons t ts => exact h.elim
  | cons e es ih =>
    intro ts tenv tenvE
    constructor
    · intro h
      cases h with
      | cons _ _ _ t ts h1 h2 => exact ⟨h1, (ih _ _ _).1 h2⟩
    · intro h
      cases ts with
      | nil => exact h.elim
      | cons t ts => exact type_es.cons _ _ _ _ _ _ h.1 ((ih _ _ _).2 h.2)

/- HOL4:
Theorem type_es_length:
 ∀tenv tenvE es ts.
  type_es tenv tenvE es ts ⇒ (LENGTH es = LENGTH ts) -/
theorem type_es_length :
    ∀ (tenv : type_env) (tenvE : tenv_val_exp) (es : List exp) (ts : List typ),
      type_es tenv tenvE es ts → es.length = ts.length := by
  intro tenv tenvE es ts h
  exact Aux.LIST_REL_length ((type_es_list_rel _ _ _ _).1 h)

theorem Aux.type_funs_mem {tenv : type_env} {E : tenv_val_exp}
    {funs : List (varN × varN × exp)} {b : List (varN × typ)} (h : type_funs tenv E funs b) :
    ∀ x t, (x, t) ∈ b → ∃ t1 t2, t = Tfn t1 t2 ∧ check_freevars (num_tvs E) [] t := by
  induction funs generalizing b with
  | nil => cases h; intro x t hx; cases hx
  | cons f funs ih =>
    cases h with
    | cons _ fn n e funs b t1 t2 h1 h2 h3 h4 =>
      intro x t hx
      rcases List.mem_cons.1 hx with hx | hx
      · cases hx; exact ⟨t1, t2, rfl, h1⟩
      · exact ih h3 x t hx

theorem Aux.type_funs_fst {tenv : type_env} {E : tenv_val_exp}
    {funs : List (varN × varN × exp)} {b : List (varN × typ)} (h : type_funs tenv E funs b) :
    b.map Prod.fst = funs.map Prod.fst := by
  induction funs generalizing b with
  | nil => cases h; rfl
  | cons f funs ih =>
    cases h with
    | cons _ fn n e funs b t1 t2 h1 h2 h3 h4 => simp [ih h3]

/- HOL4:
Theorem tenv_val_exp_ok_bvl_funs:
   !funs env tenv bindings tenv_val tenvE.
    type_funs tenv (bind_var_list 0 bindings tenvE) funs env ∧
    tenv_val_exp_ok tenvE
    ⇒
    tenv_val_exp_ok (bind_var_list 0 env tenvE) -/
theorem tenv_val_exp_ok_bvl_funs {α : Type} :
    ∀ (funs : List (varN × varN × exp)) (env : List (varN × typ)) (tenv : type_env)
      (bindings : List (varN × typ)) (tenv_val : α) (tenvE : tenv_val_exp),
      type_funs tenv (bind_var_list 0 bindings tenvE) funs env ∧
      tenv_val_exp_ok tenvE →
      tenv_val_exp_ok (bind_var_list 0 env tenvE) := by
  rintro funs env tenv bindings _ tenvE ⟨h, hE⟩
  refine tenv_val_exp_ok_bvl _ _ ⟨hE, ?_⟩
  rw [Aux.EVERY_map]
  rintro ⟨x, t⟩ hx
  obtain ⟨_, _, _, hc⟩ := Aux.type_funs_mem h x t hx
  rw [num_tvs_bind_var_list] at hc
  exact hc

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
      EVERY (check_freevars (num_tvs tenvE) []) (env.map Prod.snd)) := by
  have hc : ∀ n ti, check_freevars n [] (Tapp [] ti) := fun tvs ti => Aux.cf_app.2 (by simp)
  have hfn : ∀ n t1 t2, check_freevars n [] (Tfn t1 t2) ↔
      check_freevars n [] t1 ∧ check_freevars n [] t2 := by
    intro n t1 t2
    unfold Tfn
    rw [Aux.cf_app]
    simp
  apply Aux.type_e_ind
  case intLit => intros; exact hc _ _
  case char => intros; exact hc _ _
  case strLit => intros; exact hc _ _
  case word8 => intros; exact hc _ _
  case word64 => intros; exact hc _ _
  case float64 => intros; exact hc _ _
  case raise => intro tenv E e t h _ _ _; exact h
  case handle => intro tenv E e pes t bs _ _ _ _ _ ih _ hh; exact ih hh
  case con =>
    intro tenv E cn es tvs tn ts' ts h1 _ _ _ _ _
    exact Aux.cf_app.2 (EVERY_iff_forall.1 h1)
  case tup =>
    intro tenv E es ts _ ih hh
    exact Aux.cf_app.2 (EVERY_iff_forall.1 (ih hh))
  case var =>
    rintro tenv E n t targs tvs rfl h1 h2 ⟨hE, hv⟩
    unfold lookup_var at h2
    cases hl : lookup_varE n E with
    | some x =>
      rw [hl] at h2
      cases h2
      unfold lookup_varE at hl
      cases n with
      | Short x =>
        have := tveLookup_freevars_subst E targs x t 0
          ⟨by rw [Nat.zero_add]; exact h1, hl, hE⟩
        rw [Nat.zero_add] at this
        exact this
      | Long mn id => cases hl
    | none =>
      rw [hl] at h2
      exact deBruijn_subst_check_freevars2 _ _ _ _ () () ⟨hv _ _ h2, h1⟩
  case fn =>
    intro tenv E n e t1 t2 h1 _ ih hh
    exact (hfn _ _ _).2 ⟨h1, ih ⟨⟨by rw [Nat.zero_add]; exact h1, hh.1⟩, hh.2⟩⟩
  case app => intro tenv E o es ts t _ _ h _ _; exact h
  case log => intros; exact hc _ _
  case ite => intro tenv E e1 e2 e3 t _ _ _ _ ih _ hh; exact ih hh
  case mat =>
    intro tenv E e pes t1 t2 bs _ h2 _ h4 _ _ ih hh
    obtain ⟨pe, hpe⟩ := List.exists_mem_of_ne_nil _ h2
    have := ih pe hpe ⟨tenv_val_exp_ok_bvl _ _ ⟨hh.1,
      (type_p_freevars.1 _ _ _ _ _ (h4 pe hpe)).2⟩, hh.2⟩
    rw [num_tvs_bind_var_list] at this
    exact this
  case letc =>
    intro tenv E n e1 e2 t1 t2 _ _ ih1 ih2 hh
    cases n with
    | none => exact ih2 hh
    | some n => exact ih2 ⟨⟨by rw [Nat.zero_add]; exact ih1 hh, hh.1⟩, hh.2⟩
  case letrec =>
    intro tenv E funs e t b h1 _ _ ih hh
    have := ih ⟨tenv_val_exp_ok_bvl_funs _ _ _ _ () _ ⟨h1, hh.1⟩, hh.2⟩
    rw [num_tvs_bind_var_list] at this
    exact this
  case tannot => intro tenv E e t _ _ _ ih hh; exact ih hh
  case lannot => intro tenv E e l t _ ih hh; exact ih hh
  case nil => intros; trivial
  case cons => intro tenv E e es t ts _ _ ih1 ih2 hh; exact ⟨ih1 hh, ih2 hh⟩
  case fnil => intros; trivial
  case fcons =>
    intro tenv E fn n e funs b t1 t2 h1 _ _ _ _ ih hh
    exact ⟨h1, ih hh⟩

theorem Aux.sub_t_of {sk : Nat} {targs : List typ} {ty : prim_type} :
    deBruijn_subst sk targs (t_of ty) = t_of ty := by
  rcases ty with _ | _ | _ | _ | (_ | _) | _ <;> exact Aux.sub_const

theorem Aux.type_op_subst {o : op} {ts : List typ} {t : typ} (sk : Nat) (targs : List typ)
    (h : type_op o ts t) :
    type_op o (ts.map (deBruijn_subst sk targs)) (deBruijn_subst sk targs t) := by
  unfold type_op at h
  split at h
  case h_5 =>
    obtain ⟨h1, rfl, h3⟩ := h
    refine ⟨?_, Aux.sub_t_of, by simpa using h3⟩
    rw [Aux.EVERY_map]
    rw [EVERY_iff_forall] at h1
    intro t ht
    rw [h1 t ht, Aux.sub_t_of]
  all_goals first
    | exact h.elim
    | (simp_all [type_op, Tfn, Tbool, Tint, Tchar, Tstring, Tword8, Tword64, Tref, Ttup,
        Tlist, Tvector, Tarray, Tword8array, Aux.sub_app]; done)
    | (obtain ⟨rfl, rfl, h⟩ := h
       simp_all [type_op, Tbool, Aux.sub_app, Aux.sub_t_of]; done)
    | (obtain ⟨rfl, t2, rfl⟩ := h
       simp [type_op, Ttup, Tarray, Aux.sub_app]; done)
    | (obtain ⟨rfl, rfl, rfl, h⟩ := h
       simp [type_op, Tbool, Aux.sub_app, Aux.sub_t_of, h]; done)
    | (obtain ⟨rfl, rfl⟩ := h
       simp [type_op, Tint, Tvector, Tarray, Aux.sub_app]; done)

theorem Aux.merge_bind (targs : List typ) (n : varN) (t : typ) (E1 X : tenv_val_exp) :
    db_merge (deBruijn_subst_tenvE targs (Bind_name n 0 t E1)) X =
      Bind_name n 0 (deBruijn_subst (num_tvs E1) (targs.map (deBruijn_inc 0 (num_tvs E1))) t)
        (db_merge (deBruijn_subst_tenvE targs E1) X) := by
  simp only [deBruijn_subst_tenvE, db_merge, Nat.zero_add]

theorem Aux.merge_bvl (targs : List typ) (b : List (varN × typ)) (E1 X : tenv_val_exp) :
    db_merge (deBruijn_subst_tenvE targs (bind_var_list 0 b E1)) X =
      bind_var_list 0 (b.map (fun (x, t) => (x,
        deBruijn_subst (num_tvs E1) (targs.map (deBruijn_inc 0 (num_tvs E1))) t)))
        (db_merge (deBruijn_subst_tenvE targs E1) X) := by
  rw [deBruijn_subst_E_bvl, db_merge_bvl]
  simp only [Nat.zero_add]

theorem Aux.ALOOKUP_map_fst {α β γ : Type} (f : β → γ) (l : List (α × β)) (k : α) :
    ALOOKUP (l.map (fun (x, t) => (x, f t))) k = (ALOOKUP l k).map f := by
  rw [← Aux.ALOOKUP_map]

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
        targs' = targs.map (deBruijn_inc 0 (num_tvs tenvE1)) →
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
        targs' = targs.map (deBruijn_inc 0 (num_tvs tenvE1)) →
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
        targs' = targs.map (deBruijn_inc 0 (num_tvs tenvE1)) →
        type_funs tenv (db_merge (deBruijn_subst_tenvE targs tenvE1) (bind_tvar tvs tenvE2))
          funs
          (env.map (fun (x, t) => (x, deBruijn_subst (num_tvs tenvE1) targs' t)))) := by
  have hcf : ∀ (E1 : tenv_val_exp) (targs : List typ) (tvs : Nat) (t : typ),
      num_tvs tenvE2 = 0 → EVERY (check_freevars tvs []) targs →
      check_freevars (num_tvs (db_merge E1 (bind_tvar targs.length tenvE2))) [] t →
      check_freevars (num_tvs (db_merge (deBruijn_subst_tenvE targs E1) (bind_tvar tvs tenvE2)))
        [] (deBruijn_subst (num_tvs E1) (targs.map (deBruijn_inc 0 (num_tvs E1))) t) := by
    intro E1 targs tvs t h0 he h
    rw [num_tvs_db_merge, Aux.num_tvs_bt, h0, Nat.add_zero] at h
    rw [num_tvs_db_merge, Aux.num_tvs_bt, h0, Nat.add_zero, num_tvs_deBruijn_subst_tenvE]
    exact check_freevars_lem _ _ _ h _ _ _ ⟨rfl, he⟩
  have hpat : ∀ (E1 : tenv_val_exp) (targs : List typ) (tvs : Nat) (tenv : type_env) (p : pat)
      (t : typ) (b : List (varN × typ)),
      num_tvs tenvE2 = 0 → EVERY (check_freevars tvs []) targs →
      tenv_abbrev_ok tenv.t → tenv_ctor_ok tenv.c →
      type_p (num_tvs (db_merge E1 (bind_tvar targs.length tenvE2))) tenv p t b →
      type_p (num_tvs (db_merge (deBruijn_subst_tenvE targs E1) (bind_tvar tvs tenvE2))) tenv p
        (deBruijn_subst (num_tvs E1) (targs.map (deBruijn_inc 0 (num_tvs E1))) t)
        (b.map (fun (x, t) => (x,
          deBruijn_subst (num_tvs E1) (targs.map (deBruijn_inc 0 (num_tvs E1))) t))) := by
    intro E1 targs tvs tenv p t b h0 he ha hc h
    rw [num_tvs_db_merge, Aux.num_tvs_bt, h0, Nat.add_zero] at h
    rw [num_tvs_db_merge, Aux.num_tvs_bt, h0, Nat.add_zero, num_tvs_deBruijn_subst_tenvE]
    exact type_p_subst.1 _ _ _ _ _ h _ _ _ _ ⟨ha, hc, rfl, he, rfl⟩
  apply Aux.type_e_ind
  case intLit =>
    rintro tenv E n E1 targs tvs targs' -
    rw [show deBruijn_subst (num_tvs E1) targs' Tint = Tint from Aux.sub_const]
    exact type_e.intLit _ _ _
  case char =>
    rintro tenv E n E1 targs tvs targs' -
    rw [show deBruijn_subst (num_tvs E1) targs' Tchar = Tchar from Aux.sub_const]
    exact type_e.char _ _ _
  case strLit =>
    rintro tenv E n E1 targs tvs targs' -
    rw [show deBruijn_subst (num_tvs E1) targs' Tstring = Tstring from Aux.sub_const]
    exact type_e.strLit _ _ _
  case word8 =>
    rintro tenv E n E1 targs tvs targs' -
    rw [show deBruijn_subst (num_tvs E1) targs' Tword8 = Tword8 from Aux.sub_const]
    exact type_e.word8 _ _ _
  case word64 =>
    rintro tenv E n E1 targs tvs targs' -
    rw [show deBruijn_subst (num_tvs E1) targs' Tword64 = Tword64 from Aux.sub_const]
    exact type_e.word64 _ _ _
  case float64 =>
    rintro tenv E n E1 targs tvs targs' -
    rw [show deBruijn_subst (num_tvs E1) targs' Tdouble = Tdouble from Aux.sub_const]
    exact type_e.float64 _ _ _
  case raise =>
    rintro tenv E e t h _ ih E1 targs tvs targs' ⟨h0, ha, hc, hv, hE, he, rfl, rfl⟩
    have := ih E1 targs tvs _ ⟨h0, ha, hc, hv, hE, he, rfl, rfl⟩
    rw [show deBruijn_subst (num_tvs E1) _ Texn = Texn from Aux.sub_const] at this
    exact type_e.raise _ _ _ _ (hcf _ _ _ _ h0 he h) this
  case handle =>
    rintro tenv E e pes t bs _ h2 h3 h4 _ ih1 ih2 E1 targs tvs targs'
      ⟨h0, ha, hc, hv, hE, he, rfl, rfl⟩
    refine type_e.handle _ _ _ _ _ (fun pe => (bs pe).map (fun (x, t) => (x,
        deBruijn_subst (num_tvs E1) (targs.map (deBruijn_inc 0 (num_tvs E1))) t)))
      (ih1 E1 targs tvs _ ⟨h0, ha, hc, hv, hE, he, rfl, rfl⟩) h2 h3 (fun pe hpe => ?_)
      (fun pe hpe => ?_)
    · have := hpat E1 targs tvs tenv pe.1 _ _ h0 he ha hc (h4 pe hpe)
      rw [show deBruijn_subst (num_tvs E1) _ Texn = Texn from Aux.sub_const] at this
      exact this
    · have := ih2 pe hpe (bind_var_list 0 (bs pe) E1) targs tvs _ ⟨h0, ha, hc, hv,
        tenv_val_exp_ok_bvl _ _ ⟨hE, (type_p_freevars.1 _ _ _ _ _ (h4 pe hpe)).2⟩, he,
        (db_merge_bvl _ _ _ _).symm, rfl⟩
      rw [Aux.merge_bvl, num_tvs_bind_var_list] at this
      exact this
  case con =>
    rintro tenv E cn es tvs0 tn ts' ts h1 h2 _ h4 ih E1 targs tvs targs'
      ⟨h0, ha, hc, hv, hE, he, rfl, rfl⟩
    have := ih E1 targs tvs _ ⟨h0, ha, hc, hv, hE, he, rfl, rfl⟩
    rw [type_subst_deBruijn_subst_list () tvs0 () ts' _ ts _
      ⟨h2, tenv_ctor_ok_lookup _ _ _ _ _ ⟨hc, h4⟩⟩] at this
    rw [Aux.sub_app]
    refine type_e.con _ _ _ _ tvs0 _ _ ts ?_ (by simpa using h2) this h4
    rw [Aux.EVERY_map]
    rw [EVERY_iff_forall] at h1
    exact fun t ht => hcf _ _ _ _ h0 he (h1 t ht)
  case tup =>
    rintro tenv E es ts _ ih E1 targs tvs targs' hh
    rw [show deBruijn_subst (num_tvs E1) targs' (Ttup ts) =
      Ttup (ts.map (deBruijn_subst (num_tvs E1) targs')) from Aux.sub_app]
    exact type_e.tup _ _ _ _ (ih E1 targs tvs _ hh)
  case var =>
    rintro tenv E n t targs0 tvs0 rfl h1 h2 E1 targs tvs targs'
      ⟨h0, ha, hc, hv, hE, he, rfl, rfl⟩
    rw [(type_e_subst_lem7 (α := Unit) (β := Unit) (γ := Unit) (δ := Unit)).1 t (num_tvs E1)
      targs0 targs () ()]
    have hE2 : tenv_val_exp_ok tenvE2 := by
      have := tenv_val_exp_ok_db_merge _ _ hE
      exact (Aux.ok_bt _ _).1 this
    have hclosed : check_freevars targs0.length [] t →
        deBruijn_subst (targs0.length + num_tvs E1)
          (targs.map (deBruijn_inc 0 (targs0.length + num_tvs E1))) t = t := fun h =>
      nil_deBruijn_subst _ _ _ (check_freevars_add _ _ _ h _ (by omega))
    refine type_e.var _ _ _ _ _ _ (List.length_map _).symm ?_ ?_
    · rw [Aux.EVERY_map]
      rw [EVERY_iff_forall] at h1
      exact fun t ht => hcf _ _ _ _ h0 he (h1 t ht)
    · unfold lookup_var at h2 ⊢
      cases n with
      | Long mn id =>
        have h2 : nsLookup tenv.v (Long mn id) = some (targs0.length, t) := h2
        rw [hclosed (hv _ _ h2)]
        exact h2
      | Short x =>
        have hlE : ∀ E, lookup_varE (Short x) E = tveLookup x 0 E := fun _ => rfl
        rw [hlE] at h2 ⊢
        cases hl : tveLookup x 0 (db_merge E1 (bind_tvar targs.length tenvE2)) with
        | some p =>
          rw [hl] at h2
          cases h2
          rcases (tveLookup_db_merge_some _ _ _ _ _ _).1 hl with hl | ⟨hl1, hl2⟩
          · have := tveLookup_subst_some _ _ targs _ _ _ hl
            rw [(tveLookup_db_merge_some _ _ _ (bind_tvar tvs tenvE2) _ _).2 (Or.inl this)]
            simp only [Nat.add_zero]
          · rw [Aux.tveLookup_bt] at hl2
            have hcl := tveLookup_freevars _ _ _ _ _ ⟨hE2, h0, hl2⟩
            have hl3 : tveLookup x (num_tvs E1 + 0 + tvs) tenvE2 = some (targs0.length, t) :=
              (tveLookup_no_tvs _ _ _ _ _ ⟨hE2, h0⟩).2
                ((tveLookup_no_tvs _ _ _ _ _ ⟨hE2, h0⟩).1 hl2)
            rw [(tveLookup_db_merge_some x 0 (deBruijn_subst_tenvE targs E1)
              (bind_tvar tvs tenvE2) targs0.length t).2 (Or.inr
                ⟨(tveLookup_subst_none _ _ _ _).2 hl1, by
                  rw [Aux.tveLookup_bt, num_tvs_deBruijn_subst_tenvE]; exact hl3⟩)]
            rw [hclosed hcl]
        | none =>
          rw [hl] at h2
          have h2 : nsLookup tenv.v (Short x) = some (targs0.length, t) := h2
          obtain ⟨hl1, hl2⟩ := (tveLookup_db_merge_none _ _ _ _).1 hl
          rw [(tveLookup_db_merge_none x 0 (deBruijn_subst_tenvE targs E1)
            (bind_tvar tvs tenvE2)).2 ⟨(tveLookup_subst_none _ _ _ _).2 hl1, by
              rw [Aux.tveLookup_bt] at hl2 ⊢
              exact (tveLookup_inc_none _ _ _).2 ((tveLookup_inc_none _ _ _).1 hl2)⟩]
          rw [hclosed (hv _ _ h2)]
          exact h2
  case fn =>
    rintro tenv E n e t1 t2 h1 _ ih E1 targs tvs targs' ⟨h0, ha, hc, hv, hE, he, rfl, rfl⟩
    rw [show deBruijn_subst (num_tvs E1) (targs.map (deBruijn_inc 0 (num_tvs E1))) (Tfn t1 t2) =
      Tfn (deBruijn_subst (num_tvs E1) (targs.map (deBruijn_inc 0 (num_tvs E1))) t1)
        (deBruijn_subst (num_tvs E1) (targs.map (deBruijn_inc 0 (num_tvs E1))) t2)
      from Aux.sub_app]
    have := ih (Bind_name n 0 t1 E1) targs tvs _ ⟨h0, ha, hc, hv,
      ⟨by rw [Nat.zero_add]; exact h1, hE⟩, he, rfl, rfl⟩
    rw [Aux.merge_bind] at this
    exact type_e.fn _ _ _ _ _ _ (hcf _ _ _ _ h0 he h1) this
  case app =>
    rintro tenv E o es ts t _ h2 h3 ih E1 targs tvs targs' ⟨h0, ha, hc, hv, hE, he, rfl, rfl⟩
    exact type_e.app _ _ _ _ _ _ (ih E1 targs tvs _ ⟨h0, ha, hc, hv, hE, he, rfl, rfl⟩)
      (Aux.type_op_subst _ _ h2) (hcf _ _ _ _ h0 he h3)
  case log =>
    rintro tenv E l e1 e2 _ _ ih1 ih2 E1 targs tvs targs' hh
    have h1 := ih1 E1 targs tvs _ hh
    have h2 := ih2 E1 targs tvs _ hh
    rw [show deBruijn_subst (num_tvs E1) targs' Tbool = Tbool from Aux.sub_const] at h1 h2 ⊢
    exact type_e.log _ _ _ _ _ h1 h2
  case ite =>
    rintro tenv E e1 e2 e3 t _ _ _ ih1 ih2 ih3 E1 targs tvs targs' hh
    have h1 := ih1 E1 targs tvs _ hh
    rw [show deBruijn_subst (num_tvs E1) targs' Tbool = Tbool from Aux.sub_const] at h1
    exact type_e.if' _ _ _ _ _ _ h1 (ih2 E1 targs tvs _ hh) (ih3 E1 targs tvs _ hh)
  case mat =>
    rintro tenv E e pes t1 t2 bs _ h2 h3 h4 _ ih1 ih2 E1 targs tvs targs'
      ⟨h0, ha, hc, hv, hE, he, rfl, rfl⟩
    refine type_e.mat _ _ _ _ _ _ (fun pe => (bs pe).map (fun (x, t) => (x,
        deBruijn_subst (num_tvs E1) (targs.map (deBruijn_inc 0 (num_tvs E1))) t)))
      (ih1 E1 targs tvs _ ⟨h0, ha, hc, hv, hE, he, rfl, rfl⟩) h2 h3 (fun pe hpe => ?_)
      (fun pe hpe => ?_)
    · exact hpat E1 targs tvs tenv pe.1 _ _ h0 he ha hc (h4 pe hpe)
    · have := ih2 pe hpe (bind_var_list 0 (bs pe) E1) targs tvs _ ⟨h0, ha, hc, hv,
        tenv_val_exp_ok_bvl _ _ ⟨hE, (type_p_freevars.1 _ _ _ _ _ (h4 pe hpe)).2⟩, he,
        (db_merge_bvl _ _ _ _).symm, rfl⟩
      rw [Aux.merge_bvl, num_tvs_bind_var_list] at this
      exact this
  case letc =>
    rintro tenv E n e1 e2 t1 t2 h1 _ ih1 ih2 E1 targs tvs targs'
      ⟨h0, ha, hc, hv, hE, he, rfl, rfl⟩
    refine type_e.let' _ _ _ _ _ _ _ (ih1 E1 targs tvs _ ⟨h0, ha, hc, hv, hE, he, rfl, rfl⟩) ?_
    cases n with
    | none => exact ih2 E1 targs tvs _ ⟨h0, ha, hc, hv, hE, he, rfl, rfl⟩
    | some n =>
      have := ih2 (Bind_name n 0 t1 E1) targs tvs _ ⟨h0, ha, hc, hv,
        ⟨by rw [Nat.zero_add]; exact type_e_freevars.1 _ _ _ _ h1 ⟨hE, hv⟩, hE⟩, he, rfl, rfl⟩
      rw [Aux.merge_bind] at this
      exact this
  case letrec =>
    rintro tenv E funs e t b h1 _ ih1 ih2 E1 targs tvs targs' ⟨h0, ha, hc, hv, hE, he, rfl, rfl⟩
    have hok := tenv_val_exp_ok_bvl_funs _ _ _ _ () _ ⟨h1, hE⟩
    have a1 := ih1 (bind_var_list 0 b E1) targs tvs _ ⟨h0, ha, hc, hv, hok, he,
      (db_merge_bvl _ _ _ _).symm, rfl⟩
    have a2 := ih2 (bind_var_list 0 b E1) targs tvs _ ⟨h0, ha, hc, hv, hok, he,
      (db_merge_bvl _ _ _ _).symm, rfl⟩
    rw [Aux.merge_bvl, num_tvs_bind_var_list] at a1 a2
    exact type_e.letrec _ _ _ _ _ _ a1 a2
  case tannot =>
    rintro tenv E e t h1 h2 _ ih E1 targs tvs targs' hh
    have hcl := nil_deBruijn_subst (num_tvs E1) targs' _
      (check_freevars_type_name_subst [] t (num_tvs E1) tenv.t ⟨hh.2.1, h2, h1⟩)
    have := ih E1 targs tvs _ hh
    rw [hcl] at this ⊢
    exact type_e.tannot _ _ _ _ h1 h2 this
  case lannot =>
    rintro tenv E e l t _ ih E1 targs tvs targs' hh
    exact type_e.lannot _ _ _ _ _ (ih E1 targs tvs _ hh)
  case nil => rintro tenv E E1 targs tvs targs' -; exact type_es.nil _ _
  case cons =>
    rintro tenv E e es t ts _ _ ih1 ih2 E1 targs tvs targs' hh
    exact type_es.cons _ _ _ _ _ _ (ih1 E1 targs tvs _ hh) (ih2 E1 targs tvs _ hh)
  case fnil => rintro tenv E E1 targs tvs targs' -; exact type_funs.nil _ _
  case fcons =>
    rintro tenv E fn n e funs b t1 t2 h1 _ _ h4 ih1 ih2 E1 targs tvs targs'
      ⟨h0, ha, hc, hv, hE, he, rfl, rfl⟩
    have hT : deBruijn_subst (num_tvs E1) (targs.map (deBruijn_inc 0 (num_tvs E1))) (Tfn t1 t2) =
      Tfn (deBruijn_subst (num_tvs E1) (targs.map (deBruijn_inc 0 (num_tvs E1))) t1)
        (deBruijn_subst (num_tvs E1) (targs.map (deBruijn_inc 0 (num_tvs E1))) t2) := Aux.sub_app
    have h1' : check_freevars (num_tvs (db_merge E1 (bind_tvar targs.length tenvE2))) [] t1 :=
      Aux.cf_app.1 h1 t1 (by simp)
    have a1 := ih1 (Bind_name n 0 t1 E1) targs tvs _ ⟨h0, ha, hc, hv,
      ⟨by rw [Nat.zero_add]; exact h1', hE⟩, he, rfl, rfl⟩
    rw [Aux.merge_bind] at a1
    have a2 := ih2 E1 targs tvs _ ⟨h0, ha, hc, hv, hE, he, rfl, rfl⟩
    have a3 := hcf _ _ _ _ h0 he h1
    rw [hT] at a3
    simp only [List.map_cons]
    rw [hT]
    refine type_funs.cons _ _ _ _ _ _ _ _ _ a3 a1 a2 ?_
    rw [Aux.ALOOKUP_map_fst, h4]; rfl

/- HOL4:
Theorem type_funs_Tfn:
   ∀tenv tenvE funs bindings tvs t n.
    type_funs tenv tenvE funs bindings ∧
    ALOOKUP bindings n = SOME t
    ⇒
    ∃t1 t2. (t = Tfn t1 t2) ∧ check_freevars (num_tvs tenvE) [] (Tfn t1 t2) -/
theorem type_funs_Tfn {α : Type} :
    ∀ (tenv : type_env) (tenvE : tenv_val_exp) (funs : List (varN × varN × exp))
      (bindings : List (varN × typ)) (tvs : α) (t : typ) (n : varN),
      type_funs tenv tenvE funs bindings ∧
      ALOOKUP bindings n = some t →
      ∃ t1 t2 : typ, t = Tfn t1 t2 ∧ check_freevars (num_tvs tenvE) [] (Tfn t1 t2) := by
  rintro tenv tenvE funs b _ t n ⟨h, hl⟩
  obtain ⟨t1, t2, rfl, hc⟩ := Aux.type_funs_mem h n t (Aux.ALOOKUP_mem hl)
  exact ⟨t1, t2, rfl, hc⟩

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
      type_funs tenv tenvE funs bindings →
      ∃ t : typ, ALOOKUP bindings fn = some t := by
  rintro fn tenvE funs b n e tenv ⟨hm, h⟩
  cases hl : ALOOKUP b fn with
  | some t => exact ⟨t, rfl⟩
  | none =>
    rw [Aux.ALOOKUP_eq_none, Aux.type_funs_fst h] at hl
    exact absurd (List.mem_map.2 ⟨_, hm, rfl⟩) hl

/- HOL4:
Theorem type_funs_find_recfun:
 ∀fn env funs bindings e tenv tenvE t.
  ALOOKUP bindings fn = SOME t ∧
  type_funs tenv tenvE funs bindings
  ⇒
  (∃n e. find_recfun fn funs = SOME (n,e)) -/
theorem type_funs_find_recfun {α β : Type} :
    ∀ (fn : varN) (env : α) (funs : List (varN × varN × exp)) (bindings : List (varN × typ))
      (e : β) (tenv : type_env) (tenvE : tenv_val_exp) (t : typ),
      ALOOKUP bindings fn = some t ∧
      type_funs tenv tenvE funs bindings →
      ∃ (n : varN) (e : exp), find_recfun fn funs = some (n, e) := by
  rintro fn _ funs b _ tenv tenvE t ⟨hl, h⟩
  induction funs generalizing b with
  | nil => cases h; simp [ALOOKUP] at hl
  | cons f funs ih =>
    cases h with
    | cons _ f n e funs b t1 t2 h1 h2 h3 h4 =>
      simp only [find_recfun]
      simp only [ALOOKUP] at hl
      split
      · exact ⟨n, e, rfl⟩
      · rename_i hf
        rw [if_neg hf] at hl
        exact ih b hl h3

/- HOL4:
Theorem type_recfun_lookup:
   ∀fn funs n e tenv tenvE bindings tvs t1 t2.
    find_recfun fn funs = SOME (n,e) ∧
    type_funs tenv tenvE funs bindings ∧
    ALOOKUP bindings fn = SOME (Tfn t1 t2)
    ⇒
    type_e tenv (Bind_name n 0 t1 tenvE) e t2 ∧
    check_freevars (num_tvs tenvE) [] (Tfn t1 t2) -/
theorem type_recfun_lookup {α : Type} :
    ∀ (fn : varN) (funs : List (varN × varN × exp)) (n : varN) (e : exp) (tenv : type_env)
      (tenvE : tenv_val_exp) (bindings : List (varN × typ)) (tvs : α) (t1 t2 : typ),
      find_recfun fn funs = some (n, e) ∧
      type_funs tenv tenvE funs bindings ∧
      ALOOKUP bindings fn = some (Tfn t1 t2) →
      type_e tenv (Bind_name n 0 t1 tenvE) e t2 ∧
      check_freevars (num_tvs tenvE) [] (Tfn t1 t2) := by
  rintro fn funs n e tenv tenvE b _ t1 t2 ⟨hf, h, hl⟩
  induction funs generalizing b with
  | nil => simp [find_recfun] at hf
  | cons f funs ih =>
    cases h with
    | cons _ f n' e' funs b t1' t2' h1 h2 h3 h4 =>
      simp only [find_recfun] at hf
      simp only [ALOOKUP] at hl
      split at hf
      · rename_i hfn
        rw [if_pos hfn] at hl
        cases hf
        simp only [Option.some.injEq, Tfn, typ.Tapp.injEq, List.cons.injEq, and_true] at hl
        obtain ⟨rfl, rfl⟩ := hl
        exact ⟨h2, h1⟩
      · rename_i hfn
        rw [if_neg hfn] at hl
        exact ih b hf h3 hl

/- HOL4:
Theorem type_funs_distinct:
 ∀tenv tenvE funs bindings .
  type_funs tenv tenvE funs bindings
  ⇒
  ALL_DISTINCT (MAP (λ(x,y,z). x) funs) -/
theorem type_funs_distinct :
    ∀ (tenv : type_env) (tenvE : tenv_val_exp) (funs : List (varN × varN × exp))
      (bindings : List (varN × typ)),
      type_funs tenv tenvE funs bindings →
      ALL_DISTINCT (funs.map (fun (x, _, _) => x)) := by
  intro tenv tenvE funs b h
  show ALL_DISTINCT (funs.map Prod.fst)
  induction funs generalizing b with
  | nil => trivial
  | cons f funs ih =>
    cases h with
    | cons _ f n' e' funs b t1' t2' h1 h2 h3 h4 =>
      refine ⟨?_, ih _ h3⟩
      rw [Aux.ALOOKUP_eq_none, Aux.type_funs_fst h3] at h4
      exact h4

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
  type_e tenv (Bind_name x 0 (deBruijn_subst 0 targs t1) (bind_tvar tvs tenvE)) e (deBruijn_subst 0 targs t) -/
theorem type_e_subst_lem {α : Type} (x : varN) (t1 : typ) :
    ∀ (tenv : type_env) (tenvE : tenv_val_exp) (e : exp) (t : typ) (targs : List typ) (tvs : Nat)
      (targs' : α),
      type_e tenv (Bind_name x 0 t1 (bind_tvar targs.length tenvE)) e t ∧
      num_tvs tenvE = 0 ∧
      tenv_abbrev_ok tenv.t ∧
      tenv_ctor_ok tenv.c ∧
      tenv_val_ok tenv.v ∧
      tenv_val_exp_ok (bind_tvar targs.length tenvE) ∧
      EVERY (check_freevars tvs []) targs ∧
      check_freevars targs.length [] t1 →
      type_e tenv (Bind_name x 0 (deBruijn_subst 0 targs t1) (bind_tvar tvs tenvE)) e
        (deBruijn_subst 0 targs t) := by
  rintro tenv tenvE e t targs tvs _ ⟨h, h0, ha, hc, hv, hE, he, ht⟩
  have := (type_e_subst tenvE).1 _ _ _ _ h (Bind_name x 0 t1 tenv_val_exp.Empty) targs tvs _
    ⟨h0, ha, hc, hv, ⟨by rw [Aux.num_tvs_bt, h0, Nat.zero_add]; exact ht, hE⟩, he, rfl, rfl⟩
  rw [Aux.merge_bind] at this
  simp only [num_tvs, deBruijn_subst_tenvE, db_merge, deBruijn_inc0.2] at this
  exact this

theorem Aux.mem_tdc {α β γ : Type} {tenvT : Namespace mlstring mlstring (List mlstring × typ)}
    {next : Nat} {tds : List (α × β × List (conN × List ast_t))} {ids : List γ}
    {stamp : CmlTS.stamp} {x : α × List typ × γ}
    (h : (stamp, x) ∈ type_def_to_ctMap tenvT next tds ids) (hl : tds.length = ids.length) :
    ∃ (j : Nat) (td : α × β × List (conN × List ast_t)) (id : γ) (cn : conN) (ts : List ast_t),
      tds[j]? = some td ∧ ids[j]? = some id ∧ (cn, ts) ∈ td.2.2 ∧
      stamp = TypeStamp cn (next + j) ∧ x = (td.1, ts.map (type_name_subst tenvT), id) := by
  induction tds generalizing next ids with
  | nil =>
    cases ids with
    | nil => simp [type_def_to_ctMap] at h
    | cons id ids => simp at hl
  | cons td tds ih =>
    obtain ⟨tvs, tn, ctors⟩ := td
    cases ids with
    | nil => simp at hl
    | cons id ids =>
      rw [type_def_to_ctMap] at h
      rcases List.mem_append.1 h with h | h
      · obtain ⟨j, td, id', cn, ts, h1, h2, h3, h4, h5⟩ := ih h (by simpa using hl)
        refine ⟨j + 1, td, id', cn, ts, by simpa using h1, by simpa using h2, h3, ?_, h5⟩
        rw [h4]; congr 1; omega
      · rw [List.mem_reverse, List.mem_map] at h
        obtain ⟨⟨cn, ts⟩, hm, he⟩ := h
        cases he
        exact ⟨0, (tvs, tn, ctors), id, cn, ts, rfl, rfl, hm, rfl, rfl⟩

/- HOL4:
Theorem mem_type_def_to_ctMap:
   !tenvT next tds ids stamp x.
    MEM (stamp,x) (type_def_to_ctMap tenvT next tds ids) ∧
    LENGTH tds = LENGTH ids
    ⇒
    ?cn i. stamp = TypeStamp cn i ∧ next ≤ i ∧ i < next + LENGTH tds -/
theorem mem_type_def_to_ctMap {α β γ : Type} :
    ∀ (tenvT : Namespace mlstring mlstring (List mlstring × typ)) (next : Nat)
      (tds : List (α × β × List (conN × List ast_t))) (ids : List γ) (stamp : CmlTS.stamp)
      (x : α × List typ × γ),
      (stamp, x) ∈ type_def_to_ctMap tenvT next tds ids ∧
      tds.length = ids.length →
      ∃ (cn : conN) (i : Nat), stamp = TypeStamp cn i ∧ next ≤ i ∧ i < next + tds.length := by
  rintro tenvT next tds ids stamp x ⟨h, hl⟩
  obtain ⟨j, td, id', cn, ts, h1, h2, h3, h4, h5⟩ := Aux.mem_tdc h hl
  have := (List.getElem?_eq_some_iff.1 h1).1
  exact ⟨cn, next + j, h4, by omega, by omega⟩

theorem Aux.FUNION_some {α β : Type} {f g : fmap α β} {x : α} {v : β}
    (h : FLOOKUP (FUNION f g) x = some v) : FLOOKUP f x = some v ∨ FLOOKUP g x = some v := by
  rw [Aux.FLOOKUP_FUNION] at h
  split at h
  · rename_i w hw; cases h; exact Or.inl hw
  · exact Or.inr h

/- HOL4:
Theorem ctMap_ok_merge_imp:
   !ctMap1 ctMap2.
    DISJOINT (FRANGE ((SND o SND) o_f ctMap1)) (FRANGE ((SND o SND) o_f ctMap2)) ∧
    ctMap_ok ctMap1 ∧ ctMap_ok ctMap2 ⇒
    ctMap_ok (FUNION ctMap1 ctMap2) -/
theorem ctMap_ok_merge_imp :
    ∀ (ctMap1 ctMap2 : ctMap_ty),
      DISJOINT (FRANGE (o_f (Prod.snd ∘ Prod.snd) ctMap1))
        (FRANGE (o_f (Prod.snd ∘ Prod.snd) ctMap2)) ∧
      ctMap_ok ctMap1 ∧ ctMap_ok ctMap2 →
      ctMap_ok (FUNION ctMap1 ctMap2) := by
  rintro m1 m2 ⟨hd, ⟨a1, a2, a3, a4⟩, ⟨b1, b2, b3, b4⟩⟩
  rw [Aux.disjoint_iff] at hd
  have hcross : ∀ s1 tvs1 ts1 ti s2 tvs2 ts2, FLOOKUP m1 s1 = some (tvs1, ts1, ti) →
      FLOOKUP m2 s2 = some (tvs2, ts2, ti) → False := by
    intro s1 tvs1 ts1 ti s2 tvs2 ts2 h1 h2
    exact hd ti ⟨s1, by rw [Aux.FLOOKUP_o_f, h1]; rfl⟩ ⟨s2, by rw [Aux.FLOOKUP_o_f, h2]; rfl⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x y h
    rcases Aux.FUNION_some h with h | h
    · exact a1 x y h
    · exact b1 x y h
  · intro ex tvs ts ti h
    rcases Aux.FUNION_some h with h | h
    · exact a2 _ _ _ _ h
    · exact b2 _ _ _ _ h
  · intro cn x tvs ts ti h
    rcases Aux.FUNION_some h with h | h
    · exact a3 _ _ _ _ _ h
    · exact b3 _ _ _ _ _ h
  · rintro s1 tvs1 ts1 ti s2 tvs2 ts2 ⟨h1, h2⟩
    rcases Aux.FUNION_some h1 with h1 | h1 <;> rcases Aux.FUNION_some h2 with h2 | h2
    · exact a4 _ _ _ _ _ _ _ ⟨h1, h2⟩
    · exact (hcross _ _ _ _ _ _ _ h1 h2).elim
    · exact (hcross _ _ _ _ _ _ _ h2 h1).elim
    · exact b4 _ _ _ _ _ _ _ ⟨h1, h2⟩

/- HOL4:
Theorem ctMap_ok_lookup:
 !ctMap cn tvs ts ti tn.
  ctMap_ok ctMap ∧ (FLOOKUP ctMap tn = SOME (tvs,ts,ti))
  ⇒
  EVERY (check_freevars 0 tvs) ts -/
theorem ctMap_ok_lookup {α : Type} :
    ∀ (ctMap : ctMap_ty) (cn : α) (tvs : List tvarN) (ts : List typ) (ti : type_ident)
      (tn : stamp),
      ctMap_ok ctMap ∧ FLOOKUP ctMap tn = some (tvs, ts, ti) →
      EVERY (check_freevars 0 tvs) ts := by
  rintro ctMap _ tvs ts ti tn ⟨h, hl⟩
  exact h.1 tn (tvs, ts, ti) hl

/- HOL4:
Theorem type_def_to_ctMap_mem:
   !tenvT next tds tids.
    ALOOKUP (type_def_to_ctMap tenvT next tds tids) k = SOME x ∧
    LENGTH tds = LENGTH tids
    ⇒
    MEM (SND (SND x)) tids -/
theorem type_def_to_ctMap_mem {α β γ : Type} (k : stamp) (x : α × List typ × γ) :
    ∀ (tenvT : Namespace mlstring mlstring (List mlstring × typ)) (next : Nat)
      (tds : List (α × β × List (conN × List ast_t))) (tids : List γ),
      ALOOKUP (type_def_to_ctMap tenvT next tds tids) k = some x ∧
      tds.length = tids.length →
      x.2.2 ∈ tids := by
  rintro tenvT next tds tids ⟨h, hl⟩
  obtain ⟨j, td, id', cn, ts, h1, h2, h3, h4, rfl⟩ := Aux.mem_tdc (Aux.ALOOKUP_mem h) hl
  exact List.mem_of_getElem? h2

/- HOL4:
Theorem fupdate2_union[local]:
  !m a1 a2. m |++ a1 |++ a2 = FEMPTY |++ a2 ⊌ (m |++ a1) -/
theorem fupdate2_union {α β : Type} :
    ∀ (m : fmap α β) (a1 a2 : List (α × β)),
      FUPDATE_LIST (FUPDATE_LIST m a1) a2 =
        FUNION (FUPDATE_LIST FEMPTY a2) (FUPDATE_LIST m a1) := by
  intro m a1 a2
  refine Aux.fmap_ext fun x => ?_
  rw [Aux.FLOOKUP_FUNION, Aux.FLOOKUP_FUPDATE_LIST, Aux.FLOOKUP_FUPDATE_LIST (f := FEMPTY)]
  cases ALOOKUP a2.reverse x <;> rfl

theorem Aux.check_ctor_tenv_mem {tenvT : Namespace modN typeN (List tvarN × typ)}
    {tds : List (List tvarN × mlstring × List (conN × List ast_t))}
    (h : check_ctor_tenv tenvT tds) {td : List tvarN × mlstring × List (conN × List ast_t)}
    (htd : td ∈ tds) {cn : conN} {ts : List ast_t} (hm : (cn, ts) ∈ td.2.2) :
    ∀ t, t ∈ ts → check_freevars_ast td.1 t ∧ check_type_names tenvT t := by
  induction tds with
  | nil => cases htd
  | cons td' tds ih =>
    obtain ⟨tvs, tn, ctors⟩ := td'
    obtain ⟨_, _, h3, _, h5⟩ := h
    rcases List.mem_cons.1 htd with rfl | htd
    · rw [EVERY_iff_forall] at h3
      obtain ⟨a, b⟩ := h3 (cn, ts) hm
      rw [EVERY_iff_forall] at a b
      exact fun t ht => ⟨a t ht, b t ht⟩
    · exact ih h5 htd

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
      (tds : List (List tvarN × mlstring × List (conN × List ast_t)))
      (tids : List type_ident),
      ALL_DISTINCT tids ∧
      DISJOINT (LIST_TO_SET tids) (LIST_TO_SET prim_type_nums) ∧
      tds.length = tids.length ∧
      check_ctor_tenv tenvT tds ∧
      tenv_abbrev_ok tenvT →
      ctMap_ok (FUPDATE_LIST FEMPTY (type_def_to_ctMap tenvT next tds tids).reverse) := by
  rintro tenvT next tds tids ⟨hd, hdis, hl, hc, ha⟩
  rw [Aux.disjoint_iff] at hdis
  rw [Aux.ALL_DISTINCT_iff] at hd
  have hmem : ∀ s x, FLOOKUP (FUPDATE_LIST FEMPTY
      (type_def_to_ctMap tenvT next tds tids).reverse) s = some x →
      (s, x) ∈ type_def_to_ctMap tenvT next tds tids := by
    intro s x h
    rw [Aux.FUPDATE_LIST_reverse, Aux.FLOOKUP_alist_to_fmap] at h
    exact Aux.ALOOKUP_mem h
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s x h
    obtain ⟨j, td, id', cn, ts, h1, h2, h3, h4, rfl⟩ := Aux.mem_tdc (hmem _ _ h) hl
    show EVERY (check_freevars 0 td.1) (ts.map (type_name_subst tenvT))
    rw [Aux.EVERY_map]
    intro t ht
    obtain ⟨b1, b2⟩ := Aux.check_ctor_tenv_mem hc (List.mem_of_getElem? h1) h3 t ht
    exact check_freevars_type_name_subst _ _ _ _ ⟨ha, b2, b1⟩
  · intro ex tvs ts ti h
    obtain ⟨j, td, id', cn, ts, h1, h2, h3, h4, h5⟩ := Aux.mem_tdc (hmem _ _ h) hl
    cases h4
  · intro cn x tvs ts ti h hti
    obtain ⟨j, td, id', cn, ts, h1, h2, h3, h4, h5⟩ := Aux.mem_tdc (hmem _ _ h) hl
    cases h5
    exact hdis _ (List.mem_of_getElem? h2) hti
  · rintro s1 tvs1 ts1 ti s2 tvs2 ts2 ⟨h, h'⟩
    obtain ⟨j, td, id', cn, ts, h1, h2, h3, rfl, h5⟩ := Aux.mem_tdc (hmem _ _ h) hl
    obtain ⟨j', td', id'', cn', ts', h1', h2', h3', rfl, h5'⟩ := Aux.mem_tdc (hmem _ _ h') hl
    cases h5
    cases h5'
    have : j = j' := List.getElem?_inj (List.getElem?_eq_some_iff.1 h2).1 hd (h2.trans h2'.symm)
    subst this
    rfl

/- HOL4:
Theorem nsLookup_add_tenvE1:
   !tenvE tenvV n tvs t tvs2.
    check_freevars tvs2 [] t ∧
    tveLookup n tvs tenvE = SOME (tvs2,t) ⇒
    nsLookup (add_tenvE tenvE tenvV) (Short n) = SOME (tvs2,t) -/
theorem nsLookup_add_tenvE1 {m : Type} :
    ∀ (tenvE : tenv_val_exp) (tenvV : Namespace m varN (Nat × typ)) (n : varN) (tvs : Nat)
      (t : typ) (tvs2 : Nat),
      check_freevars tvs2 [] t ∧
      tveLookup n tvs tenvE = some (tvs2, t) →
      nsLookup (add_tenvE tenvE tenvV) (Short n) = some (tvs2, t) := by
  rintro tenvE tenvV n tvs t tvs2 ⟨hc, hl⟩
  induction tenvE generalizing tvs with
  | Empty => simp [tveLookup] at hl
  | Bind_tvar k e ih => exact ih _ hl
  | Bind_name x k t0 e ih =>
    simp only [tveLookup] at hl
    simp only [add_tenvE]
    rw [Aux.nsLookup_nsBind_if]
    split at hl
    · rename_i hx
      cases hl
      rw [if_pos (by rw [hx]), nil_deBruijn_inc _ _ _ (Or.inr hc)]
    · rename_i hx
      rw [if_neg (by simp only [ident.Short.injEq]; exact fun h => hx h.symm)]
      exact ih _ hl

/- HOL4:
Theorem nsLookup_add_tenvE2:
   !tenvE tenvV n tvs t tvs2.
    tveLookup n tvs tenvE = NONE ∧
    nsLookup tenvV (Short n) = SOME (tvs2,t) ⇒
    nsLookup (add_tenvE tenvE tenvV) (Short n) = SOME (tvs2,t) -/
theorem nsLookup_add_tenvE2 {m : Type} :
    ∀ (tenvE : tenv_val_exp) (tenvV : Namespace m varN (Nat × typ)) (n : varN) (tvs : Nat)
      (t : typ) (tvs2 : Nat),
      tveLookup n tvs tenvE = none ∧
      nsLookup tenvV (Short n) = some (tvs2, t) →
      nsLookup (add_tenvE tenvE tenvV) (Short n) = some (tvs2, t) := by
  rintro tenvE tenvV n tvs t tvs2 ⟨hl, hv⟩
  induction tenvE generalizing tvs with
  | Empty => exact hv
  | Bind_tvar k e ih => exact ih _ hl
  | Bind_name x k t0 e ih =>
    simp only [tveLookup] at hl
    simp only [add_tenvE]
    rw [Aux.nsLookup_nsBind_if]
    split at hl
    · cases hl
    · rename_i hx
      rw [if_neg (by simp only [ident.Short.injEq]; exact fun h => hx h.symm)]
      exact ih _ hl

/- HOL4:
Theorem nsLookup_add_tenvE3:
   !tenvE tenvV n t tvs2 mn.
    nsLookup tenvV (Long mn n) = SOME (tvs2,t) ⇒
    nsLookup (add_tenvE tenvE tenvV) (Long mn n) = SOME (tvs2,t) -/
theorem nsLookup_add_tenvE3 {m : Type} :
    ∀ (tenvE : tenv_val_exp) (tenvV : Namespace m varN (Nat × typ)) (n : ident m varN)
      (t : typ) (tvs2 : Nat) (mn : m),
      nsLookup tenvV (Long mn n) = some (tvs2, t) →
      nsLookup (add_tenvE tenvE tenvV) (Long mn n) = some (tvs2, t) := by
  intro tenvE tenvV n t tvs2 mn hv
  induction tenvE with
  | Empty => exact hv
  | Bind_tvar k e ih => exact ih
  | Bind_name x k t0 e ih =>
    simp only [add_tenvE]
    rw [Aux.nsLookup_nsBind_if, if_neg (by simp)]
    exact ih

/- HOL4:
Theorem add_tenvE_bvl:
   !n bindings tenvE tenvV.
    add_tenvE (bind_var_list n bindings tenvE) tenvV =
    nsBindList (MAP (\(x,t). (x, (n, t))) bindings) (add_tenvE tenvE tenvV) -/
theorem add_tenvE_bvl {m : Type} :
    ∀ (n : Nat) (bindings : List (mlstring × typ)) (tenvE : tenv_val_exp)
      (tenvV : Namespace m varN (Nat × typ)),
      add_tenvE (bind_var_list n bindings tenvE) tenvV =
        nsBindList (bindings.map (fun (x, t) => (x, (n, t)))) (add_tenvE tenvE tenvV) := by
  intro n b tenvE tenvV
  induction b with
  | nil => rfl
  | cons p b ih =>
    obtain ⟨x, t⟩ := p
    simp only [bind_var_list, add_tenvE, ih]
    rfl

/- HOL4:
Theorem type_v_freevars:
 !tvs tenvC tenvS v t. type_v tvs tenvC tenvS v t ⇒ check_freevars tvs [] t -/
theorem type_v_freevars :
    ∀ (tvs : Nat) (tenvC : ctMap_ty) (tenvS : tenv_store) (v : value) (t : typ),
      type_v tvs tenvC tenvS v t → check_freevars tvs [] t := by
  have hc : ∀ n ti, check_freevars n [] (Tapp [] ti) := fun tvs ti => Aux.cf_app.2 (by simp)
  have h1 : ∀ n ti t, check_freevars n [] t → check_freevars n [] (Tapp [t] ti) := by
    intro n ti t h
    refine Aux.cf_app.2 fun t' ht => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rw [ht]; exact h
  intro tvs tenvC tenvS v t h
  induction h with
  | intLit => exact hc _ _
  | char => exact hc _ _
  | strLit => exact hc _ _
  | word8 => exact hc _ _
  | word64 => exact hc _ _
  | float64 => exact hc _ _
  | conv _ _ _ _ _ _ ts' _ _ h => exact Aux.cf_app.2 (EVERY_iff_forall.1 h)
  | tup tvs ctMap tenvS vs ts hl _ ih =>
    refine Aux.cf_app.2 fun t ht => ?_
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 ht
    have hlt := (List.getElem?_eq_some_iff.1 hi).1
    exact ih i _ t (List.getElem?_eq_getElem (by omega)) hi
  | closure tvs ctMap tenvS env tenv tenvE n e t1 t2 ho hE h0 _ _ _ ht1 he _ =>
    refine Aux.cf_app.2 fun t ht => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    have hn : num_tvs (bind_tvar tvs tenvE) = tvs := by
      rw [Aux.num_tvs_bt, h0]; rfl
    rcases ht with rfl | rfl
    · exact ht1
    · have := type_e_freevars.1 _ _ _ _ he
        ⟨⟨by rw [hn, Nat.zero_add]; exact ht1, (Aux.ok_bt _ _).2 hE⟩, ho.1⟩
      simp only [num_tvs] at this
      rw [hn] at this
      exact this
  | recclosure tvs ctMap tenvS env funs n t tenv tenvE b ho hE h0 _ _ _ hf hl _ _ _ =>
    obtain ⟨t1, t2, rfl, hc⟩ := type_funs_Tfn _ _ _ _ () _ _ ⟨hf, hl⟩
    rw [num_tvs_bind_var_list, Aux.num_tvs_bt, h0] at hc
    exact hc
  | ref tvs ctMap tenvS n t h _ =>
    exact h1 _ _ _ (check_freevars_add _ _ _ h _ (by omega))
  | w8array => exact hc _ _
  | varray tvs ctMap tenvS n t h _ =>
    exact h1 _ _ _ (check_freevars_add _ _ _ h _ (by omega))
  | vector tvs ctMap tenvS vs t h _ _ =>
    exact h1 _ _ _ (check_freevars_add _ _ _ h _ (by omega))

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
(named `type_subst_thm` because `type_subst` is a constant) -/
theorem type_subst_thm (targs : List typ) (tvs' : Nat) :
    ∀ (tvs : Nat) (ctMap : ctMap_ty) (tenvS : tenv_store) (v : value) (t : typ),
      type_v tvs ctMap tenvS v t →
      tvs = targs.length ∧
      ctMap_ok ctMap ∧
      EVERY (check_freevars tvs' []) targs ∧
      check_freevars targs.length [] t →
      type_v tvs' ctMap tenvS v (deBruijn_subst 0 targs t) := by
  intro tvs ctMap tenvS v t h
  have hcl : ∀ t, check_freevars 0 [] t → deBruijn_subst 0 targs t = t :=
    fun t h => nil_deBruijn_subst 0 targs t h
  induction h with
  | intLit =>
    intro _
    rw [show deBruijn_subst 0 targs Tint = Tint from Aux.sub_const]
    exact type_v.intLit _ _ _ _
  | char =>
    intro _
    rw [show deBruijn_subst 0 targs Tchar = Tchar from Aux.sub_const]
    exact type_v.char _ _ _ _
  | strLit =>
    intro _
    rw [show deBruijn_subst 0 targs Tstring = Tstring from Aux.sub_const]
    exact type_v.strLit _ _ _ _
  | word8 =>
    intro _
    rw [show deBruijn_subst 0 targs Tword8 = Tword8 from Aux.sub_const]
    exact type_v.word8 _ _ _ _
  | word64 =>
    intro _
    rw [show deBruijn_subst 0 targs Tword64 = Tword64 from Aux.sub_const]
    exact type_v.word64 _ _ _ _
  | float64 =>
    intro _
    rw [show deBruijn_subst 0 targs Tdouble = Tdouble from Aux.sub_const]
    exact type_v.float64 _ _ _ _
  | conv tvs ctMap tenvS vs tvs0 stamp ts' ts ti h1 h2 h3 h4 h5 ih =>
    rintro ⟨rfl, hct, he, _⟩
    rw [Aux.sub_app]
    have hok := EVERY_iff_forall.1 (ctMap_ok_lookup ctMap () _ _ _ _ ⟨hct, h5⟩)
    refine type_v.conv _ _ _ _ tvs0 _ _ ts _ ?_ (by simpa using h2) (by simpa using h3) ?_ h5
    · rw [Aux.EVERY_map]
      rw [EVERY_iff_forall] at h1
      exact fun t ht => deBruijn_subst_check_freevars2 _ _ _ _ () () ⟨h1 t ht, he⟩
    · intro i v t hv ht
      rw [Aux.FUPDATE_LIST_reverse, List.getElem?_map, Option.map_eq_some_iff] at ht
      obtain ⟨t0, ht0, rfl⟩ := ht
      have hcomm := Aux.type_subst_comm (deBruijn_subst 0 targs) (fun _ _ => Aux.sub_app) h2 t0
        (hok t0 (List.mem_of_getElem? ht0))
      have hi : (ts.map (type_subst (FUPDATE_LIST FEMPTY (tvs0.zip ts').reverse)))[i]? =
          some (type_subst (alist_to_fmap (tvs0.zip ts')) t0) := by
        rw [Aux.FUPDATE_LIST_reverse, List.getElem?_map, ht0]; rfl
      have := ih i v _ hv hi ⟨rfl, hct, he, type_v_freevars _ _ _ _ _ (h4 i v _ hv hi)⟩
      rw [hcomm] at this
      exact this
  | tup tvs ctMap tenvS vs ts h1 h2 ih =>
    rintro ⟨rfl, hct, he, _⟩
    rw [show deBruijn_subst 0 targs (Ttup ts) = Ttup (ts.map (deBruijn_subst 0 targs))
      from Aux.sub_app]
    refine type_v.tup _ _ _ _ _ (by simpa using h1) ?_
    intro i v t hv ht
    rw [List.getElem?_map, Option.map_eq_some_iff] at ht
    obtain ⟨t0, ht0, rfl⟩ := ht
    exact ih i v t0 hv ht0 ⟨rfl, hct, he, type_v_freevars _ _ _ _ _ (h2 i v t0 hv ht0)⟩
  | closure tvs ctMap tenvS env tenv tenvE n e t1 t2 ho hE h0 hc hv1 hv2 ht1 hte _ =>
    rintro ⟨rfl, hct, he, hfv⟩
    rw [show deBruijn_subst 0 targs (Tfn t1 t2) =
      Tfn (deBruijn_subst 0 targs t1) (deBruijn_subst 0 targs t2) from Aux.sub_app]
    refine type_v.closure _ _ _ _ tenv tenvE _ _ _ _ ho hE h0 hc hv1 hv2 ?_ ?_
    · exact deBruijn_subst_check_freevars2 _ _ _ _ () () ⟨ht1, he⟩
    · exact type_e_subst_lem n t1 tenv tenvE e t2 targs tvs' () ⟨hte, h0, ho.2.2, ho.2.1, ho.1,
        (Aux.ok_bt _ _).2 hE, he, ht1⟩
  | recclosure tvs ctMap tenvS env funs n t tenv tenvE b ho hE h0 hc hv1 hv2 hf hl hd hm _ =>
    rintro ⟨rfl, hct, he, hfv⟩
    refine type_v.recclosure _ _ _ _ _ _ _ tenv tenvE
      (b.map (fun (x, t) => (x, deBruijn_subst 0 targs t))) ho hE h0 hc hv1 hv2 ?_ ?_ hd hm
    · have := (type_e_subst tenvE).2.2 _ _ _ _ hf (bind_var_list 0 b tenv_val_exp.Empty) targs
        tvs' _ ⟨h0, ho.2.2, ho.2.1, ho.1,
          tenv_val_exp_ok_bvl_funs _ _ _ _ () _ ⟨hf, (Aux.ok_bt _ _).2 hE⟩, he,
          by rw [db_merge_bvl]; rfl, rfl⟩
      rw [Aux.merge_bvl] at this
      simp only [num_tvs_bind_var_list, num_tvs, deBruijn_subst_tenvE, db_merge,
        deBruijn_inc0.2] at this
      exact this
    · rw [Aux.ALOOKUP_map_fst, hl]; rfl
  | ref tvs ctMap tenvS n t h1 h2 =>
    intro _
    rw [show deBruijn_subst 0 targs (Tref t) = Tref (deBruijn_subst 0 targs t) from Aux.sub_app,
      hcl t h1]
    exact type_v.ref _ _ _ _ _ h1 h2
  | w8array tvs ctMap tenvS n h =>
    intro _
    rw [show deBruijn_subst 0 targs Tword8array = Tword8array from Aux.sub_const]
    exact type_v.w8array _ _ _ _ h
  | varray tvs ctMap tenvS n t h1 h2 =>
    intro _
    rw [show deBruijn_subst 0 targs (Tarray t) = Tarray (deBruijn_subst 0 targs t)
      from Aux.sub_app, hcl t h1]
    exact type_v.varray _ _ _ _ _ h1 h2
  | vector tvs ctMap tenvS vs t h1 h2 ih =>
    rintro ⟨rfl, hct, he, _⟩
    rw [show deBruijn_subst 0 targs (Tvector t) = Tvector (deBruijn_subst 0 targs t)
      from Aux.sub_app, hcl t h1]
    refine type_v.vector _ _ _ _ _ h1 fun v hv => ?_
    have := ih v hv ⟨rfl, hct, he, check_freevars_add _ _ _ h1 _ (by omega)⟩
    rw [hcl t h1] at this
    exact this

/- HOL4:
Theorem check_ctor_tenv_ok:
 !tenvT tds tis.
 LENGTH tds = LENGTH tis ∧
 check_ctor_tenv tenvT tds ∧
 tenv_abbrev_ok tenvT
 ⇒
 tenv_ctor_ok (build_ctor_tenv tenvT tds tis) -/
theorem check_ctor_tenv_ok :
    ∀ {m δ : Type} (tenvT : Namespace modN typeN (List tvarN × typ))
      (tds : List (List tvarN × mlstring × List (conN × List ast_t)))
      (tis : List δ),
      tds.length = tis.length ∧
      check_ctor_tenv tenvT tds ∧
      tenv_abbrev_ok tenvT →
      tenv_ctor_ok (build_ctor_tenv tenvT tds tis : Namespace m conN (List tvarN × List typ × δ)) := by
  rintro m δ tenvT tds tis ⟨hl, hc, ha⟩
  induction tds generalizing tis with
  | nil =>
    cases tis with
    | nil => exact nsAll_nsEmpty _
    | cons id tis => simp at hl
  | cons td tds ih =>
    have hm := fun (cn : conN) (ts : List ast_t) =>
      Aux.check_ctor_tenv_mem (cn := cn) (ts := ts) hc (td := td) List.mem_cons_self
    obtain ⟨tvs, tn, ctors⟩ := td
    cases tis with
    | nil => simp at hl
    | cons id tis =>
      rw [build_ctor_tenv]
      refine nsAll_nsAppend _ _ _ ⟨ih tis (by simpa using hl) hc.2.2.2.2, ?_⟩
      refine nsAll_alist_to_ns _ _ ?_
      rw [EVERY_iff_forall]
      rintro ⟨n, x⟩ hx
      rw [List.mem_reverse, List.mem_map] at hx
      obtain ⟨⟨cn, ts⟩, hcn, he⟩ := hx
      cases he
      show EVERY (check_freevars 0 tvs) (ts.map (type_name_subst tenvT))
      rw [Aux.EVERY_map]
      intro t ht
      obtain ⟨b1, b2⟩ := hm _ ts hcn t ht
      exact check_freevars_type_name_subst _ _ _ _ ⟨ha, b2, b1⟩

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
    (∀ (check : Bool) (tenv : type_env) (d : dec) (tdecs : Set type_ident)
      (new_tenv : type_env),
      type_d check tenv d tdecs new_tenv →
      type_d false tenv d tdecs new_tenv) ∧
    (∀ (check : Bool) (tenv : type_env) (d : List dec) (tdecs : Set type_ident)
      (new_tenv : type_env),
      type_ds check tenv d tdecs new_tenv →
      type_ds false tenv d tdecs new_tenv) := by
  apply Aux.type_d_ind
  case dlet_poly =>
    intro c tvs tenv p e t b l h1 h2 h3 h4 _
    exact type_d.dlet_poly _ _ _ _ _ t _ _ h1 h2 h3 h4 (fun h => by cases h)
  case dlet_mono =>
    intro c tenv p e t b l _ h2 h3 h4
    exact type_d.dlet_mono _ _ _ _ t _ _ (fun h => by cases h) h2 h3 h4
  case dletrec =>
    intro c tenv funs b tvs l h1 _
    exact type_d.dletrec _ _ _ _ _ _ h1 (fun h => by cases h)
  case dtype =>
    intro c tenv tdefs tids tenvT l h1 h2 h3 h4 h5
    exact type_d.dtype _ _ _ _ _ _ h1 h2 h3 h4 h5
  case dtabbrev =>
    intro c tenv tvs tn t l h1 h2 h3
    exact type_d.dtabbrev _ _ _ _ _ _ h1 h2 h3
  case dexn =>
    intro c tenv cn ts l h1 h2
    exact type_d.dexn _ _ _ _ _ h1 h2
  case dmod =>
    intro c tenv mn ds decls tenv' _ ih
    exact type_d.dmod _ _ _ _ _ _ ih
  case dlocal =>
    intro c tenv lds ds t1 t2 d1 d2 _ _ h3 ih1 ih2
    exact type_d.dlocal _ _ _ _ _ _ _ _ ih1 ih2 h3
  case nil => intro c tenv; exact type_ds.nil _ _
  case cons =>
    intro c tenv d ds t1 t2 d1 d2 _ _ h3 ih1 ih2
    exact type_ds.cons _ _ _ _ _ _ _ _ ih1 ih2 h3

/- HOL4:
Theorem extend_dec_tenv_ok:
   !tenv tenv'. tenv_ok tenv ∧ tenv_ok tenv' ⇒ tenv_ok (extend_dec_tenv tenv tenv') -/
theorem extend_dec_tenv_ok :
    ∀ (tenv tenv' : type_env),
      tenv_ok tenv ∧ tenv_ok tenv' → tenv_ok (extend_dec_tenv tenv tenv') := by
  rintro tenv tenv' ⟨⟨h1, h2, h3⟩, ⟨h4, h5, h6⟩⟩
  exact ⟨nsAll_nsAppend _ _ _ ⟨h1, h4⟩, nsAll_nsAppend _ _ _ ⟨h2, h5⟩,
    nsAll_nsAppend _ _ _ ⟨h3, h6⟩⟩

theorem Aux.tenv_add_tvs_ok {m : Type} {tvs : Nat} {b : List (varN × typ)}
    (h : EVERY (check_freevars tvs []) (b.map Prod.snd)) :
    tenv_val_ok (alist_to_ns (tenv_add_tvs tvs b) : Namespace m varN (Nat × typ)) := by
  refine nsAll_alist_to_ns _ _ ?_
  rw [EVERY_iff_forall]
  rintro ⟨n, x⟩ hx
  obtain ⟨⟨y, t⟩, hy, he⟩ := List.mem_map.1 hx
  cases he
  exact Aux.EVERY_map.1 h _ hy

theorem Aux.mem_zipWith {α β γ : Type} {f : α → β → γ} {l1 : List α} {l2 : List β} {x : γ}
    (h : x ∈ List.zipWith f l1 l2) : ∃ a b, a ∈ l1 ∧ b ∈ l2 ∧ x = f a b := by
  induction l1 generalizing l2 with
  | nil => simp at h
  | cons a l1 ih =>
    cases l2 with
    | nil => simp at h
    | cons b l2 =>
      rw [List.zipWith_cons_cons] at h
      rcases List.mem_cons.1 h with h | h
      · exact ⟨a, b, List.mem_cons_self, List.mem_cons_self, h⟩
      · obtain ⟨a', b', ha, hb, hx⟩ := ih h
        exact ⟨a', b', List.mem_cons_of_mem _ ha, List.mem_cons_of_mem _ hb, hx⟩

theorem Aux.tenvT_ok {m : Type} {tdefs : type_def} {tids : List type_ident} :
    tenv_abbrev_ok (alist_to_ns
        (List.zipWith (fun (tvs, tn, _) i => (tn, (tvs, Tapp (tvs.map Tvar) i)))
          tdefs tids) : Namespace m typeN (List tvarN × typ)) := by
  refine nsAll_alist_to_ns _ _ ?_
  rw [EVERY_iff_forall]
  rintro ⟨n, x⟩ hx
  obtain ⟨⟨tvs, tn, cs⟩, i, _, _, he⟩ := Aux.mem_zipWith hx
  cases he
  refine Aux.cf_app.2 fun t ht => ?_
  obtain ⟨tv, htv, rfl⟩ := List.mem_map.1 ht
  exact Aux.cf_var.2 htv

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
    (∀ (check : Bool) (tenv : type_env) (d : dec) (tdecs : Set type_ident) (tenv' : type_env),
      type_d check tenv d tdecs tenv' →
      tenv_ok tenv →
      tenv_ok tenv') ∧
    (∀ (check : Bool) (tenv : type_env) (d : List dec) (tdecs : Set type_ident)
      (tenv' : type_env),
      type_ds check tenv d tdecs tenv' →
      tenv_ok tenv →
      tenv_ok tenv') := by
  apply Aux.type_d_ind
  case dlet_poly =>
    intro c tvs tenv p e t b l h1 h2 h3 h4 _ _
    exact ⟨Aux.tenv_add_tvs_ok (type_p_freevars.1 _ _ _ _ _ h3).2, nsAll_nsEmpty _,
      nsAll_nsEmpty _⟩
  case dlet_mono =>
    intro c tenv p e t b l _ h2 h3 h4 _
    exact ⟨Aux.tenv_add_tvs_ok (type_p_freevars.1 _ _ _ _ _ h3).2, nsAll_nsEmpty _,
      nsAll_nsEmpty _⟩
  case dletrec =>
    intro c tenv funs b tvs l h1 _ _
    refine ⟨Aux.tenv_add_tvs_ok ?_, nsAll_nsEmpty _, nsAll_nsEmpty _⟩
    rw [Aux.EVERY_map]
    rintro ⟨x, t⟩ hx
    obtain ⟨_, _, _, hc⟩ := Aux.type_funs_mem h1 x t hx
    rw [num_tvs_bind_var_list, Aux.num_tvs_bt] at hc
    exact hc
  case dtype =>
    intro c tenv tdefs tids tenvT l h1 h2 h3 h4 h5 hok
    have hT : tenv_abbrev_ok tenvT := by rw [h5]; exact Aux.tenvT_ok
    exact ⟨nsAll_nsEmpty _, check_ctor_tenv_ok _ _ _
      ⟨h4.symm, h3, nsAll_nsAppend _ _ _ ⟨hT, hok.2.2⟩⟩, hT⟩
  case dtabbrev =>
    intro c tenv tvs tn t l h1 h2 h3 hok
    refine ⟨nsAll_nsEmpty _, nsAll_nsEmpty _, (nsAll_nsSing _ _ _).2 ?_⟩
    exact check_freevars_type_name_subst _ _ _ _ ⟨hok.2.2, h2, h1⟩
  case dexn =>
    intro c tenv cn ts l h1 h2 hok
    refine ⟨nsAll_nsEmpty _, (nsAll_nsSing _ _ _).2 ?_, nsAll_nsEmpty _⟩
    show EVERY (check_freevars 0 []) (ts.map (type_name_subst tenv.t))
    rw [Aux.EVERY_map]
    rw [EVERY_iff_forall] at h1 h2
    exact fun t ht => check_freevars_type_name_subst _ _ _ _ ⟨hok.2.2, h2 t ht, h1 t ht⟩
  case dmod =>
    intro c tenv mn ds decls tenv' _ ih hok
    obtain ⟨h1, h2, h3⟩ := ih hok
    exact ⟨(nsAll_nsLift _ _ _).2 h1, (nsAll_nsLift _ _ _).2 h2, (nsAll_nsLift _ _ _).2 h3⟩
  case dlocal =>
    intro c tenv lds ds t1 t2 d1 d2 _ _ h3 ih1 ih2 hok
    exact ih2 (extend_dec_tenv_ok _ _ ⟨ih1 hok, hok⟩)
  case nil => intro c tenv _; exact tenv_ok_empty
  case cons =>
    intro c tenv d ds t1 t2 d1 d2 _ _ h3 ih1 ih2 hok
    exact extend_dec_tenv_ok _ _ ⟨ih2 (extend_dec_tenv_ok _ _ ⟨ih1 hok, hok⟩), ih1 hok⟩

/- HOL4:
Theorem type_d_tenv_ok:
  ∀check tenv d tdecs tenv'.
   type_d check tenv d tdecs tenv' ∧
   tenv_ok tenv
   ⇒
   tenv_ok (extend_dec_tenv tenv' tenv) -/
theorem type_d_tenv_ok :
    ∀ (check : Bool) (tenv : type_env) (d : dec) (tdecs : Set type_ident) (tenv' : type_env),
      type_d check tenv d tdecs tenv' ∧
      tenv_ok tenv →
      tenv_ok (extend_dec_tenv tenv' tenv) := by
  rintro check tenv d tdecs tenv' ⟨h, hok⟩
  exact extend_dec_tenv_ok _ _ ⟨type_d_tenv_ok_helper.1 _ _ _ _ _ h hok, hok⟩

/- HOL4:
Theorem type_ds_empty[simp]:
  !check tenv decls r.
  type_ds check tenv [] decls r ⇔
  decls = {} ∧ r = <| v := nsEmpty; c:= nsEmpty; t := nsEmpty |> -/
theorem type_ds_empty :
    ∀ (check : Bool) (tenv : type_env) (decls : Set type_ident) (r : type_env),
      type_ds check tenv [] decls r ↔
      (decls = ∅ ∧ r = { v := nsEmpty, c := nsEmpty, t := nsEmpty }) := by
  intro check tenv decls r
  constructor
  · intro h; cases h; exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩; exact type_ds.nil _ _

theorem Aux.union_empty {α : Type} (s : Set α) : s ∪ ∅ = s :=
  Aux.set_ext fun _ => ⟨fun h => h.elim id False.elim, Or.inl⟩

theorem Aux.disjoint_empty {α : Type} (s : Set α) : DISJOINT s ∅ :=
  Aux.disjoint_iff.2 fun _ _ h => False.elim h

theorem Aux.extend_empty (tenv : type_env) :
    extend_dec_tenv { v := nsEmpty, c := nsEmpty, t := nsEmpty } tenv = tenv := by
  simp [extend_dec_tenv, nsAppend_nsEmpty]

/- HOL4:
Theorem type_ds_sing[simp]:
  !check tenv d decls r.
  type_ds check tenv [d] decls r ⇔ type_d check tenv d decls r -/
theorem type_ds_sing :
    ∀ (check : Bool) (tenv : type_env) (d : dec) (decls : Set type_ident) (r : type_env),
      type_ds check tenv [d] decls r ↔ type_d check tenv d decls r := by
  intro check tenv d decls r
  constructor
  · intro h
    cases h with
    | cons _ _ _ t1 t2 d1 d2 h1 h2 h3 =>
      obtain ⟨rfl, rfl⟩ := (type_ds_empty _ _ _ _).1 h2
      rw [Aux.union_empty, Aux.extend_empty]
      exact h1
  · intro h
    have := type_ds.cons _ _ _ _ _ _ _ _ h (type_ds.nil _ _) (Aux.disjoint_empty _)
    rw [Aux.union_empty, Aux.extend_empty] at this
    exact this

end

end CmlTS
