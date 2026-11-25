import CmlTS.Ast
import CmlTS.Namespace
import CmlTS.TypeSystem
import CmlTS.TypeSoundInvariants
import CmlTS.NamespaceProps
import CmlTS.SemanticPrimitivesProps
import CmlTS.Proofs.TypAux

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

/-! Theorems, in HOL4 source order. -/

/- HOL4:
Theorem unchanged_tenv[simp]:
  !(tenv : type_env).
  <| v := tenv.v; c := tenv.c; t := tenv.t |> = tenv -/
theorem unchanged_tenv :
    ∀ (tenv : type_env), ({ v := tenv.v, c := tenv.c, t := tenv.t } : type_env) = tenv :=
  fun _ => rfl

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
    tenv_val_ok (nsEmpty : Namespace m n (Nat × typ)) := nsAll_nsEmpty _

/- HOL4:
Theorem tenv_ctor_ok_nsEmpty[simp]:
   tenv_ctor_ok nsEmpty -/
theorem tenv_ctor_ok_nsEmpty {m n α : Type} :
    tenv_ctor_ok (nsEmpty : Namespace m n (List mlstring × List typ × α)) := nsAll_nsEmpty _

/- HOL4:
Theorem tenv_abbrev_ok_nsEmpty[simp]:
   tenv_abbrev_ok nsEmpty -/
theorem tenv_abbrev_ok_nsEmpty {m n : Type} :
    tenv_abbrev_ok (nsEmpty : Namespace m n (List mlstring × typ)) := nsAll_nsEmpty _

/- HOL4:
Theorem tenv_ok_empty[simp]:
   tenv_ok <| v := nsEmpty; c := nsEmpty; t := nsEmpty |> -/
theorem tenv_ok_empty :
    tenv_ok { v := nsEmpty, c := nsEmpty, t := nsEmpty } :=
  ⟨nsAll_nsEmpty _, nsAll_nsEmpty _, nsAll_nsEmpty _⟩

/- HOL4:
Theorem check_freevars_add:
 (!tvs tvs' t. check_freevars tvs tvs' t ⇒
  !tvs''. tvs'' ≥ tvs ⇒ check_freevars tvs'' tvs' t) -/
theorem check_freevars_add :
    ∀ (tvs : Nat) (tvs' : List mlstring) (t : typ), check_freevars tvs tvs' t →
      ∀ (tvs'' : Nat), tvs'' ≥ tvs → check_freevars tvs'' tvs' t := by
  intro tvs tvs' t h tvs'' hge
  induction t using Aux.typ_ind with
  | tvar tv => simpa only [check_freevars] using h
  | tvar_db n =>
    simp only [check_freevars] at h ⊢
    omega
  | tapp ts ti ih =>
    simp only [check_freevars, EVERY_iff_forall] at h ⊢
    exact fun t ht => ih t ht (h t ht)

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
  induction t using Aux.typ_ind with
  | tvar tv =>
    simp only [check_freevars] at h
    simp only [type_subst, Aux.FLOOKUP_alist_to_fmap]
    obtain ⟨x, hx⟩ := Aux.ALOOKUP_zip_some hl h
    rw [hx]
    exact EVERY_iff_forall.mp hts _ (Aux.ALOOKUP_zip_mem hx).2
  | tvar_db n =>
    simp only [check_freevars, type_subst] at h ⊢
    exact h
  | tapp ts ti ih =>
    simp only [check_freevars, type_subst, EVERY_iff_forall, List.mem_map] at h ⊢
    rintro t ⟨t', ht', rfl⟩
    exact ih t' ht' (h t' ht')

theorem Aux.map_id_of {l : List typ} {f : typ → typ} (h : ∀ x, x ∈ l → f x = x) :
    l.map f = l := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    rw [List.map_cons, h a List.mem_cons_self,
      ih fun x hx => h x (List.mem_cons_of_mem _ hx)]

/- HOL4:
Theorem deBruijn_inc0:
 (!t sk. deBruijn_inc sk 0 t = t) ∧
 (!ts sk. MAP (deBruijn_inc sk 0) ts = ts) -/
theorem deBruijn_inc0 :
    (∀ (t : typ) (sk : Nat), deBruijn_inc sk 0 t = t) ∧
    (∀ (ts : List typ) (sk : Nat), ts.map (deBruijn_inc sk 0) = ts) := by
  have h : ∀ (t : typ) (sk : Nat), deBruijn_inc sk 0 t = t := by
    intro t sk
    induction t using Aux.typ_ind with
    | tvar tv => simp only [deBruijn_inc]
    | tvar_db n => simp only [deBruijn_inc, Nat.add_zero, ite_self]
    | tapp ts ti ih =>
      simp only [deBruijn_inc]
      congr 1
      exact Aux.map_id_of ih
  exact ⟨h, fun ts sk => Aux.map_id_of fun t _ => h t sk⟩

/- HOL4:
Theorem deBruijn_inc_deBruijn_inc:
 !sk i2 t i1.
  deBruijn_inc sk i1 (deBruijn_inc sk i2 t) = deBruijn_inc sk (i1 + i2) t -/
theorem deBruijn_inc_deBruijn_inc :
    ∀ (sk i2 : Nat) (t : typ) (i1 : Nat),
      deBruijn_inc sk i1 (deBruijn_inc sk i2 t) = deBruijn_inc sk (i1 + i2) t := by
  intro sk i2 t i1
  induction t using Aux.typ_ind with
  | tvar tv => simp only [deBruijn_inc]
  | tvar_db n =>
    simp only [deBruijn_inc]
    by_cases h : n < sk
    · simp only [if_pos h, deBruijn_inc]
    · have h2 : ¬ n + i2 < sk := by omega
      simp only [if_neg h, deBruijn_inc, if_neg h2]
      congr 1; omega
  | tapp ts ti ih =>
    simp only [deBruijn_inc, List.map_map]
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
  | tvar tv => simp only [deBruijn_inc]
  | tvar_db n =>
    have h2 : ¬ n + (sk + i2) < sk := by omega
    simp only [deBruijn_inc, if_neg (Nat.not_lt_zero n), if_neg h2]
    congr 1; omega
  | tapp ts ti ih =>
    simp only [deBruijn_inc, List.map_map]
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
  induction t using Aux.typ_ind with
  | tvar tv =>
    simp only [check_freevars] at h
    obtain ⟨x, hx⟩ := Aux.ALOOKUP_zip_some hl h
    simp only [type_subst, Aux.FLOOKUP_alist_to_fmap, Aux.ALOOKUP_zip_map, hx, Option.map]
  | tvar_db n =>
    simp only [check_freevars] at h
    omega
  | tapp ts' ti ih =>
    simp only [check_freevars, EVERY_iff_forall] at h
    simp only [type_subst, deBruijn_inc, List.map_map]
    congr 1
    exact List.map_congr_left fun t ht => ih t ht (h t ht)

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
    type_subst_deBruijn_inc_single _ t ts tvs inc sk ⟨hl, rfl, h t ht⟩

/- HOL4:
Theorem check_freevars_deBruijn_inc[local]:
  !tvs tvs' t. check_freevars tvs tvs' t ⇒
  !n n'. check_freevars (n+tvs) tvs' (deBruijn_inc n' n t) -/
theorem check_freevars_deBruijn_inc :
    ∀ (tvs : Nat) (tvs' : List mlstring) (t : typ), check_freevars tvs tvs' t →
      ∀ (n n' : Nat), check_freevars (n + tvs) tvs' (deBruijn_inc n' n t) := by
  intro tvs tvs' t h n n'
  induction t using Aux.typ_ind with
  | tvar tv => simpa only [check_freevars, deBruijn_inc] using h
  | tvar_db k =>
    simp only [check_freevars] at h
    simp only [deBruijn_inc]
    split <;> simp only [check_freevars] <;> omega
  | tapp ts ti ih =>
    simp only [check_freevars, deBruijn_inc, EVERY_iff_forall, List.mem_map] at h ⊢
    rintro t ⟨t', ht', rfl⟩
    exact ih t' ht' (h t' ht')

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
  | tvar tv => simp only [deBruijn_inc]
  | tvar_db k =>
    simp only [deBruijn_inc] at h ⊢
    by_cases hk : k < skip
    · rw [if_pos hk]
    · rw [if_neg hk] at h
      simp only [check_freevars] at h
      omega
  | tapp ts ti ih =>
    simp only [check_freevars, deBruijn_inc, EVERY_iff_forall, List.mem_map] at h ⊢
    congr 1
    refine Aux.map_id_of fun t ht => ih t ht ?_
    rcases h with h | h
    · exact Or.inl (h t ht)
    · exact Or.inr (h _ ⟨t, ht, rfl⟩)

theorem Aux.subst_db {skip : Nat} {ts : List typ} {n : Nat} :
    (n < skip → deBruijn_subst skip ts (Tvar_db n) = Tvar_db n) ∧
    (skip ≤ n → n < ts.length + skip →
      deBruijn_subst skip ts (Tvar_db n) = EL (n - skip) ts) ∧
    (ts.length + skip ≤ n →
      deBruijn_subst skip ts (Tvar_db n) = Tvar_db (n - ts.length)) := by
  refine ⟨fun h => ?_, fun h1 h2 => ?_, fun h => ?_⟩
  · have h' : ¬ (¬ n < skip ∧ n < ts.length + skip) := fun hh => hh.1 h
    have h'' : ¬ ¬ n < skip := fun hh => hh h
    simp only [deBruijn_subst, if_neg h', if_neg h'']
  · have h' : ¬ n < skip ∧ n < ts.length + skip := ⟨by omega, h2⟩
    simp only [deBruijn_subst, if_pos h']
  · have h' : ¬ (¬ n < skip ∧ n < ts.length + skip) := fun hh => by omega
    have h'' : ¬ n < skip := by omega
    simp only [deBruijn_subst, if_neg h', if_pos h'']

/-- The general fact on the free variables of a substituted type. -/
theorem Aux.check_freevars_subst_gen {tvs tvs1 : Nat} {tvs' : List mlstring} {t : typ}
    {ts : List typ} {skip : Nat} (h : check_freevars tvs tvs' t)
    (h1 : skip ≤ tvs1) (h2 : tvs ≤ ts.length + tvs1)
    (hts : EVERY (check_freevars tvs1 tvs') ts) :
    check_freevars tvs1 tvs' (deBruijn_subst skip ts t) := by
  induction t using Aux.typ_ind with
  | tvar tv => simpa only [check_freevars, deBruijn_subst] using h
  | tvar_db k =>
    simp only [check_freevars] at h
    obtain ⟨a1, a2, a3⟩ := Aux.subst_db (skip := skip) (ts := ts) (n := k)
    by_cases hk : k < skip
    · rw [a1 hk]; simp only [check_freevars]; omega
    · by_cases hk2 : k < ts.length + skip
      · rw [a2 (by omega) hk2]
        exact Aux.EVERY_EL hts _ (by omega)
      · rw [a3 (by omega)]; simp only [check_freevars]; omega
  | tapp ts ti ih =>
    simp only [check_freevars, deBruijn_subst, EVERY_iff_forall, List.mem_map] at h ⊢
    rintro t ⟨t', ht', rfl⟩
    exact ih t' ht' (h t' ht')

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
      check_freevars tvs tvs' (deBruijn_subst 0 ts t) :=
  fun _ _ _ _ _ ⟨h, hts⟩ =>
    Aux.check_freevars_subst_gen h (Nat.zero_le _) (Nat.le_add_left _ _) hts

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
      check_freevars tvs tvs' (deBruijn_subst 0 ts t) :=
  fun _ _ _ _ _ _ ⟨h, hts⟩ =>
    Aux.check_freevars_subst_gen h (Nat.zero_le _) (Nat.le_add_right _ _) hts

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
  exact Aux.check_freevars_subst_gen (check_freevars_deBruijn_inc _ _ _ h tvs1 targs.length)
    (Nat.zero_le _) (by omega) hts

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
  exact Aux.check_freevars_subst_gen h (Nat.zero_le _) (by omega) hts

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
  rintro s t tvs - ts ts' inc ⟨hl, h, -⟩
  induction t using Aux.typ_ind with
  | tvar tv =>
    simp only [check_freevars] at h
    obtain ⟨x, hx⟩ := Aux.ALOOKUP_zip_some hl h
    simp only [type_subst, Aux.FLOOKUP_alist_to_fmap, Aux.ALOOKUP_zip_map, hx, Option.map]
  | tvar_db n =>
    simp only [check_freevars] at h
    omega
  | tapp ts' ti ih =>
    simp only [check_freevars, EVERY_iff_forall] at h
    simp only [type_subst, deBruijn_subst, List.map_map]
    congr 1
    exact List.map_congr_left fun t ht => ih t ht (h t ht)

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
  rintro - tvs - ts ts' ts'' inc ⟨hl, h⟩
  rw [EVERY_iff_forall] at h
  rw [List.map_map]
  exact List.map_congr_left fun t ht =>
    type_subst_deBruijn_subst_single _ t tvs () ts ts' inc ⟨hl, h t ht, rfl⟩

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
  refine Aux.check_freevars_subst_gen h (by omega) (by simp; omega) ?_
  rw [EVERY_iff_forall] at hts ⊢
  intro x hx
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
  exact check_freevars_deBruijn_inc _ _ _ (hts y hy) n1 0

/- HOL4:
Theorem nil_deBruijn_subst:
 ∀skip tvs t. check_freevars skip [] t ⇒ (deBruijn_subst skip tvs t = t) -/
theorem nil_deBruijn_subst :
    ∀ (skip : Nat) (tvs : List typ) (t : typ),
      check_freevars skip [] t → deBruijn_subst skip tvs t = t := by
  intro skip tvs t h
  induction t using Aux.typ_ind with
  | tvar tv => simp only [deBruijn_subst]
  | tvar_db k =>
    simp only [check_freevars] at h
    exact Aux.subst_db.1 h
  | tapp ts ti ih =>
    simp only [check_freevars, EVERY_iff_forall] at h
    simp only [deBruijn_subst]
    congr 1
    exact Aux.map_id_of fun t ht => ih t ht (h t ht)

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
  have h : ∀ (t : typ) (sk : Nat) (targs targs' : List typ),
      check_freevars targs.length [] t →
      deBruijn_subst sk (targs'.map (deBruijn_inc 0 sk)) (deBruijn_subst 0 targs t) =
        deBruijn_subst 0
          (targs.map (deBruijn_subst sk (targs'.map (deBruijn_inc 0 sk)))) t := by
    intro t sk targs targs' h
    induction t using Aux.typ_ind with
    | tvar tv => simp only [deBruijn_subst]
    | tvar_db k =>
      simp only [check_freevars] at h
      rw [Aux.subst_db.2.1 (Nat.zero_le _) (by omega),
        Aux.subst_db.2.1 (Nat.zero_le _) (by simp; omega), Aux.EL_map _ _ _ (by omega)]
    | tapp ts ti ih =>
      simp only [check_freevars, EVERY_iff_forall] at h
      simp only [deBruijn_subst, List.map_map]
      congr 1
      exact List.map_congr_left fun t ht => ih t ht (h t ht)
  refine ⟨fun t sk targs targs' _ => h t sk targs targs', fun ts sk targs targs' _ hts => ?_⟩
  rw [EVERY_iff_forall] at hts
  rw [List.map_map]
  exact List.map_congr_left fun t ht => h t sk targs targs' (hts t ht)

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
          (deBruijn_subst n (targs.map (deBruijn_inc 0 n)) t) :=
  fun tvs tvs2 t h tvs' targs n hh => check_freevars_lem tvs tvs2 t h targs n tvs' hh

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
  have h : ∀ (t : typ) (n inc n' : Nat) (targs : List typ),
      deBruijn_inc n inc
          (deBruijn_subst (n + n') (targs.map (deBruijn_inc 0 (n + n'))) t) =
        deBruijn_subst (n + inc + n') (targs.map (deBruijn_inc 0 (n + inc + n')))
          (deBruijn_inc n inc t) := by
    intro t n inc n' targs
    induction t using Aux.typ_ind with
    | tvar tv => simp only [deBruijn_subst, deBruijn_inc]
    | tvar_db m =>
      have hl : ∀ k, (targs.map (deBruijn_inc 0 k)).length = targs.length := by simp
      by_cases h1 : m < n
      · rw [Aux.subst_db.1 (by omega)]
        simp only [deBruijn_inc, if_pos h1]
        rw [Aux.subst_db.1 (by omega)]
      · by_cases h2 : m < n + n'
        · rw [Aux.subst_db.1 h2]
          simp only [deBruijn_inc, if_neg h1]
          rw [Aux.subst_db.1 (by omega)]
        · by_cases h3 : m < targs.length + (n + n')
          · rw [Aux.subst_db.2.1 (by omega) (by rw [hl]; exact h3),
              Aux.EL_map _ _ _ (by omega), deBuijn_inc_lem1]
            simp only [deBruijn_inc, if_neg h1]
            rw [Aux.subst_db.2.1 (by omega) (by rw [hl]; omega), Aux.EL_map _ _ _ (by omega)]
            have e1 : m + inc - (n + inc + n') = m - (n + n') := by omega
            have e2 : inc + (n + n') = n + inc + n' := by omega
            rw [e1, e2]
          · rw [Aux.subst_db.2.2 (by rw [hl]; omega), hl]
            have h4 : ¬ m - targs.length < n := by omega
            simp only [deBruijn_inc, if_neg h1, if_neg h4]
            rw [Aux.subst_db.2.2 (by rw [hl]; omega), hl]
            congr 1; omega
    | tapp ts ti ih =>
      simp only [deBruijn_subst, deBruijn_inc, List.map_map]
      congr 1
      exact List.map_congr_left ih
  refine ⟨h, fun ts n inc n' targs => ?_⟩
  rw [List.map_map, List.map_map]
  exact List.map_congr_left fun t _ => h t n inc n' targs

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
  have h : ∀ (t : typ) (ts : List typ) (inc : Nat),
      deBruijn_subst 0 ts (deBruijn_inc 0 (inc + ts.length) t) = deBruijn_inc 0 inc t := by
    intro t ts inc
    induction t using Aux.typ_ind with
    | tvar tv => simp only [deBruijn_subst, deBruijn_inc]
    | tvar_db m =>
      simp only [deBruijn_inc, if_neg (Nat.not_lt_zero m)]
      rw [Aux.subst_db.2.2 (by omega)]
      congr 1; omega
    | tapp ts ti ih =>
      simp only [deBruijn_subst, deBruijn_inc, List.map_map]
      congr 1
      exact List.map_congr_left ih
  refine ⟨h, fun ts' ts inc => ?_⟩
  rw [List.map_map]
  exact List.map_congr_left fun t _ => h t ts inc

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
  have h : ∀ (t : typ) (sk : Nat) (targs targs' : List typ),
      deBruijn_subst sk (targs'.map (deBruijn_inc 0 sk)) (deBruijn_subst 0 targs t) =
        deBruijn_subst 0 (targs.map (deBruijn_subst sk (targs'.map (deBruijn_inc 0 sk))))
          (deBruijn_subst (targs.length + sk)
            (targs'.map (deBruijn_inc 0 (targs.length + sk))) t) := by
    intro t sk targs targs'
    induction t using Aux.typ_ind with
    | tvar tv => simp only [deBruijn_subst]
    | tvar_db n =>
      have hl : ∀ k, (targs'.map (deBruijn_inc 0 k)).length = targs'.length := by simp
      have hl2 : (targs.map (deBruijn_subst sk (targs'.map (deBruijn_inc 0 sk)))).length =
        targs.length := by simp
      by_cases h1 : n < targs.length
      · rw [(Aux.subst_db (n := n) (skip := targs.length + sk)).1 (by omega),
          (Aux.subst_db (n := n) (skip := 0) (ts := targs)).2.1 (Nat.zero_le _) (by omega),
          (Aux.subst_db (n := n) (skip := 0)).2.1 (Nat.zero_le _) (by omega),
          Aux.EL_map _ _ _ (by omega)]
      · rw [(Aux.subst_db (n := n) (skip := 0) (ts := targs)).2.2 (by omega)]
        by_cases h2 : n < targs.length + sk
        · rw [(Aux.subst_db (n := n - targs.length) (skip := sk)).1 (by omega),
            (Aux.subst_db (n := n) (skip := targs.length + sk)).1 (by omega),
            (Aux.subst_db (n := n) (skip := 0)).2.2 (by omega), hl2]
        · by_cases h3 : n < targs'.length + (targs.length + sk)
          · rw [(Aux.subst_db (n := n - targs.length) (skip := sk)).2.1 (by omega)
                (by rw [hl]; omega),
              (Aux.subst_db (n := n) (skip := targs.length + sk)).2.1 (by omega)
                (by rw [hl]; omega),
              Aux.EL_map _ _ _ (by omega), Aux.EL_map _ _ _ (by omega)]
            have e1 : n - targs.length - sk = n - (targs.length + sk) := by omega
            have e2 : targs.length + sk =
              sk + (targs.map (deBruijn_subst sk (targs'.map (deBruijn_inc 0 sk)))).length := by
              rw [hl2]; omega
            rw [e1, e2, subst_inc_cancel.1]
          · rw [(Aux.subst_db (n := n - targs.length) (skip := sk)).2.2 (by rw [hl]; omega),
              (Aux.subst_db (n := n) (skip := targs.length + sk)).2.2 (by rw [hl]; omega),
              hl, hl, (Aux.subst_db (n := n - targs'.length) (skip := 0)).2.2 (by omega), hl2]
            congr 1; omega
    | tapp ts ti ih =>
      simp only [deBruijn_subst, List.map_map]
      congr 1
      exact List.map_congr_left ih
  refine ⟨fun t sk targs targs' _ _ => h t sk targs targs', fun ts sk targs targs' _ _ => ?_⟩
  rw [List.map_map, List.map_map]
  exact List.map_congr_left fun t _ => h t sk targs targs'

theorem Aux.COUNT_LIST_length (n : Nat) : (COUNT_LIST n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [COUNT_LIST, ih]

theorem Aux.EL_COUNT_LIST (n k : Nat) (h : k < n) : EL k (COUNT_LIST n) = k := by
  induction n generalizing k with
  | zero => omega
  | succ n ih =>
    cases k with
    | zero => rfl
    | succ k =>
      show EL k ((COUNT_LIST n).map Nat.succ) = k + 1
      rw [Aux.EL_map _ _ _ (by rw [Aux.COUNT_LIST_length]; omega), ih k (by omega)]

/- HOL4:
Theorem deBruijn_subst_id:
 (!t n. check_freevars n [] t ⇒ (deBruijn_subst 0 (MAP Tvar_db (COUNT_LIST n)) t = t)) ∧
 (!ts n. EVERY (check_freevars n []) ts ⇒ (MAP (deBruijn_subst 0 (MAP Tvar_db (COUNT_LIST n))) ts = ts)) -/
theorem deBruijn_subst_id :
    (∀ (t : typ) (n : Nat), check_freevars n [] t →
      deBruijn_subst 0 ((COUNT_LIST n).map Tvar_db) t = t) ∧
    (∀ (ts : List typ) (n : Nat), EVERY (check_freevars n []) ts →
      ts.map (deBruijn_subst 0 ((COUNT_LIST n).map Tvar_db)) = ts) := by
  have h : ∀ (t : typ) (n : Nat), check_freevars n [] t →
      deBruijn_subst 0 ((COUNT_LIST n).map Tvar_db) t = t := by
    intro t n h
    induction t using Aux.typ_ind with
    | tvar tv => simp only [deBruijn_subst]
    | tvar_db k =>
      simp only [check_freevars] at h
      have hl := Aux.COUNT_LIST_length n
      rw [Aux.subst_db.2.1 (Nat.zero_le _) (by simp only [List.length_map]; omega),
        Aux.EL_map _ _ _ (by omega), Nat.sub_zero, Aux.EL_COUNT_LIST _ _ h]
    | tapp ts ti ih =>
      simp only [check_freevars, EVERY_iff_forall] at h
      simp only [deBruijn_subst]
      congr 1
      exact Aux.map_id_of fun t ht => ih t ht (h t ht)
  refine ⟨h, fun ts n hts => ?_⟩
  rw [EVERY_iff_forall] at hts
  exact Aux.map_id_of fun t ht => h t n (hts t ht)

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
  exact Aux.check_freevars_subst_gen h2 (Nat.zero_le _) (Nat.le_add_right _ _) h1

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
      check_freevars 0 tvs t :=
  fun _ _ _ _ ⟨h1, h2⟩ => h1 _ _ h2

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
  rintro tvs t dbmax tenvT ⟨hok, h1, h2⟩
  induction t using Aux.ast_ind with
  | tvar tv =>
    simp only [check_freevars_ast, type_name_subst, check_freevars] at h2 ⊢
    exact h2
  | tfun t1 t2 ih1 ih2 =>
    simp only [check_freevars_ast, check_type_names] at h1 h2
    simp only [type_name_subst, Tfn, check_freevars, EVERY]
    exact ⟨ih1 h1.1 h2.1, ih2 h1.2 h2.2, trivial⟩
  | ttup ts ih =>
    simp only [check_freevars_ast, check_type_names, EVERY_iff_forall] at h1 h2
    simp only [type_name_subst, Ttup, check_freevars, EVERY_iff_forall, List.mem_map]
    rintro t ⟨t', ht', rfl⟩
    exact ih t' ht' (h1 t' ht') (h2 t' ht')
  | tapp ts tn ih =>
    simp only [check_freevars_ast, check_type_names, EVERY_iff_forall] at h1 h2
    obtain ⟨h1, h3⟩ := h1
    have hargs : EVERY (check_freevars dbmax tvs) (ts.map (fun t => type_name_subst tenvT t)) := by
      simp only [EVERY_iff_forall, List.mem_map]
      rintro t ⟨t', ht', rfl⟩
      exact ih t' ht' (h3 t' ht') (h2 t' ht')
    simp only [type_name_subst]
    cases hl : nsLookup tenvT tn with
    | none => rw [hl] at h1; exact h1.elim
    | some p =>
      obtain ⟨tvs', t⟩ := p
      rw [hl] at h1
      exact check_freevars_subst_single _ _ _ _ _ ⟨by rw [List.length_map]; exact h1,
        check_freevars_add _ _ _ (tenv_abbrev_ok_lookup _ _ _ _ ⟨hok, hl⟩) _ (Nat.zero_le _),
        hargs⟩

/- HOL4:
Theorem tenv_ctor_ok_merge[simp]:
   !tenvC1 tenvC2.
    tenv_ctor_ok tenvC1 ∧ tenv_ctor_ok tenvC2
    ⇒
    tenv_ctor_ok (nsAppend tenvC1 tenvC2) -/
theorem tenv_ctor_ok_merge {m n α : Type} :
    ∀ (tenvC1 tenvC2 : Namespace m n (List mlstring × List typ × α)),
      tenv_ctor_ok tenvC1 ∧ tenv_ctor_ok tenvC2 →
      tenv_ctor_ok (nsAppend tenvC1 tenvC2) :=
  fun _ _ h => nsAll_nsAppend _ _ _ h

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
      EVERY (check_freevars 0 tvs) ts :=
  fun _ _ _ _ _ ⟨h1, h2⟩ => h1 _ _ h2

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
  · intro tvs e1 e2
    unfold bind_tvar
    split <;> rfl
  · intro tvs e
    unfold bind_tvar
    split
    · rename_i h; subst h; simp
    · rfl
  · intros; rfl
  · intros; rfl
  · intros; rfl
  · intro n inc tvs e
    unfold bind_tvar
    split
    · rename_i h; subst h; rfl
    · rfl
  · intro tvs e
    unfold bind_tvar
    split <;> rfl
  · intro targs tvs e
    unfold bind_tvar
    split <;> rfl

/- HOL4:
Theorem bind_tvar0[simp]:
 !x. bind_tvar 0 x = x -/
theorem bind_tvar0 :
    ∀ (x : tenv_val_exp), bind_tvar 0 x = x := by
  intro x
  simp [bind_tvar]

theorem Aux.num_tvs_bind_tvar (tvs : Nat) (e : tenv_val_exp) :
    num_tvs (bind_tvar tvs e) = tvs + num_tvs e :=
  (bind_tvar_rewrites (α := Unit) (β := Unit)).2.1 tvs e

theorem Aux.tveLookup_bind_tvar (n : mlstring) (inc tvs : Nat) (e : tenv_val_exp) :
    tveLookup n inc (bind_tvar tvs e) = tveLookup n (inc + tvs) e :=
  (bind_tvar_rewrites (α := Unit) (β := Unit)).2.2.2.2.2.1 n inc tvs e

theorem Aux.ok_bind_tvar (tvs : Nat) (e : tenv_val_exp) :
    tenv_val_exp_ok (bind_tvar tvs e) ↔ tenv_val_exp_ok e :=
  (bind_tvar_rewrites (α := Unit) (β := Unit)).2.2.2.2.2.2.1 tvs e

theorem Aux.db_merge_bind_tvar (tvs : Nat) (e1 e2 : tenv_val_exp) :
    db_merge (bind_tvar tvs e1) e2 = bind_tvar tvs (db_merge e1 e2) :=
  (bind_tvar_rewrites (α := Unit) (β := Unit)).1 tvs e1 e2

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
  | Empty => exact Iff.rfl
  | Bind_tvar tvs e ih => exact ih _
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
    simp only [db_merge, tveLookup, num_tvs, ih]
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
  induction e generalizing inc with
  | Empty => exact Iff.rfl
  | Bind_tvar tvs e ih =>
    simp only [tveLookup]
    rw [ih, ih (0 + tvs)]
  | Bind_name x tvs t e ih =>
    simp only [tveLookup]
    split
    · simp
    · exact ih _

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
  rintro n tvs tenvE tvs' t ⟨h1, h2, h3⟩
  induction tenvE generalizing tvs with
  | Empty => simp [tveLookup] at h3
  | Bind_tvar k e ih =>
    simp only [num_tvs] at h2
    exact ih (tvs + k) h1 (by omega) h3
  | Bind_name x k t' e ih =>
    simp only [num_tvs] at h2
    simp only [tenv_val_exp_ok, h2, Nat.add_zero] at h1
    simp only [tveLookup] at h3
    split at h3
    · cases h3
      rw [nil_deBruijn_inc _ _ _ (Or.inl h1.1)]
      exact h1.1
    · exact ih _ h1.2 h2 h3

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
  | cons p l ih =>
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
  | cons p l ih =>
    obtain ⟨x, t⟩ := p
    simp only [bind_var_list, num_tvs, ih]

theorem Aux.bvl_ok (tvs : Nat) (tenvE : tenv_val_exp) (env : List (mlstring × typ))
    (h1 : tenv_val_exp_ok tenvE)
    (h2 : EVERY (check_freevars (tvs + num_tvs tenvE) []) (env.map Prod.snd)) :
    tenv_val_exp_ok (bind_var_list tvs env tenvE) := by
  induction env with
  | nil => exact h1
  | cons p l ih =>
    obtain ⟨x, t⟩ := p
    simp only [List.map_cons, EVERY] at h2
    simp only [bind_var_list, tenv_val_exp_ok, num_tvs_bind_var_list]
    exact ⟨h2.1, ih h2.2⟩

/- HOL4:
Theorem tenv_val_exp_ok_bvl:
 !tenvE env.
  tenv_val_exp_ok tenvE ∧ EVERY (check_freevars (num_tvs tenvE) []) (MAP SND env)
  ⇒
  tenv_val_exp_ok (bind_var_list 0 env tenvE) -/
theorem tenv_val_exp_ok_bvl :
    ∀ (tenvE : tenv_val_exp) (env : List (mlstring × typ)),
      tenv_val_exp_ok tenvE ∧ EVERY (check_freevars (num_tvs tenvE) []) (env.map Prod.snd) →
      tenv_val_exp_ok (bind_var_list 0 env tenvE) :=
  fun tenvE env ⟨h1, h2⟩ => Aux.bvl_ok 0 tenvE env h1 (by rwa [Nat.zero_add])

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
  | Bind_name x k t' e ih =>
    simp only [tveLookup] at h
    simp only [deBruijn_subst_tenvE, tveLookup, num_tvs]
    split at h
    · rename_i hx
      cases h
      rw [if_pos hx, type_e_subst_lem5.1]
    · rename_i hx
      rw [if_neg hx]
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
  | Bind_name x k t e ih => simp only [db_merge, num_tvs, ih]

/- HOL4:
Theorem num_tvs_deBruijn_subst_tenvE[simp]:
 !targs tenvE. num_tvs (deBruijn_subst_tenvE targs tenvE) = num_tvs tenvE -/
theorem num_tvs_deBruijn_subst_tenvE :
    ∀ (targs : List typ) (tenvE : tenv_val_exp),
      num_tvs (deBruijn_subst_tenvE targs tenvE) = num_tvs tenvE := by
  intro targs e
  induction e with
  | Empty => rfl
  | Bind_tvar k e ih => simp only [deBruijn_subst_tenvE, num_tvs, ih]
  | Bind_name x k t e ih => simp only [deBruijn_subst_tenvE, num_tvs, ih]

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
  induction e generalizing inc inc2 with
  | Empty => simp [tveLookup] at h
  | Bind_tvar k e ih =>
    simp only [tveLookup] at h ⊢
    obtain ⟨t', h1, h2⟩ := ih (inc + k) (inc2 + k) h
    exact ⟨deBruijn_inc tvs k t', by rw [deBruijn_inc_deBruijn_inc, h1],
      by rw [deBruijn_inc_deBruijn_inc, h2]⟩
  | Bind_name x k t' e ih =>
    simp only [tveLookup] at h ⊢
    split at h
    · rename_i hx
      cases h
      exact ⟨t', rfl, by rw [if_pos hx]⟩
    · rename_i hx
      rw [if_neg hx]
      exact ih _ _ h

theorem Aux.tveLookup_freevars_gen :
    ∀ (e : tenv_val_exp) (n : mlstring) (inc : Nat) (t : typ) (tvs : Nat),
      tenv_val_exp_ok e → tveLookup n inc e = some (tvs, t) →
      check_freevars (tvs + inc + num_tvs e) [] t := by
  intro e n inc t tvs h1 h2
  induction e generalizing inc with
  | Empty => simp [tveLookup] at h2
  | Bind_tvar k e ih =>
    simp only [tveLookup] at h2
    simp only [num_tvs]
    have := ih _ h1 h2
    have e' : tvs + (inc + k) + num_tvs e = tvs + inc + (k + num_tvs e) := by omega
    rwa [e'] at this
  | Bind_name x k t' e ih =>
    simp only [tenv_val_exp_ok] at h1
    simp only [tveLookup] at h2
    simp only [num_tvs]
    split at h2
    · cases h2
      have := check_freevars_deBruijn_inc _ _ _ h1.1 inc tvs
      have e' : inc + (tvs + num_tvs e) = tvs + inc + num_tvs e := by omega
      rwa [e'] at this
    · exact ih _ h1.2 h2

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
  exact Aux.check_freevars_subst_gen (Aux.tveLookup_freevars_gen _ _ _ _ _ h3 h2)
    (Nat.zero_le _) (by omega) h1

/- HOL4:
Theorem tenv_val_exp_ok_db_merge:
 !e1 e2. tenv_val_exp_ok (db_merge e1 e2) ⇒ tenv_val_exp_ok e2 -/
theorem tenv_val_exp_ok_db_merge :
    ∀ (e1 e2 : tenv_val_exp), tenv_val_exp_ok (db_merge e1 e2) → tenv_val_exp_ok e2 := by
  intro e1 e2 h
  induction e1 with
  | Empty => exact h
  | Bind_tvar k e ih => exact ih h
  | Bind_name x k t e ih => exact ih h.2

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
      check_freevars (tvs + inc + num_tvs e) [] t :=
  fun e n inc t tvs ⟨h1, h2⟩ => Aux.tveLookup_freevars_gen e n inc t tvs h1 h2

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
  rintro tvs l tenv n t ⟨h1, h2⟩
  induction tenv generalizing tvs with
  | Empty => exact Iff.rfl
  | Bind_tvar k e ih =>
    simp only [num_tvs] at h2
    have hk : k = 0 := by omega
    subst hk
    exact ih tvs h1 (by omega)
  | Bind_name x k t' e ih =>
    simp only [num_tvs] at h2
    simp only [tenv_val_exp_ok, h2, Nat.add_zero] at h1
    simp only [tveLookup]
    split
    · rw [nil_deBruijn_inc _ _ _ (Or.inl h1.1), nil_deBruijn_inc _ _ _ (Or.inl h1.1)]
    · exact ih _ h1.2 h2

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
  | cons p l ih =>
    obtain ⟨x, t⟩ := p
    simp only [bind_var_list, deBruijn_subst_tenvE, List.map_cons, num_tvs_bind_var_list, ih]

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
  | cons p l ih =>
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
    simp only [db_merge, tveLookup, num_tvs, ih]
    have : num_tvs e + (inc + k) = k + num_tvs e + inc := by omega
    rw [this]
  | Bind_name x k t' e ih =>
    simp only [db_merge, tveLookup, num_tvs]
    split
    · simp
    · exact ih _

/- HOL4:
Theorem type_op_cases =
  ``type_op op ts t3``
  [HOL4 proof text removed]
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
      | skip
    all_goals (repeat' (obtain ⟨_, h⟩ := h))
    all_goals subst_vars
    all_goals simp only [reduceCtorEq, false_and, exists_false, false_or, or_false]
    all_goals first
      | ((repeat' first | exact True.intro | rfl | assumption | apply And.intro | apply Exists.intro); done)
      | (refine Or.inl ?_; (repeat' first | exact True.intro | rfl | assumption | apply And.intro | apply Exists.intro); done)
      | (refine Or.inr ?_; (repeat' first | exact True.intro | rfl | assumption | apply And.intro | apply Exists.intro); done)
      | trace_state
  · intro h
    repeat' (apply Or.elim h <;> clear h <;> intro h)
    all_goals (repeat' (obtain ⟨_, h⟩ := h))
    all_goals subst_vars
    all_goals simp only [type_op.eq_def]
    all_goals first
      | ((repeat' first | exact True.intro | rfl | assumption | apply And.intro | apply Exists.intro); done)
      | trace_state

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
    | cons _ _ t ts b b' h1 h2 => simp [ih _ _ h2]

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
  refine Aux.type_p_ind
    (P := fun tvs _ _ t env' => check_freevars tvs [] t ∧
      EVERY (check_freevars tvs []) (env'.map Prod.snd))
    (Q := fun tvs _ _ ts env' => EVERY (check_freevars tvs []) ts ∧
      EVERY (check_freevars tvs []) (env'.map Prod.snd))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro tvs tenv t h; exact ⟨h, trivial⟩
  · intro tvs tenv n t h; exact ⟨h, h, trivial⟩
  · intros; simp [Tint, check_freevars, EVERY]
  · intros; simp [Tchar, check_freevars, EVERY]
  · intros; simp [Tstring, check_freevars, EVERY]
  · intros; simp [Tword8, check_freevars, EVERY]
  · intros; simp [Tword64, check_freevars, EVERY]
  · intro tvs tenv cn ps ts tvs' tn ts' b h1 h2 h3 h4 ih
    refine ⟨?_, ih.2⟩
    simp only [check_freevars]
    exact h1
  · intro tvs tenv ps ts b h1 ih
    refine ⟨?_, ih.2⟩
    simp only [Ttup, check_freevars]
    exact ih.1
  · intro tvs tenv p t b h1 ih
    refine ⟨?_, ih.2⟩
    simp only [Tref, check_freevars]
    exact ⟨ih.1, trivial⟩
  · intro tvs tenv p v t b h1 ih
    refine ⟨ih.1, ?_⟩
    rw [List.map_append, Aux.EVERY_append]
    exact ⟨ih.2, ih.1, trivial⟩
  · intro tvs tenv p t b h1 h2 h3 ih
    exact ih
  · intros; exact ⟨trivial, trivial⟩
  · intro tvs tenv p ps t ts b b' h1 h2 ih1 ih2
    refine ⟨⟨ih1.1, ih2.1⟩, ?_⟩
    rw [List.map_append, Aux.EVERY_append]
    exact ⟨ih2.2, ih1.2⟩

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
  have H := Aux.type_p_ind
    (P := fun n tenv p t new_bindings => ∀ (inc tvs : Nat) (targs : List typ),
        tenv_abbrev_ok tenv.t → tenv_ctor_ok tenv.c → n = inc + targs.length →
        EVERY (check_freevars tvs []) targs →
        type_p (inc + tvs) tenv p (deBruijn_subst inc (targs.map (deBruijn_inc 0 inc)) t)
          (new_bindings.map (fun (x, t) =>
            (x, deBruijn_subst inc (targs.map (deBruijn_inc 0 inc)) t))))
    (Q := fun n tenv ps ts new_bindings => ∀ (inc tvs : Nat) (targs : List typ),
        tenv_abbrev_ok tenv.t → tenv_ctor_ok tenv.c → n = inc + targs.length →
        EVERY (check_freevars tvs []) targs →
        type_ps (inc + tvs) tenv ps
          (ts.map (deBruijn_subst inc (targs.map (deBruijn_inc 0 inc))))
          (new_bindings.map (fun (x, t) =>
            (x, deBruijn_subst inc (targs.map (deBruijn_inc 0 inc)) t))))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · refine ⟨?_, ?_⟩
    · rintro n tenv p t nb h targs' inc tvs targs ⟨h1, h2, h3, h4, rfl⟩
      exact H.1 n tenv p t nb h inc tvs targs h1 h2 h3 h4
    · rintro n tenv p t nb h targs' inc targs tvs ⟨h1, h2, h3, h4, rfl⟩
      exact H.2 n tenv p t nb h inc tvs targs h1 h2 h3 h4
  · intro n tenv t h inc tvs targs h1 h2 h3 h4
    exact type_p.any _ _ _ (type_e_subst_lem3 _ _ _ h _ _ _ ⟨h3, h4⟩)
  · intro n tenv x t h inc tvs targs h1 h2 h3 h4
    exact type_p.var _ _ _ _ (type_e_subst_lem3 _ _ _ h _ _ _ ⟨h3, h4⟩)
  · intro n tenv k inc tvs targs h1 h2 h3 h4
    simp only [Tint, deBruijn_subst, List.map_nil]; exact type_p.intLit _ _ _
  · intro n tenv k inc tvs targs h1 h2 h3 h4
    simp only [Tchar, deBruijn_subst, List.map_nil]; exact type_p.char _ _ _
  · intro n tenv k inc tvs targs h1 h2 h3 h4
    simp only [Tstring, deBruijn_subst, List.map_nil]; exact type_p.strLit _ _ _
  · intro n tenv k inc tvs targs h1 h2 h3 h4
    simp only [Tword8, deBruijn_subst, List.map_nil]; exact type_p.word8 _ _ _
  · intro n tenv k inc tvs targs h1 h2 h3 h4
    simp only [Tword64, deBruijn_subst, List.map_nil]; exact type_p.word64 _ _ _
  · intro n tenv cn ps ts tvs' tn ts' b hc hl hps hlk ih inc tvs targs h1 h2 h3 h4
    have := ih inc tvs targs h1 h2 h3 h4
    rw [type_subst_deBruijn_subst_list () tvs' () ts' _ ts inc
      ⟨hl.symm, tenv_ctor_ok_lookup _ _ _ _ _ ⟨h2, hlk⟩⟩] at this
    simp only [deBruijn_subst]
    refine type_p.con _ _ _ _ _ _ _ _ _ ?_ (by rw [List.length_map]; exact hl) this hlk
    rw [EVERY_iff_forall] at hc ⊢
    intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    exact type_e_subst_lem3 _ _ _ (hc y hy) _ _ _ ⟨h3, h4⟩
  · intro n tenv ps ts b hps ih inc tvs targs h1 h2 h3 h4
    simp only [Ttup, deBruijn_subst]
    exact type_p.tup _ _ _ _ _ (ih inc tvs targs h1 h2 h3 h4)
  · intro n tenv p t b hp ih inc tvs targs h1 h2 h3 h4
    simp only [Tref, deBruijn_subst]
    exact type_p.ref _ _ _ _ _ (ih inc tvs targs h1 h2 h3 h4)
  · intro n tenv p v t b hp ih inc tvs targs h1 h2 h3 h4
    rw [List.map_append]
    exact type_p.pas _ _ _ _ _ _ (ih inc tvs targs h1 h2 h3 h4)
  · intro n tenv p t b hc1 hc2 hp ih inc tvs targs h1 h2 h3 h4
    have := ih inc tvs targs h1 h2 h3 h4
    have hn : deBruijn_subst inc (targs.map (deBruijn_inc 0 inc)) (type_name_subst tenv.t t) =
      type_name_subst tenv.t t :=
      nil_deBruijn_subst _ _ _ (check_freevars_type_name_subst _ _ _ _ ⟨h1, hc2, hc1⟩)
    rw [hn] at this ⊢
    exact type_p.tannot _ _ _ _ _ hc1 hc2 this
  · intro n tenv inc tvs targs h1 h2 h3 h4
    exact type_ps.nil _ _
  · intro n tenv p ps t ts b b' hp hps ih1 ih2 inc tvs targs h1 h2 h3 h4
    rw [List.map_append]
    exact type_ps.cons _ _ _ _ _ _ _ _ (ih1 inc tvs targs h1 h2 h3 h4)
      (ih2 inc tvs targs h1 h2 h3 h4)

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
      EVERY (check_freevars tvs []) (bindings.map Prod.snd) →
      tenv_val_exp_ok tenv' → tenv_val_exp_ok (bind_var_list tvs bindings tenv') := by
    intro tvs bindings tenv' h1 h2
    exact Aux.bvl_ok _ _ _ h2
      (Aux.EVERY_mono (fun x _ hx => check_freevars_add _ _ _ hx _ (Nat.le_add_right _ _)) h1)
  exact ⟨fun tvs tenvC p t b h tenv' => key _ _ _ (type_p_freevars.1 _ _ _ _ _ h).2,
    fun tvs tenvC p t b h tenv' => key _ _ _ (type_p_freevars.2 _ _ _ _ _ h).2⟩

theorem Aux.type_p_env :
    (∀ (tvs : Nat) (tenv : type_env) (p : pat) (t : typ) (b : List (varN × typ)),
      type_p tvs tenv p t b →
      ∀ tenv' : type_env, tenv'.c = tenv.c → tenv'.t = tenv.t → type_p tvs tenv' p t b) ∧
    (∀ (tvs : Nat) (tenv : type_env) (ps : List pat) (ts : List typ) (b : List (varN × typ)),
      type_ps tvs tenv ps ts b →
      ∀ tenv' : type_env, tenv'.c = tenv.c → tenv'.t = tenv.t → type_ps tvs tenv' ps ts b) := by
  refine Aux.type_p_ind
    (P := fun tvs tenv p t b =>
      ∀ tenv' : type_env, tenv'.c = tenv.c → tenv'.t = tenv.t → type_p tvs tenv' p t b)
    (Q := fun tvs tenv ps ts b =>
      ∀ tenv' : type_env, tenv'.c = tenv.c → tenv'.t = tenv.t → type_ps tvs tenv' ps ts b)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro tvs tenv t h tenv' hc ht; exact type_p.any _ _ _ h
  · intro tvs tenv x t h tenv' hc ht; exact type_p.var _ _ _ _ h
  · intro _ _ _ _ _ _; exact type_p.intLit _ _ _
  · intro _ _ _ _ _ _; exact type_p.char _ _ _
  · intro _ _ _ _ _ _; exact type_p.strLit _ _ _
  · intro _ _ _ _ _ _; exact type_p.word8 _ _ _
  · intro _ _ _ _ _ _; exact type_p.word64 _ _ _
  · intro tvs tenv cn ps ts tvs' tn ts' b h1 h2 h3 h4 ih tenv' hc ht
    exact type_p.con _ _ _ _ _ _ _ _ _ h1 h2 (ih tenv' hc ht) (by rw [hc]; exact h4)
  · intro tvs tenv ps ts b h1 ih tenv' hc ht
    exact type_p.tup _ _ _ _ _ (ih tenv' hc ht)
  · intro tvs tenv p t b h1 ih tenv' hc ht
    exact type_p.ref _ _ _ _ _ (ih tenv' hc ht)
  · intro tvs tenv p v t b h1 ih tenv' hc ht
    exact type_p.pas _ _ _ _ _ _ (ih tenv' hc ht)
  · intro tvs tenv p t b h1 h2 h3 ih tenv' hc ht
    have := ih tenv' hc ht
    rw [← ht] at this h2 ⊢
    exact type_p.tannot _ _ _ _ _ h1 h2 this
  · intro _ _ _ _ _; exact type_ps.nil _ _
  · intro tvs tenv p ps t ts b b' h1 h2 ih1 ih2 tenv' hc ht
    exact type_ps.cons _ _ _ _ _ _ _ _ (ih1 tenv' hc ht) (ih2 tenv' hc ht)

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
      type_ps tvs tenv ps t bindings ↔ type_ps tvs { tenv with v := tenvV } ps t bindings) :=
  ⟨fun _ _ _ _ _ _ => ⟨fun h => Aux.type_p_env.1 _ _ _ _ _ h _ rfl rfl,
      fun h => Aux.type_p_env.1 _ _ _ _ _ h _ rfl rfl⟩,
    fun _ _ _ _ _ _ => ⟨fun h => Aux.type_p_env.2 _ _ _ _ _ h _ rfl rfl,
      fun h => Aux.type_p_env.2 _ _ _ _ _ h _ rfl rfl⟩⟩

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
      | cons _ _ _ t ts h1 h2 => exact ⟨h1, (ih _ _ _).mp h2⟩
    · intro h
      cases ts with
      | nil => exact h.elim
      | cons t ts => exact type_es.cons _ _ _ _ _ _ h.1 ((ih _ _ _).mpr h.2)

/- HOL4:
Theorem type_es_length:
 ∀tenv tenvE es ts.
  type_es tenv tenvE es ts ⇒ (LENGTH es = LENGTH ts) -/
theorem type_es_length :
    ∀ (tenv : type_env) (tenvE : tenv_val_exp) (es : List exp) (ts : List typ),
      type_es tenv tenvE es ts → es.length = ts.length :=
  fun _ _ _ _ h => Aux.LIST_REL_length ((type_es_list_rel _ _ _ _).mp h)

theorem Aux.type_funs_cons_inv {tenv : type_env} {tenvE : tenv_val_exp} {fn n : varN} {e : exp}
    {funs : List (varN × varN × exp)} {bs : List (varN × typ)}
    (h : type_funs tenv tenvE ((fn, n, e) :: funs) bs) :
    ∃ t1 t2 bs', bs = (fn, Tfn t1 t2) :: bs' ∧
      check_freevars (num_tvs tenvE) [] (Tfn t1 t2) ∧
      type_e tenv (Bind_name n 0 t1 tenvE) e t2 ∧ type_funs tenv tenvE funs bs' ∧
      ALOOKUP bs' fn = none := by
  cases h with
  | cons _ _ _ _ _ bs' t1 t2 h1 h2 h3 h4 => exact ⟨t1, t2, bs', rfl, h1, h2, h3, h4⟩

theorem Aux.type_funs_nil_inv {tenv : type_env} {tenvE : tenv_val_exp}
    {bs : List (varN × typ)} (h : type_funs tenv tenvE [] bs) : bs = [] := by
  cases h; rfl

theorem Aux.type_funs_check {tenv : type_env} {tenvE : tenv_val_exp}
    {funs : List (varN × varN × exp)} {bs : List (varN × typ)}
    (h : type_funs tenv tenvE funs bs) :
    EVERY (check_freevars (num_tvs tenvE) []) (bs.map Prod.snd) := by
  induction funs generalizing bs with
  | nil => rw [Aux.type_funs_nil_inv h]; trivial
  | cons f funs ih =>
    obtain ⟨fn, n, e⟩ := f
    obtain ⟨t1, t2, bs', rfl, h1, h2, h3, h4⟩ := Aux.type_funs_cons_inv h
    exact ⟨h1, ih h3⟩

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
  rintro funs env tenv bindings - tenvE ⟨h1, h2⟩
  have := Aux.type_funs_check h1
  rw [num_tvs_bind_var_list] at this
  exact tenv_val_exp_ok_bvl _ _ ⟨h2, this⟩

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
  refine Aux.type_e_ind
    (P := fun tenv tenvE _ t => tenv_val_exp_ok tenvE ∧ tenv_val_ok tenv.v →
      check_freevars (num_tvs tenvE) [] t)
    (Q := fun tenv tenvE _ ts => tenv_val_exp_ok tenvE ∧ tenv_val_ok tenv.v →
      EVERY (check_freevars (num_tvs tenvE) []) ts)
    (R := fun tenv tenvE _ env => tenv_val_exp_ok tenvE ∧ tenv_val_ok tenv.v →
      EVERY (check_freevars (num_tvs tenvE) []) (env.map Prod.snd))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intros; simp [Tint, check_freevars, EVERY]
  · intros; simp [Tchar, check_freevars, EVERY]
  · intros; simp [Tstring, check_freevars, EVERY]
  · intros; simp [Tword8, check_freevars, EVERY]
  · intros; simp [Tword64, check_freevars, EVERY]
  · intros; simp [Tdouble, check_freevars, EVERY]
  · intro tenv tenvE e t h1 h2 ih h; exact h1
  · intro tenv tenvE e pes t bs h1 h2 h3 h4 h5 ih1 ih2 h
    exact ih1 h
  · intro tenv tenvE cn es tvs tn ts' ts h1 h2 h3 h4 ih h
    simp only [check_freevars]; exact h1
  · intro tenv tenvE es ts h1 ih h
    simp only [Ttup, check_freevars]; exact ih h
  · rintro tenv tenvE n t targs tvs rfl h1 h2 ⟨h3, h4⟩
    unfold lookup_var at h2
    split at h2
    · rename_i x hx
      cases h2
      unfold lookup_varE at hx
      split at hx
      · have := tveLookup_freevars_subst tenvE targs _ t 0
          ⟨by rw [Nat.zero_add]; exact h1, hx, h3⟩
        rwa [Nat.zero_add] at this
      · cases hx
    · have := h4 _ _ h2
      exact deBruijn_subst_check_freevars2 _ _ _ _ () () ⟨this, h1⟩
  · intro tenv tenvE n e t1 t2 h1 h2 ih h
    simp only [Tfn, check_freevars, EVERY]
    refine ⟨h1, ih ⟨⟨?_, h.1⟩, h.2⟩, trivial⟩
    rw [Nat.zero_add]; exact h1
  · intro tenv tenvE o es ts t h1 h2 h3 ih h; exact h3
  · intro tenv tenvE l e1 e2 h1 h2 ih1 ih2 h; exact ih1 h
  · intro tenv tenvE e1 e2 e3 t h1 h2 h3 ih1 ih2 ih3 h; exact ih2 h
  · intro tenv tenvE e pes t1 t2 bs h1 h2 h3 h4 h5 ih1 ih2 h
    cases pes with
    | nil => exact absurd rfl h2
    | cons pe pes =>
      have := ih2 pe List.mem_cons_self
        ⟨tenv_val_exp_ok_bvl _ _ ⟨h.1,
          (type_p_freevars.1 _ _ _ _ _ (h4 pe List.mem_cons_self)).2⟩, h.2⟩
      rwa [num_tvs_bind_var_list] at this
  · intro tenv tenvE n e1 e2 t1 t2 h1 h2 ih1 ih2 h
    cases n with
    | none => exact ih2 h
    | some x =>
      refine ih2 ⟨⟨?_, h.1⟩, h.2⟩
      rw [Nat.zero_add]; exact ih1 h
  · intro tenv tenvE funs e t bindings h1 h2 ih1 ih2 h
    have := ih2 ⟨tenv_val_exp_ok_bvl_funs _ _ _ _ () _ ⟨h1, h.1⟩, h.2⟩
    rwa [num_tvs_bind_var_list] at this
  · intro tenv tenvE e t h1 h2 h3 ih h; exact ih h
  · intro tenv tenvE e l t h1 ih h; exact ih h
  · intro _ _ _; trivial
  · intro tenv tenvE e es t ts h1 h2 ih1 ih2 h
    exact ⟨ih1 h, ih2 h⟩
  · intro _ _ _; trivial
  · intro tenv tenvE fn n e funs bs t1 t2 h1 h2 h3 h4 ih1 ih2 h
    exact ⟨h1, ih2 h⟩

theorem Aux.subst_t_of (k : Nat) (ts : List typ) (ty : prim_type) :
    deBruijn_subst k ts (t_of ty) = t_of ty := by
  cases ty with
  | WordT sz => cases sz <;> simp [t_of, Tword8, Tword64, deBruijn_subst]
  | _ => simp [t_of, Tbool, Tint, Tchar, Tstring, Tdouble, deBruijn_subst]

theorem Aux.type_op_subst (k : Nat) (targs : List typ) (o : op) (ts : List typ) (t : typ)
    (h : type_op o ts t) :
    type_op o (ts.map (deBruijn_subst k targs)) (deBruijn_subst k targs t) := by
  rw [type_op_cases] at h
  repeat' (apply Or.elim h <;> clear h <;> intro h)
  all_goals (repeat' (obtain ⟨_, h⟩ := h))
  all_goals subst_vars
  all_goals simp only [List.map_cons, List.map_nil, deBruijn_subst, Tfn, Tword8, Tword64, Tbool,
    Tref, Ttup, Tint, Tword8array, Tstring, Tlist, Tchar, Tvector, Tarray, type_op.eq_def,
    Aux.subst_t_of, List.length_map]
  all_goals first
    | ((repeat' first | exact True.intro | rfl | assumption | apply And.intro | apply Exists.intro); done)
    | skip
  rename_i hev
  simp only [EVERY_iff_forall, List.mem_map] at hev ⊢
  refine ⟨?_, trivial, h⟩
  rintro x ⟨y, hy, rfl⟩
  rw [hev y hy, Aux.subst_t_of]

theorem Aux.num_E {tenvE1 tenvE2 : tenv_val_exp} (targs : List typ) (tvs : Nat)
    (h0 : num_tvs tenvE2 = 0) :
    num_tvs (db_merge tenvE1 (bind_tvar targs.length tenvE2)) =
      num_tvs tenvE1 + targs.length ∧
    num_tvs (db_merge (deBruijn_subst_tenvE targs tenvE1) (bind_tvar tvs tenvE2)) =
      num_tvs tenvE1 + tvs := by
  rw [num_tvs_db_merge, num_tvs_db_merge, Aux.num_tvs_bind_tvar, Aux.num_tvs_bind_tvar,
    num_tvs_deBruijn_subst_tenvE]
  omega

theorem Aux.chk_E {tenvE1 tenvE2 : tenv_val_exp} {targs : List typ} {tvs : Nat}
    (h0 : num_tvs tenvE2 = 0) (h5 : EVERY (check_freevars tvs []) targs) {t : typ}
    (h : check_freevars (num_tvs (db_merge tenvE1 (bind_tvar targs.length tenvE2))) [] t) :
    check_freevars
      (num_tvs (db_merge (deBruijn_subst_tenvE targs tenvE1) (bind_tvar tvs tenvE2))) []
      (deBruijn_subst (num_tvs tenvE1) (targs.map (deBruijn_inc 0 (num_tvs tenvE1))) t) := by
  obtain ⟨e1, e2⟩ := Aux.num_E (tenvE1 := tenvE1) targs tvs h0
  rw [e1] at h
  rw [e2]
  exact type_e_subst_lem3 _ _ _ h _ _ _ ⟨rfl, h5⟩

theorem Aux.bvl_E (targs : List typ) (tvs : Nat) (bs : List (mlstring × typ))
    (tenvE1 tenvE2 : tenv_val_exp) :
    db_merge (deBruijn_subst_tenvE targs (bind_var_list 0 bs tenvE1)) (bind_tvar tvs tenvE2) =
      bind_var_list 0 (bs.map (fun (x, t) => (x, deBruijn_subst (num_tvs tenvE1)
        (targs.map (deBruijn_inc 0 (num_tvs tenvE1))) t)))
        (db_merge (deBruijn_subst_tenvE targs tenvE1) (bind_tvar tvs tenvE2)) := by
  rw [deBruijn_subst_E_bvl, db_merge_bvl, Nat.zero_add]

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
  have H := Aux.type_e_ind
    (P := fun tenv tenvE e t => ∀ (tenvE1 : tenv_val_exp) (targs : List typ) (tvs : Nat),
      num_tvs tenvE2 = 0 → tenv_abbrev_ok tenv.t → tenv_ctor_ok tenv.c → tenv_val_ok tenv.v →
      tenv_val_exp_ok tenvE → EVERY (check_freevars tvs []) targs →
      tenvE = db_merge tenvE1 (bind_tvar targs.length tenvE2) →
      type_e tenv (db_merge (deBruijn_subst_tenvE targs tenvE1) (bind_tvar tvs tenvE2)) e
        (deBruijn_subst (num_tvs tenvE1) (targs.map (deBruijn_inc 0 (num_tvs tenvE1))) t))
    (Q := fun tenv tenvE es ts => ∀ (tenvE1 : tenv_val_exp) (targs : List typ) (tvs : Nat),
      num_tvs tenvE2 = 0 → tenv_abbrev_ok tenv.t → tenv_ctor_ok tenv.c → tenv_val_ok tenv.v →
      tenv_val_exp_ok tenvE → EVERY (check_freevars tvs []) targs →
      tenvE = db_merge tenvE1 (bind_tvar targs.length tenvE2) →
      type_es tenv (db_merge (deBruijn_subst_tenvE targs tenvE1) (bind_tvar tvs tenvE2)) es
        (ts.map (deBruijn_subst (num_tvs tenvE1) (targs.map (deBruijn_inc 0 (num_tvs tenvE1))))))
    (R := fun tenv tenvE funs env => ∀ (tenvE1 : tenv_val_exp) (targs : List typ) (tvs : Nat),
      num_tvs tenvE2 = 0 → tenv_abbrev_ok tenv.t → tenv_ctor_ok tenv.c → tenv_val_ok tenv.v →
      tenv_val_exp_ok tenvE → EVERY (check_freevars tvs []) targs →
      tenvE = db_merge tenvE1 (bind_tvar targs.length tenvE2) →
      type_funs tenv (db_merge (deBruijn_subst_tenvE targs tenvE1) (bind_tvar tvs tenvE2)) funs
        (env.map (fun (x, t) => (x, deBruijn_subst (num_tvs tenvE1)
          (targs.map (deBruijn_inc 0 (num_tvs tenvE1))) t))))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · refine ⟨?_, ?_, ?_⟩
    · rintro tenv tenvE e t h tenvE1 targs tvs targs' ⟨h0, h1, h2, h3, h4, h5, h6, rfl⟩
      exact H.1 tenv tenvE e t h tenvE1 targs tvs h0 h1 h2 h3 h4 h5 h6
    · rintro tenv tenvE e t h tenvE1 targs tvs targs' ⟨h0, h1, h2, h3, h4, h5, h6, rfl⟩
      exact H.2.1 tenv tenvE e t h tenvE1 targs tvs h0 h1 h2 h3 h4 h5 h6
    · rintro tenv tenvE e t h tenvE1 targs tvs targs' ⟨h0, h1, h2, h3, h4, h5, h6, rfl⟩
      exact H.2.2 tenv tenvE e t h tenvE1 targs tvs h0 h1 h2 h3 h4 h5 h6
  · intro tenv tenvE n tenvE1 targs tvs h0 h1 h2 h3 h4 h5 h6
    simp only [Tint, deBruijn_subst, List.map_nil]; exact type_e.intLit _ _ _
  · intro tenv tenvE n tenvE1 targs tvs h0 h1 h2 h3 h4 h5 h6
    simp only [Tchar, deBruijn_subst, List.map_nil]; exact type_e.char _ _ _
  · intro tenv tenvE n tenvE1 targs tvs h0 h1 h2 h3 h4 h5 h6
    simp only [Tstring, deBruijn_subst, List.map_nil]; exact type_e.strLit _ _ _
  · intro tenv tenvE n tenvE1 targs tvs h0 h1 h2 h3 h4 h5 h6
    simp only [Tword8, deBruijn_subst, List.map_nil]; exact type_e.word8 _ _ _
  · intro tenv tenvE n tenvE1 targs tvs h0 h1 h2 h3 h4 h5 h6
    simp only [Tword64, deBruijn_subst, List.map_nil]; exact type_e.word64 _ _ _
  · intro tenv tenvE n tenvE1 targs tvs h0 h1 h2 h3 h4 h5 h6
    simp only [Tdouble, deBruijn_subst, List.map_nil]; exact type_e.float64 _ _ _
  · intro tenv tenvE e t hc he ih tenvE1 targs tvs h0 h1 h2 h3 h4 h5 h6
    subst h6
    have := ih tenvE1 targs tvs h0 h1 h2 h3 h4 h5 rfl
    simp only [Texn, deBruijn_subst, List.map_nil] at this
    exact type_e.raise _ _ _ _ (Aux.chk_E h0 h5 hc) this
  · intro tenv tenvE e pes t bs he hne hd hp hpe ih1 ih2 tenvE1 targs tvs h0 h1 h2 h3 h4 h5 h6
    subst h6
    obtain ⟨n1, n2⟩ := Aux.num_E (tenvE1 := tenvE1) targs tvs h0
    refine type_e.handle _ _ _ _ _ (fun pe => (bs pe).map (fun (x, t) =>
      (x, deBruijn_subst (num_tvs tenvE1) (targs.map (deBruijn_inc 0 (num_tvs tenvE1))) t)))
      (ih1 tenvE1 targs tvs h0 h1 h2 h3 h4 h5 rfl) hne hd (fun pe hm => ?_) (fun pe hm => ?_)
    · have := type_p_subst.1 _ _ _ _ _ (hp pe hm) _ (num_tvs tenvE1) tvs targs
        ⟨h1, h2, n1, h5, rfl⟩
      rw [n2]
      simpa only [Texn, deBruijn_subst, List.map_nil] using this
    · have := ih2 pe hm (bind_var_list 0 (bs pe) tenvE1) targs tvs h0 h1 h2 h3
        (tenv_val_exp_ok_bvl _ _ ⟨h4, (type_p_freevars.1 _ _ _ _ _ (hp pe hm)).2⟩) h5
        (db_merge_bvl _ _ _ _).symm
      rw [Aux.bvl_E, num_tvs_bind_var_list] at this
      exact this
  · intro tenv tenvE cn es tvs' tn ts' ts hc hl hes hlk ih tenvE1 targs tvs h0 h1 h2 h3 h4 h5 h6
    subst h6
    have := ih tenvE1 targs tvs h0 h1 h2 h3 h4 h5 rfl
    rw [type_subst_deBruijn_subst_list () tvs' () ts' _ ts _
      ⟨hl, tenv_ctor_ok_lookup _ _ _ _ _ ⟨h2, hlk⟩⟩] at this
    simp only [deBruijn_subst]
    refine type_e.con _ _ _ _ _ _ _ _ ?_ (by rw [List.length_map]; exact hl) this hlk
    rw [EVERY_iff_forall] at hc ⊢
    intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    exact Aux.chk_E h0 h5 (hc y hy)
  · intro tenv tenvE es ts hes ih tenvE1 targs tvs h0 h1 h2 h3 h4 h5 h6
    simp only [Ttup, deBruijn_subst]
    exact type_e.tup _ _ _ _ (ih tenvE1 targs tvs h0 h1 h2 h3 h4 h5 h6)
  · intro tenv tenvE n t targs0 tvs0 htv hc hlk tenvE1 targs tvs h0 h1 h2 h3 h4 h5 h6
    subst h6 htv
    rw [(type_e_subst_lem7 (α := Unit) (β := Unit) (γ := Unit) (δ := Unit)).1 t _ targs0 targs
      () ()]
    refine type_e.var _ _ _ _ _ targs0.length (by rw [List.length_map]) ?_ ?_
    · rw [EVERY_iff_forall] at hc ⊢
      intro x hx
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
      exact Aux.chk_E h0 h5 (hc y hy)
    · have hok2 : tenv_val_exp_ok tenvE2 :=
        (Aux.ok_bind_tvar _ _).mp (tenv_val_exp_ok_db_merge _ _ h4)
      have key : ∀ t, check_freevars targs0.length [] t →
          deBruijn_subst (targs0.length + num_tvs tenvE1)
            (targs.map (deBruijn_inc 0 (targs0.length + num_tvs tenvE1))) t = t :=
        fun t h => nil_deBruijn_subst _ _ _ (check_freevars_add _ _ _ h _ (Nat.le_add_right _ _))
      have hnone : ∀ x, tveLookup x 0 (db_merge tenvE1 (bind_tvar targs.length tenvE2)) = none →
          tveLookup x 0 (db_merge (deBruijn_subst_tenvE targs tenvE1) (bind_tvar tvs tenvE2)) =
            none := by
        intro x hx
        rw [tveLookup_db_merge_none] at hx ⊢
        refine ⟨(tveLookup_subst_none _ _ _ _).mpr hx.1, ?_⟩
        have hx2 := hx.2
        rw [Aux.tveLookup_bind_tvar, tveLookup_inc_none] at hx2 ⊢
        exact hx2
      unfold lookup_var at hlk ⊢
      cases n with
      | Long mn id =>
        simp only [lookup_varE] at hlk ⊢
        rw [key t (h3 _ _ hlk)]
        exact hlk
      | Short x =>
        simp only [lookup_varE] at hlk ⊢
        cases hl : tveLookup x 0 (db_merge tenvE1 (bind_tvar targs.length tenvE2)) with
        | none =>
          rw [hl] at hlk
          rw [hnone x hl, key t (h3 _ _ hlk)]
          exact hlk
        | some p =>
          rw [hl] at hlk
          simp only [Option.some.injEq] at hlk
          subst hlk
          rw [tveLookup_db_merge_some] at hl
          have : tveLookup x 0 (db_merge (deBruijn_subst_tenvE targs tenvE1)
              (bind_tvar tvs tenvE2)) = some (targs0.length,
              deBruijn_subst (targs0.length + num_tvs tenvE1)
                (targs.map (deBruijn_inc 0 (targs0.length + num_tvs tenvE1))) t) := by
            rw [tveLookup_db_merge_some]
            rcases hl with hl | ⟨hl1, hl2⟩
            · exact Or.inl (tveLookup_subst_some _ _ _ _ _ _ hl)
            · refine Or.inr ⟨(tveLookup_subst_none _ _ _ _).mpr hl1, ?_⟩
              rw [Aux.tveLookup_bind_tvar, tveLookup_no_tvs _ _ _ _ _ ⟨hok2, h0⟩] at hl2 ⊢
              rw [key t (tveLookup_freevars _ _ _ _ _ ⟨hok2, h0, hl2⟩)]
              exact hl2
          rw [this]
  · intro tenv tenvE n e t1 t2 hc he ih tenvE1 targs tvs h0 h1 h2 h3 h4 h5 h6
    subst h6
    have := ih (Bind_name n 0 t1 tenvE1) targs tvs h0 h1 h2 h3
      ⟨by rw [Nat.zero_add]; exact hc, h4⟩ h5 rfl
    simp only [deBruijn_subst_tenvE, db_merge, num_tvs, Nat.zero_add] at this
    simp only [Tfn, deBruijn_subst, List.map_cons, List.map_nil]
    exact type_e.fn _ _ _ _ _ _ (Aux.chk_E h0 h5 hc) this
  · intro tenv tenvE o es ts t hes ho hc ih tenvE1 targs tvs h0 h1 h2 h3 h4 h5 h6
    subst h6
    exact type_e.app _ _ _ _ _ _ (ih tenvE1 targs tvs h0 h1 h2 h3 h4 h5 rfl)
      (Aux.type_op_subst _ _ _ _ _ ho) (Aux.chk_E h0 h5 hc)
  · intro tenv tenvE l e1 e2 he1 he2 ih1 ih2 tenvE1 targs tvs h0 h1 h2 h3 h4 h5 h6
    have a1 := ih1 tenvE1 targs tvs h0 h1 h2 h3 h4 h5 h6
    have a2 := ih2 tenvE1 targs tvs h0 h1 h2 h3 h4 h5 h6
    simp only [Tbool, deBruijn_subst, List.map_nil] at a1 a2 ⊢
    exact type_e.log _ _ _ _ _ a1 a2
  · intro tenv tenvE e1 e2 e3 t he1 he2 he3 ih1 ih2 ih3 tenvE1 targs tvs h0 h1 h2 h3 h4 h5 h6
    have a1 := ih1 tenvE1 targs tvs h0 h1 h2 h3 h4 h5 h6
    simp only [Tbool, deBruijn_subst, List.map_nil] at a1
    exact type_e.if' _ _ _ _ _ _ a1 (ih2 tenvE1 targs tvs h0 h1 h2 h3 h4 h5 h6)
      (ih3 tenvE1 targs tvs h0 h1 h2 h3 h4 h5 h6)
  · intro tenv tenvE e pes t1 t2 bs he hne hd hp hpe ih1 ih2 tenvE1 targs tvs h0 h1 h2 h3 h4 h5 h6
    subst h6
    obtain ⟨n1, n2⟩ := Aux.num_E (tenvE1 := tenvE1) targs tvs h0
    refine type_e.mat _ _ _ _ _ _ (fun pe => (bs pe).map (fun (x, t) =>
      (x, deBruijn_subst (num_tvs tenvE1) (targs.map (deBruijn_inc 0 (num_tvs tenvE1))) t)))
      (ih1 tenvE1 targs tvs h0 h1 h2 h3 h4 h5 rfl) hne hd (fun pe hm => ?_) (fun pe hm => ?_)
    · have := type_p_subst.1 _ _ _ _ _ (hp pe hm) _ (num_tvs tenvE1) tvs targs
        ⟨h1, h2, n1, h5, rfl⟩
      rw [n2]
      exact this
    · have := ih2 pe hm (bind_var_list 0 (bs pe) tenvE1) targs tvs h0 h1 h2 h3
        (tenv_val_exp_ok_bvl _ _ ⟨h4, (type_p_freevars.1 _ _ _ _ _ (hp pe hm)).2⟩) h5
        (db_merge_bvl _ _ _ _).symm
      rw [Aux.bvl_E, num_tvs_bind_var_list] at this
      exact this
  · intro tenv tenvE n e1 e2 t1 t2 he1 he2 ih1 ih2 tenvE1 targs tvs h0 h1 h2 h3 h4 h5 h6
    subst h6
    refine type_e.let' _ _ _ _ _ _ _ (ih1 tenvE1 targs tvs h0 h1 h2 h3 h4 h5 rfl) ?_
    cases n with
    | none => exact ih2 tenvE1 targs tvs h0 h1 h2 h3 h4 h5 rfl
    | some x =>
      have hc := type_e_freevars.1 _ _ _ _ he1 ⟨h4, h3⟩
      have := ih2 (Bind_name x 0 t1 tenvE1) targs tvs h0 h1 h2 h3
        ⟨by rw [Nat.zero_add]; exact hc, h4⟩ h5 rfl
      simp only [deBruijn_subst_tenvE, db_merge, num_tvs, Nat.zero_add] at this
      exact this
  · intro tenv tenvE funs e t bindings hf he ih1 ih2 tenvE1 targs tvs h0 h1 h2 h3 h4 h5 h6
    subst h6
    have hok := tenv_val_exp_ok_bvl_funs _ _ _ _ () _ ⟨hf, h4⟩
    have a1 := ih1 (bind_var_list 0 bindings tenvE1) targs tvs h0 h1 h2 h3 hok h5
      (db_merge_bvl _ _ _ _).symm
    have a2 := ih2 (bind_var_list 0 bindings tenvE1) targs tvs h0 h1 h2 h3 hok h5
      (db_merge_bvl _ _ _ _).symm
    rw [Aux.bvl_E, num_tvs_bind_var_list] at a1 a2
    exact type_e.letrec _ _ _ _ _ _ a1 a2
  · intro tenv tenvE e t hc1 hc2 he ih tenvE1 targs tvs h0 h1 h2 h3 h4 h5 h6
    have := ih tenvE1 targs tvs h0 h1 h2 h3 h4 h5 h6
    rw [nil_deBruijn_subst _ _ _ (check_freevars_type_name_subst _ _ _ _ ⟨h1, hc2, hc1⟩)]
      at this ⊢
    exact type_e.tannot _ _ _ _ hc1 hc2 this
  · intro tenv tenvE e l t he ih tenvE1 targs tvs h0 h1 h2 h3 h4 h5 h6
    exact type_e.lannot _ _ _ _ _ (ih tenvE1 targs tvs h0 h1 h2 h3 h4 h5 h6)
  · intro tenv tenvE tenvE1 targs tvs h0 h1 h2 h3 h4 h5 h6
    exact type_es.nil _ _
  · intro tenv tenvE e es t ts he hes ih1 ih2 tenvE1 targs tvs h0 h1 h2 h3 h4 h5 h6
    exact type_es.cons _ _ _ _ _ _ (ih1 tenvE1 targs tvs h0 h1 h2 h3 h4 h5 h6)
      (ih2 tenvE1 targs tvs h0 h1 h2 h3 h4 h5 h6)
  · intro tenv tenvE tenvE1 targs tvs h0 h1 h2 h3 h4 h5 h6
    exact type_funs.nil _ _
  · intro tenv tenvE fn n e funs bs t1 t2 hc he hf hl ih1 ih2 tenvE1 targs tvs h0 h1 h2 h3 h4 h5 h6
    subst h6
    have hc1 : check_freevars (num_tvs (db_merge tenvE1 (bind_tvar targs.length tenvE2))) [] t1 := by
      simp only [Tfn, check_freevars, EVERY] at hc
      exact hc.1
    have a1 := ih1 (Bind_name n 0 t1 tenvE1) targs tvs h0 h1 h2 h3
      ⟨by rw [Nat.zero_add]; exact hc1, h4⟩ h5 rfl
    simp only [deBruijn_subst_tenvE, db_merge, num_tvs, Nat.zero_add] at a1
    have a2 := ih2 tenvE1 targs tvs h0 h1 h2 h3 h4 h5 rfl
    have a3 := Aux.chk_E h0 h5 hc
    simp only [Tfn, deBruijn_subst, List.map_cons, List.map_nil] at a3 ⊢
    refine type_funs.cons _ _ _ _ _ _ _ _ _ a3 a1 a2 ?_
    have := Aux.ALOOKUP_map_snd (f := deBruijn_subst (num_tvs tenvE1)
      (targs.map (deBruijn_inc 0 (num_tvs tenvE1)))) (l := bs) (k := fn)
    rw [hl] at this
    exact this

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
  rintro tenv tenvE funs bindings - t n ⟨h1, h2⟩
  induction funs generalizing bindings with
  | nil => rw [Aux.type_funs_nil_inv h1] at h2; simp [ALOOKUP] at h2
  | cons f funs ih =>
    obtain ⟨fn, x, e⟩ := f
    obtain ⟨t1, t2, bs', rfl, a1, a2, a3, a4⟩ := Aux.type_funs_cons_inv h1
    simp only [ALOOKUP] at h2
    split at h2
    · cases h2; exact ⟨t1, t2, rfl, a1⟩
    · exact ih _ a3 h2

theorem Aux.type_funs_fst {tenv : type_env} {tenvE : tenv_val_exp}
    {funs : List (varN × varN × exp)} {bs : List (varN × typ)}
    (h : type_funs tenv tenvE funs bs) : funs.map Prod.fst = bs.map Prod.fst := by
  induction funs generalizing bs with
  | nil => rw [Aux.type_funs_nil_inv h]; rfl
  | cons f funs ih =>
    obtain ⟨fn, n, e⟩ := f
    obtain ⟨t1, t2, bs', rfl, h1, h2, h3, h4⟩ := Aux.type_funs_cons_inv h
    simp only [List.map_cons, ih h3]

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
  rintro fn tenvE funs bindings n e tenv ⟨h1, h2⟩
  apply Aux.mem_ALOOKUP_some
  rw [← Aux.type_funs_fst h2]
  exact List.mem_map.mpr ⟨_, h1, rfl⟩

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
  rintro fn - funs bindings - tenv tenvE t ⟨h1, h2⟩
  induction funs generalizing bindings with
  | nil => rw [Aux.type_funs_nil_inv h2] at h1; simp [ALOOKUP] at h1
  | cons f funs ih =>
    obtain ⟨g, x, e⟩ := f
    obtain ⟨t1, t2, bs', rfl, a1, a2, a3, a4⟩ := Aux.type_funs_cons_inv h2
    simp only [ALOOKUP] at h1
    rw [find_recfun]
    split at h1
    · rename_i hg
      exact ⟨x, e, by rw [if_pos hg]⟩
    · rename_i hg
      rw [if_neg hg]
      exact ih _ h1 a3

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
  rintro fn funs n e tenv tenvE bindings - t1 t2 ⟨h1, h2, h3⟩
  induction funs generalizing bindings with
  | nil => rw [Aux.type_funs_nil_inv h2] at h3; simp [ALOOKUP] at h3
  | cons f funs ih =>
    obtain ⟨g, x, e'⟩ := f
    obtain ⟨t1', t2', bs', rfl, a1, a2, a3, a4⟩ := Aux.type_funs_cons_inv h2
    simp only [ALOOKUP] at h3
    rw [find_recfun] at h1
    split at h3
    · rename_i hg
      rw [if_pos hg] at h1
      cases h1
      have h3 : some (Tfn t1' t2') = some (Tfn t1 t2) := h3
      simp only [Tfn, Option.some.injEq, typ.Tapp.injEq, List.cons.injEq, and_true] at h3
      obtain ⟨rfl, rfl⟩ := h3
      exact ⟨a2, a1⟩
    · rename_i hg
      rw [if_neg hg] at h1
      exact ih _ h1 a3 h3

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
  intro tenv tenvE funs bindings h
  induction funs generalizing bindings with
  | nil => trivial
  | cons f funs ih =>
    obtain ⟨g, x, e⟩ := f
    obtain ⟨t1, t2, bs', rfl, a1, a2, a3, a4⟩ := Aux.type_funs_cons_inv h
    refine ⟨?_, ih _ a3⟩
    have := Aux.ALOOKUP_none_iff.mp a4
    rw [← Aux.type_funs_fst a3] at this
    exact this

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
  rintro tenv tenvE e t targs tvs - ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
  have := (type_e_subst tenvE).1 _ _ _ _ h1 (Bind_name x 0 t1 tenv_val_exp.Empty) targs tvs _
    ⟨h2, h3, h4, h5, ⟨?_, h6⟩, h7, rfl, rfl⟩
  · simp only [deBruijn_subst_tenvE, db_merge, num_tvs, Nat.zero_add, deBruijn_inc0.2] at this
    exact this
  · rw [Nat.zero_add, Aux.num_tvs_bind_tvar, h2]
    exact h8

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
  intro tenvT next tds
  induction tds generalizing next with
  | nil =>
    rintro ids stamp x ⟨h1, h2⟩
    cases ids with
    | nil => simp [type_def_to_ctMap] at h1
    | cons _ _ => simp at h2
  | cons td tds ih =>
    rintro ids stamp x ⟨h1, h2⟩
    obtain ⟨tvs, tn, ctors⟩ := td
    cases ids with
    | nil => simp at h2
    | cons id ids =>
      simp only [type_def_to_ctMap, List.mem_append, List.mem_reverse, List.mem_map] at h1
      rcases h1 with h1 | ⟨⟨cn, ts⟩, hm, he⟩
      · obtain ⟨cn, i, rfl, a, b⟩ := ih (next + 1) ids stamp x ⟨h1, by simpa using h2⟩
        exact ⟨cn, i, rfl, by omega, by simp only [List.length_cons]; omega⟩
      · cases he
        exact ⟨cn, next, rfl, Nat.le_refl _, by simp only [List.length_cons]; omega⟩

theorem Aux.mem_ctMap {α β γ : Type}
    (tenvT : Namespace mlstring mlstring (List mlstring × typ))
    (tds : List (α × β × List (conN × List ast_t))) :
    ∀ (next : Nat) (ids : List γ) (stamp : CmlTS.stamp) (tvs : α) (ts : List typ) (id : γ),
      (stamp, (tvs, ts, id)) ∈ type_def_to_ctMap tenvT next tds ids →
      tds.length = ids.length →
      ∃ (j : Nat) (cn : conN) (tn : β) (ctors : List (conN × List ast_t)) (tsa : List ast_t),
        tds[j]? = some (tvs, tn, ctors) ∧ ids[j]? = some id ∧ stamp = TypeStamp cn (next + j) ∧
        (cn, tsa) ∈ ctors ∧ ts = tsa.map (type_name_subst tenvT) := by
  induction tds with
  | nil =>
    intro next ids stamp tvs ts id h1 h2
    cases ids with
    | nil => simp [type_def_to_ctMap] at h1
    | cons _ _ => simp at h2
  | cons td tds ih =>
    intro next ids stamp tvs ts id h1 h2
    obtain ⟨tvs', tn, ctors⟩ := td
    cases ids with
    | nil => simp at h2
    | cons id' ids =>
      simp only [type_def_to_ctMap, List.mem_append, List.mem_reverse, List.mem_map] at h1
      rcases h1 with h1 | ⟨⟨cn, tsa⟩, hm, he⟩
      · obtain ⟨j, cn, tn, ctors, tsa, a, b, rfl, c, d⟩ :=
          ih (next + 1) ids stamp tvs ts id h1 (by simpa using h2)
        refine ⟨j + 1, cn, tn, ctors, tsa, by simpa using a, by simpa using b, ?_, c, d⟩
        congr 1; omega
      · cases he
        exact ⟨0, cn, tn, ctors, tsa, by simp, by simp, rfl, hm, rfl⟩

theorem Aux.check_ctor_tenv_mem {tenvT : Namespace modN typeN (List tvarN × typ)}
    {tds : List (List tvarN × mlstring × List (conN × List ast_t))}
    (h : check_ctor_tenv tenvT tds) :
    ∀ tvs tn ctors, (tvs, tn, ctors) ∈ tds → ALL_DISTINCT tvs ∧
      check_dup_ctors (tvs, tn, ctors) ∧
      ∀ cn ts, (cn, ts) ∈ ctors →
        EVERY (check_freevars_ast tvs) ts ∧ EVERY (check_type_names tenvT) ts := by
  induction tds with
  | nil => intro tvs tn ctors hm; simp at hm
  | cons td tds ih =>
    obtain ⟨tvs', tn', ctors'⟩ := td
    intro tvs tn ctors hm
    simp only [check_ctor_tenv] at h
    obtain ⟨a, b, c, d, e⟩ := h
    rcases List.mem_cons.mp hm with hm | hm
    · cases hm
      exact ⟨b, a, fun cn ts hc => EVERY_iff_forall.mp c (cn, ts) hc⟩
    · exact ih e _ _ _ hm

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
  rintro ctMap1 ctMap2 ⟨hd, ⟨a1, a2, a3, a4⟩, ⟨b1, b2, b3, b4⟩⟩
  rw [Aux.DISJOINT_iff] at hd
  have key : ∀ k x, FLOOKUP (FUNION ctMap1 ctMap2) k = some x →
      FLOOKUP ctMap1 k = some x ∨ FLOOKUP ctMap2 k = some x := by
    intro k x h
    rw [Aux.FLOOKUP_FUNION] at h
    cases h1 : FLOOKUP ctMap1 k with
    | none => rw [h1] at h; exact Or.inr h
    | some y => rw [h1] at h; exact Or.inl h
  have hd' : ∀ k1 k2 tvs1 ts1 ti tvs2 ts2, FLOOKUP ctMap1 k1 = some (tvs1, ts1, ti) →
      FLOOKUP ctMap2 k2 = some (tvs2, ts2, ti) → False := by
    intro k1 k2 tvs1 ts1 ti tvs2 ts2 h1 h2
    refine hd ti ⟨k1, ?_⟩ ⟨k2, ?_⟩
    · rw [Aux.FLOOKUP_o_f, h1]; rfl
    · rw [Aux.FLOOKUP_o_f, h2]; rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro k x h
    rcases key k x h with h | h
    · exact a1 k x h
    · exact b1 k x h
  · intro ex tvs ts ti h
    rcases key _ _ h with h | h
    · exact a2 _ _ _ _ h
    · exact b2 _ _ _ _ h
  · intro cn x tvs ts ti h
    rcases key _ _ h with h | h
    · exact a3 _ _ _ _ _ h
    · exact b3 _ _ _ _ _ h
  · rintro s1 tvs1 ts1 ti s2 tvs2 ts2 ⟨h1, h2⟩
    rcases key _ _ h1 with h1 | h1 <;> rcases key _ _ h2 with h2 | h2
    · exact a4 _ _ _ _ _ _ _ ⟨h1, h2⟩
    · exact (hd' _ _ _ _ _ _ _ h1 h2).elim
    · exact (hd' _ _ _ _ _ _ _ h2 h1).elim
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
      EVERY (check_freevars 0 tvs) ts :=
  fun _ _ _ _ _ _ ⟨h1, h2⟩ => h1.1 _ _ h2

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
  rintro tenvT next tds tids ⟨h1, h2⟩
  obtain ⟨tvs, ts, id⟩ := x
  obtain ⟨j, cn, tn, ctors, tsa, a, b, -⟩ :=
    Aux.mem_ctMap tenvT tds next tids k tvs ts id (Aux.ALOOKUP_mem h1) h2
  exact List.mem_of_getElem? b

/- HOL4:
Theorem fupdate2_union[local]:
  !m a1 a2. m |++ a1 |++ a2 = FEMPTY |++ a2 ⊌ (m |++ a1) -/
theorem fupdate2_union {α β : Type} :
    ∀ (m : fmap α β) (a1 a2 : List (α × β)),
      FUPDATE_LIST (FUPDATE_LIST m a1) a2 =
        FUNION (FUPDATE_LIST FEMPTY a2) (FUPDATE_LIST m a1) := by
  intro m a1 a2
  apply Aux.fmap_ext
  intro x
  rw [Aux.FLOOKUP_FUNION, Aux.FLOOKUP_FUPDATE_LIST, Aux.FLOOKUP_FUPDATE_LIST (f := FEMPTY)]
  cases ALOOKUP a2.reverse x <;> rfl

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
  rintro tenvT next tds tids ⟨h1, h2, h3, h4, h5⟩
  rw [Aux.FUPDATE_LIST_reverse]
  have key : ∀ stamp tvs ts ti,
      FLOOKUP (alist_to_fmap (type_def_to_ctMap tenvT next tds tids)) stamp =
        some (tvs, ts, ti) →
      ∃ (j : Nat) (cn : conN), tids[j]? = some ti ∧ stamp = TypeStamp cn (next + j) ∧
        EVERY (check_freevars 0 tvs) ts := by
    intro stamp tvs ts ti h
    rw [Aux.FLOOKUP_alist_to_fmap] at h
    obtain ⟨j, cn, tn, ctors, tsa, a, b, c, d, rfl⟩ :=
      Aux.mem_ctMap tenvT tds next tids stamp tvs ts ti (Aux.ALOOKUP_mem h) h3
    refine ⟨j, cn, b, c, ?_⟩
    obtain ⟨-, -, hc⟩ := Aux.check_ctor_tenv_mem h4 _ _ _ (List.mem_of_getElem? a)
    obtain ⟨f1, f2⟩ := hc _ _ d
    rw [EVERY_iff_forall] at f1 f2 ⊢
    intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    exact check_freevars_type_name_subst _ _ _ _ ⟨h5, f2 y hy, f1 y hy⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro stamp ⟨tvs, ts, ti⟩ h
    obtain ⟨j, cn, a, b, c⟩ := key _ _ _ _ h
    exact c
  · intro ex tvs ts ti h
    obtain ⟨j, cn, a, b, c⟩ := key _ _ _ _ h
    cases b
  · intro cn x tvs ts ti h hm
    obtain ⟨j, cn, a, b, c⟩ := key _ _ _ _ h
    exact Aux.DISJOINT_iff.mp h2 ti (List.mem_of_getElem? a) hm
  · rintro s1 tvs1 ts1 ti s2 tvs2 ts2 ⟨g1, g2⟩
    obtain ⟨j1, cn1, a1, rfl, -⟩ := key _ _ _ _ g1
    obtain ⟨j2, cn2, a2, rfl, -⟩ := key _ _ _ _ g2
    have hj : j1 = j2 := by
      have hlt : j1 < tids.length := (List.getElem?_eq_some_iff.mp a1).1
      exact List.getElem?_inj hlt (Aux.ALL_DISTINCT_iff.mp h1) (a1.trans a2.symm)
    subst hj
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
  rintro tenvE tenvV n tvs t tvs2 ⟨h1, h2⟩
  induction tenvE generalizing tvs with
  | Empty => simp [tveLookup] at h2
  | Bind_tvar k e ih => exact ih _ h2
  | Bind_name x k t' e ih =>
    simp only [tveLookup] at h2
    simp only [add_tenvE, Aux.nsLookup_nsBind_if, ident.Short.injEq]
    split at h2
    · rename_i hx
      cases h2
      rw [if_pos hx.symm, nil_deBruijn_inc _ _ _ (Or.inr h1)]
    · rename_i hx
      rw [if_neg (fun e => hx e.symm)]
      exact ih _ h2

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
  rintro tenvE tenvV n tvs t tvs2 ⟨h1, h2⟩
  induction tenvE generalizing tvs with
  | Empty => exact h2
  | Bind_tvar k e ih => exact ih _ h1
  | Bind_name x k t' e ih =>
    simp only [tveLookup] at h1
    simp only [add_tenvE, Aux.nsLookup_nsBind_if, ident.Short.injEq]
    split at h1
    · cases h1
    · rename_i hx
      rw [if_neg (fun e => hx e.symm)]
      exact ih _ h1

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
  intro tenvE tenvV n t tvs2 mn h
  induction tenvE with
  | Empty => exact h
  | Bind_tvar k e ih => exact ih
  | Bind_name x k t' e ih =>
    simp only [add_tenvE, Aux.nsLookup_nsBind_if, reduceCtorEq, if_false]
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
  intro n bindings tenvE tenvV
  induction bindings with
  | nil => rfl
  | cons p l ih =>
    obtain ⟨x, t⟩ := p
    simp only [bind_var_list, add_tenvE, ih]
    rfl

theorem Aux.EVERY_pointwise {P : typ → Prop} {vs : List value} {ts : List typ}
    (hl : vs.length = ts.length)
    (h : ∀ (i : Nat) (v : value) (t : typ), vs[i]? = some v → ts[i]? = some t → P t) :
    EVERY P ts := by
  rw [EVERY_iff_forall]
  intro t ht
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp ht
  have hi' : i < vs.length := by omega
  exact h i vs[i] _ (List.getElem?_eq_getElem hi') (List.getElem?_eq_getElem hi)

theorem Aux.num_tvs_funs (bindings : List (mlstring × typ)) (tvs : Nat) (tenvE : tenv_val_exp)
    (h : num_tvs tenvE = 0) :
    num_tvs (bind_var_list 0 bindings (bind_tvar tvs tenvE)) = tvs := by
  rw [num_tvs_bind_var_list, Aux.num_tvs_bind_tvar, h, Nat.add_zero]

/- HOL4:
Theorem type_v_freevars:
 !tvs tenvC tenvS v t. type_v tvs tenvC tenvS v t ⇒ check_freevars tvs [] t -/
theorem type_v_freevars :
    ∀ (tvs : Nat) (tenvC : ctMap_ty) (tenvS : tenv_store) (v : value) (t : typ),
      type_v tvs tenvC tenvS v t → check_freevars tvs [] t := by
  intro tvs tenvC tenvS v t h
  induction h with
  | intLit => simp [Tint, check_freevars, EVERY]
  | char => simp [Tchar, check_freevars, EVERY]
  | strLit => simp [Tstring, check_freevars, EVERY]
  | word8 => simp [Tword8, check_freevars, EVERY]
  | word64 => simp [Tword64, check_freevars, EVERY]
  | float64 => simp [Tdouble, check_freevars, EVERY]
  | conv tvs ctMap tenvS vs tvs' stamp ts' ts ti h1 h2 h3 h4 h5 ih =>
    simp only [check_freevars]
    exact h1
  | tup tvs ctMap tenvS vs ts h1 h2 ih =>
    simp only [Ttup, check_freevars]
    exact Aux.EVERY_pointwise h1 ih
  | closure tvs ctMap tenvS env tenv tenvE n e t1 t2 h1 h2 h3 h4 h5 h6 h7 h8 ih =>
    have hn : num_tvs (Bind_name n 0 t1 (bind_tvar tvs tenvE)) = tvs := by
      simp only [num_tvs, Aux.num_tvs_bind_tvar, h3, Nat.add_zero]
    have := type_e_freevars.1 _ _ _ _ h8 ⟨⟨?_, (Aux.ok_bind_tvar _ _).mpr h2⟩, h1.1⟩
    · rw [hn] at this
      simp only [Tfn, check_freevars, EVERY]
      exact ⟨h7, this, trivial⟩
    · rw [Nat.zero_add, Aux.num_tvs_bind_tvar, h3]
      exact h7
  | recclosure tvs ctMap tenvS env funs n t tenv tenvE bindings h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 ih =>
    obtain ⟨t1, t2, rfl, hc⟩ := type_funs_Tfn _ _ _ _ () _ _ ⟨h7, h8⟩
    rwa [Aux.num_tvs_funs _ _ _ h3] at hc
  | ref tvs ctMap tenvS n t h1 h2 =>
    simp only [Tref, check_freevars, EVERY]
    exact ⟨check_freevars_add _ _ _ h1 _ (Nat.zero_le _), trivial⟩
  | w8array => simp [Tword8array, check_freevars, EVERY]
  | varray tvs ctMap tenvS n t h1 h2 =>
    simp only [Tarray, check_freevars, EVERY]
    exact ⟨check_freevars_add _ _ _ h1 _ (Nat.zero_le _), trivial⟩
  | vector tvs ctMap tenvS vs t h1 h2 ih =>
    simp only [Tvector, check_freevars, EVERY]
    exact ⟨check_freevars_add _ _ _ h1 _ (Nat.zero_le _), trivial⟩

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
  have key : ∀ (tvs : Nat) (ctMap : ctMap_ty) (tenvS : tenv_store) (v : value) (t : typ),
      type_v tvs ctMap tenvS v t → tvs = targs.length → ctMap_ok ctMap →
      EVERY (check_freevars tvs' []) targs →
      type_v tvs' ctMap tenvS v (deBruijn_subst 0 targs t) := by
    intro tvs ctMap tenvS v t h
    have nil0 : ∀ t, check_freevars 0 [] t → deBruijn_subst 0 targs t = t :=
      fun t h => nil_deBruijn_subst _ _ _ h
    induction h with
    | intLit => intros; simp only [Tint, deBruijn_subst, List.map_nil]; exact type_v.intLit _ _ _ _
    | char => intros; simp only [Tchar, deBruijn_subst, List.map_nil]; exact type_v.char _ _ _ _
    | strLit =>
      intros; simp only [Tstring, deBruijn_subst, List.map_nil]; exact type_v.strLit _ _ _ _
    | word8 => intros; simp only [Tword8, deBruijn_subst, List.map_nil]; exact type_v.word8 _ _ _ _
    | word64 =>
      intros; simp only [Tword64, deBruijn_subst, List.map_nil]; exact type_v.word64 _ _ _ _
    | float64 =>
      intros; simp only [Tdouble, deBruijn_subst, List.map_nil]; exact type_v.float64 _ _ _ _
    | conv tvs ctMap tenvS vs tvs'' stamp ts' ts ti h1 h2 h3 h4 h5 ih =>
      rintro rfl hok hts
      have hck := ctMap_ok_lookup _ () _ _ _ _ ⟨hok, h5⟩
      have e1 := type_subst_deBruijn_subst_list () tvs'' () ts' targs ts 0 ⟨h2, hck⟩
      rw [Aux.FUPDATE_LIST_reverse] at h3 ih
      simp only [deBruijn_subst]
      refine type_v.conv _ _ _ _ _ _ _ _ _ ?_ (by rw [List.length_map]; exact h2) ?_ ?_ h5
      · rw [EVERY_iff_forall] at h1 ⊢
        intro x hx
        obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
        exact deBruijn_subst_check_freevars2 _ _ _ _ () () ⟨h1 y hy, hts⟩
      · rw [Aux.FUPDATE_LIST_reverse, ← e1, List.length_map]
        exact h3
      · intro i v t hv ht
        rw [Aux.FUPDATE_LIST_reverse, ← e1, List.getElem?_map] at ht
        cases ht2 : (ts.map (type_subst (alist_to_fmap (tvs''.zip ts'))))[i]? with
        | none => rw [ht2] at ht; simp at ht
        | some t0 =>
          rw [ht2] at ht
          simp only [Option.map_some, Option.some.injEq] at ht
          subst ht
          exact ih i v t0 hv ht2 rfl hok hts
    | tup tvs ctMap tenvS vs ts h1 h2 ih =>
      rintro rfl hok hts
      simp only [Ttup, deBruijn_subst]
      refine type_v.tup _ _ _ _ _ (by rw [List.length_map]; exact h1) ?_
      intro i v t hv ht
      rw [List.getElem?_map] at ht
      cases ht2 : ts[i]? with
      | none => rw [ht2] at ht; simp at ht
      | some t0 =>
        rw [ht2] at ht
        simp only [Option.map_some, Option.some.injEq] at ht
        subst ht
        exact ih i v t0 hv ht2 rfl hok hts
    | closure tvs ctMap tenvS env tenv tenvE n e t1 t2 h1 h2 h3 h4 h5 h6 h7 h8 ih =>
      rintro rfl hok hts
      simp only [Tfn, deBruijn_subst, List.map_cons, List.map_nil]
      exact type_v.closure _ _ _ _ _ _ _ _ _ _ h1 h2 h3 h4 h5 h6
        (deBruijn_subst_check_freevars2 _ _ _ _ () () ⟨h7, hts⟩)
        (type_e_subst_lem _ _ _ _ _ _ _ _ () ⟨h8, h3, h1.2.2, h1.2.1, h1.1,
          (Aux.ok_bind_tvar _ _).mpr h2, hts, h7⟩)
    | recclosure tvs ctMap tenvS env funs n t tenv tenvE bindings h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 ih =>
      rintro rfl hok hts
      have hok2 := tenv_val_exp_ok_bvl_funs _ _ _ _ () _
        ⟨h7, (Aux.ok_bind_tvar targs.length tenvE).mpr h2⟩
      have := (type_e_subst tenvE).2.2 _ _ _ _ h7 (bind_var_list 0 bindings tenv_val_exp.Empty)
        targs tvs' _ ⟨h3, h1.2.2, h1.2.1, h1.1, hok2, hts,
          by rw [db_merge_bvl]; rfl, rfl⟩
      rw [Aux.bvl_E, num_tvs_bind_var_list] at this
      simp only [num_tvs, deBruijn_inc0.2, deBruijn_subst_tenvE, db_merge] at this
      refine type_v.recclosure _ _ _ _ _ _ _ _ _ _ h1 h2 h3 h4 h5 h6 this ?_ h9 h10
      have e := Aux.ALOOKUP_map_snd (f := deBruijn_subst 0 targs) (l := bindings) (k := n)
      rw [h8] at e
      exact e
    | ref tvs ctMap tenvS n t h1 h2 =>
      rintro rfl hok hts
      simp only [Tref, deBruijn_subst, List.map_cons, List.map_nil, nil0 t h1]
      exact type_v.ref _ _ _ _ _ h1 h2
    | w8array tvs ctMap tenvS n h1 =>
      rintro rfl hok hts
      simp only [Tword8array, deBruijn_subst, List.map_nil]
      exact type_v.w8array _ _ _ _ h1
    | varray tvs ctMap tenvS n t h1 h2 =>
      rintro rfl hok hts
      simp only [Tarray, deBruijn_subst, List.map_cons, List.map_nil, nil0 t h1]
      exact type_v.varray _ _ _ _ _ h1 h2
    | vector tvs ctMap tenvS vs t h1 h2 ih =>
      rintro rfl hok hts
      simp only [Tvector, deBruijn_subst, List.map_cons, List.map_nil, nil0 t h1]
      refine type_v.vector _ _ _ _ _ h1 (fun v hv => ?_)
      have := ih v hv rfl hok hts
      rwa [nil0 t h1] at this
  intro tvs ctMap tenvS v t h ⟨h1, h2, h3, h4⟩
  exact key tvs ctMap tenvS v t h h1 h2 h3

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
  intro m δ tenvT tds
  induction tds with
  | nil =>
    rintro tis ⟨h1, h2, h3⟩
    cases tis with
    | nil => exact nsAll_nsEmpty _
    | cons _ _ => simp at h1
  | cons td tds ih =>
    rintro tis ⟨h1, h2, h3⟩
    obtain ⟨tvs, tn, ctors⟩ := td
    cases tis with
    | nil => simp at h1
    | cons id ids =>
      have hm := Aux.check_ctor_tenv_mem h2 tvs tn ctors List.mem_cons_self
      simp only [check_ctor_tenv] at h2
      simp only [build_ctor_tenv]
      refine tenv_ctor_ok_merge _ _ ⟨ih ids ⟨by simpa using h1, h2.2.2.2.2, h3⟩, ?_⟩
      apply nsAll_alist_to_ns
      rw [Aux.EVERY_reverse, EVERY_iff_forall]
      intro x hx
      obtain ⟨⟨cn, ts⟩, hc, rfl⟩ := List.mem_map.mp hx
      obtain ⟨f1, f2⟩ := hm.2.2 _ _ hc
      show EVERY (check_freevars 0 tvs) _
      rw [EVERY_iff_forall] at f1 f2 ⊢
      intro y hy
      obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hy
      exact check_freevars_type_name_subst _ _ _ _ ⟨h3, f2 z hz, f1 z hz⟩

/-- Rule induction for `type_d`/`type_ds`. -/
theorem Aux.type_d_ind {ec : Bool}
    {P : type_env → dec → Set type_ident → type_env → Prop}
    {Q : type_env → List dec → Set type_ident → type_env → Prop}
    (dlet_poly : ∀ tvs tenv p e t bindings locs, is_value e → ALL_DISTINCT (pat_bindings p []) →
      type_p tvs tenv p t bindings → type_e tenv (bind_tvar tvs tenv_val_exp.Empty) e t →
      P tenv (Dlet locs p e) ∅
        { v := alist_to_ns (tenv_add_tvs tvs bindings), c := nsEmpty, t := nsEmpty })
    (dlet_mono : ∀ tenv p e t bindings locs, ALL_DISTINCT (pat_bindings p []) →
      type_p 0 tenv p t bindings → type_e tenv tenv_val_exp.Empty e t →
      P tenv (Dlet locs p e) ∅
        { v := alist_to_ns (tenv_add_tvs 0 bindings), c := nsEmpty, t := nsEmpty })
    (dletrec : ∀ tenv funs bindings tvs locs,
      type_funs tenv (bind_var_list 0 bindings (bind_tvar tvs tenv_val_exp.Empty)) funs bindings →
      P tenv (Dletrec locs funs) ∅
        { v := alist_to_ns (tenv_add_tvs tvs bindings), c := nsEmpty, t := nsEmpty })
    (dtype : ∀ tenv tdefs type_identities tenvT locs, ALL_DISTINCT type_identities →
      DISJOINT (LIST_TO_SET type_identities)
        (LIST_TO_SET (Tlist_num :: (Tbool_num :: prim_type_nums))) →
      check_ctor_tenv (nsAppend tenvT tenv.t) tdefs →
      type_identities.length = tdefs.length →
      tenvT = alist_to_ns
        (List.zipWith (fun (tvs, tn, _) i => (tn, (tvs, Tapp (tvs.map Tvar) i)))
          tdefs type_identities) →
      P tenv (Dtype locs tdefs) (LIST_TO_SET type_identities)
        { v := nsEmpty
          c := build_ctor_tenv (nsAppend tenvT tenv.t) tdefs type_identities
          t := tenvT })
    (dtabbrev : ∀ tenv tvs tn t locs, check_freevars_ast tvs t → check_type_names tenv.t t →
      ALL_DISTINCT tvs →
      P tenv (Dtabbrev locs tvs tn t) ∅
        { v := nsEmpty, c := nsEmpty, t := nsSing tn (tvs, type_name_subst tenv.t t) })
    (dexn : ∀ tenv cn ts locs, EVERY (check_freevars_ast []) ts →
      EVERY (check_type_names tenv.t) ts →
      P tenv (Dexn locs cn ts) ∅
        { v := nsEmpty
          c := nsSing cn ([], ts.map (type_name_subst tenv.t), Texn_num)
          t := nsEmpty })
    (dmod : ∀ tenv mn ds decls tenv', type_ds ec tenv ds decls tenv' → Q tenv ds decls tenv' →
      P tenv (Dmod mn ds) decls (tenvLift mn tenv'))
    (dlocal : ∀ tenv lds ds tenv1 tenv2 decls1 decls2, type_ds ec tenv lds decls1 tenv1 →
      type_ds ec (extend_dec_tenv tenv1 tenv) ds decls2 tenv2 → DISJOINT decls1 decls2 →
      Q tenv lds decls1 tenv1 → Q (extend_dec_tenv tenv1 tenv) ds decls2 tenv2 →
      P tenv (Dlocal lds ds) (decls1 ∪ decls2) tenv2)
    (nil : ∀ tenv, Q tenv [] ∅ { v := nsEmpty, c := nsEmpty, t := nsEmpty })
    (cons : ∀ tenv d ds tenv1 tenv2 decls1 decls2, type_d ec tenv d decls1 tenv1 →
      type_ds ec (extend_dec_tenv tenv1 tenv) ds decls2 tenv2 → DISJOINT decls1 decls2 →
      P tenv d decls1 tenv1 → Q (extend_dec_tenv tenv1 tenv) ds decls2 tenv2 →
      Q tenv (d :: ds) (decls1 ∪ decls2) (extend_dec_tenv tenv2 tenv1)) :
    (∀ tenv d decls tenv', type_d ec tenv d decls tenv' → P tenv d decls tenv') ∧
    (∀ tenv ds decls tenv', type_ds ec tenv ds decls tenv' → Q tenv ds decls tenv') := by
  constructor
  · intro tenv d decls tenv' h
    exact type_d.rec (motive_1 := fun tenv d s t _ => P tenv d s t)
      (motive_2 := fun tenv ds s t _ => Q tenv ds s t)
      (fun tvs tenv p e t b locs h1 h2 h3 h4 _ => dlet_poly tvs tenv p e t b locs h1 h2 h3 h4)
      (fun tenv p e t b locs _ h2 h3 h4 => dlet_mono tenv p e t b locs h2 h3 h4)
      (fun tenv funs b tvs locs h1 _ => dletrec tenv funs b tvs locs h1)
      dtype dtabbrev dexn dmod dlocal nil cons h
  · intro tenv d decls tenv' h
    exact type_ds.rec (motive_1 := fun tenv d s t _ => P tenv d s t)
      (motive_2 := fun tenv ds s t _ => Q tenv ds s t)
      (fun tvs tenv p e t b locs h1 h2 h3 h4 _ => dlet_poly tvs tenv p e t b locs h1 h2 h3 h4)
      (fun tenv p e t b locs _ h2 h3 h4 => dlet_mono tenv p e t b locs h2 h3 h4)
      (fun tenv funs b tvs locs h1 _ => dletrec tenv funs b tvs locs h1)
      dtype dtabbrev dexn dmod dlocal nil cons h

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
  have H := fun check => Aux.type_d_ind (ec := check)
    (P := fun tenv d s t => type_d false tenv d s t)
    (Q := fun tenv ds s t => type_ds false tenv ds s t)
    (fun tvs tenv p e t b locs h1 h2 h3 h4 =>
      type_d.dlet_poly _ _ _ _ _ _ _ _ h1 h2 h3 h4 (fun h => by cases h))
    (fun tenv p e t b locs h2 h3 h4 =>
      type_d.dlet_mono _ _ _ _ _ _ _ (fun h => by cases h) h2 h3 h4)
    (fun tenv funs b tvs locs h1 => type_d.dletrec _ _ _ _ _ _ h1 (fun h => by cases h))
    (fun tenv tdefs ti tenvT locs h1 h2 h3 h4 h5 =>
      type_d.dtype _ _ _ _ _ _ h1 h2 h3 h4 h5)
    (fun tenv tvs tn t locs h1 h2 h3 => type_d.dtabbrev _ _ _ _ _ _ h1 h2 h3)
    (fun tenv cn ts locs h1 h2 => type_d.dexn _ _ _ _ _ h1 h2)
    (fun tenv mn ds decls tenv' _ ih => type_d.dmod _ _ _ _ _ _ ih)
    (fun tenv lds ds t1 t2 d1 d2 _ _ hd ih1 ih2 => type_d.dlocal _ _ _ _ _ _ _ _ ih1 ih2 hd)
    (fun tenv => type_ds.nil _ _)
    (fun tenv d ds t1 t2 d1 d2 _ _ hd ih1 ih2 => type_ds.cons _ _ _ _ _ _ _ _ ih1 ih2 hd)
  exact ⟨fun check => (H check).1, fun check => (H check).2⟩

/- HOL4:
Theorem extend_dec_tenv_ok:
   !tenv tenv'. tenv_ok tenv ∧ tenv_ok tenv' ⇒ tenv_ok (extend_dec_tenv tenv tenv') -/
theorem extend_dec_tenv_ok :
    ∀ (tenv tenv' : type_env),
      tenv_ok tenv ∧ tenv_ok tenv' → tenv_ok (extend_dec_tenv tenv tenv') :=
  fun _ _ ⟨⟨a1, a2, a3⟩, ⟨b1, b2, b3⟩⟩ =>
    ⟨nsAll_nsAppend _ _ _ ⟨a1, b1⟩, nsAll_nsAppend _ _ _ ⟨a2, b2⟩, nsAll_nsAppend _ _ _ ⟨a3, b3⟩⟩

theorem Aux.tenv_add_tvs_ok (tvs : Nat) (bindings : List (mlstring × typ))
    (h : EVERY (check_freevars tvs []) (bindings.map Prod.snd)) :
    tenv_val_ok (alist_to_ns (tenv_add_tvs tvs bindings) : tenv_val) := by
  apply nsAll_alist_to_ns
  unfold tenv_add_tvs
  rw [EVERY_iff_forall] at h ⊢
  intro x hx
  obtain ⟨⟨n, t⟩, hm, rfl⟩ := List.mem_map.mp hx
  exact h t (List.mem_map.mpr ⟨_, hm, rfl⟩)

theorem Aux.zipWith_abbrev_ok (tdefs : type_def) (ids : List type_ident) :
    tenv_abbrev_ok (alist_to_ns
      (List.zipWith (fun (tvs, tn, _) i => (tn, (tvs, Tapp (tvs.map Tvar) i))) tdefs ids) :
      tenv_abbrev) := by
  apply nsAll_alist_to_ns
  induction tdefs generalizing ids with
  | nil => trivial
  | cons td tds ih =>
    obtain ⟨tvs, tn, ctors⟩ := td
    cases ids with
    | nil => trivial
    | cons i ids =>
      refine ⟨?_, ih ids⟩
      show check_freevars 0 tvs (Tapp (tvs.map Tvar) i)
      simp only [check_freevars, EVERY_iff_forall, List.mem_map]
      rintro t ⟨tv, htv, rfl⟩
      simp only [check_freevars]
      exact htv

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
  have H := fun check => Aux.type_d_ind (ec := check)
    (P := fun tenv _ _ t => tenv_ok tenv → tenv_ok t)
    (Q := fun tenv _ _ t => tenv_ok tenv → tenv_ok t)
    (fun tvs tenv p e t b locs h1 h2 h3 h4 _ =>
      ⟨Aux.tenv_add_tvs_ok _ _ (type_p_freevars.1 _ _ _ _ _ h3).2, nsAll_nsEmpty _,
        nsAll_nsEmpty _⟩)
    (fun tenv p e t b locs h2 h3 h4 _ =>
      ⟨Aux.tenv_add_tvs_ok _ _ (type_p_freevars.1 _ _ _ _ _ h3).2, nsAll_nsEmpty _,
        nsAll_nsEmpty _⟩)
    (fun tenv funs b tvs locs h1 _ =>
      ⟨Aux.tenv_add_tvs_ok _ _ (by
        have := Aux.type_funs_check h1
        rwa [Aux.num_tvs_funs _ _ _ rfl] at this), nsAll_nsEmpty _, nsAll_nsEmpty _⟩)
    (fun tenv tdefs ti tenvT locs h1 h2 h3 h4 h5 hok => by
      have hT : tenv_abbrev_ok tenvT := by
        rw [h5]; exact Aux.zipWith_abbrev_ok _ _
      exact ⟨nsAll_nsEmpty _, check_ctor_tenv_ok _ _ _
        ⟨h4.symm, h3, nsAll_nsAppend _ _ _ ⟨hT, hok.2.2⟩⟩, hT⟩)
    (fun tenv tvs tn t locs h1 h2 h3 hok =>
      ⟨nsAll_nsEmpty _, nsAll_nsEmpty _, (nsAll_nsSing _ _ _).mpr
        (check_freevars_type_name_subst _ _ _ _ ⟨hok.2.2, h2, h1⟩)⟩)
    (fun tenv cn ts locs h1 h2 hok =>
      ⟨nsAll_nsEmpty _, (nsAll_nsSing _ _ _).mpr (by
        show EVERY (check_freevars 0 []) (ts.map (type_name_subst tenv.t))
        rw [EVERY_iff_forall] at h1 h2 ⊢
        intro x hx
        obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
        exact check_freevars_type_name_subst _ _ _ _ ⟨hok.2.2, h2 y hy, h1 y hy⟩),
        nsAll_nsEmpty _⟩)
    (fun tenv mn ds decls tenv' _ ih hok =>
      have h := ih hok
      ⟨(nsAll_nsLift _ _ _).mpr h.1, (nsAll_nsLift _ _ _).mpr h.2.1,
        (nsAll_nsLift _ _ _).mpr h.2.2⟩)
    (fun tenv lds ds t1 t2 d1 d2 _ _ hd ih1 ih2 hok =>
      ih2 (extend_dec_tenv_ok _ _ ⟨ih1 hok, hok⟩))
    (fun tenv _ => tenv_ok_empty)
    (fun tenv d ds t1 t2 d1 d2 _ _ hd ih1 ih2 hok =>
      extend_dec_tenv_ok _ _ ⟨ih2 (extend_dec_tenv_ok _ _ ⟨ih1 hok, hok⟩), ih1 hok⟩)
  exact ⟨fun check => (H check).1, fun check => (H check).2⟩

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
      tenv_ok (extend_dec_tenv tenv' tenv) :=
  fun _ _ _ _ _ ⟨h1, h2⟩ =>
    extend_dec_tenv_ok _ _ ⟨type_d_tenv_ok_helper.1 _ _ _ _ _ h1 h2, h2⟩

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

theorem Aux.type_ds_cons_inv {check : Bool} {tenv : type_env} {d : dec} {ds : List dec}
    {decls : Set type_ident} {r : type_env} (h : type_ds check tenv (d :: ds) decls r) :
    ∃ tenv1 tenv2 decls1 decls2, decls = decls1 ∪ decls2 ∧ r = extend_dec_tenv tenv2 tenv1 ∧
      type_d check tenv d decls1 tenv1 ∧
      type_ds check (extend_dec_tenv tenv1 tenv) ds decls2 tenv2 ∧ DISJOINT decls1 decls2 := by
  cases h with
  | cons _ _ _ t1 t2 d1 d2 h1 h2 h3 => exact ⟨t1, t2, d1, d2, rfl, rfl, h1, h2, h3⟩

theorem Aux.union_empty {α : Type} (s : Set α) : s ∪ ∅ = s := by
  apply Aux.set_ext
  intro x
  exact ⟨fun h => h.elim id (fun h => h.elim), Or.inl⟩

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
    obtain ⟨t1, t2, d1, d2, rfl, rfl, h1, h2, h3⟩ := Aux.type_ds_cons_inv h
    obtain ⟨rfl, rfl⟩ := (type_ds_empty _ _ _ _).mp h2
    rw [Aux.union_empty, Aux.extend_empty]
    exact h1
  · intro h
    have := type_ds.cons check tenv d [] r _ decls _ h (type_ds.nil _ _)
      (Aux.DISJOINT_iff.mpr fun x _ h => h)
    rwa [Aux.union_empty, Aux.extend_empty] at this

end

end CmlTS
