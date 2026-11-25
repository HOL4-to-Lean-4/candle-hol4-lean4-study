import CmlTS.Ast
import CmlTS.Namespace
import CmlTS.Proofs.Lib

/-
HOL4 theory `namespaceProps` (namespacePropsScript.sml).
-/

namespace CmlTS

noncomputable section

open scoped Classical

variable {α β κ : Type}

/- HOL4:
Definition alist_rel_restr_def:
  (alist_rel_restr R l1 l2 [] ⇔ T) ∧
  (alist_rel_restr R l1 l2 (k1::keys) ⇔
    case ALOOKUP l1 k1 of
    | NONE => F
    | SOME v1 =>
      case ALOOKUP l2 k1 of
      | NONE => F
      | SOME v2 => R k1 v1 v2 ∧ alist_rel_restr R l1 l2 keys)
End -/
def alist_rel_restr (R : κ → α → β → Prop) (l1 : List (κ × α)) (l2 : List (κ × β)) :
    List κ → Prop
  | [] => True
  | k1 :: keys =>
    match ALOOKUP l1 k1 with
    | none => False
    | some v1 =>
      match ALOOKUP l2 k1 with
      | none => False
      | some v2 => R k1 v1 v2 ∧ alist_rel_restr R l1 l2 keys

/- HOL4:
Definition alistSub_def:
  alistSub R e1 e2 ⇔ alist_rel_restr R e1 e2 (MAP FST e1)
End -/
def alistSub (R : κ → α → β → Prop) (e1 : List (κ × α)) (e2 : List (κ × β)) : Prop :=
  alist_rel_restr R e1 e2 (e1.map Prod.fst)

/-! Helper lemmas (not HOL4 constants): the congruence rule `alistSub_cong`
that HOL4's `Termination` of `nsSub_compute` relies on (HOL4 exports it with
`DefnBase.export_cong`). -/

/-- Pairs of `l1` that are values found by `ALOOKUP`. -/
theorem ALOOKUP_mem_aux {l : List (κ × α)} {k : κ} {x : α} (h : ALOOKUP l k = some x) :
    (k, x) ∈ l := by
  induction l with
  | nil => simp [ALOOKUP] at h
  | cons p t ih =>
    obtain ⟨a, b⟩ := p
    simp only [ALOOKUP] at h
    split at h
    · simp_all
    · exact List.mem_cons_of_mem _ (ih h)

/-- `alistSub` with a relation that also gets the membership of the left value. -/
def alistSub_attach (e1 : List (κ × α)) (e2 : List (κ × β))
    (R : (k : κ) → (x : α) → (k, x) ∈ e1 → β → Prop) : Prop :=
  ∀ k, k ∈ e1.map Prod.fst →
    ∃ v1 v2, ∃ h : ALOOKUP e1 k = some v1, ALOOKUP e2 k = some v2 ∧ R k v1 (ALOOKUP_mem_aux h) v2

theorem alist_rel_restr_iff_aux (R : κ → α → β → Prop) (l1 : List (κ × α)) (l2 : List (κ × β))
    (keys : List κ) :
    alist_rel_restr R l1 l2 keys ↔
      ∀ k, k ∈ keys → ∃ v1 v2, ALOOKUP l1 k = some v1 ∧ ALOOKUP l2 k = some v2 ∧ R k v1 v2 := by
  induction keys with
  | nil => simp [alist_rel_restr]
  | cons k1 keys ih =>
    simp only [alist_rel_restr, List.mem_cons, forall_eq_or_imp]
    cases h1 : ALOOKUP l1 k1 with
    | none => simp
    | some v1 =>
      cases h2 : ALOOKUP l2 k1 with
      | none => simp
      | some v2 => simp [ih]

theorem alistSub_attach_iff_aux (e1 : List (κ × α)) (e2 : List (κ × β)) (R : κ → α → β → Prop) :
    alistSub_attach e1 e2 (fun k x _ y => R k x y) ↔ alistSub R e1 e2 := by
  unfold alistSub alistSub_attach
  rw [alist_rel_restr_iff_aux]
  constructor
  · intro h k hk
    obtain ⟨v1, v2, ha, hb, hr⟩ := h k hk
    exact ⟨v1, v2, ha, hb, hr⟩
  · intro h k hk
    obtain ⟨v1, v2, ha, hb, hr⟩ := h k hk
    exact ⟨v1, v2, ha, hb, hr⟩

variable {m n v w : Type}

/-- `nsSub_compute` in the form Lean's termination checker accepts; the HOL4
equation is `nsSub_compute_def_aux` below. -/
def nsSub_compute (path : List m) (R : ident m n → v → w → Prop) :
    Namespace m n v → Namespace m n w → Prop
  | Namespace.Bind e1V e1M, Namespace.Bind e2V e2M =>
    alistSub (fun k v1 v2 => R (mk_id path.reverse k) v1 v2) e1V e2V ∧
    alistSub_attach e1M e2M (fun k v1 _ v2 => nsSub_compute (k :: path) R v1 v2)
termination_by e1 _ => sizeOf e1
decreasing_by
  rename_i h
  exact Namespace_sizeOf_aux (p := (k, v1)) h

/- HOL4:
Definition nsSub_compute_def:
  nsSub_compute path R (Bind e1V e1M) (Bind e2V e2M) ⇔
    alistSub (\k v1 v2. R (mk_id (REVERSE path) k) v1 v2) e1V e2V ∧
    alistSub (\k v1 v2. nsSub_compute (k::path) R v1 v2) e1M e2M
Termination
  wf_rel_tac `measure (\(p,r,env,_). namespace_size (\x.0) (\x.0) (\x.0) env)`
  ...
End -/
theorem nsSub_compute_def_aux (path : List m) (R : ident m n → v → w → Prop)
    (e1V : List (n × v)) (e1M : List (m × Namespace m n v))
    (e2V : List (n × w)) (e2M : List (m × Namespace m n w)) :
    nsSub_compute path R (Namespace.Bind e1V e1M) (Namespace.Bind e2V e2M) ↔
      alistSub (fun k v1 v2 => R (mk_id path.reverse k) v1 v2) e1V e2V ∧
      alistSub (fun k v1 v2 => nsSub_compute (k :: path) R v1 v2) e1M e2M := by
  rw [nsSub_compute, ← alistSub_attach_iff_aux e1M e2M]

/-! ### Theorems

The type variables are written `μ ν` (HOL4 `'m 'n`) and `α β` (values), so that the HOL4 names
`m n v` stay free for term variables. -/

/- HOL4:
Theorem mk_id_surj:
   !id. ?p n. id = mk_id p n -/
theorem mk_id_surj {μ ν : Type} :
    ∀ id : ident μ ν, ∃ (p : List μ) (n : ν), id = mk_id p n := by
  intro id
  induction id with
  | Short x => exact ⟨[], x, rfl⟩
  | Long mn id ih =>
    obtain ⟨p, n, rfl⟩ := ih
    exact ⟨mn :: p, n, rfl⟩

/- HOL4:
Theorem mk_id_thm:
   !id. mk_id (id_to_mods id) (id_to_n id) = id -/
theorem mk_id_thm {μ ν : Type} :
    ∀ id : ident μ ν, mk_id (id_to_mods id) (id_to_n id) = id := by
  intro id
  induction id with
  | Short x => rfl
  | Long mn id ih => simp [id_to_mods, id_to_n, mk_id, ih]

/- HOL4:
Theorem nsSub_mono[mono]:
   (!x y z. R1 x y z ⇒ R2 x y z) ⇒ (nsSub R1 e1 e2 ⇒ nsSub R2 e1 e2) -/
theorem nsSub_mono {μ ν α β : Type} {R1 R2 : ident μ ν → α → β → Prop}
    {e1 : Namespace μ ν α} {e2 : Namespace μ ν β} :
    (∀ x y z, R1 x y z → R2 x y z) → (nsSub R1 e1 e2 → nsSub R2 e1 e2) := by
  rintro h ⟨h1, h2⟩
  refine ⟨fun id v1 hv => ?_, h2⟩
  obtain ⟨v2, h3, h4⟩ := h1 id v1 hv
  exact ⟨v2, h3, h _ _ _ h4⟩

/- HOL4:
Theorem nsAll2_mono[mono]:
   (!x y z. R1 x y z ⇒ R2 x y z) ⇒ nsAll2 R1 e1 e2 ⇒ nsAll2 R2 e1 e2 -/
theorem nsAll2_mono {μ ν α β : Type} {R1 R2 : ident μ ν → α → β → Prop}
    {e1 : Namespace μ ν α} {e2 : Namespace μ ν β} :
    (∀ x y z, R1 x y z → R2 x y z) → nsAll2 R1 e1 e2 → nsAll2 R2 e1 e2 := by
  rintro h ⟨h1, h2⟩
  exact ⟨nsSub_mono h h1, nsSub_mono (fun x y z => h x z y) h2⟩

/- HOL4:
Theorem nsLookup_nsEmpty[simp]:
   !id. nsLookup nsEmpty id = NONE -/
theorem nsLookup_nsEmpty {μ ν α : Type} :
    ∀ id : ident μ ν, nsLookup (nsEmpty : Namespace μ ν α) id = none := by
  intro id
  cases id <;> simp [nsLookup, nsEmpty, ALOOKUP]

/- HOL4:
Theorem nsLookupMod_nsEmpty[simp]:
   !x y. nsLookupMod nsEmpty (x::y) = NONE -/
theorem nsLookupMod_nsEmpty {μ ν α : Type} :
    ∀ (x : μ) (y : List μ),
      nsLookupMod (nsEmpty : Namespace μ ν α) (x :: y) = none := by
  intro x y
  simp [nsLookupMod, nsEmpty, ALOOKUP]

/- HOL4:
Theorem nsAppend_nsEmpty[simp]:
   !env. nsAppend env nsEmpty = env ∧ nsAppend nsEmpty env = env -/
theorem nsAppend_nsEmpty {μ ν α : Type} :
    ∀ env : Namespace μ ν α, nsAppend env nsEmpty = env ∧ nsAppend nsEmpty env = env := by
  rintro ⟨vs, ms⟩
  simp [nsAppend, nsEmpty]

/- HOL4:
Theorem alist_to_ns_nil[simp]:
   alist_to_ns [] = nsEmpty -/
theorem alist_to_ns_nil {μ ν α : Type} :
    alist_to_ns [] = (nsEmpty : Namespace μ ν α) := rfl

/- HOL4:
Theorem nsSub_nsEmpty[simp]:
   !r env. nsSub r nsEmpty env -/
theorem nsSub_nsEmpty {μ ν α β : Type} :
    ∀ (r : ident μ ν → α → β → Prop) (env : Namespace μ ν β), nsSub r nsEmpty env := by
  intro r env
  refine ⟨fun id v1 h => ?_, fun path h => ?_⟩
  · rw [nsLookup_nsEmpty] at h; cases h
  · cases path with
    | nil => simp [nsLookupMod] at h
    | cons x y => exact nsLookupMod_nsEmpty x y

/- HOL4:
Theorem nsAll_nsEmpty[simp]:
   !f. nsAll f nsEmpty -/
theorem nsAll_nsEmpty {μ ν α : Type} :
    ∀ f : ident μ ν → α → Prop, nsAll f nsEmpty := by
  intro f id x h
  rw [nsLookup_nsEmpty] at h; cases h

/- HOL4:
Theorem nsAll2_nsEmpty[simp]:
   !f. nsAll2 f nsEmpty nsEmpty -/
theorem nsAll2_nsEmpty {μ ν α β : Type} :
    ∀ f : ident μ ν → α → β → Prop, nsAll2 f nsEmpty nsEmpty := by
  intro f
  exact ⟨nsSub_nsEmpty _ _, nsSub_nsEmpty _ _⟩

/- HOL4:
Theorem alist_to_ns_cons[simp]:
   !k v l. alist_to_ns ((k,v)::l) = nsBind k v (alist_to_ns l) -/
theorem alist_to_ns_cons {μ ν α : Type} :
    ∀ (k : ν) (v : α) (l : List (ν × α)),
      (alist_to_ns ((k, v) :: l) : Namespace μ ν α) = nsBind k v (alist_to_ns l) := by
  intro k v l; rfl

/- HOL4:
Theorem nsAppend_nsBind[simp]:
   !k v e1 e2. nsAppend (nsBind k v e1) e2 = nsBind k v (nsAppend e1 e2) -/
theorem nsAppend_nsBind {μ ν α : Type} :
    ∀ (k : ν) (v : α) (e1 e2 : Namespace μ ν α),
      nsAppend (nsBind k v e1) e2 = nsBind k v (nsAppend e1 e2) := by
  rintro k v ⟨v1, m1⟩ ⟨v2, m2⟩; rfl

/- HOL4:
Theorem nsAppend_assoc[simp]:
   !e1 e2 e3. nsAppend e1 (nsAppend e2 e3) = nsAppend (nsAppend e1 e2) e3 -/
theorem nsAppend_assoc {μ ν α : Type} :
    ∀ e1 e2 e3 : Namespace μ ν α,
      nsAppend e1 (nsAppend e2 e3) = nsAppend (nsAppend e1 e2) e3 := by
  rintro ⟨v1, m1⟩ ⟨v2, m2⟩ ⟨v3, m3⟩
  simp [nsAppend]

/- HOL4:
Theorem nsLookup_nsBind[simp]:
   (!n v e. nsLookup (nsBind n v e) (Short n) = SOME v) ∧
   (!n n' v e. n ≠ Short n' ⇒ nsLookup (nsBind n' v e) n = nsLookup e n)
(the two conjuncts have independent HOL4 type variables) -/
theorem nsLookup_nsBind {μ ν α μ' ν' α' : Type} :
    (∀ (n : ν) (v : α) (e : Namespace μ ν α),
      nsLookup (nsBind n v e) (Short n) = some v) ∧
    (∀ (n : ident μ' ν') (n' : ν') (v : α') (e : Namespace μ' ν' α'),
      n ≠ Short n' → nsLookup (nsBind n' v e) n = nsLookup e n) := by
  constructor
  · rintro n v ⟨vs, ms⟩
    simp [nsLookup, nsBind, ALOOKUP]
  · rintro n n' v ⟨vs, ms⟩ h
    cases n with
    | Short x =>
      have : ¬ n' = x := fun e => h (by rw [e])
      simp [nsLookup, nsBind, ALOOKUP, this]
    | Long mn id => simp [nsLookup, nsBind]

theorem Aux.nsLookup_nsBind_if {μ ν α : Type} (k : ν) (v : α) (e : Namespace μ ν α)
    (id : ident μ ν) :
    nsLookup (nsBind k v e) id = if id = Short k then some v else nsLookup e id := by
  by_cases h : id = Short k
  · rw [if_pos h, h, (nsLookup_nsBind (μ' := μ) (ν' := ν) (α' := α)).1]
  · rw [if_neg h, (nsLookup_nsBind (μ := μ) (ν := ν) (α := α)).2 _ _ _ _ h]

/- HOL4:
Theorem nsAppend_nsSing[simp]:
   !n x e. nsAppend (nsSing n x) e = nsBind n x e -/
theorem nsAppend_nsSing {μ ν α : Type} :
    ∀ (n : ν) (x : α) (e : Namespace μ ν α),
      nsAppend (nsSing n x) e = nsBind n x e := by
  rintro n x ⟨vs, ms⟩; rfl

/- HOL4:
Theorem nsLookup_nsSing[simp]:
   !n v id. nsLookup (nsSing n v) id = if id = Short n then SOME v else NONE -/
theorem nsLookup_nsSing {μ ν α : Type} :
    ∀ (n : ν) (v : α) (id : ident μ ν),
      nsLookup (nsSing n v) id = if id = Short n then some v else none := by
  intro n v id
  have : (nsSing n v : Namespace μ ν α) = nsBind n v nsEmpty := rfl
  rw [this, Aux.nsLookup_nsBind_if, nsLookup_nsEmpty]

/- HOL4:
Theorem nsAll_nsSing[simp]:
   !R n v. nsAll R (nsSing n v) ⇔ R (Short n) v -/
theorem nsAll_nsSing {μ ν α : Type} :
    ∀ (R : ident μ ν → α → Prop) (n : ν) (v : α),
      nsAll R (nsSing n v) ↔ R (Short n) v := by
  intro R n v
  simp only [nsAll, nsLookup_nsSing]
  constructor
  · intro h; exact h (Short n) v (by simp)
  · intro h id x hx
    split at hx
    · rename_i e; cases hx; rw [e]; exact h
    · cases hx

/- HOL4:
Theorem nsAll2_nsSing[simp]:
   !R n1 v1 n2 v2. nsAll2 R (nsSing n1 v1) (nsSing n2 v2) ⇔ n1 = n2 ∧ R (Short n1) v1 v2 -/
theorem nsAll2_nsSing {μ ν α β : Type} :
    ∀ (R : ident μ ν → α → β → Prop) (n1 : ν) (v1 : α) (n2 : ν) (v2 : β),
      nsAll2 R (nsSing n1 v1) (nsSing n2 v2) ↔ (n1 = n2 ∧ R (Short n1) v1 v2) := by
  intro R n1 v1 n2 v2
  have hm : ∀ {γ δ : Type} (x : ν) (y : γ) (x' : ν) (y' : δ) (p : List μ),
      nsLookupMod (nsSing x y : Namespace μ ν γ) p = none →
      nsLookupMod (nsSing x' y' : Namespace μ ν δ) p = none := by
    intro γ δ x y x' y' p h
    cases p with
    | nil => simp [nsLookupMod] at h
    | cons a b => simp [nsLookupMod, nsSing, ALOOKUP]
  constructor
  · rintro ⟨⟨h1, -⟩, -⟩
    obtain ⟨v, h2, h3⟩ := h1 (Short n1) v1 (by rw [nsLookup_nsSing, if_pos rfl])
    rw [nsLookup_nsSing] at h2
    split at h2
    · rename_i e; cases h2; cases e; exact ⟨rfl, h3⟩
    · cases h2
  · rintro ⟨rfl, hr⟩
    refine ⟨⟨?_, hm _ _ _ _⟩, ⟨?_, hm _ _ _ _⟩⟩
    · intro id x h
      rw [nsLookup_nsSing] at h ⊢
      split at h
      · rename_i e; cases h; subst e; exact ⟨v2, if_pos rfl, hr⟩
      · cases h
    · intro id x h
      rw [nsLookup_nsSing] at h ⊢
      split at h
      · rename_i e; cases h; subst e; exact ⟨v1, if_pos rfl, hr⟩
      · cases h

/- HOL4:
Theorem nsBind_11[simp]:
   !x y n x' y' n'. nsBind x y n = nsBind x' y' n' ⇔ x = x' ∧ y = y' ∧ n = n' -/
theorem nsBind_11 {μ ν α : Type} :
    ∀ (x : ν) (y : α) (n : Namespace μ ν α) (x' : ν) (y' : α) (n' : Namespace μ ν α),
      nsBind x y n = nsBind x' y' n' ↔ (x = x' ∧ y = y' ∧ n = n') := by
  rintro x y ⟨vs, ms⟩ x' y' ⟨vs', ms'⟩
  simp [nsBind, and_assoc]

/- HOL4:
Theorem alist_to_ns_11[simp]:
   !l1 l2. alist_to_ns l1 = alist_to_ns l2 ⇔ l1 = l2 -/
theorem alist_to_ns_11 {μ ν α : Type} :
    ∀ l1 l2 : List (ν × α),
      (alist_to_ns l1 : Namespace μ ν α) = alist_to_ns l2 ↔ l1 = l2 := by
  intro l1 l2
  simp [alist_to_ns]

/- HOL4:
Theorem nsLookup_nsLift:
   !mn e id.
    nsLookup (nsLift mn e) id =
    case id of
    | Long mn' id' =>
      if mn = mn' then
        nsLookup e id'
      else
        NONE
    | Short _ => NONE -/
theorem nsLookup_nsLift {μ ν α : Type} :
    ∀ (mn : μ) (e : Namespace μ ν α) (id : ident μ ν),
      nsLookup (nsLift mn e) id =
        (match id with
        | Long mn' id' => if mn = mn' then nsLookup e id' else none
        | Short _ => none) := by
  intro mn e id
  cases id with
  | Short x => simp [nsLift, nsLookup, ALOOKUP]
  | Long mn' id' =>
    by_cases h : mn = mn' <;> simp [nsLift, nsLookup, ALOOKUP, h]

/- HOL4:
Theorem nsLookupMod_nsLift:
   !mn e path.
    nsLookupMod (nsLift mn e) path =
    case path of
    | [] => SOME (nsLift mn e)
    | (mn'::path') =>
      if mn = mn' then
        nsLookupMod e path'
      else
        NONE -/
theorem nsLookupMod_nsLift {μ ν α : Type} :
    ∀ (mn : μ) (e : Namespace μ ν α) (path : List μ),
      nsLookupMod (nsLift mn e) path =
        (match path with
        | [] => some (nsLift mn e)
        | mn' :: path' => if mn = mn' then nsLookupMod e path' else none) := by
  intro mn e path
  cases path with
  | nil => simp [nsLookupMod]
  | cons mn' p' =>
    by_cases h : mn = mn' <;> simp [nsLift, nsLookupMod, ALOOKUP, h]

/- HOL4:
Theorem nsLookup_nsAppend_some:
   ∀e1 id e2 v.
    nsLookup (nsAppend e1 e2) id = SOME v
    ⇔
    nsLookup e1 id = SOME v ∨
    (nsLookup e1 id = NONE ∧ nsLookup e2 id = SOME v ∧
     !p1 p2. p1 ≠ [] ∧ id_to_mods id = p1++p2 ⇒ nsLookupMod e1 p1 = NONE) -/
theorem nsLookup_nsAppend_some {μ ν α : Type} :
    ∀ (e1 : Namespace μ ν α) (id : ident μ ν) (e2 : Namespace μ ν α) (v : α),
      nsLookup (nsAppend e1 e2) id = some v
      ↔
      (nsLookup e1 id = some v ∨
        (nsLookup e1 id = none ∧ nsLookup e2 id = some v ∧
          ∀ p1 p2, p1 ≠ [] ∧ id_to_mods id = p1 ++ p2 → nsLookupMod e1 p1 = none)) := by
  rintro ⟨v1, m1⟩ id ⟨v2, m2⟩ v
  cases id with
  | Short x =>
    simp only [nsAppend, nsLookup, Aux.ALOOKUP_append]
    cases ALOOKUP v1 x with
    | some y => simp
    | none =>
      simp only [id_to_mods, reduceCtorEq, true_and, false_or]
      constructor
      · intro h
        refine ⟨h, ?_⟩
        rintro p1 p2 ⟨hp, e⟩
        cases p1 with
        | nil => exact absurd rfl hp
        | cons a b => simp at e
      · intro h; exact h.1
  | Long mn id =>
    simp only [nsAppend, nsLookup, Aux.ALOOKUP_append]
    cases hm : ALOOKUP m1 mn with
    | some env =>
      simp only
      constructor
      · exact Or.inl
      · rintro (h | ⟨-, -, h⟩)
        · exact h
        · have := h [mn] (id_to_mods id) ⟨by simp, rfl⟩
          simp [nsLookupMod, hm] at this
    | none =>
      simp only [reduceCtorEq, true_and, false_or]
      constructor
      · intro h
        refine ⟨h, ?_⟩
        rintro p1 p2 ⟨hp, e⟩
        cases p1 with
        | nil => exact absurd rfl hp
        | cons a b =>
          simp only [id_to_mods, List.cons_append, List.cons.injEq] at e
          simp [nsLookupMod, ← e.1, hm]
      · intro h; exact h.1

/- HOL4:
Theorem nsAppend_to_nsBindList:
   !l. nsAppend (alist_to_ns l) e = nsBindList l e -/
theorem nsAppend_to_nsBindList {μ ν α : Type} {e : Namespace μ ν α} :
    ∀ l : List (ν × α), nsAppend (alist_to_ns l) e = nsBindList l e := by
  intro l
  induction l with
  | nil => exact (nsAppend_nsEmpty e).2
  | cons p l ih =>
    obtain ⟨k, x⟩ := p
    rw [alist_to_ns_cons, nsAppend_nsBind, ih]
    rfl

/- HOL4:
Theorem nsLookupMod_nsAppend_none:
   !e1 e2 path.
    nsLookupMod (nsAppend e1 e2) path = NONE
    ⇔
    (nsLookupMod e1 path = NONE ∧
     (nsLookupMod e2 path = NONE ∨
      ?p1 p2 e3. p1 ≠ [] ∧ path = p1++p2 ∧ nsLookupMod e1 p1 = SOME e3)) -/
theorem nsLookupMod_nsAppend_none {μ ν α : Type} :
    ∀ (e1 e2 : Namespace μ ν α) (path : List μ),
      nsLookupMod (nsAppend e1 e2) path = none
      ↔
      (nsLookupMod e1 path = none ∧
        (nsLookupMod e2 path = none ∨
          ∃ p1 p2 e3, p1 ≠ [] ∧ path = p1 ++ p2 ∧ nsLookupMod e1 p1 = some e3)) := by
  rintro ⟨v1, m1⟩ ⟨v2, m2⟩ path
  cases path with
  | nil => simp [nsLookupMod]
  | cons mn path =>
    simp only [nsAppend, nsLookupMod, Aux.ALOOKUP_append]
    cases hm : ALOOKUP m1 mn with
    | some env =>
      simp only
      constructor
      · intro h
        exact ⟨h, Or.inr ⟨[mn], path, env, by simp, rfl, by simp [nsLookupMod, hm]⟩⟩
      · exact fun h => h.1
    | none =>
      simp only [true_and]
      constructor
      · exact Or.inl
      · rintro (h | ⟨p1, p2, e3, hp, e, h⟩)
        · exact h
        · cases p1 with
          | nil => exact absurd rfl hp
          | cons a b =>
            simp only [List.cons_append, List.cons.injEq] at e
            simp [nsLookupMod, ← e.1, hm] at h

/- HOL4:
Theorem eALL_T[simp]:
   !e. nsAll (\n x. T) e -/
theorem eALL_T {μ ν α : Type} :
    ∀ e : Namespace μ ν α, nsAll (fun _n _x => True) e := by
  intro e id x _; trivial

/- HOL4:
Theorem nsLookup_nsAll:
   !env x P v. nsAll P env ∧ nsLookup env x = SOME v ⇒ P x v -/
theorem nsLookup_nsAll {μ ν α : Type} :
    ∀ (env : Namespace μ ν α) (x : ident μ ν) (P : ident μ ν → α → Prop) (v : α),
      nsAll P env ∧ nsLookup env x = some v → P x v := by
  rintro env x P v ⟨h1, h2⟩
  exact h1 x v h2

/- HOL4:
Theorem nsAll_nsAppend:
   !f e1 e2. nsAll f e1 ∧ nsAll f e2 ⇒ nsAll f (nsAppend e1 e2) -/
theorem nsAll_nsAppend {μ ν α : Type} :
    ∀ (f : ident μ ν → α → Prop) (e1 e2 : Namespace μ ν α),
      nsAll f e1 ∧ nsAll f e2 → nsAll f (nsAppend e1 e2) := by
  rintro f e1 e2 ⟨h1, h2⟩ id x h
  rcases (nsLookup_nsAppend_some e1 id e2 x).1 h with h | ⟨-, h, -⟩
  · exact h1 id x h
  · exact h2 id x h

/- HOL4:
Theorem nsAll_alist_to_ns:
   !R l. EVERY (λ(n,v). R (Short n) v) l ⇒ nsAll R (alist_to_ns l) -/
theorem nsAll_alist_to_ns {μ ν α : Type} :
    ∀ (R : ident μ ν → α → Prop) (l : List (ν × α)),
      EVERY (fun (n, v) => R (Short n) v) l → nsAll R (alist_to_ns l) := by
  intro R l h id x hx
  rw [EVERY_iff_forall] at h
  cases id with
  | Short k => exact h (k, x) (Aux.ALOOKUP_mem hx)
  | Long mn id => simp [alist_to_ns, nsLookup, ALOOKUP] at hx

/- HOL4:
Theorem nsAll_nsLift[simp]:
   !R mn e. nsAll R (nsLift mn e) ⇔ nsAll (\id. R (Long mn id)) e -/
theorem nsAll_nsLift {μ ν α : Type} :
    ∀ (R : ident μ ν → α → Prop) (mn : μ) (e : Namespace μ ν α),
      nsAll R (nsLift mn e) ↔ nsAll (fun id => R (Long mn id)) e := by
  intro R mn e
  constructor
  · intro h id x hx
    exact h (Long mn id) x (by simp [nsLookup_nsLift, hx])
  · intro h id x hx
    rw [nsLookup_nsLift] at hx
    cases id with
    | Short k => cases hx
    | Long mn' id' =>
      simp only at hx
      split at hx
      · rename_i e; subst e; exact h id' x hx
      · cases hx

/- HOL4:
Theorem nsAll_nsAppend_left:
   !P n1 n2. nsAll P (nsAppend n1 n2) ⇒ nsAll P n1 -/
theorem nsAll_nsAppend_left {μ ν α : Type} :
    ∀ (P : ident μ ν → α → Prop) (n1 n2 : Namespace μ ν α),
      nsAll P (nsAppend n1 n2) → nsAll P n1 := by
  intro P n1 n2 h id x hx
  exact h id x ((nsLookup_nsAppend_some n1 id n2 x).2 (Or.inl hx))

/- HOL4:
Theorem nsSub_conj:
   !P Q e1 e2. nsSub (\id x y. P id x y ∧ Q id x y) e1 e2 ⇔ nsSub P e1 e2 ∧
  nsSub Q e1 e2 -/
theorem nsSub_conj {μ ν α β : Type} :
    ∀ (P Q : ident μ ν → α → β → Prop) (e1 : Namespace μ ν α) (e2 : Namespace μ ν β),
      nsSub (fun id x y => P id x y ∧ Q id x y) e1 e2 ↔
        (nsSub P e1 e2 ∧ nsSub Q e1 e2) := by
  intro P Q e1 e2
  constructor
  · intro h
    exact ⟨nsSub_mono (fun _ _ _ h => h.1) h, nsSub_mono (fun _ _ _ h => h.2) h⟩
  · rintro ⟨⟨h1, h2⟩, ⟨h3, -⟩⟩
    refine ⟨fun id v1 hv => ?_, h2⟩
    obtain ⟨v2, ha, hb⟩ := h1 id v1 hv
    obtain ⟨v2', hc, hd⟩ := h3 id v1 hv
    rw [ha] at hc; cases hc
    exact ⟨v2, ha, hb, hd⟩

/- HOL4:
Theorem nsSub_refl:
   !P R. (!n x. P n x ⇒ R n x x) ⇒ !e. nsAll P e ⇒ nsSub R e e -/
theorem nsSub_refl {μ ν α : Type} :
    ∀ (P : ident μ ν → α → Prop) (R : ident μ ν → α → α → Prop),
      (∀ n x, P n x → R n x x) → ∀ e : Namespace μ ν α, nsAll P e → nsSub R e e := by
  intro P R h e ha
  exact ⟨fun id v hv => ⟨v, hv, h _ _ (ha id v hv)⟩, fun _ h => h⟩

theorem Aux.nsLookupMod_nsBind_none {μ ν α : Type} (k : ν) (v : α) (e : Namespace μ ν α)
    (p : List μ) : nsLookupMod (nsBind k v e) p = none ↔ nsLookupMod e p = none := by
  obtain ⟨vs, ms⟩ := e
  cases p <;> simp [nsLookupMod, nsBind]

/- HOL4:
Theorem nsSub_nsBind:
   !R x v1 v2 e1 e2.
     R (Short x) v1 v2 ∧ nsSub R e1 e2 ⇒ nsSub R (nsBind x v1 e1) (nsBind x v2 e2) -/
theorem nsSub_nsBind {μ ν α β : Type} :
    ∀ (R : ident μ ν → α → β → Prop) (x : ν) (v1 : α) (v2 : β)
      (e1 : Namespace μ ν α) (e2 : Namespace μ ν β),
      R (Short x) v1 v2 ∧ nsSub R e1 e2 → nsSub R (nsBind x v1 e1) (nsBind x v2 e2) := by
  rintro R x v1 v2 e1 e2 ⟨hr, h1, h2⟩
  refine ⟨fun id v hv => ?_, fun p => ?_⟩
  · rw [Aux.nsLookup_nsBind_if] at hv ⊢
    split at hv
    · rename_i e
      cases hv
      exact ⟨v2, by rw [if_pos e], by rw [e]; exact hr⟩
    · rename_i e
      rw [if_neg e]
      exact h1 id v hv
  · rw [Aux.nsLookupMod_nsBind_none, Aux.nsLookupMod_nsBind_none]
    exact h2 p

theorem Aux.nsSub_nsAppend {μ ν α β : Type} {R : ident μ ν → α → β → Prop}
    {e1 e2 : Namespace μ ν α} {e1' e2' : Namespace μ ν β}
    (h1 : nsSub R e1 e1') (h1' : ∀ p, nsLookupMod e1 p = none → nsLookupMod e1' p = none)
    (h1n : ∀ id, nsLookup e1 id = none → nsLookup e1' id = none)
    (h2 : nsSub R e2 e2') : nsSub R (nsAppend e1 e2) (nsAppend e1' e2') := by
  refine ⟨fun id v hv => ?_, fun p hp => ?_⟩
  · rcases (nsLookup_nsAppend_some e1 id e2 v).1 hv with h | ⟨ha, hb, hc⟩
    · obtain ⟨w, hw, hr⟩ := h1.1 id v h
      exact ⟨w, (nsLookup_nsAppend_some _ _ _ _).2 (Or.inl hw), hr⟩
    · obtain ⟨w, hw, hr⟩ := h2.1 id v hb
      exact ⟨w, (nsLookup_nsAppend_some _ _ _ _).2
        (Or.inr ⟨h1n id ha, hw, fun p1 p2 h => h1' _ (hc p1 p2 h)⟩), hr⟩
  · rw [nsLookupMod_nsAppend_none] at hp ⊢
    obtain ⟨ha, hb⟩ := hp
    refine ⟨h1.2 p ha, ?_⟩
    rcases hb with hb | ⟨p1, p2, e3, hp1, he, hl⟩
    · exact Or.inl (h2.2 p hb)
    · right
      refine ⟨p1, p2, ?_⟩
      cases hn : nsLookupMod e1 p1 with
      | some e4 => exact ⟨e4, hp1, he, rfl⟩
      | none => rw [h1' p1 hn] at hl; cases hl

/- HOL4:
Theorem nsSub_nsAppend2:
   !R e1 e2 e2'. nsSub R e1 e1 ∧ nsSub R e2 e2' ⇒ nsSub R (nsAppend e1 e2) (nsAppend e1 e2') -/
theorem nsSub_nsAppend2 {μ ν α : Type} :
    ∀ (R : ident μ ν → α → α → Prop) (e1 e2 e2' : Namespace μ ν α),
      nsSub R e1 e1 ∧ nsSub R e2 e2' → nsSub R (nsAppend e1 e2) (nsAppend e1 e2') := by
  rintro R e1 e2 e2' ⟨h1, h2⟩
  exact Aux.nsSub_nsAppend h1 (fun _ h => h) (fun _ h => h) h2

/- HOL4:
Theorem alist_rel_restr_thm:
   !R e1 e2 keys.
    alist_rel_restr R e1 e2 keys ⇔
      !k. MEM k keys ⇒ ?v1 v2. ALOOKUP e1 k = SOME v1 ∧ ALOOKUP e2 k = SOME v2 ∧ R k v1 v2 -/
theorem alist_rel_restr_thm {κ α β : Type} :
    ∀ (R : κ → α → β → Prop) (e1 : List (κ × α)) (e2 : List (κ × β)) (keys : List κ),
      alist_rel_restr R e1 e2 keys ↔
        (∀ k, k ∈ keys →
          ∃ v1 v2, ALOOKUP e1 k = some v1 ∧ ALOOKUP e2 k = some v2 ∧ R k v1 v2) :=
  alist_rel_restr_iff_aux

/- HOL4:
Theorem alistSub_cong:
   !l1 l2 l1' l2' R R'.
    l1 = l1' ∧ l2 = l2' ∧ (!n x y. ALOOKUP l1' n = SOME x ∧ ALOOKUP l2' n = SOME y ⇒ R n x y = R' n x y) ⇒
    (alistSub R l1 l2 ⇔ alistSub R' l1' l2') -/
theorem alistSub_cong {κ α β : Type} :
    ∀ (l1 : List (κ × α)) (l2 : List (κ × β)) (l1' : List (κ × α)) (l2' : List (κ × β))
      (R R' : κ → α → β → Prop),
      l1 = l1' ∧ l2 = l2' ∧
        (∀ n x y, ALOOKUP l1' n = some x ∧ ALOOKUP l2' n = some y → (R n x y ↔ R' n x y)) →
      (alistSub R l1 l2 ↔ alistSub R' l1' l2') := by
  rintro l1 l2 _ _ R R' ⟨rfl, rfl, h⟩
  unfold alistSub
  rw [alist_rel_restr_thm, alist_rel_restr_thm]
  constructor
  · intro H k hk
    obtain ⟨v1, v2, ha, hb, hr⟩ := H k hk
    exact ⟨v1, v2, ha, hb, (h _ _ _ ⟨ha, hb⟩).1 hr⟩
  · intro H k hk
    obtain ⟨v1, v2, ha, hb, hr⟩ := H k hk
    exact ⟨v1, v2, ha, hb, (h _ _ _ ⟨ha, hb⟩).2 hr⟩

/- HOL4:
Theorem nsLookup_FOLDR_nsLift:
   !e p k. nsLookup (FOLDR nsLift e p) (mk_id p k) = nsLookup e (Short k) -/
theorem nsLookup_FOLDR_nsLift {μ ν α : Type} :
    ∀ (e : Namespace μ ν α) (p : List μ) (k : ν),
      nsLookup (p.foldr nsLift e) (mk_id p k) = nsLookup e (Short k) := by
  intro e p k
  induction p with
  | nil => rfl
  | cons a p ih => simp [mk_id, nsLookup_nsLift, ih]

/- HOL4:
Theorem nsLookup_FOLDR_nsLift_some:
   !e p id v.
    nsLookup (FOLDR nsLift e p) id = SOME v ⇔
    (p = [] ∧ nsLookup e id = SOME v) ∨
    (p ≠ [] ∧ ?p2 n. id = mk_id (p++p2) n ∧ nsLookup e (mk_id p2 n) = SOME v) -/
theorem nsLookup_FOLDR_nsLift_some {μ ν α : Type} :
    ∀ (e : Namespace μ ν α) (p : List μ) (id : ident μ ν) (v : α),
      nsLookup (p.foldr nsLift e) id = some v ↔
        ((p = [] ∧ nsLookup e id = some v) ∨
          (p ≠ [] ∧ ∃ p2 n, id = mk_id (p ++ p2) n ∧ nsLookup e (mk_id p2 n) = some v)) := by
  have key : ∀ (e : Namespace μ ν α) (p : List μ) (id : ident μ ν) (v : α),
      nsLookup (p.foldr nsLift e) id = some v ↔
        ∃ p2 n, id = mk_id (p ++ p2) n ∧ nsLookup e (mk_id p2 n) = some v := by
    intro e p
    induction p with
    | nil =>
      intro id v
      constructor
      · intro h
        exact ⟨id_to_mods id, id_to_n id, (mk_id_thm id).symm, by rw [mk_id_thm]; exact h⟩
      · rintro ⟨p2, n, rfl, h⟩; exact h
    | cons a p ih =>
      intro id v
      rw [List.foldr_cons, nsLookup_nsLift]
      cases id with
      | Short x =>
        simp only [reduceCtorEq, false_iff]
        rintro ⟨p2, n, e, _⟩
        simp [mk_id] at e
      | Long mn id' =>
        simp only [List.cons_append, mk_id, ident.Long.injEq]
        split
        · rename_i e1
          rw [ih]
          constructor
          · rintro ⟨p2, n, h1, h2⟩; exact ⟨p2, n, ⟨e1.symm, h1⟩, h2⟩
          · rintro ⟨p2, n, ⟨-, h1⟩, h2⟩; exact ⟨p2, n, h1, h2⟩
        · rename_i e1
          simp only [reduceCtorEq, false_iff]
          rintro ⟨p2, n, ⟨h1, -⟩, h2⟩
          exact e1 h1.symm
  intro e p id v
  cases p with
  | nil => simp
  | cons a p => rw [key]; simp

/- HOL4:
Theorem nsLookupMod_FOLDR_nsLift_none:
   !e p1 p2. nsLookupMod (FOLDR nsLift e p1) p2 = NONE ⇔
    (IS_PREFIX p1 p2 ∨ IS_PREFIX p2 p1) ⇒
    ?p3. p2 = p1++p3 ∧ nsLookupMod e p3 = NONE -/
theorem nsLookupMod_FOLDR_nsLift_none {μ ν α : Type} :
    ∀ (e : Namespace μ ν α) (p1 p2 : List μ),
      nsLookupMod (p1.foldr nsLift e) p2 = none ↔
        ((IS_PREFIX p1 p2 ∨ IS_PREFIX p2 p1) →
          ∃ p3, p2 = p1 ++ p3 ∧ nsLookupMod e p3 = none) := by
  intro e p1
  induction p1 with
  | nil =>
    intro p2
    simp [IS_PREFIX, isPREFIX]
  | cons a p1 ih =>
    intro p2
    rw [List.foldr_cons, nsLookupMod_nsLift]
    cases p2 with
    | nil => simp [IS_PREFIX, isPREFIX]
    | cons b p2 =>
      simp only [IS_PREFIX, isPREFIX, List.cons_append, List.cons.injEq]
      split
      · rename_i e1
        subst e1
        rw [ih]
        simp [IS_PREFIX]
      · rename_i e1
        have e2 : ¬ b = a := fun h => e1 h.symm
        simp [e1, e2]

/- HOL4:
Theorem nsAll2_conj:
   !P Q e1 e2. nsAll2 (\id x y. P id x y ∧ Q id x y) e1 e2 ⇔ nsAll2 P e1 e2 ∧ nsAll2 Q e1 e2 -/
theorem nsAll2_conj {μ ν α β : Type} :
    ∀ (P Q : ident μ ν → α → β → Prop) (e1 : Namespace μ ν α) (e2 : Namespace μ ν β),
      nsAll2 (fun id x y => P id x y ∧ Q id x y) e1 e2 ↔
        (nsAll2 P e1 e2 ∧ nsAll2 Q e1 e2) := by
  intro P Q e1 e2
  unfold nsAll2
  rw [nsSub_conj, nsSub_conj (fun x y z => P x z y) (fun x y z => Q x z y)]
  constructor
  · rintro ⟨⟨a, b⟩, c, d⟩; exact ⟨⟨a, c⟩, b, d⟩
  · rintro ⟨⟨a, c⟩, b, d⟩; exact ⟨⟨a, b⟩, c, d⟩

/- HOL4:
Theorem nsAll2_nsLookup2:
   !R e1 e2 n v2.
    nsLookup e2 n = SOME v2 ∧
    nsAll2 R e1 e2
    ⇒
    ?v1. nsLookup e1 n = SOME v1 ∧ R n v1 v2 -/
theorem nsAll2_nsLookup2 {μ ν α β : Type} :
    ∀ (R : ident μ ν → α → β → Prop) (e1 : Namespace μ ν α) (e2 : Namespace μ ν β)
      (n : ident μ ν) (v2 : β),
      nsLookup e2 n = some v2 ∧ nsAll2 R e1 e2 →
      ∃ v1, nsLookup e1 n = some v1 ∧ R n v1 v2 := by
  rintro R e1 e2 n v2 ⟨h, -, h2⟩
  exact h2.1 n v2 h

theorem Aux.nsAll2_nsLookup1 {μ ν α β : Type} {R : ident μ ν → α → β → Prop}
    {e1 : Namespace μ ν α} {e2 : Namespace μ ν β} {n : ident μ ν} {v1 : α}
    (h : nsAll2 R e1 e2) (h1 : nsLookup e1 n = some v1) :
    ∃ v2, nsLookup e2 n = some v2 ∧ R n v1 v2 := h.1.1 n v1 h1

/- HOL4:
Theorem nsAll2_nsLookup_none:
   !R e1 e2 n.
    nsAll2 R e1 e2
    ⇒
    (nsLookup e1 n = NONE ⇔ nsLookup e2 n = NONE) -/
theorem nsAll2_nsLookup_none {μ ν α β : Type} :
    ∀ (R : ident μ ν → α → β → Prop) (e1 : Namespace μ ν α) (e2 : Namespace μ ν β)
      (n : ident μ ν),
      nsAll2 R e1 e2 → (nsLookup e1 n = none ↔ nsLookup e2 n = none) := by
  rintro R e1 e2 n ⟨h1, h2⟩
  constructor
  · intro h
    cases hn : nsLookup e2 n with
    | none => rfl
    | some v =>
      obtain ⟨w, hw, -⟩ := h2.1 n v hn
      rw [h] at hw; cases hw
  · intro h
    cases hn : nsLookup e1 n with
    | none => rfl
    | some v =>
      obtain ⟨w, hw, -⟩ := h1.1 n v hn
      rw [h] at hw; cases hw

/- HOL4:
Theorem nsAll2_nsBind:
   !R x v1 v2 e1 e2.
     R (Short x) v1 v2 ∧ nsAll2 R e1 e2 ⇒ nsAll2 R (nsBind x v1 e1) (nsBind x v2 e2) -/
theorem nsAll2_nsBind {μ ν α β : Type} :
    ∀ (R : ident μ ν → α → β → Prop) (x : ν) (v1 : α) (v2 : β)
      (e1 : Namespace μ ν α) (e2 : Namespace μ ν β),
      R (Short x) v1 v2 ∧ nsAll2 R e1 e2 → nsAll2 R (nsBind x v1 e1) (nsBind x v2 e2) := by
  rintro R x v1 v2 e1 e2 ⟨hr, h1, h2⟩
  exact ⟨nsSub_nsBind _ _ _ _ _ _ ⟨hr, h1⟩, nsSub_nsBind _ _ _ _ _ _ ⟨hr, h2⟩⟩

/- HOL4:
Theorem nsAll2_nsBindList:
   !R l1 l2 e1 e2.
     LIST_REL (\(x,y) (x',y'). x = x' ∧ R (Short x) y y') l1 l2 ∧ nsAll2 R e1 e2
     ⇒
     nsAll2 R (nsBindList l1 e1) (nsBindList l2 e2) -/
theorem nsAll2_nsBindList {μ ν α β : Type} :
    ∀ (R : ident μ ν → α → β → Prop) (l1 : List (ν × α)) (l2 : List (ν × β))
      (e1 : Namespace μ ν α) (e2 : Namespace μ ν β),
      LIST_REL (fun (x, y) (x', y') => x = x' ∧ R (Short x) y y') l1 l2 ∧ nsAll2 R e1 e2 →
      nsAll2 R (nsBindList l1 e1) (nsBindList l2 e2) := by
  intro R l1
  induction l1 with
  | nil =>
    rintro l2 e1 e2 ⟨h, h2⟩
    cases l2 with
    | nil => exact h2
    | cons b l2 => exact h.elim
  | cons a l1 ih =>
    rintro l2 e1 e2 ⟨h, h2⟩
    cases l2 with
    | nil => exact h.elim
    | cons b l2 =>
      obtain ⟨x, y⟩ := a
      obtain ⟨x', y'⟩ := b
      obtain ⟨⟨rfl, hr⟩, h⟩ := h
      exact nsAll2_nsBind R x y y' _ _ ⟨hr, ih l2 e1 e2 ⟨h, h2⟩⟩

/- HOL4:
Theorem nsAll2_nsAppend:
   !R e1 e1' e2 e2'.
    nsAll2 R e1 e2 ∧ nsAll2 R e1' e2' ⇒ nsAll2 R (nsAppend e1 e1') (nsAppend e2 e2') -/
theorem nsAll2_nsAppend {μ ν α β : Type} :
    ∀ (R : ident μ ν → α → β → Prop) (e1 e1' : Namespace μ ν α) (e2 e2' : Namespace μ ν β),
      nsAll2 R e1 e2 ∧ nsAll2 R e1' e2' →
      nsAll2 R (nsAppend e1 e1') (nsAppend e2 e2') := by
  rintro R e1 e1' e2 e2' ⟨h1, h2⟩
  exact ⟨Aux.nsSub_nsAppend h1.1 h1.2.2 (fun id => (nsAll2_nsLookup_none R e1 e2 id h1).1) h2.1,
    Aux.nsSub_nsAppend h1.2 h1.1.2 (fun id => (nsAll2_nsLookup_none R e1 e2 id h1).2) h2.2⟩

/- HOL4:
Theorem nsAll2_alist_to_ns:
   !R l1 l2. LIST_REL (\(x,y) (x',y'). x = x' ∧ R (Short x) y y') l1 l2 ⇒ nsAll2 R (alist_to_ns l1) (alist_to_ns l2) -/
theorem nsAll2_alist_to_ns {μ ν α β : Type} :
    ∀ (R : ident μ ν → α → β → Prop) (l1 : List (ν × α)) (l2 : List (ν × β)),
      LIST_REL (fun (x, y) (x', y') => x = x' ∧ R (Short x) y y') l1 l2 →
      nsAll2 R (alist_to_ns l1) (alist_to_ns l2) := by
  intro R l1 l2 h
  have := nsAll2_nsBindList R l1 l2 nsEmpty nsEmpty ⟨h, nsAll2_nsEmpty R⟩
  rw [← nsAppend_to_nsBindList, ← nsAppend_to_nsBindList, (nsAppend_nsEmpty _).1,
    (nsAppend_nsEmpty _).1] at this
  exact this

/- HOL4:
Theorem nsAll2_nsLift[simp]:
   !R mn e1 e2. nsAll2 R (nsLift mn e1) (nsLift mn e2) ⇔ nsAll2 (\id. R (Long mn id)) e1 e2 -/
theorem nsAll2_nsLift {μ ν α β : Type} :
    ∀ (R : ident μ ν → α → β → Prop) (mn : μ) (e1 : Namespace μ ν α) (e2 : Namespace μ ν β),
      nsAll2 R (nsLift mn e1) (nsLift mn e2) ↔ nsAll2 (fun id => R (Long mn id)) e1 e2 := by
  have key : ∀ {α β : Type} (R : ident μ ν → α → β → Prop) (mn : μ) (e1 : Namespace μ ν α)
      (e2 : Namespace μ ν β),
      nsSub R (nsLift mn e1) (nsLift mn e2) ↔ nsSub (fun id => R (Long mn id)) e1 e2 := by
    intro α β R mn e1 e2
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨fun id v hv => ?_, fun p hp => ?_⟩
      · obtain ⟨w, hw, hr⟩ := h1 (Long mn id) v (by simp [nsLookup_nsLift, hv])
        exact ⟨w, by simpa [nsLookup_nsLift] using hw, hr⟩
      · have := h2 (mn :: p) (by simp [nsLookupMod_nsLift, hp])
        simpa [nsLookupMod_nsLift] using this
    · rintro ⟨h1, h2⟩
      refine ⟨fun id v hv => ?_, fun p hp => ?_⟩
      · rw [nsLookup_nsLift] at hv ⊢
        cases id with
        | Short k => cases hv
        | Long mn' id' =>
          simp only at hv ⊢
          split at hv
          · rename_i e
            subst e
            rw [if_pos rfl]
            exact h1 id' v hv
          · cases hv
      · rw [nsLookupMod_nsLift] at hp ⊢
        cases p with
        | nil => cases hp
        | cons mn' p =>
          simp only at hp ⊢
          split at hp
          · rename_i e
            rw [if_pos e]
            exact h2 p hp
          · rename_i e
            rw [if_neg e]
  intro R mn e1 e2
  unfold nsAll2
  rw [key, key]

end

end CmlTS
