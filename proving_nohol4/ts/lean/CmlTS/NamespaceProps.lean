import CmlTS.Ast
import CmlTS.Namespace

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
  [HOL4 proof text removed]
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
  | Long mn id ih => simp only [id_to_mods, id_to_n, mk_id, ih]

/- HOL4:
Theorem nsSub_mono[mono]:
   (!x y z. R1 x y z ⇒ R2 x y z) ⇒ (nsSub R1 e1 e2 ⇒ nsSub R2 e1 e2) -/
theorem nsSub_mono {μ ν α β : Type} {R1 R2 : ident μ ν → α → β → Prop}
    {e1 : Namespace μ ν α} {e2 : Namespace μ ν β} :
    (∀ x y z, R1 x y z → R2 x y z) → (nsSub R1 e1 e2 → nsSub R2 e1 e2) := by
  rintro h ⟨h1, h2⟩
  refine ⟨fun id v1 hv => ?_, h2⟩
  obtain ⟨v2, hv2, hr⟩ := h1 id v1 hv
  exact ⟨v2, hv2, h _ _ _ hr⟩

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
  cases id <;> simp [nsEmpty, nsLookup, ALOOKUP]

/- HOL4:
Theorem nsLookupMod_nsEmpty[simp]:
   !x y. nsLookupMod nsEmpty (x::y) = NONE -/
theorem nsLookupMod_nsEmpty {μ ν α : Type} :
    ∀ (x : μ) (y : List μ),
      nsLookupMod (nsEmpty : Namespace μ ν α) (x :: y) = none := by
  intro x y
  simp [nsEmpty, nsLookupMod, ALOOKUP]

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
  intro f id v h
  rw [nsLookup_nsEmpty] at h; cases h

/- HOL4:
Theorem nsAll2_nsEmpty[simp]:
   !f. nsAll2 f nsEmpty nsEmpty -/
theorem nsAll2_nsEmpty {μ ν α β : Type} :
    ∀ f : ident μ ν → α → β → Prop, nsAll2 f nsEmpty nsEmpty :=
  fun f => ⟨nsSub_nsEmpty _ _, nsSub_nsEmpty _ _⟩

/- HOL4:
Theorem alist_to_ns_cons[simp]:
   !k v l. alist_to_ns ((k,v)::l) = nsBind k v (alist_to_ns l) -/
theorem alist_to_ns_cons {μ ν α : Type} :
    ∀ (k : ν) (v : α) (l : List (ν × α)),
      (alist_to_ns ((k, v) :: l) : Namespace μ ν α) = nsBind k v (alist_to_ns l) :=
  fun _ _ _ => rfl

/- HOL4:
Theorem nsAppend_nsBind[simp]:
   !k v e1 e2. nsAppend (nsBind k v e1) e2 = nsBind k v (nsAppend e1 e2) -/
theorem nsAppend_nsBind {μ ν α : Type} :
    ∀ (k : ν) (v : α) (e1 e2 : Namespace μ ν α),
      nsAppend (nsBind k v e1) e2 = nsBind k v (nsAppend e1 e2) := by
  rintro k v ⟨_, _⟩ ⟨_, _⟩
  rfl

/- HOL4:
Theorem nsAppend_assoc[simp]:
   !e1 e2 e3. nsAppend e1 (nsAppend e2 e3) = nsAppend (nsAppend e1 e2) e3 -/
theorem nsAppend_assoc {μ ν α : Type} :
    ∀ e1 e2 e3 : Namespace μ ν α,
      nsAppend e1 (nsAppend e2 e3) = nsAppend (nsAppend e1 e2) e3 := by
  rintro ⟨_, _⟩ ⟨_, _⟩ ⟨_, _⟩
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
  · rintro n v ⟨_, _⟩
    simp [nsBind, nsLookup, ALOOKUP]
  · rintro (x | ⟨mn, id⟩) n' v ⟨_, _⟩ h
    · have : ¬ n' = x := fun e => h (e ▸ rfl)
      simp [nsBind, nsLookup, ALOOKUP, this]
    · simp [nsBind, nsLookup]

theorem Aux.nsLookup_nsBind_if {μ ν α : Type} (n : ν) (v : α) (e : Namespace μ ν α)
    (id : ident μ ν) :
    nsLookup (nsBind n v e) id = if id = Short n then some v else nsLookup e id := by
  split
  · rename_i h; subst h
    exact (nsLookup_nsBind (μ' := μ) (ν' := ν) (α' := α)).1 n v e
  · rename_i h
    exact (nsLookup_nsBind (μ := μ) (ν := ν) (α := α)).2 id n v e h

theorem Aux.nsLookupMod_nsBind_none {μ ν α : Type} (n : ν) (v : α) (e : Namespace μ ν α)
    (p : List μ) : nsLookupMod (nsBind n v e) p = none ↔ nsLookupMod e p = none := by
  obtain ⟨_, _⟩ := e
  cases p <;> simp [nsBind, nsLookupMod]

/- HOL4:
Theorem nsAppend_nsSing[simp]:
   !n x e. nsAppend (nsSing n x) e = nsBind n x e -/
theorem nsAppend_nsSing {μ ν α : Type} :
    ∀ (n : ν) (x : α) (e : Namespace μ ν α),
      nsAppend (nsSing n x) e = nsBind n x e := by
  rintro n x ⟨_, _⟩
  rfl

/- HOL4:
Theorem nsLookup_nsSing[simp]:
   !n v id. nsLookup (nsSing n v) id = if id = Short n then SOME v else NONE -/
theorem nsLookup_nsSing {μ ν α : Type} :
    ∀ (n : ν) (v : α) (id : ident μ ν),
      nsLookup (nsSing n v) id = if id = Short n then some v else none := by
  intro n v id
  have : nsSing n v = nsBind n v (nsEmpty : Namespace μ ν α) := rfl
  rw [this, Aux.nsLookup_nsBind_if, nsLookup_nsEmpty]

/- HOL4:
Theorem nsAll_nsSing[simp]:
   !R n v. nsAll R (nsSing n v) ⇔ R (Short n) v -/
theorem nsAll_nsSing {μ ν α : Type} :
    ∀ (R : ident μ ν → α → Prop) (n : ν) (v : α),
      nsAll R (nsSing n v) ↔ R (Short n) v := by
  intro R n v
  constructor
  · intro h
    exact h (Short n) v (by rw [nsLookup_nsSing]; simp)
  · intro h id x hx
    rw [nsLookup_nsSing] at hx
    split at hx
    · rename_i hid; cases hx; subst hid; exact h
    · cases hx

/- HOL4:
Theorem nsAll2_nsSing[simp]:
   !R n1 v1 n2 v2. nsAll2 R (nsSing n1 v1) (nsSing n2 v2) ⇔ n1 = n2 ∧ R (Short n1) v1 v2 -/
theorem nsAll2_nsSing {μ ν α β : Type} :
    ∀ (R : ident μ ν → α → β → Prop) (n1 : ν) (v1 : α) (n2 : ν) (v2 : β),
      nsAll2 R (nsSing n1 v1) (nsSing n2 v2) ↔ (n1 = n2 ∧ R (Short n1) v1 v2) := by
  intro R n1 v1 n2 v2
  constructor
  · rintro ⟨⟨h1, -⟩, -⟩
    obtain ⟨x, hx, hr⟩ := h1 (Short n1) v1 (by rw [nsLookup_nsSing]; simp)
    rw [nsLookup_nsSing] at hx
    split at hx
    · rename_i hid; cases hx; cases hid; exact ⟨rfl, hr⟩
    · cases hx
  · rintro ⟨rfl, hr⟩
    refine ⟨⟨fun id x hx => ?_, fun p hp => ?_⟩, ⟨fun id x hx => ?_, fun p hp => ?_⟩⟩
    · rw [nsLookup_nsSing] at hx ⊢
      split at hx
      · rename_i hid; cases hx; subst hid; exact ⟨v2, by simp, hr⟩
      · cases hx
    · cases p <;> simp_all [nsSing, nsLookupMod, ALOOKUP]
    · rw [nsLookup_nsSing] at hx ⊢
      split at hx
      · rename_i hid; cases hx; subst hid; exact ⟨v1, by simp, hr⟩
      · cases hx
    · cases p <;> simp_all [nsSing, nsLookupMod, ALOOKUP]

/- HOL4:
Theorem nsBind_11[simp]:
   !x y n x' y' n'. nsBind x y n = nsBind x' y' n' ⇔ x = x' ∧ y = y' ∧ n = n' -/
theorem nsBind_11 {μ ν α : Type} :
    ∀ (x : ν) (y : α) (n : Namespace μ ν α) (x' : ν) (y' : α) (n' : Namespace μ ν α),
      nsBind x y n = nsBind x' y' n' ↔ (x = x' ∧ y = y' ∧ n = n') := by
  rintro x y ⟨_, _⟩ x' y' ⟨_, _⟩
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
    simp only [nsLift, nsLookup, ALOOKUP]
    by_cases h : mn = mn' <;> simp [h]

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
  | cons mn' path' =>
    simp only [nsLift, nsLookupMod, ALOOKUP]
    by_cases h : mn = mn' <;> simp [h]

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
    simp only [nsAppend, nsLookup, Aux.ALOOKUP_append, id_to_mods]
    cases h : ALOOKUP v1 x with
    | some y => simp
    | none =>
      simp only [reduceCtorEq, false_or, true_and]
      constructor
      · intro h2
        refine ⟨h2, ?_⟩
        rintro p1 p2 ⟨hp, he⟩
        have := List.append_eq_nil_iff.mp he.symm
        exact absurd this.1 hp
      · exact fun h2 => h2.1
  | Long mn id =>
    simp only [nsAppend, nsLookup, Aux.ALOOKUP_append, id_to_mods]
    cases h : ALOOKUP m1 mn with
    | some env =>
      simp only
      constructor
      · exact Or.inl
      · rintro (h2 | ⟨-, -, h2⟩)
        · exact h2
        · have := h2 [mn] (id_to_mods id) ⟨by simp, by simp⟩
          simp [nsLookupMod, h] at this
    | none =>
      simp only [reduceCtorEq, false_or, true_and]
      constructor
      · intro h2
        refine ⟨h2, ?_⟩
        rintro p1 p2 ⟨hp, he⟩
        cases p1 with
        | nil => exact absurd rfl hp
        | cons a p1 =>
          simp only [List.cons_append, List.cons.injEq] at he
          obtain ⟨rfl, -⟩ := he
          simp [nsLookupMod, h]
      · exact fun h2 => h2.1

/- HOL4:
Theorem nsAppend_to_nsBindList:
   !l. nsAppend (alist_to_ns l) e = nsBindList l e -/
theorem nsAppend_to_nsBindList {μ ν α : Type} {e : Namespace μ ν α} :
    ∀ l : List (ν × α), nsAppend (alist_to_ns l) e = nsBindList l e := by
  intro l
  induction l with
  | nil => obtain ⟨_, _⟩ := e; rfl
  | cons p t ih =>
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
    cases h : ALOOKUP m1 mn with
    | some env =>
      simp only
      constructor
      · intro h2
        exact ⟨h2, Or.inr ⟨[mn], path, env, by simp, by simp, by simp [nsLookupMod, h]⟩⟩
      · exact fun h2 => h2.1
    | none =>
      simp only [true_and]
      constructor
      · exact Or.inl
      · rintro (h2 | ⟨p1, p2, e3, hp, he, h3⟩)
        · exact h2
        · cases p1 with
          | nil => exact absurd rfl hp
          | cons a p1 =>
            simp only [List.cons_append, List.cons.injEq] at he
            obtain ⟨rfl, -⟩ := he
            simp [nsLookupMod, h] at h3

/- HOL4:
Theorem eALL_T[simp]:
   !e. nsAll (\n x. T) e -/
theorem eALL_T {μ ν α : Type} :
    ∀ e : Namespace μ ν α, nsAll (fun _n _x => True) e := fun _ _ _ _ => trivial

/- HOL4:
Theorem nsLookup_nsAll:
   !env x P v. nsAll P env ∧ nsLookup env x = SOME v ⇒ P x v -/
theorem nsLookup_nsAll {μ ν α : Type} :
    ∀ (env : Namespace μ ν α) (x : ident μ ν) (P : ident μ ν → α → Prop) (v : α),
      nsAll P env ∧ nsLookup env x = some v → P x v := fun _ _ _ _ h => h.1 _ _ h.2

/- HOL4:
Theorem nsAll_nsAppend:
   !f e1 e2. nsAll f e1 ∧ nsAll f e2 ⇒ nsAll f (nsAppend e1 e2) -/
theorem nsAll_nsAppend {μ ν α : Type} :
    ∀ (f : ident μ ν → α → Prop) (e1 e2 : Namespace μ ν α),
      nsAll f e1 ∧ nsAll f e2 → nsAll f (nsAppend e1 e2) := by
  rintro f e1 e2 ⟨h1, h2⟩ id x hx
  rw [nsLookup_nsAppend_some] at hx
  rcases hx with hx | ⟨-, hx, -⟩
  · exact h1 _ _ hx
  · exact h2 _ _ hx

/- HOL4:
Theorem nsAll_alist_to_ns:
   !R l. EVERY (λ(n,v). R (Short n) v) l ⇒ nsAll R (alist_to_ns l) -/
theorem nsAll_alist_to_ns {μ ν α : Type} :
    ∀ (R : ident μ ν → α → Prop) (l : List (ν × α)),
      EVERY (fun (n, v) => R (Short n) v) l → nsAll R (alist_to_ns l) := by
  intro R l h id x hx
  cases id with
  | Short n =>
    simp only [alist_to_ns, nsLookup] at hx
    exact EVERY_iff_forall.mp h _ (Aux.ALOOKUP_mem hx)
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
    exact h (Long mn id) x (by rw [nsLookup_nsLift]; simpa using hx)
  · intro h id x hx
    rw [nsLookup_nsLift] at hx
    cases id with
    | Short n => simp at hx
    | Long mn' id =>
      simp only at hx
      split at hx
      · rename_i he; subst he; exact h _ _ hx
      · cases hx

/- HOL4:
Theorem nsAll_nsAppend_left:
   !P n1 n2. nsAll P (nsAppend n1 n2) ⇒ nsAll P n1 -/
theorem nsAll_nsAppend_left {μ ν α : Type} :
    ∀ (P : ident μ ν → α → Prop) (n1 n2 : Namespace μ ν α),
      nsAll P (nsAppend n1 n2) → nsAll P n1 := by
  intro P n1 n2 h id x hx
  exact h id x ((nsLookup_nsAppend_some _ _ _ _).mpr (Or.inl hx))

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
    refine ⟨fun id x hx => ?_, h2⟩
    obtain ⟨y, hy, hp⟩ := h1 id x hx
    obtain ⟨z, hz, hq⟩ := h3 id x hx
    rw [hy] at hz
    cases hz
    exact ⟨y, hy, hp, hq⟩

/- HOL4:
Theorem nsSub_refl:
   !P R. (!n x. P n x ⇒ R n x x) ⇒ !e. nsAll P e ⇒ nsSub R e e -/
theorem nsSub_refl {μ ν α : Type} :
    ∀ (P : ident μ ν → α → Prop) (R : ident μ ν → α → α → Prop),
      (∀ n x, P n x → R n x x) → ∀ e : Namespace μ ν α, nsAll P e → nsSub R e e :=
  fun _ _ h _ ha => ⟨fun id x hx => ⟨x, hx, h _ _ (ha id x hx)⟩, fun _ hp => hp⟩

/- HOL4:
Theorem nsSub_nsBind:
   !R x v1 v2 e1 e2.
     R (Short x) v1 v2 ∧ nsSub R e1 e2 ⇒ nsSub R (nsBind x v1 e1) (nsBind x v2 e2) -/
theorem nsSub_nsBind {μ ν α β : Type} :
    ∀ (R : ident μ ν → α → β → Prop) (x : ν) (v1 : α) (v2 : β)
      (e1 : Namespace μ ν α) (e2 : Namespace μ ν β),
      R (Short x) v1 v2 ∧ nsSub R e1 e2 → nsSub R (nsBind x v1 e1) (nsBind x v2 e2) := by
  rintro R x v1 v2 e1 e2 ⟨hr, h1, h2⟩
  refine ⟨fun id y hy => ?_, fun p hp => ?_⟩
  · rw [Aux.nsLookup_nsBind_if] at hy ⊢
    split at hy
    · rename_i hid; cases hy; subst hid; exact ⟨v2, by simp, hr⟩
    · rename_i hid; rw [if_neg hid]; exact h1 _ _ hy
  · rw [Aux.nsLookupMod_nsBind_none] at hp ⊢
    exact h2 _ hp

theorem Aux.nsSub_nsAppend {μ ν α β : Type} (R : ident μ ν → α → β → Prop)
    (e1 e1' : Namespace μ ν α) (e2 e2' : Namespace μ ν β)
    (h1 : nsSub R e1 e2) (h1' : nsSub R e1' e2')
    (h2 : ∀ id, nsLookup e1 id = none → nsLookup e2 id = none)
    (h3 : ∀ p, nsLookupMod e1 p = none → nsLookupMod e2 p = none) :
    nsSub R (nsAppend e1 e1') (nsAppend e2 e2') := by
  refine ⟨fun id x hx => ?_, fun p hp => ?_⟩
  · rw [nsLookup_nsAppend_some] at hx
    rcases hx with hx | ⟨hn, hx, hm⟩
    · obtain ⟨y, hy, hr⟩ := h1.1 _ _ hx
      exact ⟨y, (nsLookup_nsAppend_some _ _ _ _).mpr (Or.inl hy), hr⟩
    · obtain ⟨y, hy, hr⟩ := h1'.1 _ _ hx
      exact ⟨y, (nsLookup_nsAppend_some _ _ _ _).mpr
        (Or.inr ⟨h2 _ hn, hy, fun p1 p2 hp => h3 _ (hm p1 p2 hp)⟩), hr⟩
  · rw [nsLookupMod_nsAppend_none] at hp ⊢
    obtain ⟨hp1, hp2⟩ := hp
    refine ⟨h1.2 _ hp1, ?_⟩
    rcases hp2 with hp2 | ⟨p1, p2, e3, hne, he, hl⟩
    · exact Or.inl (h1'.2 _ hp2)
    · refine Or.inr ⟨p1, p2, ?_⟩
      cases h4 : nsLookupMod e1 p1 with
      | none => rw [h3 _ h4] at hl; cases hl
      | some e4 => exact ⟨e4, hne, he, rfl⟩

/- HOL4:
Theorem nsSub_nsAppend2:
   !R e1 e2 e2'. nsSub R e1 e1 ∧ nsSub R e2 e2' ⇒ nsSub R (nsAppend e1 e2) (nsAppend e1 e2') -/
theorem nsSub_nsAppend2 {μ ν α : Type} :
    ∀ (R : ident μ ν → α → α → Prop) (e1 e2 e2' : Namespace μ ν α),
      nsSub R e1 e1 ∧ nsSub R e2 e2' → nsSub R (nsAppend e1 e2) (nsAppend e1 e2') :=
  fun R e1 e2 e2' h => Aux.nsSub_nsAppend R e1 e2 e1 e2' h.1 h.2 (fun _ h => h) (fun _ h => h)

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
  fun R e1 e2 keys => alist_rel_restr_iff_aux R e1 e2 keys

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
  rintro l1 l2 l1' l2' R R' ⟨rfl, rfl, h⟩
  unfold alistSub
  rw [alist_rel_restr_thm, alist_rel_restr_thm]
  constructor
  · intro h1 k hk
    obtain ⟨v1, v2, ha, hb, hr⟩ := h1 k hk
    exact ⟨v1, v2, ha, hb, (h _ _ _ ⟨ha, hb⟩).mp hr⟩
  · intro h1 k hk
    obtain ⟨v1, v2, ha, hb, hr⟩ := h1 k hk
    exact ⟨v1, v2, ha, hb, (h _ _ _ ⟨ha, hb⟩).mpr hr⟩

/- HOL4:
Theorem nsLookup_FOLDR_nsLift:
   !e p k. nsLookup (FOLDR nsLift e p) (mk_id p k) = nsLookup e (Short k) -/
theorem nsLookup_FOLDR_nsLift {μ ν α : Type} :
    ∀ (e : Namespace μ ν α) (p : List μ) (k : ν),
      nsLookup (p.foldr nsLift e) (mk_id p k) = nsLookup e (Short k) := by
  intro e p k
  induction p with
  | nil => rfl
  | cons a t ih =>
    rw [List.foldr_cons, nsLookup_nsLift]
    simpa [mk_id] using ih

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
  intro e p
  induction p with
  | nil => intro id v; simp
  | cons a t ih =>
    intro id v
    rw [List.foldr_cons, nsLookup_nsLift]
    cases id with
    | Short x => simp [mk_id]
    | Long mn id =>
      simp only [List.cons_append, mk_id, ident.Long.injEq]
      by_cases h : a = mn
      · subst h
        rw [if_pos rfl, ih]
        constructor
        · rintro (⟨rfl, h2⟩ | ⟨h1, p2, n, rfl, h2⟩)
          · obtain ⟨p, n, rfl⟩ := mk_id_surj id
            exact Or.inr ⟨by simp, p, n, ⟨rfl, rfl⟩, h2⟩
          · exact Or.inr ⟨by simp, p2, n, ⟨rfl, rfl⟩, h2⟩
        · rintro (⟨h1, -⟩ | ⟨-, p2, n, ⟨-, rfl⟩, h2⟩)
          · simp at h1
          · cases t with
            | nil => exact Or.inl ⟨rfl, h2⟩
            | cons b t => exact Or.inr ⟨by simp, p2, n, rfl, h2⟩
      · rw [if_neg h]
        constructor
        · intro h2; cases h2
        · rintro (⟨h1, -⟩ | ⟨-, p2, n, ⟨rfl, -⟩, -⟩)
          · simp at h1
          · exact absurd rfl h

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
  | cons a t ih =>
    intro p2
    rw [List.foldr_cons, nsLookupMod_nsLift]
    cases p2 with
    | nil => simp [IS_PREFIX, isPREFIX]
    | cons b q =>
      simp only [IS_PREFIX, isPREFIX, List.cons_append, List.cons.injEq]
      by_cases h : a = b
      · subst h
        simp only [if_true, true_and]
        exact ih q
      · have h' : ¬ b = a := fun e => h e.symm
        simp [h, h']

/- HOL4:
Theorem nsAll2_conj:
   !P Q e1 e2. nsAll2 (\id x y. P id x y ∧ Q id x y) e1 e2 ⇔ nsAll2 P e1 e2 ∧ nsAll2 Q e1 e2 -/
theorem nsAll2_conj {μ ν α β : Type} :
    ∀ (P Q : ident μ ν → α → β → Prop) (e1 : Namespace μ ν α) (e2 : Namespace μ ν β),
      nsAll2 (fun id x y => P id x y ∧ Q id x y) e1 e2 ↔
        (nsAll2 P e1 e2 ∧ nsAll2 Q e1 e2) := by
  intro P Q e1 e2
  unfold nsAll2
  rw [nsSub_conj, nsSub_conj (fun id x y => P id y x) (fun id x y => Q id y x)]
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
      ∃ v1, nsLookup e1 n = some v1 ∧ R n v1 v2 :=
  fun _ _ _ _ _ h => h.2.2.1 _ _ h.1

theorem Aux.nsAll2_nsLookup1 {μ ν α β : Type}
    (R : ident μ ν → α → β → Prop) (e1 : Namespace μ ν α) (e2 : Namespace μ ν β)
    (n : ident μ ν) (v1 : α) (h1 : nsLookup e1 n = some v1) (h2 : nsAll2 R e1 e2) :
    ∃ v2, nsLookup e2 n = some v2 ∧ R n v1 v2 := h2.1.1 _ _ h1

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
    cases h3 : nsLookup e2 n with
    | none => rfl
    | some x =>
      obtain ⟨y, hy, -⟩ := h2.1 _ _ h3
      rw [h] at hy; cases hy
  · intro h
    cases h3 : nsLookup e1 n with
    | none => rfl
    | some x =>
      obtain ⟨y, hy, -⟩ := h1.1 _ _ h3
      rw [h] at hy; cases hy

/- HOL4:
Theorem nsAll2_nsBind:
   !R x v1 v2 e1 e2.
     R (Short x) v1 v2 ∧ nsAll2 R e1 e2 ⇒ nsAll2 R (nsBind x v1 e1) (nsBind x v2 e2) -/
theorem nsAll2_nsBind {μ ν α β : Type} :
    ∀ (R : ident μ ν → α → β → Prop) (x : ν) (v1 : α) (v2 : β)
      (e1 : Namespace μ ν α) (e2 : Namespace μ ν β),
      R (Short x) v1 v2 ∧ nsAll2 R e1 e2 → nsAll2 R (nsBind x v1 e1) (nsBind x v2 e2) :=
  fun _ x v1 v2 e1 e2 h => ⟨nsSub_nsBind _ x v1 v2 e1 e2 ⟨h.1, h.2.1⟩,
    nsSub_nsBind _ x v2 v1 e2 e1 ⟨h.1, h.2.2⟩⟩

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
    rintro l2 e1 e2 ⟨h1, h2⟩
    cases l2 with
    | nil => exact h2
    | cons _ _ => simp [LIST_REL] at h1
  | cons p t ih =>
    rintro l2 e1 e2 ⟨h1, h2⟩
    cases l2 with
    | nil => simp [LIST_REL] at h1
    | cons q t2 =>
      obtain ⟨x, y⟩ := p
      obtain ⟨x', y'⟩ := q
      simp only [LIST_REL] at h1
      obtain ⟨⟨rfl, hr⟩, h1⟩ := h1
      exact nsAll2_nsBind _ _ _ _ _ _ ⟨hr, ih t2 e1 e2 ⟨h1, h2⟩⟩

/- HOL4:
Theorem nsAll2_nsAppend:
   !R e1 e1' e2 e2'.
    nsAll2 R e1 e2 ∧ nsAll2 R e1' e2' ⇒ nsAll2 R (nsAppend e1 e1') (nsAppend e2 e2') -/
theorem nsAll2_nsAppend {μ ν α β : Type} :
    ∀ (R : ident μ ν → α → β → Prop) (e1 e1' : Namespace μ ν α) (e2 e2' : Namespace μ ν β),
      nsAll2 R e1 e2 ∧ nsAll2 R e1' e2' →
      nsAll2 R (nsAppend e1 e1') (nsAppend e2 e2') := by
  rintro R e1 e1' e2 e2' ⟨h, h'⟩
  have hn := fun id => nsAll2_nsLookup_none R e1 e2 id h
  exact ⟨Aux.nsSub_nsAppend _ _ _ _ _ h.1 h'.1 (fun id => (hn id).mp) (fun p => h.2.2 p),
    Aux.nsSub_nsAppend _ _ _ _ _ h.2 h'.2 (fun id => (hn id).mpr) (fun p => h.1.2 p)⟩

/- HOL4:
Theorem nsAll2_alist_to_ns:
   !R l1 l2. LIST_REL (\(x,y) (x',y'). x = x' ∧ R (Short x) y y') l1 l2 ⇒ nsAll2 R (alist_to_ns l1) (alist_to_ns l2) -/
theorem nsAll2_alist_to_ns {μ ν α β : Type} :
    ∀ (R : ident μ ν → α → β → Prop) (l1 : List (ν × α)) (l2 : List (ν × β)),
      LIST_REL (fun (x, y) (x', y') => x = x' ∧ R (Short x) y y') l1 l2 →
      nsAll2 R (alist_to_ns l1) (alist_to_ns l2) := by
  intro R l1 l2 h
  rw [← (nsAppend_nsEmpty (alist_to_ns l1)).1, ← (nsAppend_nsEmpty (alist_to_ns l2)).1,
    nsAppend_to_nsBindList, nsAppend_to_nsBindList]
  exact nsAll2_nsBindList _ _ _ _ _ ⟨h, nsAll2_nsEmpty _⟩

theorem Aux.nsSub_nsLift {μ ν α β : Type}
    (R : ident μ ν → α → β → Prop) (mn : μ) (e1 : Namespace μ ν α) (e2 : Namespace μ ν β) :
      nsSub R (nsLift mn e1) (nsLift mn e2) ↔ nsSub (fun id => R (Long mn id)) e1 e2 := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun id x hx => ?_, fun p hp => ?_⟩
    · obtain ⟨y, hy, hr⟩ := h1 (Long mn id) x (by rw [nsLookup_nsLift]; simpa using hx)
      rw [nsLookup_nsLift] at hy
      exact ⟨y, by simpa using hy, hr⟩
    · have := h2 (mn :: p) (by rw [nsLookupMod_nsLift]; simpa using hp)
      rw [nsLookupMod_nsLift] at this
      simpa using this
  · rintro ⟨h1, h2⟩
    refine ⟨fun id x hx => ?_, fun p hp => ?_⟩
    · rw [nsLookup_nsLift] at hx ⊢
      cases id with
      | Short n => simp at hx
      | Long mn' id =>
        simp only at hx ⊢
        split at hx
        · rename_i he; subst he; simpa using h1 _ _ hx
        · cases hx
    · rw [nsLookupMod_nsLift] at hp ⊢
      cases p with
      | nil => simp at hp
      | cons mn' p =>
        simp only at hp ⊢
        split
        · rename_i he; rw [if_pos he] at hp; exact h2 _ hp
        · rfl

/- HOL4:
Theorem nsAll2_nsLift[simp]:
   !R mn e1 e2. nsAll2 R (nsLift mn e1) (nsLift mn e2) ⇔ nsAll2 (\id. R (Long mn id)) e1 e2 -/
theorem nsAll2_nsLift {μ ν α β : Type} :
    ∀ (R : ident μ ν → α → β → Prop) (mn : μ) (e1 : Namespace μ ν α) (e2 : Namespace μ ν β),
      nsAll2 R (nsLift mn e1) (nsLift mn e2) ↔ nsAll2 (fun id => R (Long mn id)) e1 e2 := by
  intro R mn e1 e2
  unfold nsAll2
  rw [Aux.nsSub_nsLift, Aux.nsSub_nsLift]

end

end CmlTS
