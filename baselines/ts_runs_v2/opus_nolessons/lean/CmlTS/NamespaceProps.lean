import CmlTS.Ast
import CmlTS.Namespace
/-
  Translation of HOL4 theory `namespaceProps` (namespacePropsScript.sml): definitions.
-/
set_option autoImplicit false

namespace CmlTS
open Classical

/- HOL4:
   !id. ?p n. id = mk_id p n -/
theorem mk_id_surj {μ ν : Type} :
    ∀ id : ident μ ν, ∃ p n, id = mk_id p n := by
  sorry

/- HOL4:
   !id. mk_id (id_to_mods id) (id_to_n id) = id -/
theorem mk_id_thm {μ ν : Type} :
    ∀ id : ident μ ν, mk_id (id_to_mods id) (id_to_n id) = id := by
  sorry

/- HOL4:
   (!x y z. R1 x y z ⇒ R2 x y z) ⇒ (nsSub R1 e1 e2 ⇒ nsSub R2 e1 e2) -/
theorem nsSub_mono {μ ν α β : Type} {R1 R2 : ident μ ν → α → β → Prop}
    {e1 : Namespace μ ν α} {e2 : Namespace μ ν β} :
    (∀ x y z, R1 x y z → R2 x y z) → (nsSub R1 e1 e2 → nsSub R2 e1 e2) := by
  sorry

/- HOL4:
   (!x y z. R1 x y z ⇒ R2 x y z) ⇒ nsAll2 R1 e1 e2 ⇒ nsAll2 R2 e1 e2 -/
theorem nsAll2_mono {μ ν α β : Type} {R1 R2 : ident μ ν → α → β → Prop}
    {e1 : Namespace μ ν α} {e2 : Namespace μ ν β} :
    (∀ x y z, R1 x y z → R2 x y z) → nsAll2 R1 e1 e2 → nsAll2 R2 e1 e2 := by
  sorry

/- HOL4:
   !id. nsLookup nsEmpty id = NONE -/
theorem nsLookup_nsEmpty {μ ν α : Type} :
    ∀ id : ident μ ν, nsLookup (nsEmpty : Namespace μ ν α) id = none := by
  sorry

/- HOL4:
   !x y. nsLookupMod nsEmpty (x::y) = NONE -/
theorem nsLookupMod_nsEmpty {μ ν α : Type} :
    ∀ (x : μ) (y : List μ), nsLookupMod (nsEmpty : Namespace μ ν α) (x :: y) = none := by
  sorry

/- HOL4:
   !env. nsAppend env nsEmpty = env ∧ nsAppend nsEmpty env = env -/
theorem nsAppend_nsEmpty {μ ν α : Type} :
    ∀ env : Namespace μ ν α, nsAppend env nsEmpty = env ∧ nsAppend nsEmpty env = env := by
  sorry

/- HOL4:
   alist_to_ns [] = nsEmpty -/
theorem alist_to_ns_nil {μ ν α : Type} : (alist_to_ns [] : Namespace μ ν α) = nsEmpty := by
  sorry

/- HOL4:
   !r env. nsSub r nsEmpty env -/
theorem nsSub_nsEmpty {μ ν α β : Type} :
    ∀ (r : ident μ ν → α → β → Prop) (env : Namespace μ ν β), nsSub r nsEmpty env := by
  sorry

/- HOL4:
   !f. nsAll f nsEmpty -/
theorem nsAll_nsEmpty {μ ν α : Type} :
    ∀ f : ident μ ν → α → Prop, nsAll f nsEmpty := by
  sorry

/- HOL4:
   !f. nsAll2 f nsEmpty nsEmpty -/
theorem nsAll2_nsEmpty {μ ν α β : Type} :
    ∀ f : ident μ ν → α → β → Prop, nsAll2 f nsEmpty nsEmpty := by
  sorry

/- HOL4:
   !k v l. alist_to_ns ((k,v)::l) = nsBind k v (alist_to_ns l) -/
theorem alist_to_ns_cons {μ ν α : Type} :
    ∀ (k : ν) (v : α) (l : List (ν × α)),
      (alist_to_ns ((k, v) :: l) : Namespace μ ν α) = nsBind k v (alist_to_ns l) := by
  sorry

/- HOL4:
   !k v e1 e2. nsAppend (nsBind k v e1) e2 = nsBind k v (nsAppend e1 e2) -/
theorem nsAppend_nsBind {μ ν α : Type} :
    ∀ (k : ν) (v : α) (e1 e2 : Namespace μ ν α),
      nsAppend (nsBind k v e1) e2 = nsBind k v (nsAppend e1 e2) := by
  sorry

/- HOL4:
   !e1 e2 e3. nsAppend e1 (nsAppend e2 e3) = nsAppend (nsAppend e1 e2) e3 -/
theorem nsAppend_assoc {μ ν α : Type} :
    ∀ e1 e2 e3 : Namespace μ ν α,
      nsAppend e1 (nsAppend e2 e3) = nsAppend (nsAppend e1 e2) e3 := by
  sorry

/- HOL4:
   (!n v e. nsLookup (nsBind n v e) (Short n) = SOME v) ∧
   (!n n' v e. n ≠ Short n' ⇒ nsLookup (nsBind n' v e) n = nsLookup e n)
   (the two conjuncts share no variable, so HOL4 gives them different type variables) -/
theorem nsLookup_nsBind {μ ν α μ' ν' α' : Type} :
    (∀ (n : ν) (v : α) (e : Namespace μ ν α), nsLookup (nsBind n v e) (Short n) = some v) ∧
    (∀ (n : ident μ' ν') (n' : ν') (v : α') (e : Namespace μ' ν' α'),
      n ≠ Short n' → nsLookup (nsBind n' v e) n = nsLookup e n) := by
  sorry

/- HOL4:
   !n x e. nsAppend (nsSing n x) e = nsBind n x e -/
theorem nsAppend_nsSing {μ ν α : Type} :
    ∀ (n : ν) (x : α) (e : Namespace μ ν α), nsAppend (nsSing n x) e = nsBind n x e := by
  sorry

/- HOL4:
   !n v id. nsLookup (nsSing n v) id = if id = Short n then SOME v else NONE -/
theorem nsLookup_nsSing {μ ν α : Type} :
    ∀ (n : ν) (v : α) (id : ident μ ν),
      nsLookup (nsSing n v) id = if id = Short n then some v else none := by
  sorry

/- HOL4:
   !R n v. nsAll R (nsSing n v) ⇔ R (Short n) v -/
theorem nsAll_nsSing {μ ν α : Type} :
    ∀ (R : ident μ ν → α → Prop) (n : ν) (v : α), nsAll R (nsSing n v) ↔ R (Short n) v := by
  sorry

/- HOL4:
   !R n1 v1 n2 v2. nsAll2 R (nsSing n1 v1) (nsSing n2 v2) ⇔ n1 = n2 ∧ R (Short n1) v1 v2 -/
theorem nsAll2_nsSing {μ ν α β : Type} :
    ∀ (R : ident μ ν → α → β → Prop) (n1 : ν) (v1 : α) (n2 : ν) (v2 : β),
      nsAll2 R (nsSing n1 v1) (nsSing n2 v2) ↔ n1 = n2 ∧ R (Short n1) v1 v2 := by
  sorry

/- HOL4:
   !x y n x' y' n'. nsBind x y n = nsBind x' y' n' ⇔ x = x' ∧ y = y' ∧ n = n' -/
theorem nsBind_11 {μ ν α : Type} :
    ∀ (x : ν) (y : α) (n : Namespace μ ν α) (x' : ν) (y' : α) (n' : Namespace μ ν α),
      nsBind x y n = nsBind x' y' n' ↔ x = x' ∧ y = y' ∧ n = n' := by
  sorry

/- HOL4:
   !l1 l2. alist_to_ns l1 = alist_to_ns l2 ⇔ l1 = l2 -/
theorem alist_to_ns_11 {μ ν α : Type} :
    ∀ l1 l2 : List (ν × α),
      (alist_to_ns l1 : Namespace μ ν α) = alist_to_ns l2 ↔ l1 = l2 := by
  sorry

/- HOL4:
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
        match id with
        | .Long mn' id' => if mn = mn' then nsLookup e id' else none
        | .Short _ => none := by
  sorry

/- HOL4:
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
        match path with
        | [] => some (nsLift mn e)
        | mn' :: path' => if mn = mn' then nsLookupMod e path' else none := by
  sorry

/- HOL4:
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
      nsLookup e1 id = some v ∨
      (nsLookup e1 id = none ∧ nsLookup e2 id = some v ∧
        ∀ p1 p2, p1 ≠ [] ∧ id_to_mods id = p1 ++ p2 → nsLookupMod e1 p1 = none) := by
  sorry

/- HOL4:
   !l. nsAppend (alist_to_ns l) e = nsBindList l e -/
theorem nsAppend_to_nsBindList {μ ν α : Type} {e : Namespace μ ν α} :
    ∀ l : List (ν × α), nsAppend (alist_to_ns l) e = nsBindList l e := by
  sorry

/- HOL4:
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
  sorry

/- HOL4:
   !e. nsAll (\n x. T) e -/
theorem eALL_T {μ ν α : Type} :
    ∀ e : Namespace μ ν α, nsAll (fun _n _x => True) e := by
  sorry

/- HOL4:
   !env x P v. nsAll P env ∧ nsLookup env x = SOME v ⇒ P x v -/
theorem nsLookup_nsAll {μ ν α : Type} :
    ∀ (env : Namespace μ ν α) (x : ident μ ν) (P : ident μ ν → α → Prop) (v : α),
      nsAll P env ∧ nsLookup env x = some v → P x v := by
  sorry

/- HOL4:
   !f e1 e2. nsAll f e1 ∧ nsAll f e2 ⇒ nsAll f (nsAppend e1 e2) -/
theorem nsAll_nsAppend {μ ν α : Type} :
    ∀ (f : ident μ ν → α → Prop) (e1 e2 : Namespace μ ν α),
      nsAll f e1 ∧ nsAll f e2 → nsAll f (nsAppend e1 e2) := by
  sorry

/- HOL4:
   !R l. EVERY (λ(n,v). R (Short n) v) l ⇒ nsAll R (alist_to_ns l) -/
theorem nsAll_alist_to_ns {μ ν α : Type} :
    ∀ (R : ident μ ν → α → Prop) (l : List (ν × α)),
      EVERY (fun (n, v) => R (Short n) v) l → nsAll R (alist_to_ns l) := by
  sorry

/- HOL4:
   !R mn e. nsAll R (nsLift mn e) ⇔ nsAll (\id. R (Long mn id)) e -/
theorem nsAll_nsLift {μ ν α : Type} :
    ∀ (R : ident μ ν → α → Prop) (mn : μ) (e : Namespace μ ν α),
      nsAll R (nsLift mn e) ↔ nsAll (fun id => R (Long mn id)) e := by
  sorry

/- HOL4:
   !P n1 n2. nsAll P (nsAppend n1 n2) ⇒ nsAll P n1 -/
theorem nsAll_nsAppend_left {μ ν α : Type} :
    ∀ (P : ident μ ν → α → Prop) (n1 n2 : Namespace μ ν α),
      nsAll P (nsAppend n1 n2) → nsAll P n1 := by
  sorry

/- HOL4:
   !P Q e1 e2. nsSub (\id x y. P id x y ∧ Q id x y) e1 e2 ⇔ nsSub P e1 e2 ∧
  nsSub Q e1 e2 -/
theorem nsSub_conj {μ ν α β : Type} :
    ∀ (P Q : ident μ ν → α → β → Prop) (e1 : Namespace μ ν α) (e2 : Namespace μ ν β),
      nsSub (fun id x y => P id x y ∧ Q id x y) e1 e2 ↔ nsSub P e1 e2 ∧ nsSub Q e1 e2 := by
  sorry

/- HOL4:
   !P R. (!n x. P n x ⇒ R n x x) ⇒ !e. nsAll P e ⇒ nsSub R e e -/
theorem nsSub_refl {μ ν α : Type} :
    ∀ (P : ident μ ν → α → Prop) (R : ident μ ν → α → α → Prop),
      (∀ n x, P n x → R n x x) → ∀ e : Namespace μ ν α, nsAll P e → nsSub R e e := by
  sorry

/- HOL4:
   !R x v1 v2 e1 e2.
     R (Short x) v1 v2 ∧ nsSub R e1 e2 ⇒ nsSub R (nsBind x v1 e1) (nsBind x v2 e2) -/
theorem nsSub_nsBind {μ ν α β : Type} :
    ∀ (R : ident μ ν → α → β → Prop) (x : ν) (v1 : α) (v2 : β)
      (e1 : Namespace μ ν α) (e2 : Namespace μ ν β),
      R (Short x) v1 v2 ∧ nsSub R e1 e2 → nsSub R (nsBind x v1 e1) (nsBind x v2 e2) := by
  sorry

/- HOL4:
   !R e1 e2 e2'. nsSub R e1 e1 ∧ nsSub R e2 e2' ⇒ nsSub R (nsAppend e1 e2) (nsAppend e1 e2') -/
theorem nsSub_nsAppend2 {μ ν α : Type} :
    ∀ (R : ident μ ν → α → α → Prop) (e1 e2 e2' : Namespace μ ν α),
      nsSub R e1 e1 ∧ nsSub R e2 e2' → nsSub R (nsAppend e1 e2) (nsAppend e1 e2') := by
  sorry

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
def alist_rel_restr {k v1 v2 : Type} (R : k → v1 → v2 → Prop) (l1 : List (k × v1))
    (l2 : List (k × v2)) : List k → Prop
  | [] => True
  | k1 :: keys =>
    match ALOOKUP l1 k1 with
    | none => False
    | some x1 =>
      match ALOOKUP l2 k1 with
      | none => False
      | some x2 => R k1 x1 x2 ∧ alist_rel_restr R l1 l2 keys

/- HOL4:
   !R e1 e2 keys.
    alist_rel_restr R e1 e2 keys ⇔
      !k. MEM k keys ⇒ ?v1 v2. ALOOKUP e1 k = SOME v1 ∧ ALOOKUP e2 k = SOME v2 ∧ R k v1 v2 -/
theorem alist_rel_restr_thm {κ α β : Type} :
    ∀ (R : κ → α → β → Prop) (e1 : List (κ × α)) (e2 : List (κ × β)) (keys : List κ),
      alist_rel_restr R e1 e2 keys ↔
        ∀ k, k ∈ keys → ∃ v1 v2, ALOOKUP e1 k = some v1 ∧ ALOOKUP e2 k = some v2 ∧ R k v1 v2 := by
  sorry

/- HOL4:
Definition alistSub_def:
  alistSub R e1 e2 ⇔ alist_rel_restr R e1 e2 (MAP FST e1)
End -/
def alistSub {k v1 v2 : Type} (R : k → v1 → v2 → Prop) (e1 : List (k × v1))
    (e2 : List (k × v2)) : Prop :=
  alist_rel_restr R e1 e2 (e1.map Prod.fst)

/- HOL4:
   !l1 l2 l1' l2' R R'.
    l1 = l1' ∧ l2 = l2' ∧ (!n x y. ALOOKUP l1' n = SOME x ∧ ALOOKUP l2' n = SOME y ⇒ R n x y = R' n x y) ⇒
    (alistSub R l1 l2 ⇔ alistSub R' l1' l2') -/
theorem alistSub_cong {κ α β : Type} :
    ∀ (l1 : List (κ × α)) (l2 : List (κ × β)) (l1' : List (κ × α)) (l2' : List (κ × β))
      (R R' : κ → α → β → Prop),
      l1 = l1' ∧ l2 = l2' ∧
        (∀ n x y, ALOOKUP l1' n = some x ∧ ALOOKUP l2' n = some y → (R n x y ↔ R' n x y)) →
      (alistSub R l1 l2 ↔ alistSub R' l1' l2') := by
  sorry

theorem ALOOKUP_mem {k v : Type} {l : List (k × v)} {a : k} {b : v}
    (h : ALOOKUP l a = some b) : (a, b) ∈ l := by
  induction l with
  | nil => simp [ALOOKUP] at h
  | cons p t ih =>
    obtain ⟨x, y⟩ := p
    simp only [ALOOKUP] at h
    split at h
    · simp_all
    · exact List.mem_cons_of_mem _ (ih h)

/- HOL4:
Definition nsSub_compute_def:
  nsSub_compute path R (Bind e1V e1M) (Bind e2V e2M) ⇔
    alistSub (\k v1 v2. R (mk_id (REVERSE path) k) v1 v2) e1V e2V ∧
    alistSub (\k v1 v2. nsSub_compute (k::path) R v1 v2) e1M e2M
End
   HOL4 proves termination with the congruence rule `alistSub_cong`: `alistSub R e1 e2` only uses
   `R k v1 v2` when `ALOOKUP e1 k = SOME v1`.  Here that fact is an explicit (always true)
   conjunct; `nsSub_compute_def` below is the HOL4 equation. -/
def nsSub_compute {m n v1 v2 : Type} (path : List m) (R : ident m n → v1 → v2 → Prop) :
    Namespace m n v1 → Namespace m n v2 → Prop
  | .Bind e1V e1M, .Bind e2V e2M =>
    alistSub (fun k x1 x2 => R (mk_id (List.reverse path) k) x1 x2) e1V e2V ∧
    alistSub (fun k x1 x2 =>
      ∃ _ : ALOOKUP e1M k = some x1, nsSub_compute (k :: path) R x1 x2) e1M e2M
termination_by e1 _ => e1
decreasing_by
  have := sizeOf_snd_lt_of_mem (ALOOKUP_mem (by assumption))
  simp at this ⊢
  omega

theorem alist_rel_restr_congr {k v1 v2 : Type} {R R' : k → v1 → v2 → Prop} {l1 : List (k × v1)}
    {l2 : List (k × v2)} (h : ∀ a x y, ALOOKUP l1 a = some x → (R a x y ↔ R' a x y)) :
    ∀ keys, alist_rel_restr R l1 l2 keys ↔ alist_rel_restr R' l1 l2 keys
  | [] => Iff.rfl
  | k1 :: keys => by
    simp only [alist_rel_restr]
    split
    · exact Iff.rfl
    · rename_i x1 h1
      split
      · exact Iff.rfl
      · rename_i x2 h2
        rw [h k1 x1 x2 h1, alist_rel_restr_congr h keys]

/-- The HOL4 equation `nsSub_compute_def`. -/
theorem nsSub_compute_def {m n v1 v2 : Type} (path : List m) (R : ident m n → v1 → v2 → Prop)
    (e1V : List (n × v1)) (e1M : List (m × Namespace m n v1))
    (e2V : List (n × v2)) (e2M : List (m × Namespace m n v2)) :
    nsSub_compute path R (.Bind e1V e1M) (.Bind e2V e2M) ↔
      alistSub (fun k x1 x2 => R (mk_id (List.reverse path) k) x1 x2) e1V e2V ∧
      alistSub (fun k x1 x2 => nsSub_compute (k :: path) R x1 x2) e1M e2M := by
  rw [nsSub_compute]
  refine and_congr Iff.rfl (alist_rel_restr_congr (fun a x y h => ?_) _)
  simp [h]

/- HOL4:
   !e p k. nsLookup (FOLDR nsLift e p) (mk_id p k) = nsLookup e (Short k) -/
theorem nsLookup_FOLDR_nsLift {μ ν α : Type} :
    ∀ (e : Namespace μ ν α) (p : List μ) (k : ν),
      nsLookup (List.foldr nsLift e p) (mk_id p k) = nsLookup e (Short k) := by
  sorry

/- HOL4:
   !e p id v.
    nsLookup (FOLDR nsLift e p) id = SOME v ⇔
    (p = [] ∧ nsLookup e id = SOME v) ∨
    (p ≠ [] ∧ ?p2 n. id = mk_id (p++p2) n ∧ nsLookup e (mk_id p2 n) = SOME v) -/
theorem nsLookup_FOLDR_nsLift_some {μ ν α : Type} :
    ∀ (e : Namespace μ ν α) (p : List μ) (id : ident μ ν) (v : α),
      nsLookup (List.foldr nsLift e p) id = some v ↔
        (p = [] ∧ nsLookup e id = some v) ∨
        (p ≠ [] ∧ ∃ p2 n, id = mk_id (p ++ p2) n ∧ nsLookup e (mk_id p2 n) = some v) := by
  sorry

/- HOL4:
   !e p1 p2. nsLookupMod (FOLDR nsLift e p1) p2 = NONE ⇔
    (IS_PREFIX p1 p2 ∨ IS_PREFIX p2 p1) ⇒
    ?p3. p2 = p1++p3 ∧ nsLookupMod e p3 = NONE -/
theorem nsLookupMod_FOLDR_nsLift_none {μ ν α : Type} :
    ∀ (e : Namespace μ ν α) (p1 p2 : List μ),
      nsLookupMod (List.foldr nsLift e p1) p2 = none ↔
        ((p2 <+: p1 ∨ p1 <+: p2) →
          ∃ p3, p2 = p1 ++ p3 ∧ nsLookupMod e p3 = none) := by
  sorry

/- HOL4:
   !P Q e1 e2. nsAll2 (\id x y. P id x y ∧ Q id x y) e1 e2 ⇔ nsAll2 P e1 e2 ∧ nsAll2 Q e1 e2 -/
theorem nsAll2_conj {μ ν α β : Type} :
    ∀ (P Q : ident μ ν → α → β → Prop) (e1 : Namespace μ ν α) (e2 : Namespace μ ν β),
      nsAll2 (fun id x y => P id x y ∧ Q id x y) e1 e2 ↔ nsAll2 P e1 e2 ∧ nsAll2 Q e1 e2 := by
  sorry

/- HOL4:
   !R e1 e2 n v2.
    nsLookup e2 n = SOME v2 ∧
    nsAll2 R e1 e2
    ⇒
    ?v1. nsLookup e1 n = SOME v1 ∧ R n v1 v2 -/
theorem nsAll2_nsLookup2 {μ ν α β : Type} :
    ∀ (R : ident μ ν → α → β → Prop) (e1 : Namespace μ ν α) (e2 : Namespace μ ν β)
      (n : ident μ ν) (v2 : β),
      nsLookup e2 n = some v2 ∧
      nsAll2 R e1 e2
      →
      ∃ v1, nsLookup e1 n = some v1 ∧ R n v1 v2 := by
  sorry

/- HOL4:
   !R e1 e2 n.
    nsAll2 R e1 e2
    ⇒
    (nsLookup e1 n = NONE ⇔ nsLookup e2 n = NONE) -/
theorem nsAll2_nsLookup_none {μ ν α β : Type} :
    ∀ (R : ident μ ν → α → β → Prop) (e1 : Namespace μ ν α) (e2 : Namespace μ ν β)
      (n : ident μ ν),
      nsAll2 R e1 e2
      →
      (nsLookup e1 n = none ↔ nsLookup e2 n = none) := by
  sorry

/- HOL4:
   !R x v1 v2 e1 e2.
     R (Short x) v1 v2 ∧ nsAll2 R e1 e2 ⇒ nsAll2 R (nsBind x v1 e1) (nsBind x v2 e2) -/
theorem nsAll2_nsBind {μ ν α β : Type} :
    ∀ (R : ident μ ν → α → β → Prop) (x : ν) (v1 : α) (v2 : β)
      (e1 : Namespace μ ν α) (e2 : Namespace μ ν β),
      R (Short x) v1 v2 ∧ nsAll2 R e1 e2 → nsAll2 R (nsBind x v1 e1) (nsBind x v2 e2) := by
  sorry

/- HOL4:
   !R l1 l2 e1 e2.
     LIST_REL (\(x,y) (x',y'). x = x' ∧ R (Short x) y y') l1 l2 ∧ nsAll2 R e1 e2
     ⇒
     nsAll2 R (nsBindList l1 e1) (nsBindList l2 e2) -/
theorem nsAll2_nsBindList {μ ν α β : Type} :
    ∀ (R : ident μ ν → α → β → Prop) (l1 : List (ν × α)) (l2 : List (ν × β))
      (e1 : Namespace μ ν α) (e2 : Namespace μ ν β),
      LIST_REL (fun (x, y) (x', y') => x = x' ∧ R (Short x) y y') l1 l2 ∧ nsAll2 R e1 e2
      →
      nsAll2 R (nsBindList l1 e1) (nsBindList l2 e2) := by
  sorry

/- HOL4:
   !R e1 e1' e2 e2'.
    nsAll2 R e1 e2 ∧ nsAll2 R e1' e2' ⇒ nsAll2 R (nsAppend e1 e1') (nsAppend e2 e2') -/
theorem nsAll2_nsAppend {μ ν α β : Type} :
    ∀ (R : ident μ ν → α → β → Prop) (e1 e1' : Namespace μ ν α) (e2 e2' : Namespace μ ν β),
      nsAll2 R e1 e2 ∧ nsAll2 R e1' e2' → nsAll2 R (nsAppend e1 e1') (nsAppend e2 e2') := by
  sorry

/- HOL4:
   !R l1 l2. LIST_REL (\(x,y) (x',y'). x = x' ∧ R (Short x) y y') l1 l2 ⇒ nsAll2 R (alist_to_ns l1) (alist_to_ns l2) -/
theorem nsAll2_alist_to_ns {μ ν α β : Type} :
    ∀ (R : ident μ ν → α → β → Prop) (l1 : List (ν × α)) (l2 : List (ν × β)),
      LIST_REL (fun (x, y) (x', y') => x = x' ∧ R (Short x) y y') l1 l2 →
      nsAll2 R (alist_to_ns l1) (alist_to_ns l2) := by
  sorry

/- HOL4:
   !R mn e1 e2. nsAll2 R (nsLift mn e1) (nsLift mn e2) ⇔ nsAll2 (\id. R (Long mn id)) e1 e2 -/
theorem nsAll2_nsLift {μ ν α β : Type} :
    ∀ (R : ident μ ν → α → β → Prop) (mn : μ) (e1 : Namespace μ ν α) (e2 : Namespace μ ν β),
      nsAll2 R (nsLift mn e1) (nsLift mn e2) ↔ nsAll2 (fun id => R (Long mn id)) e1 e2 := by
  sorry

end CmlTS
