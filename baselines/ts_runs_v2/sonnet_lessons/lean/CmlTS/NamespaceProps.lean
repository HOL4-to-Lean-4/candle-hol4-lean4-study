import CmlTS.Ast
import CmlTS.Namespace

/-!
# namespaceProps (HOL4 theory `namespaceProps`): proofs about the namespace datatype
-/

universe u v w

noncomputable section

open Classical

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
def alist_rel_restr {K : Type u} {V1 : Type v} {V2 : Type w} (R : K → V1 → V2 → Prop)
    (l1 : List (K × V1)) (l2 : List (K × V2)) : List K → Prop
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
def alistSub {K : Type u} {V1 : Type v} {V2 : Type w} (R : K → V1 → V2 → Prop)
    (e1 : List (K × V1)) (e2 : List (K × V2)) : Prop :=
  alist_rel_restr R e1 e2 (MAP FST e1)

/-- Auxiliary (not in HOL4): `alist_rel_restr` whose relation also receives the proof that
`ALOOKUP l1 k = SOME v1`; used to make the termination of `nsSub_compute` provable in Lean.
`alist_rel_restr_mem_eq` shows it agrees with `alist_rel_restr`. -/
def alist_rel_restr_mem {K : Type u} {V1 : Type v} {V2 : Type w} (l1 : List (K × V1))
    (l2 : List (K × V2)) (R : (k : K) → (v1 : V1) → ALOOKUP l1 k = some v1 → V2 → Prop) :
    List K → Prop
  | [] => True
  | k1 :: keys =>
    match h : ALOOKUP l1 k1 with
    | none => False
    | some v1 =>
      match ALOOKUP l2 k1 with
      | none => False
      | some v2 => R k1 v1 h v2 ∧ alist_rel_restr_mem l1 l2 R keys

theorem alist_rel_restr_mem_eq {K : Type u} {V1 : Type v} {V2 : Type w} (l1 : List (K × V1))
    (l2 : List (K × V2)) (R : K → V1 → V2 → Prop) (keys : List K) :
    alist_rel_restr_mem l1 l2 (fun k v1 _ v2 => R k v1 v2) keys = alist_rel_restr R l1 l2 keys := by
  induction keys with
  | nil => rfl
  | cons k keys ih =>
    unfold alist_rel_restr_mem alist_rel_restr
    cases h1 : ALOOKUP l1 k <;> cases h2 : ALOOKUP l2 k <;> simp [ih]

theorem sizeOf_ALOOKUP {M : Type u} {N : Type v} {V : Type w} [SizeOf M] [SizeOf N] [SizeOf V]
    (l : List (M × Namespace M N V)) (k : M) (v : Namespace M N V)
    (h : ALOOKUP l k = some v) : sizeOf v < sizeOf l := by
  induction l with
  | nil => simp [ALOOKUP] at h
  | cons p t ih =>
    obtain ⟨x, y⟩ := p
    simp only [ALOOKUP] at h
    by_cases hx : x = k
    · simp only [hx, if_true] at h
      cases h
      simp
      omega
    · simp only [hx, if_false] at h
      have := ih h
      simp
      omega

/- HOL4:
   Definition nsSub_compute_def:
     nsSub_compute path R (Bind e1V e1M) (Bind e2V e2M) ⇔
       alistSub (\k v1 v2. R (mk_id (REVERSE path) k) v1 v2) e1V e2V ∧
       alistSub (\k v1 v2. nsSub_compute (k::path) R v1 v2) e1M e2M
   Termination
     wf_rel_tac `measure (\(p,r,env,_). namespace_size (\x.0) (\x.0) (\x.0) env)`
     ...
   End
   (Lean: the second `alistSub` is `alist_rel_restr_mem` on `MAP FST e1M`, equal to
   `alistSub` by `alist_rel_restr_mem_eq`; this makes termination provable.) -/
def nsSub_compute {M : Type u} {N : Type v} {V : Type w} :
    List M → (Ident M N → V → V → Prop) → Namespace M N V → Namespace M N V → Prop
  | path, R, .Bind e1V e1M, .Bind e2V e2M =>
    alistSub (fun k v1 v2 => R (mk_id (REVERSE path) k) v1 v2) e1V e2V ∧
    alist_rel_restr_mem e1M e2M (fun k v1 _ v2 => nsSub_compute (k :: path) R v1 v2)
      (MAP FST e1M)
termination_by _ _ e1 _ => sizeOf e1
decreasing_by
  rename_i h
  have := sizeOf_ALOOKUP e1M _ _ h
  simp
  omega

/-! ## Theorems (stage 2) -/

section Thms

variable {M : Type u} {N : Type v} {V : Type w} {V' : Type _}

/- HOL4: Theorem mk_id_surj:
     !id. ?p n. id = mk_id p n -/
theorem mk_id_surj : ∀ i : Ident M N, ∃ (p : List M) (n : N), i = mk_id p n := by
  sorry

/- HOL4: Theorem mk_id_thm:
     !id. mk_id (id_to_mods id) (id_to_n id) = id -/
theorem mk_id_thm : ∀ i : Ident M N, mk_id (id_to_mods i) (id_to_n i) = i := by
  sorry

/- HOL4: Theorem nsSub_mono[mono]:
     (!x y z. R1 x y z ⇒ R2 x y z) ⇒ (nsSub R1 e1 e2 ⇒ nsSub R2 e1 e2) -/
theorem nsSub_mono (R1 R2 : Ident M N → V → V' → Prop)
    (e1 : Namespace M N V) (e2 : Namespace M N V') :
    (∀ x y z, R1 x y z → R2 x y z) → (nsSub R1 e1 e2 → nsSub R2 e1 e2) := by
  sorry

/- HOL4: Theorem nsAll2_mono[mono]:
     (!x y z. R1 x y z ⇒ R2 x y z) ⇒ nsAll2 R1 e1 e2 ⇒ nsAll2 R2 e1 e2 -/
theorem nsAll2_mono (R1 R2 : Ident M N → V → V' → Prop)
    (e1 : Namespace M N V) (e2 : Namespace M N V') :
    (∀ x y z, R1 x y z → R2 x y z) → nsAll2 R1 e1 e2 → nsAll2 R2 e1 e2 := by
  sorry

/- HOL4: Theorem nsLookup_nsEmpty[simp]:
     !id. nsLookup nsEmpty id = NONE -/
theorem nsLookup_nsEmpty : ∀ i : Ident M N, nsLookup (nsEmpty : Namespace M N V) i = none := by
  sorry

/- HOL4: Theorem nsLookupMod_nsEmpty[simp]:
     !x y. nsLookupMod nsEmpty (x::y) = NONE -/
theorem nsLookupMod_nsEmpty :
    ∀ (x : M) (y : List M), nsLookupMod (nsEmpty : Namespace M N V) (x :: y) = none := by
  sorry

/- HOL4: Theorem nsAppend_nsEmpty[simp]:
     !env. nsAppend env nsEmpty = env ∧ nsAppend nsEmpty env = env -/
theorem nsAppend_nsEmpty :
    ∀ env : Namespace M N V, nsAppend env nsEmpty = env ∧ nsAppend nsEmpty env = env := by
  sorry

/- HOL4: Theorem alist_to_ns_nil[simp]:
     alist_to_ns [] = nsEmpty -/
theorem alist_to_ns_nil : (alist_to_ns [] : Namespace M N V) = nsEmpty := by
  sorry

/- HOL4: Theorem nsSub_nsEmpty[simp]:
     !r env. nsSub r nsEmpty env -/
theorem nsSub_nsEmpty :
    ∀ (r : Ident M N → V → V' → Prop) (env : Namespace M N V'), nsSub r nsEmpty env := by
  sorry

/- HOL4: Theorem nsAll_nsEmpty[simp]:
     !f. nsAll f nsEmpty -/
theorem nsAll_nsEmpty : ∀ f : Ident M N → V → Prop, nsAll f nsEmpty := by
  sorry

/- HOL4: Theorem nsAll2_nsEmpty[simp]:
     !f. nsAll2 f nsEmpty nsEmpty -/
theorem nsAll2_nsEmpty : ∀ f : Ident M N → V → V' → Prop, nsAll2 f nsEmpty nsEmpty := by
  sorry

/- HOL4: Theorem alist_to_ns_cons[simp]:
     !k v l. alist_to_ns ((k,v)::l) = nsBind k v (alist_to_ns l) -/
theorem alist_to_ns_cons :
    ∀ (k : N) (v : V) (l : List (N × V)),
      (alist_to_ns ((k, v) :: l) : Namespace M N V) = nsBind k v (alist_to_ns l) := by
  sorry

/- HOL4: Theorem nsAppend_nsBind[simp]:
     !k v e1 e2. nsAppend (nsBind k v e1) e2 = nsBind k v (nsAppend e1 e2) -/
theorem nsAppend_nsBind :
    ∀ (k : N) (v : V) (e1 e2 : Namespace M N V),
      nsAppend (nsBind k v e1) e2 = nsBind k v (nsAppend e1 e2) := by
  sorry

/- HOL4: Theorem nsAppend_assoc[simp]:
     !e1 e2 e3. nsAppend e1 (nsAppend e2 e3) = nsAppend (nsAppend e1 e2) e3 -/
theorem nsAppend_assoc :
    ∀ e1 e2 e3 : Namespace M N V, nsAppend e1 (nsAppend e2 e3) = nsAppend (nsAppend e1 e2) e3 := by
  sorry

/- HOL4: Theorem nsLookup_nsBind[simp]:
     (!n v e. nsLookup (nsBind n v e) (Short n) = SOME v) ∧
     (!n n' v e. n ≠ Short n' ⇒ nsLookup (nsBind n' v e) n = nsLookup e n) -/
theorem nsLookup_nsBind :
    (∀ (n : N) (v : V) (e : Namespace M N V),
      nsLookup (nsBind n v e) (Ident.Short n) = some v) ∧
    (∀ (n : Ident M N) (n' : N) (v : V) (e : Namespace M N V),
      n ≠ Ident.Short n' → nsLookup (nsBind n' v e) n = nsLookup e n) := by
  sorry

/- HOL4: Theorem nsAppend_nsSing[simp]:
     !n x e. nsAppend (nsSing n x) e = nsBind n x e -/
theorem nsAppend_nsSing :
    ∀ (n : N) (x : V) (e : Namespace M N V), nsAppend (nsSing n x) e = nsBind n x e := by
  sorry

/- HOL4: Theorem nsLookup_nsSing[simp]:
     !n v id. nsLookup (nsSing n v) id = if id = Short n then SOME v else NONE -/
theorem nsLookup_nsSing :
    ∀ (n : N) (v : V) (i : Ident M N),
      nsLookup (nsSing n v) i = if i = Ident.Short n then some v else none := by
  sorry

/- HOL4: Theorem nsAll_nsSing[simp]:
     !R n v. nsAll R (nsSing n v) ⇔ R (Short n) v -/
theorem nsAll_nsSing :
    ∀ (R : Ident M N → V → Prop) (n : N) (v : V), nsAll R (nsSing n v) ↔ R (Ident.Short n) v := by
  sorry

/- HOL4: Theorem nsAll2_nsSing[simp]:
     !R n1 v1 n2 v2. nsAll2 R (nsSing n1 v1) (nsSing n2 v2) ⇔ n1 = n2 ∧ R (Short n1) v1 v2 -/
theorem nsAll2_nsSing :
    ∀ (R : Ident M N → V → V' → Prop) (n1 : N) (v1 : V) (n2 : N) (v2 : V'),
      nsAll2 R (nsSing n1 v1) (nsSing n2 v2) ↔ n1 = n2 ∧ R (Ident.Short n1) v1 v2 := by
  sorry

/- HOL4: Theorem nsBind_11[simp]:
     !x y n x' y' n'. nsBind x y n = nsBind x' y' n' ⇔ x = x' ∧ y = y' ∧ n = n' -/
theorem nsBind_11 :
    ∀ (x : N) (y : V) (n : Namespace M N V) (x' : N) (y' : V) (n' : Namespace M N V),
      nsBind x y n = nsBind x' y' n' ↔ x = x' ∧ y = y' ∧ n = n' := by
  sorry

/- HOL4: Theorem alist_to_ns_11[simp]:
     !l1 l2. alist_to_ns l1 = alist_to_ns l2 ⇔ l1 = l2 -/
theorem alist_to_ns_11 :
    ∀ l1 l2 : List (N × V),
      (alist_to_ns l1 : Namespace M N V) = alist_to_ns l2 ↔ l1 = l2 := by
  sorry

/- HOL4: Theorem nsLookup_nsLift:
     !mn e id.
      nsLookup (nsLift mn e) id =
      case id of
      | Long mn' id' =>
        if mn = mn' then
          nsLookup e id'
        else
          NONE
      | Short _ => NONE -/
theorem nsLookup_nsLift :
    ∀ (mn : M) (e : Namespace M N V) (i : Ident M N),
      nsLookup (nsLift mn e) i =
        match i with
        | Ident.Long mn' id' =>
          if mn = mn' then nsLookup e id' else none
        | Ident.Short _ => none := by
  sorry

/- HOL4: Theorem nsLookupMod_nsLift:
     !mn e path.
      nsLookupMod (nsLift mn e) path =
      case path of
      | [] => SOME (nsLift mn e)
      | (mn'::path') =>
        if mn = mn' then
          nsLookupMod e path'
        else
          NONE -/
theorem nsLookupMod_nsLift :
    ∀ (mn : M) (e : Namespace M N V) (path : List M),
      nsLookupMod (nsLift mn e) path =
        match path with
        | [] => some (nsLift mn e)
        | mn' :: path' =>
          if mn = mn' then nsLookupMod e path' else none := by
  sorry

/- HOL4: Theorem nsLookup_nsAppend_some:
     ∀e1 id e2 v.
      nsLookup (nsAppend e1 e2) id = SOME v
      ⇔
      nsLookup e1 id = SOME v ∨
      (nsLookup e1 id = NONE ∧ nsLookup e2 id = SOME v ∧
       !p1 p2. p1 ≠ [] ∧ id_to_mods id = p1++p2 ⇒ nsLookupMod e1 p1 = NONE) -/
theorem nsLookup_nsAppend_some :
    ∀ (e1 : Namespace M N V) (i : Ident M N) (e2 : Namespace M N V) (v : V),
      nsLookup (nsAppend e1 e2) i = some v
      ↔
      nsLookup e1 i = some v ∨
      (nsLookup e1 i = none ∧ nsLookup e2 i = some v ∧
       ∀ (p1 p2 : List M), p1 ≠ [] ∧ id_to_mods i = p1 ++ p2 → nsLookupMod e1 p1 = none) := by
  sorry

/- HOL4: Theorem nsAppend_to_nsBindList:
     !l. nsAppend (alist_to_ns l) e = nsBindList l e -/
theorem nsAppend_to_nsBindList (e : Namespace M N V) :
    ∀ l : List (N × V), nsAppend (alist_to_ns l) e = nsBindList l e := by
  sorry

/- HOL4: Theorem nsLookupMod_nsAppend_none:
     !e1 e2 path.
      nsLookupMod (nsAppend e1 e2) path = NONE
      ⇔
      (nsLookupMod e1 path = NONE ∧
       (nsLookupMod e2 path = NONE ∨
        ?p1 p2 e3. p1 ≠ [] ∧ path = p1++p2 ∧ nsLookupMod e1 p1 = SOME e3)) -/
theorem nsLookupMod_nsAppend_none :
    ∀ (e1 e2 : Namespace M N V) (path : List M),
      nsLookupMod (nsAppend e1 e2) path = none
      ↔
      (nsLookupMod e1 path = none ∧
       (nsLookupMod e2 path = none ∨
        ∃ (p1 p2 : List M) (e3 : Namespace M N V),
          p1 ≠ [] ∧ path = p1 ++ p2 ∧ nsLookupMod e1 p1 = some e3)) := by
  sorry

/- HOL4: Theorem eALL_T[simp]:
     !e. nsAll (\n x. T) e -/
theorem eALL_T : ∀ e : Namespace M N V, nsAll (fun _ _ => True) e := by
  sorry

/- HOL4: Theorem nsLookup_nsAll:
     !env x P v. nsAll P env ∧ nsLookup env x = SOME v ⇒ P x v -/
theorem nsLookup_nsAll :
    ∀ (env : Namespace M N V) (x : Ident M N) (P : Ident M N → V → Prop) (v : V),
      nsAll P env ∧ nsLookup env x = some v → P x v := by
  sorry

/- HOL4: Theorem nsAll_nsAppend:
     !f e1 e2. nsAll f e1 ∧ nsAll f e2 ⇒ nsAll f (nsAppend e1 e2) -/
theorem nsAll_nsAppend :
    ∀ (f : Ident M N → V → Prop) (e1 e2 : Namespace M N V),
      nsAll f e1 ∧ nsAll f e2 → nsAll f (nsAppend e1 e2) := by
  sorry

/- HOL4: Theorem nsAll_alist_to_ns:
     !R l. EVERY (λ(n,v). R (Short n) v) l ⇒ nsAll R (alist_to_ns l) -/
theorem nsAll_alist_to_ns :
    ∀ (R : Ident M N → V → Prop) (l : List (N × V)),
      EVERY (fun p : N × V => R (Ident.Short p.1) p.2) l → nsAll R (alist_to_ns l) := by
  sorry

/- HOL4: Theorem nsAll_nsLift[simp]:
     !R mn e. nsAll R (nsLift mn e) ⇔ nsAll (\id. R (Long mn id)) e -/
theorem nsAll_nsLift :
    ∀ (R : Ident M N → V → Prop) (mn : M) (e : Namespace M N V),
      nsAll R (nsLift mn e) ↔ nsAll (fun i => R (Ident.Long mn i)) e := by
  sorry

/- HOL4: Theorem nsAll_nsAppend_left:
     !P n1 n2. nsAll P (nsAppend n1 n2) ⇒ nsAll P n1 -/
theorem nsAll_nsAppend_left :
    ∀ (P : Ident M N → V → Prop) (n1 n2 : Namespace M N V),
      nsAll P (nsAppend n1 n2) → nsAll P n1 := by
  sorry

/- HOL4: Theorem nsSub_conj:
     !P Q e1 e2. nsSub (\id x y. P id x y ∧ Q id x y) e1 e2 ⇔ nsSub P e1 e2 ∧
    nsSub Q e1 e2 -/
theorem nsSub_conj :
    ∀ (P Q : Ident M N → V → V' → Prop) (e1 : Namespace M N V) (e2 : Namespace M N V'),
      nsSub (fun i x y => P i x y ∧ Q i x y) e1 e2 ↔ nsSub P e1 e2 ∧ nsSub Q e1 e2 := by
  sorry

/- HOL4: Theorem nsSub_refl:
     !P R. (!n x. P n x ⇒ R n x x) ⇒ !e. nsAll P e ⇒ nsSub R e e -/
theorem nsSub_refl :
    ∀ (P : Ident M N → V → Prop) (R : Ident M N → V → V → Prop),
      (∀ n x, P n x → R n x x) → ∀ e : Namespace M N V, nsAll P e → nsSub R e e := by
  sorry

/- HOL4: Theorem nsSub_nsBind:
     !R x v1 v2 e1 e2.
       R (Short x) v1 v2 ∧ nsSub R e1 e2 ⇒ nsSub R (nsBind x v1 e1) (nsBind x v2 e2) -/
theorem nsSub_nsBind :
    ∀ (R : Ident M N → V → V' → Prop) (x : N) (v1 : V) (v2 : V')
      (e1 : Namespace M N V) (e2 : Namespace M N V'),
      R (Ident.Short x) v1 v2 ∧ nsSub R e1 e2 → nsSub R (nsBind x v1 e1) (nsBind x v2 e2) := by
  sorry

/- HOL4: Theorem nsSub_nsAppend2:
     !R e1 e2 e2'. nsSub R e1 e1 ∧ nsSub R e2 e2' ⇒ nsSub R (nsAppend e1 e2) (nsAppend e1 e2') -/
theorem nsSub_nsAppend2 :
    ∀ (R : Ident M N → V → V → Prop) (e1 e2 e2' : Namespace M N V),
      nsSub R e1 e1 ∧ nsSub R e2 e2' → nsSub R (nsAppend e1 e2) (nsAppend e1 e2') := by
  sorry

/- HOL4: Theorem alist_rel_restr_thm:
     !R e1 e2 keys.
      alist_rel_restr R e1 e2 keys ⇔
        !k. MEM k keys ⇒ ?v1 v2. ALOOKUP e1 k = SOME v1 ∧ ALOOKUP e2 k = SOME v2 ∧ R k v1 v2 -/
theorem alist_rel_restr_thm :
    ∀ (R : N → V → V' → Prop) (e1 : List (N × V)) (e2 : List (N × V')) (keys : List N),
      alist_rel_restr R e1 e2 keys ↔
        ∀ k, MEM k keys → ∃ (v1 : V) (v2 : V'),
          ALOOKUP e1 k = some v1 ∧ ALOOKUP e2 k = some v2 ∧ R k v1 v2 := by
  sorry

/- HOL4: Theorem alistSub_cong:
     !l1 l2 l1' l2' R R'.
      l1 = l1' ∧ l2 = l2' ∧ (!n x y. ALOOKUP l1' n = SOME x ∧ ALOOKUP l2' n = SOME y ⇒ R n x y = R' n x y) ⇒
      (alistSub R l1 l2 ⇔ alistSub R' l1' l2') -/
theorem alistSub_cong :
    ∀ (l1 l1' : List (N × V)) (l2 l2' : List (N × V')) (R R' : N → V → V' → Prop),
      l1 = l1' ∧ l2 = l2' ∧
        (∀ n x y, ALOOKUP l1' n = some x ∧ ALOOKUP l2' n = some y → (R n x y = R' n x y)) →
      (alistSub R l1 l2 ↔ alistSub R' l1' l2') := by
  sorry

/- HOL4: Theorem nsLookup_FOLDR_nsLift:
     !e p k. nsLookup (FOLDR nsLift e p) (mk_id p k) = nsLookup e (Short k) -/
theorem nsLookup_FOLDR_nsLift :
    ∀ (e : Namespace M N V) (p : List M) (k : N),
      nsLookup (FOLDR nsLift e p) (mk_id p k) = nsLookup e (Ident.Short k) := by
  sorry

/- HOL4: Theorem nsLookup_FOLDR_nsLift_some:
     !e p id v.
      nsLookup (FOLDR nsLift e p) id = SOME v ⇔
      (p = [] ∧ nsLookup e id = SOME v) ∨
      (p ≠ [] ∧ ?p2 n. id = mk_id (p++p2) n ∧ nsLookup e (mk_id p2 n) = SOME v) -/
theorem nsLookup_FOLDR_nsLift_some :
    ∀ (e : Namespace M N V) (p : List M) (i : Ident M N) (v : V),
      nsLookup (FOLDR nsLift e p) i = some v ↔
      (p = [] ∧ nsLookup e i = some v) ∨
      (p ≠ [] ∧ ∃ (p2 : List M) (n : N), i = mk_id (p ++ p2) n ∧
        nsLookup e (mk_id p2 n) = some v) := by
  sorry

/- HOL4: Theorem nsLookupMod_FOLDR_nsLift_none:
     !e p1 p2. nsLookupMod (FOLDR nsLift e p1) p2 = NONE ⇔
      (IS_PREFIX p1 p2 ∨ IS_PREFIX p2 p1) ⇒
      ?p3. p2 = p1++p3 ∧ nsLookupMod e p3 = NONE -/
theorem nsLookupMod_FOLDR_nsLift_none :
    ∀ (e : Namespace M N V) (p1 p2 : List M),
      nsLookupMod (FOLDR nsLift e p1) p2 = none ↔
      ((IS_PREFIX p1 p2 ∨ IS_PREFIX p2 p1) →
        ∃ p3 : List M, p2 = p1 ++ p3 ∧ nsLookupMod e p3 = none) := by
  sorry

/- HOL4: Theorem nsAll2_conj:
     !P Q e1 e2. nsAll2 (\id x y. P id x y ∧ Q id x y) e1 e2 ⇔ nsAll2 P e1 e2 ∧ nsAll2 Q e1 e2 -/
theorem nsAll2_conj :
    ∀ (P Q : Ident M N → V → V' → Prop) (e1 : Namespace M N V) (e2 : Namespace M N V'),
      nsAll2 (fun i x y => P i x y ∧ Q i x y) e1 e2 ↔ nsAll2 P e1 e2 ∧ nsAll2 Q e1 e2 := by
  sorry

/- HOL4: Theorem nsAll2_nsLookup2:
     !R e1 e2 n v2.
      nsLookup e2 n = SOME v2 ∧
      nsAll2 R e1 e2
      ⇒
      ?v1. nsLookup e1 n = SOME v1 ∧ R n v1 v2 -/
theorem nsAll2_nsLookup2 :
    ∀ (R : Ident M N → V → V' → Prop) (e1 : Namespace M N V) (e2 : Namespace M N V')
      (n : Ident M N) (v2 : V'),
      nsLookup e2 n = some v2 ∧ nsAll2 R e1 e2 →
      ∃ v1 : V, nsLookup e1 n = some v1 ∧ R n v1 v2 := by
  sorry

/- HOL4: Theorem nsAll2_nsLookup_none:
     !R e1 e2 n.
      nsAll2 R e1 e2
      ⇒
      (nsLookup e1 n = NONE ⇔ nsLookup e2 n = NONE) -/
theorem nsAll2_nsLookup_none :
    ∀ (R : Ident M N → V → V' → Prop) (e1 : Namespace M N V) (e2 : Namespace M N V')
      (n : Ident M N),
      nsAll2 R e1 e2 → (nsLookup e1 n = none ↔ nsLookup e2 n = none) := by
  sorry

/- HOL4: Theorem nsAll2_nsBind:
     !R x v1 v2 e1 e2.
       R (Short x) v1 v2 ∧ nsAll2 R e1 e2 ⇒ nsAll2 R (nsBind x v1 e1) (nsBind x v2 e2) -/
theorem nsAll2_nsBind :
    ∀ (R : Ident M N → V → V' → Prop) (x : N) (v1 : V) (v2 : V')
      (e1 : Namespace M N V) (e2 : Namespace M N V'),
      R (Ident.Short x) v1 v2 ∧ nsAll2 R e1 e2 →
      nsAll2 R (nsBind x v1 e1) (nsBind x v2 e2) := by
  sorry

/- HOL4: Theorem nsAll2_nsBindList:
     !R l1 l2 e1 e2.
       LIST_REL (\(x,y) (x',y'). x = x' ∧ R (Short x) y y') l1 l2 ∧ nsAll2 R e1 e2
       ⇒
       nsAll2 R (nsBindList l1 e1) (nsBindList l2 e2) -/
theorem nsAll2_nsBindList :
    ∀ (R : Ident M N → V → V' → Prop) (l1 : List (N × V)) (l2 : List (N × V'))
      (e1 : Namespace M N V) (e2 : Namespace M N V'),
      LIST_REL (fun (p : N × V) (q : N × V') => p.1 = q.1 ∧ R (Ident.Short p.1) p.2 q.2) l1 l2 ∧
        nsAll2 R e1 e2 →
      nsAll2 R (nsBindList l1 e1) (nsBindList l2 e2) := by
  sorry

/- HOL4: Theorem nsAll2_nsAppend:
     !R e1 e1' e2 e2'.
      nsAll2 R e1 e2 ∧ nsAll2 R e1' e2' ⇒ nsAll2 R (nsAppend e1 e1') (nsAppend e2 e2') -/
theorem nsAll2_nsAppend :
    ∀ (R : Ident M N → V → V' → Prop) (e1 e1' : Namespace M N V) (e2 e2' : Namespace M N V'),
      nsAll2 R e1 e2 ∧ nsAll2 R e1' e2' → nsAll2 R (nsAppend e1 e1') (nsAppend e2 e2') := by
  sorry

/- HOL4: Theorem nsAll2_alist_to_ns:
     !R l1 l2. LIST_REL (\(x,y) (x',y'). x = x' ∧ R (Short x) y y') l1 l2 ⇒ nsAll2 R (alist_to_ns l1) (alist_to_ns l2) -/
theorem nsAll2_alist_to_ns :
    ∀ (R : Ident M N → V → V' → Prop) (l1 : List (N × V)) (l2 : List (N × V')),
      LIST_REL (fun (p : N × V) (q : N × V') => p.1 = q.1 ∧ R (Ident.Short p.1) p.2 q.2) l1 l2 →
      nsAll2 R (alist_to_ns l1) (alist_to_ns l2) := by
  sorry

/- HOL4: Theorem nsAll2_nsLift[simp]:
     !R mn e1 e2. nsAll2 R (nsLift mn e1) (nsLift mn e2) ⇔ nsAll2 (\id. R (Long mn id)) e1 e2 -/
theorem nsAll2_nsLift :
    ∀ (R : Ident M N → V → V' → Prop) (mn : M) (e1 : Namespace M N V) (e2 : Namespace M N V'),
      nsAll2 R (nsLift mn e1) (nsLift mn e2) ↔ nsAll2 (fun i => R (Ident.Long mn i)) e1 e2 := by
  sorry

end Thms

end
