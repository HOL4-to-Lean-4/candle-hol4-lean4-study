import CmlTS.Prelude.Core
import CmlTS.Prelude.PredSet
import CmlTS.Prelude.ListLib
import CmlTS.Prelude.FiniteMap
import CmlTS.Prelude.LList
import CmlTS.Prelude.Sptree
import CmlTS.Prelude.StringLib
import CmlTS.Prelude.Words
import CmlTS.Prelude.BinaryIeee
import CmlTS.LprefixLub
import CmlTS.Proofs.Lib

/-
HOL4 theory `misc` (miscScript.sml).
-/

namespace CmlTS

noncomputable section

open scoped Classical

variable {α β γ δ : Type}

/- HOL4:
Definition the_def:
  the _ (SOME x) = x ∧
  the x NONE =  x
End -/
def the : α → Option α → α
  | _, some x => x
  | x, none => x

/- HOL4:
Datatype:
  app_list = List ('a list) | Append app_list app_list | Nil
End -/
inductive app_list (α : Type)
  | List (l : _root_.List α)
  | Append (l1 l2 : app_list α)
  | Nil

/- HOL4:
Definition append_aux_def:
  (append_aux Nil aux = aux) /\
  (append_aux (List xs) aux = xs ++ aux) /\
  (append_aux (Append l1 l2) aux = append_aux l1 (append_aux l2 aux))
End -/
def append_aux : app_list α → List α → List α
  | app_list.Nil, aux => aux
  | app_list.List xs, aux => xs ++ aux
  | app_list.Append l1 l2, aux => append_aux l1 (append_aux l2 aux)

/- HOL4:
Definition append_def:
  append l = append_aux l []
End -/
def append (l : app_list α) : List α := append_aux l []

/- HOL4:
Definition MAP3_def[simp]:
  (MAP3 f [] [] [] = []) /\
  (MAP3 f (h1::t1) (h2::t2) (h3::t3) = f h1 h2 h3::MAP3 f t1 t2 t3)
End
(unspecified on lists of different lengths) -/
def MAP3 (f : α → β → γ → δ) : List α → List β → List γ → List δ
  | [], [], [] => []
  | h1 :: t1, h2 :: t2, h3 :: t3 => f h1 h2 h3 :: MAP3 f t1 t2 t3
  | _, _, _ => ARB

/- HOL4:
Definition tlookup_def:
  tlookup m k = case lookup k m of NONE => k | SOME k => k
End -/
def tlookup (m : spt Nat) (k : Nat) : Nat :=
  match lookup k m with
  | none => k
  | some k => k

/- HOL4:
Definition max3_def[simp]:
  max3 (x:num) y z = if x > y then (if z > x then z else x)
                     else (if z > y then z else y)
End -/
def max3 (x y z : Nat) : Nat :=
  if x > y then (if z > x then z else x) else (if z > y then z else y)

/- HOL4: Type num_set = ``:unit spt`` -/
abbrev num_set : Type := spt Unit

/- HOL4: Type num_map = ``:'a spt`` -/
abbrev num_map (α : Type) : Type := spt α

/- HOL4:
Definition UPDATE_LIST_def:
  UPDATE_LIST = FOLDL (combin$C (UNCURRY UPDATE))
End
(Overload "=++" = ``UPDATE_LIST``) -/
def UPDATE_LIST : (α → β) → List (α × β) → (α → β) := List.foldl (C (UNCURRY UPDATE))

/- HOL4:
Definition find_index_def:
  (find_index _ [] _ = NONE) ∧
  (find_index y (x::xs) n = if x = y then SOME n else find_index y xs (n+1))
End -/
def find_index : α → List α → Nat → Option Nat
  | _, [], _ => none
  | y, x :: xs, n => if x = y then some n else find_index y xs (n + 1)

/- HOL4:
Definition between_def:
  between x y z ⇔ x:num ≤ z ∧ z < y
End -/
def between (x y z : Nat) : Prop := x ≤ z ∧ z < y

/- HOL4:
Definition lookup_vars_def:
  (lookup_vars [] env = SOME []) /\
  (lookup_vars (v::vs) env =
     if v < LENGTH env then
       case lookup_vars vs env of
       | SOME xs => SOME (EL v env :: xs)
       | NONE => NONE
     else NONE)
End -/
def lookup_vars [Nonempty α] : List Nat → List α → Option (List α)
  | [], _ => some []
  | v :: vs, env =>
    if v < env.length then
      match lookup_vars vs env with
      | some xs => some (EL v env :: xs)
      | none => none
    else none

/- HOL4:
Definition enumerate_def:
  (enumerate n [] = []) ∧
  (enumerate n (x::xs) = (n,x)::enumerate (n+1n) xs)
End -/
def enumerate : Nat → List α → List (Nat × α)
  | _, [] => []
  | n, x :: xs => (n, x) :: enumerate (n + 1) xs

/- HOL4:
Definition range_def:
  range s = {v | ∃n. lookup n s = SOME v}
End -/
def range (s : spt α) : Set α := setOf fun v => ∃ n, lookup n s = some v

/-! ### Theorems -/

/- HOL4:
Theorem CARD_IMAGE_ID_BIJ:
   ∀s. FINITE s ⇒ (∀x. x ∈ s ⇒ f x ∈ s) ∧ CARD (IMAGE f s) = CARD s ⇒ BIJ f s s -/
theorem CARD_IMAGE_ID_BIJ {f : α → α} :
    ∀ s : Set α, FINITE s →
      (∀ x, x ∈ s → f x ∈ s) ∧ CARD (IMAGE f s) = CARD s → BIJ f s s := by
  rintro s hs ⟨hf, hc⟩
  obtain ⟨l, hl, hm⟩ := Aux.finite_list hs
  obtain ⟨l', h1, h2, h3, h4⟩ := Aux.exists_dedup (l.map f)
  have hI : CARD (IMAGE f s) = l'.length := by
    refine Aux.CARD_eq h1 fun x => ?_
    rw [h2, List.mem_map, Aux.mem_IMAGE]
    constructor
    · rintro ⟨a, ha, e⟩; exact ⟨a, e.symm, (hm a).1 ha⟩
    · rintro ⟨a, e, ha⟩; exact ⟨a, (hm a).2 ha, e.symm⟩
  rw [hI, Aux.CARD_eq hl hm] at hc
  have hn : (l.map f).Nodup := h4 (by simpa using hc)
  have hinj := Aux.inj_of_nodup_map hn
  have hsub : l.map f ⊆ l := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hx
    exact (hm _).2 (hf a ((hm a).1 ha))
  have hperm := (List.subperm_of_subset hn hsub).perm_of_length_le (by simp)
  refine ⟨⟨hf, fun x y hxy e => hinj x y ((hm x).2 hxy.1) ((hm y).2 hxy.2) e⟩, hf, fun x hx => ?_⟩
  have : x ∈ l.map f := hperm.mem_iff.2 ((hm x).2 hx)
  obtain ⟨a, ha, e⟩ := List.mem_map.1 this
  exact ⟨a, (hm a).1 ha, e⟩

/- HOL4:
Theorem tlookup_bij_suff:
   set (toList names) = domain names ⇒
   BIJ (tlookup names) UNIV UNIV -/
theorem tlookup_bij_suff {names : spt Nat} :
    LIST_TO_SET (spt_toList names) = domain names →
    BIJ (tlookup names) UNIV UNIV := by
  intro h
  have hval : ∀ k v, lookup k names = some v → tlookup names k = v := by
    intro k v hk; simp [tlookup, hk]
  have hout : ∀ k, ¬ k ∈ domain names → tlookup names k = k := by
    intro k hk
    cases hl : lookup k names with
    | none => simp [tlookup, hl]
    | some v => exact absurd (Aux.mem_domain.2 ⟨v, hl⟩) hk
  have himg : IMAGE (tlookup names) (domain names) = domain names := by
    rw [← h]
    refine Aux.set_ext fun x => ?_
    rw [Aux.mem_IMAGE, Aux.mem_LIST_TO_SET, Aux.mem_spt_toList]
    constructor
    · rintro ⟨k, rfl, hk⟩
      rw [h] at hk
      obtain ⟨v, hv⟩ := Aux.mem_domain.1 hk
      exact ⟨k, by rw [hval k v hv]; exact hv⟩
    · rintro ⟨k, hk⟩
      refine ⟨k, (hval k x hk).symm, ?_⟩
      rw [h]
      exact Aux.mem_domain.2 ⟨x, hk⟩
  have hfin : FINITE (domain names) := by
    obtain ⟨l, hl⟩ := Aux.domain_list names
    have : domain names = LIST_TO_SET l := Aux.set_ext fun x => (hl x).symm
    rw [this]
    clear this hl
    rintro P ⟨h0, h1⟩
    induction l with
    | nil =>
      have : LIST_TO_SET ([] : List Nat) = ∅ :=
        Aux.set_ext fun x => Iff.intro (fun h => by cases h) (fun h => False.elim h)
      rw [this]; exact h0
    | cons a l ih =>
      have : LIST_TO_SET (a :: l) = insert a (LIST_TO_SET l) :=
        Aux.set_ext fun x => by rw [Aux.mem_LIST_TO_SET, List.mem_cons]; rfl
      rw [this]; exact h1 _ ih a
  have hmaps : ∀ x, x ∈ domain names → tlookup names x ∈ domain names := by
    intro x hx
    rw [← himg]
    exact ⟨x, rfl, hx⟩
  obtain ⟨⟨_, hi⟩, _, hsu⟩ := CARD_IMAGE_ID_BIJ _ hfin ⟨hmaps, by rw [himg]⟩
  refine ⟨⟨fun _ _ => trivial, ?_⟩, fun _ _ => trivial, ?_⟩
  · rintro x y - e
    by_cases hx : x ∈ domain names <;> by_cases hy : y ∈ domain names
    · exact hi x y ⟨hx, hy⟩ e
    · rw [hout y hy] at e
      exact absurd (e ▸ hmaps x hx) hy
    · rw [hout x hx] at e
      exact absurd (e ▸ hmaps y hy) hx
    · rw [hout x hx, hout y hy] at e; exact e
  · rintro x -
    by_cases hx : x ∈ domain names
    · obtain ⟨y, hy, e⟩ := hsu x hx
      exact ⟨y, trivial, e⟩
    · exact ⟨x, trivial, hout x hx⟩

/- HOL4:
Theorem tlookup_bij_iff:
   BIJ (tlookup names) UNIV UNIV ⇔
   set (toList names) = domain names -/
theorem tlookup_bij_iff {names : spt Nat} :
    BIJ (tlookup names) UNIV UNIV ↔
    LIST_TO_SET (spt_toList names) = domain names := by
  refine ⟨?_, tlookup_bij_suff⟩
  rintro ⟨⟨_, hi⟩, _, hs⟩
  have hval : ∀ k v, lookup k names = some v → tlookup names k = v := by
    intro k v hk; simp [tlookup, hk]
  have hout : ∀ k, lookup k names = none → tlookup names k = k := by
    intro k hk; simp [tlookup, hk]
  refine Aux.set_ext fun x => ?_
  rw [Aux.mem_LIST_TO_SET, Aux.mem_spt_toList, Aux.mem_domain]
  constructor
  · rintro ⟨k, hk⟩
    cases hx : lookup x names with
    | some v => exact ⟨v, rfl⟩
    | none =>
      have : k = x := hi k x ⟨trivial, trivial⟩ (by rw [hval k x hk, hout x hx])
      subst this
      rw [hx] at hk; cases hk
  · rintro ⟨v, hv⟩
    obtain ⟨k, -, hk⟩ := hs x trivial
    cases hk' : lookup k names with
    | some w =>
      rw [hval k w hk'] at hk
      subst hk
      exact ⟨k, hk'⟩
    | none =>
      rw [hout k hk'] at hk
      subst hk
      rw [hv] at hk'; cases hk'

/- HOL4:
Theorem find_index_LESS_LENGTH:
 ∀ls n m i. (find_index n ls m = SOME i) ⇒ (m <= i) ∧ (i < m + LENGTH ls) -/
theorem find_index_LESS_LENGTH :
    ∀ (ls : List α) (n : α) (m i : Nat),
      find_index n ls m = some i → m ≤ i ∧ i < m + ls.length := by
  intro ls
  induction ls with
  | nil => intro n m i h; simp [find_index] at h
  | cons x xs ih =>
    intro n m i h
    simp only [find_index] at h
    split at h
    · cases h; simp
    · have := ih _ _ _ h
      simp only [List.length_cons]; omega

/- HOL4:
Theorem ALOOKUP_find_index_SOME:
   (ALOOKUP env k = SOME v) ⇒
    ∃i. (find_index k (MAP FST env) 0 = SOME i) ∧
        i < LENGTH env ∧ (v = SND (EL i env)) -/
theorem ALOOKUP_find_index_SOME [Nonempty α] [Nonempty β] {env : List (α × β)} {k : α} {v : β} :
    ALOOKUP env k = some v →
    ∃ i, find_index k (env.map Prod.fst) 0 = some i ∧
      i < env.length ∧ v = (EL i env).2 := by
  have key : ∀ (env : List (α × β)) (m : Nat), ALOOKUP env k = some v →
      ∃ i, find_index k (env.map Prod.fst) m = some (m + i) ∧ i < env.length ∧
        v = (EL i env).2 := by
    intro env
    induction env with
    | nil => intro m h; simp [ALOOKUP] at h
    | cons p t ih =>
      obtain ⟨a, b⟩ := p
      intro m h
      simp only [ALOOKUP] at h
      split at h
      · rename_i e
        cases h
        exact ⟨0, by simp [find_index, e], by simp, rfl⟩
      · rename_i e
        obtain ⟨i, h1, h2, h3⟩ := ih (m + 1) h
        refine ⟨i + 1, ?_, by simpa using h2, h3⟩
        simp only [List.map_cons, find_index, if_neg e, h1]
        congr 1; omega
  intro h
  obtain ⟨i, h1, h2⟩ := key env 0 h
  exact ⟨i, by simpa using h1, h2⟩

/- HOL4:
Theorem IS_PREFIX_THM:
  !l2 l1. IS_PREFIX l1 l2 <=> (LENGTH l2 <= LENGTH l1) /\ !n. n < LENGTH l2 ==> (EL n l2 = EL n l1) -/
theorem IS_PREFIX_THM [Nonempty α] :
    ∀ l2 l1 : List α,
      IS_PREFIX l1 l2 ↔
        (l2.length ≤ l1.length ∧ ∀ n, n < l2.length → EL n l2 = EL n l1) := by
  intro l2
  induction l2 with
  | nil => intro l1; simp [IS_PREFIX, isPREFIX]
  | cons a l2 ih =>
    intro l1
    cases l1 with
    | nil => simp [IS_PREFIX, isPREFIX]
    | cons b l1 =>
      have ih' := ih l1
      unfold IS_PREFIX at ih' ⊢
      simp only [isPREFIX, ih', List.length_cons, Nat.add_le_add_iff_right]
      constructor
      · rintro ⟨rfl, h1, h2⟩
        refine ⟨h1, fun n hn => ?_⟩
        cases n with
        | zero => rfl
        | succ n => exact h2 n (by omega)
      · rintro ⟨h1, h2⟩
        exact ⟨h2 0 (by omega), h1, fun n hn => h2 (n + 1) (by omega)⟩

/- HOL4:
Theorem FST_pair:
 (λ(n,v). n) = FST -/
theorem FST_pair :
    (fun ((n, _v) : α × β) => n) = (Prod.fst : α × β → α) := by
  funext p; rfl

/- HOL4:
Theorem LESS_1[simp]:
 x < 1 ⇔ (x = 0:num) -/
theorem LESS_1 {x : Nat} : x < 1 ↔ x = 0 := by omega

/- HOL4:
Theorem map_some_eq:
 !l1 l2. (MAP SOME l1 = MAP SOME l2) ⇔ (l1 = l2) -/
theorem map_some_eq :
    ∀ l1 l2 : List α, l1.map some = l2.map some ↔ l1 = l2 := by
  intro l1
  induction l1 with
  | nil => intro l2; cases l2 <;> simp
  | cons a l1 ih => intro l2; cases l2 <;> simp [ih]

/- HOL4:
Theorem map_some_eq_append:
 !l1 l2 l3. (MAP SOME l1 ++ MAP SOME l2 = MAP SOME l3) ⇔ (l1 ++ l2 = l3) -/
theorem map_some_eq_append :
    ∀ l1 l2 l3 : List α,
      l1.map some ++ l2.map some = l3.map some ↔ l1 ++ l2 = l3 := by
  intro l1 l2 l3
  rw [← List.map_append, map_some_eq]

/- HOL4:
Theorem MAP_EQ_MAP_IMP:
   !xs ys f.
      (!x y. MEM x xs /\ MEM y ys /\ (f x = f y) ==> (x = y)) ==>
      (MAP f xs = MAP f ys) ==> (xs = ys) -/
theorem MAP_EQ_MAP_IMP :
    ∀ (xs ys : List α) (f : α → β),
      (∀ x y, x ∈ xs ∧ y ∈ ys ∧ f x = f y → x = y) →
      xs.map f = ys.map f → xs = ys := by
  intro xs
  induction xs with
  | nil => intro ys f _ h; cases ys <;> simp_all
  | cons a xs ih =>
    intro ys f h e
    cases ys with
    | nil => simp at e
    | cons b ys =>
      rw [List.map_cons, List.map_cons, List.cons.injEq] at e
      rw [h a b ⟨by simp, by simp, e.1⟩,
        ih ys f (fun x y ⟨h1, h2, h3⟩ => h x y ⟨by simp [h1], by simp [h2], h3⟩) e.2]

/- HOL4:
Theorem FDOM_FLOOKUP:
   x ∈ FDOM f ⇔ ∃v. FLOOKUP f x = SOME v -/
theorem FDOM_FLOOKUP {x : α} {f : fmap α β} :
    x ∈ FDOM f ↔ ∃ v, FLOOKUP f x = some v := Aux.mem_FDOM

/- HOL4:
Theorem DROP_EMPTY:
   !ls n. (DROP n ls = []) ==> (n >= LENGTH ls) -/
theorem DROP_EMPTY :
    ∀ (ls : List α) (n : Nat), ls.drop n = [] → n ≥ ls.length := by
  intro ls n h
  simpa using h

/- HOL4:
Theorem plus_0_I[simp]:
   $+ 0n = I -/
theorem plus_0_I : (fun x : Nat => 0 + x) = I := by
  funext x; simp [I]

end

end CmlTS
