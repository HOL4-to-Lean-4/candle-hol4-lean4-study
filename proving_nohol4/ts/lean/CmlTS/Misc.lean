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
import CmlTS.Proofs.SptAux

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
  intro s hs ⟨h1, h2⟩
  obtain ⟨l, hl1, hl2⟩ := Aux.FINITE_enum hs
  obtain ⟨l', h1', h2'⟩ := Aux.nodup_enum (l.map f)
  have hmem : ∀ x, x ∈ l' ↔ x ∈ IMAGE f s := by
    intro x
    rw [h2', List.mem_map]
    constructor
    · rintro ⟨a, ha, rfl⟩; exact ⟨a, rfl, (hl2 a).mp ha⟩
    · rintro ⟨a, rfl, ha⟩; exact ⟨a, (hl2 a).mpr ha, rfl⟩
  rw [Aux.CARD_eq h1' hmem, Aux.CARD_eq hl1 hl2] at h2
  obtain ⟨hn, -⟩ := Aux.nodup_of_subset (l := l.map f) h1' (fun x hx => (h2' x).mp hx)
    (by simp [h2])
  have hinj := Aux.nodup_map_inj hn
  obtain ⟨-, hsurj⟩ := Aux.nodup_of_subset (l := l) hn
    (fun x hx => by
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
      exact (hl2 _).mpr (h1 a ((hl2 a).mp ha)))
    (by simp)
  refine ⟨⟨h1, ?_⟩, ⟨h1, ?_⟩⟩
  · rintro x y ⟨hx, hy⟩ hxy
    exact hinj x y ((hl2 x).mpr hx) ((hl2 y).mpr hy) hxy
  · intro x hx
    obtain ⟨a, ha, hfa⟩ := List.mem_map.mp (hsurj x ((hl2 x).mpr hx))
    exact ⟨a, (hl2 a).mp ha, hfa⟩

theorem Aux.tlookup_some {names : spt Nat} {k v : Nat} (h : lookup k names = some v) :
    tlookup names k = v := by simp [tlookup, h]

theorem Aux.tlookup_none {names : spt Nat} {k : Nat} (h : ¬ k ∈ domain names) :
    tlookup names k = k := by
  rw [Aux.mem_domain] at h
  cases h2 : lookup k names with
  | none => simp [tlookup, h2]
  | some v => exact absurd ⟨v, h2⟩ h

/- HOL4:
Theorem tlookup_bij_suff:
   set (toList names) = domain names ⇒
   BIJ (tlookup names) UNIV UNIV -/
theorem tlookup_bij_suff {names : spt Nat} :
    LIST_TO_SET (spt_toList names) = domain names →
    BIJ (tlookup names) UNIV UNIV := by
  intro h
  have hd : ∀ v, (∃ n, lookup n names = some v) ↔ v ∈ domain names := by
    intro v
    rw [← Aux.mem_spt_toList, ← h]
    exact Iff.rfl
  obtain ⟨l, hl1, hl2⟩ := Aux.domain_enum names
  have hsub : ∀ x, x ∈ l → x ∈ l.map (tlookup names) := by
    intro x hx
    obtain ⟨n, hn⟩ := (hd x).mpr ((hl2 x).mp hx)
    exact List.mem_map.mpr
      ⟨n, (hl2 n).mpr ((Aux.mem_domain _ n).mpr ⟨x, hn⟩), Aux.tlookup_some hn⟩
  obtain ⟨hn, -⟩ := Aux.nodup_of_subset hl1 hsub (by simp)
  have hinj := Aux.nodup_map_inj hn
  have hmap : ∀ x, x ∈ domain names → tlookup names x ∈ domain names := by
    intro x hx
    obtain ⟨v, hv⟩ := (Aux.mem_domain _ x).mp hx
    rw [Aux.tlookup_some hv]
    exact (hd v).mp ⟨x, hv⟩
  refine ⟨⟨fun _ _ => trivial, ?_⟩, ⟨fun _ _ => trivial, ?_⟩⟩
  · rintro x y - hxy
    by_cases hx : x ∈ domain names
    · by_cases hy : y ∈ domain names
      · exact hinj x y ((hl2 x).mpr hx) ((hl2 y).mpr hy) hxy
      · have := hmap x hx
        rw [hxy, Aux.tlookup_none hy] at this
        exact absurd this hy
    · by_cases hy : y ∈ domain names
      · have := hmap y hy
        rw [← hxy, Aux.tlookup_none hx] at this
        exact absurd this hx
      · rwa [Aux.tlookup_none hx, Aux.tlookup_none hy] at hxy
  · intro x _
    by_cases hx : x ∈ domain names
    · obtain ⟨a, _, ha⟩ := List.mem_map.mp (hsub x ((hl2 x).mpr hx))
      exact ⟨a, trivial, ha⟩
    · exact ⟨x, trivial, Aux.tlookup_none hx⟩

/- HOL4:
Theorem tlookup_bij_iff:
   BIJ (tlookup names) UNIV UNIV ⇔
   set (toList names) = domain names -/
theorem tlookup_bij_iff {names : spt Nat} :
    BIJ (tlookup names) UNIV UNIV ↔
    LIST_TO_SET (spt_toList names) = domain names := by
  refine ⟨?_, tlookup_bij_suff⟩
  rintro ⟨⟨-, hinj⟩, -⟩
  have hinj' : ∀ x y, tlookup names x = tlookup names y → x = y :=
    fun x y h => hinj x y ⟨trivial, trivial⟩ h
  obtain ⟨l, hl1, hl2⟩ := Aux.domain_enum names
  have hmap : ∀ x, x ∈ domain names → tlookup names x ∈ domain names := by
    intro x hx
    by_cases hc : tlookup names x ∈ domain names
    · exact hc
    · have := hinj' _ _ (Aux.tlookup_none hc)
      rw [this] at hc
      exact absurd hx hc
  obtain ⟨-, hsurj⟩ := Aux.nodup_of_subset (l := l)
    (Aux.inj_nodup_map hl1 fun x y _ _ h => hinj' x y h)
    (fun x hx => by
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
      exact (hl2 _).mpr (hmap a ((hl2 a).mp ha)))
    (by simp)
  apply Aux.set_ext
  intro v
  show v ∈ spt_toList names ↔ _
  rw [Aux.mem_spt_toList]
  constructor
  · rintro ⟨n, hn⟩
    have := hmap n ((Aux.mem_domain _ n).mpr ⟨v, hn⟩)
    rwa [Aux.tlookup_some hn] at this
  · intro hv
    obtain ⟨a, ha, hfa⟩ := List.mem_map.mp (hsurj v ((hl2 v).mpr hv))
    obtain ⟨w, hw⟩ := (Aux.mem_domain _ a).mp ((hl2 a).mp ha)
    rw [Aux.tlookup_some hw] at hfa
    exact ⟨a, hfa ▸ hw⟩

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
    · simp at h; subst h; simp
    · have := ih n (m + 1) i h
      simp only [List.length_cons]
      omega

/- HOL4:
Theorem ALOOKUP_find_index_SOME:
   (ALOOKUP env k = SOME v) ⇒
    ∃i. (find_index k (MAP FST env) 0 = SOME i) ∧
        i < LENGTH env ∧ (v = SND (EL i env)) -/
theorem ALOOKUP_find_index_SOME [Nonempty α] [Nonempty β] {env : List (α × β)} {k : α} {v : β} :
    ALOOKUP env k = some v →
    ∃ i, find_index k (env.map Prod.fst) 0 = some i ∧
      i < env.length ∧ v = (EL i env).2 := by
  have hidx : ∀ (l : List α) (n : Nat),
      find_index k l n = (find_index k l 0).map (fun i => i + n) := by
    intro l
    induction l with
    | nil => intro n; simp [find_index]
    | cons x xs ih =>
      intro n
      simp only [find_index]
      split
      · simp
      · rw [ih (n + 1), ih (0 + 1)]
        simp only [Option.map_map]
        congr 1
        funext i
        simp only [Function.comp]
        omega
  induction env with
  | nil => intro h; simp [ALOOKUP] at h
  | cons p t ih =>
    obtain ⟨a, b⟩ := p
    intro h
    simp only [ALOOKUP] at h
    simp only [List.map_cons, find_index]
    split at h
    · rename_i hak
      simp at h
      exact ⟨0, by simp [hak], by simp, by simp [EL, HD, h]⟩
    · rename_i hak
      obtain ⟨i, h1, h2, h3⟩ := ih h
      refine ⟨i + 1, ?_, by simp; omega, ?_⟩
      · rw [if_neg hak, hidx, h1]; simp
      · simp only [EL, TL]; exact h3

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
  | cons a t ih =>
    intro l1
    cases l1 with
    | nil => simp [IS_PREFIX, isPREFIX]
    | cons b t1 =>
      have := ih t1
      unfold IS_PREFIX at this ⊢
      simp only [isPREFIX, this, List.length_cons, Nat.add_le_add_iff_right]
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
    (fun ((n, _v) : α × β) => n) = (Prod.fst : α × β → α) := rfl

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
  | cons a t ih => intro l2; cases l2 <;> simp [ih]

/- HOL4:
Theorem map_some_eq_append:
 !l1 l2 l3. (MAP SOME l1 ++ MAP SOME l2 = MAP SOME l3) ⇔ (l1 ++ l2 = l3) -/
theorem map_some_eq_append :
    ∀ l1 l2 l3 : List α,
      l1.map some ++ l2.map some = l3.map some ↔ l1 ++ l2 = l3 := by
  intro l1 l2 l3
  rw [← List.map_append]
  exact map_some_eq _ _

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
  | cons a t ih =>
    intro ys f h1 h
    cases ys with
    | nil => simp at h
    | cons b t2 =>
      simp only [List.map_cons, List.cons.injEq] at h
      rw [h1 a b ⟨List.mem_cons_self, List.mem_cons_self, h.1⟩,
        ih t2 f (fun x y ⟨hx, hy, hxy⟩ =>
          h1 x y ⟨List.mem_cons_of_mem _ hx, List.mem_cons_of_mem _ hy, hxy⟩) h.2]

/- HOL4:
Theorem FDOM_FLOOKUP:
   x ∈ FDOM f ⇔ ∃v. FLOOKUP f x = SOME v -/
theorem FDOM_FLOOKUP {x : α} {f : fmap α β} :
    x ∈ FDOM f ↔ ∃ v, FLOOKUP f x = some v := by
  rw [Aux.mem_FDOM]
  cases FLOOKUP f x <;> simp

/- HOL4:
Theorem DROP_EMPTY:
   !ls n. (DROP n ls = []) ==> (n >= LENGTH ls) -/
theorem DROP_EMPTY :
    ∀ (ls : List α) (n : Nat), ls.drop n = [] → n ≥ ls.length := by
  intro ls n h
  have := congrArg List.length h
  simp at this
  omega

/- HOL4:
Theorem plus_0_I[simp]:
   $+ 0n = I -/
theorem plus_0_I : (fun x : Nat => 0 + x) = I := by
  funext x
  simp [I]

end

end CmlTS
