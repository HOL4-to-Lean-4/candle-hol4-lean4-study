import CandleLean.Prelude

/-!
# misc (CakeML `misc/miscScript.sml`), reduced to what the targets need
-/

universe u v
universe w

namespace Candle

open HOL Classical

noncomputable section

/- HOL4:
Datatype:
  app_list = List ('a list) | Append app_list app_list | Nil
End
   (constructors are `app_list.List`, `app_list.Append`, `app_list.Nil`; not exported,
   to avoid clashing with Lean's `List`) -/
inductive app_list (α : Type u) where
  | List : _root_.List α → app_list α
  | Append : app_list α → app_list α → app_list α
  | Nil : app_list α
  deriving Inhabited

/- HOL4:
Definition append_aux_def:
  (append_aux Nil aux = aux) /\
  (append_aux (List xs) aux = xs ++ aux) /\
  (append_aux (Append l1 l2) aux = append_aux l1 (append_aux l2 aux))
End -/
def append_aux {α : Type u} : app_list α → List α → List α
  | .Nil, aux => aux
  | .List xs, aux => xs ++ aux
  | .Append l1 l2, aux => append_aux l1 (append_aux l2 aux)

/- HOL4:
Definition append_def:
  append l = append_aux l []
End -/
def append {α : Type u} (l : app_list α) : List α := append_aux l []

/-! Auxiliary lemmas (namespace `Candle.Aux`). -/

theorem Aux.set_ext {α : Type u} {s t : Set α} (h : ∀ x, x ∈ s ↔ x ∈ t) : s = t :=
  funext fun x => propext (h x)

theorem Aux.mem_LIST_TO_SET {α : Type u} (x : α) (l : List α) : x ∈ LIST_TO_SET l ↔ x ∈ l := by
  induction l with
  | nil =>
    show False ↔ _
    simp
  | cons h t ih =>
    show (x = h ∨ x ∈ LIST_TO_SET t) ↔ _
    simp [ih]

theorem Aux.mem_UNION {α : Type u} (x : α) (s t : Set α) : x ∈ UNION s t ↔ x ∈ s ∨ x ∈ t := Iff.rfl

theorem Aux.mem_INTER {α : Type u} (x : α) (s t : Set α) : x ∈ INTER s t ↔ x ∈ s ∧ x ∈ t := Iff.rfl

theorem Aux.mem_INSERT {α : Type u} (x y : α) (s : Set α) : x ∈ INSERT y s ↔ x = y ∨ x ∈ s := Iff.rfl

theorem Aux.mem_EMPTY {α : Type u} (x : α) : x ∈ (EMPTY : Set α) ↔ False := Iff.rfl

theorem Aux.mem_UNIV {α : Type u} (x : α) : x ∈ (UNIV : Set α) ↔ True := Iff.rfl

theorem Aux.mem_setOf {α : Type u} (x : α) (P : α → Prop) : x ∈ setOf P ↔ P x := Iff.rfl

theorem Aux.mem_GSPEC {α : Type u} {β : Type v} (x : α) (f : β → α) (P : β → Prop) :
    x ∈ GSPEC (fun y => (f y, P y)) ↔ ∃ y, x = f y ∧ P y := by
  show (∃ y, (x, True) = (f y, P y)) ↔ _
  constructor
  · rintro ⟨y, h⟩
    rw [Prod.mk.injEq] at h
    exact ⟨y, h.1, h.2 ▸ trivial⟩
  · rintro ⟨y, h1, h2⟩
    refine ⟨y, ?_⟩
    rw [Prod.mk.injEq]
    exact ⟨h1, (eq_true h2).symm⟩

theorem Aux.mem_IMAGE {α : Type u} {β : Type v} (x : β) (f : α → β) (s : Set α) :
    x ∈ IMAGE f s ↔ ∃ y, x = f y ∧ y ∈ s := Aux.mem_GSPEC x f (fun y => y ∈ s)

theorem Aux.EVEN_iff (n : Nat) : EVEN n ↔ n % 2 = 0 := by
  induction n with
  | zero => simp [EVEN]
  | succ n ih => simp only [EVEN, ih]; omega

theorem Aux.domain_insert {α : Type u} (a : α) : ∀ (k : Nat) (t : spt α) (x : Nat),
    x ∈ sptree.domain (sptree.insert k a t) ↔ x = k ∨ x ∈ sptree.domain t := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro t x
    by_cases hk : k = 0
    · subst hk
      cases t <;> rw [sptree.insert] <;>
        simp only [if_true, sptree.domain, Aux.mem_UNION, Aux.mem_INSERT, Aux.mem_EMPTY] <;> grind
    · have ih' := ih ((k - 1) / 2) (by omega)
      by_cases he : EVEN k
      · have he' : k = 2 * ((k - 1) / 2) + 2 := by rw [Aux.EVEN_iff] at he; omega
        cases t <;> rw [sptree.insert] <;>
          simp only [hk, he, if_true, if_false, sptree.domain, Aux.mem_UNION, Aux.mem_INSERT,
            Aux.mem_EMPTY, Aux.mem_IMAGE, ih'] <;> grind
      · have he' : k = 2 * ((k - 1) / 2) + 1 := by rw [Aux.EVEN_iff] at he; omega
        cases t <;> rw [sptree.insert] <;>
          simp only [hk, he, if_true, if_false, sptree.domain, Aux.mem_UNION, Aux.mem_INSERT,
            Aux.mem_EMPTY, Aux.mem_IMAGE, ih'] <;> grind

theorem Aux.ALOOKUP_append {α : Type u} {β : Type v} (l1 l2 : List (α × β)) (x : α) :
    ALOOKUP (l1 ++ l2) x = match ALOOKUP l1 x with
      | none => ALOOKUP l2 x
      | some y => some y := by
  induction l1 with
  | nil => simp [ALOOKUP]
  | cons p t ih =>
    obtain ⟨a, b⟩ := p
    by_cases h : a = x <;> simp [ALOOKUP, h, ih]

theorem Aux.EL_eq_getElem {α : Type u} [Nonempty α] : ∀ (n : Nat) (l : List α) (h : n < l.length),
    EL n l = l[n]
  | 0, a :: t, _ => by simp [EL, HD_def]
  | n + 1, a :: t, h => by
    simp only [EL, TL]
    rw [Aux.EL_eq_getElem n t (by simpa using h)]
    simp

theorem Aux.EL_mem {α : Type u} [Nonempty α] (n : Nat) (l : List α) (h : n < l.length) :
    EL n l ∈ l := by
  rw [Aux.EL_eq_getElem n l h]; exact List.getElem_mem h

theorem Aux.UNHEX_HEX (k : Nat) (h : k < 16) : UNHEX (HEX k) = k := by
  have e0 : ORD (ch '0') = 48 := rfl
  have e9 : ORD (ch '9') = 57 := rfl
  have ea : ORD (ch 'a') = 97 := rfl
  have ef : ORD (ch 'f') = 102 := rfl
  have eA : ORD (ch 'A') = 65 := rfl
  have eF : ORD (ch 'F') = 70 := rfl
  unfold HEX
  by_cases h10 : k < 10
  · rw [if_pos h10, e0, CHR_of_lt (by omega : 48 + k < 256)]
    simp only [UNHEX, ORD] at *
    simp only [e0, e9]
    rw [if_pos (by omega)]; omega
  · rw [if_neg h10, if_pos h, eA, CHR_of_lt (by omega : 65 + (k - 10) < 256)]
    simp only [UNHEX, ORD] at *
    simp only [e0, e9, ea, ef, eA, eF]
    rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)]; omega

theorem Aux.l2n_n2l (n : Nat) : l2n 16 ((n2l 16 n).map (UNHEX ∘ HEX)) = n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    have hm : n % 16 < 16 := Nat.mod_lt _ (by omega)
    rw [n2l]
    by_cases h : n < 16
    · rw [if_pos (Or.inl h)]
      simp only [List.map_cons, List.map_nil, Function.comp, l2n, Aux.UNHEX_HEX _ hm]
      omega
    · rw [if_neg (by omega)]
      simp only [List.map_cons, l2n]
      rw [ih (n / 16) (by omega)]
      simp only [Function.comp, Aux.UNHEX_HEX _ hm]
      omega

theorem Aux.FIELDS_cons_pos (P : char → Prop) (h : char) (t : string) (hP : P h) :
    FIELDS P (h :: t) = [] :: FIELDS P t := by
  rw [FIELDS]; simp [SPLITP, hP, NULL, TL]

theorem Aux.FIELDS_cons_neg (P : char → Prop) (h : char) (t : string) (hP : ¬ P h) :
    ∃ l ls, FIELDS P t = l :: ls ∧ FIELDS P (h :: t) = (h :: l) :: ls := by
  have e1 : FIELDS P (h :: t) = if NULL (SPLITP P t).2 then [h :: (SPLITP P t).1]
      else (h :: (SPLITP P t).1) :: FIELDS P (TL (SPLITP P t).2) := by
    rw [FIELDS]; simp [SPLITP, hP, NULL]
  cases t with
  | nil => exact ⟨[], [], by simp [FIELDS], by rw [e1]; simp [SPLITP, NULL]⟩
  | cons h2 t2 =>
    by_cases hP2 : P h2
    · refine ⟨[], FIELDS P t2, Aux.FIELDS_cons_pos P h2 t2 hP2, ?_⟩
      rw [e1]; simp [SPLITP, hP2, NULL, TL]
    · have e2 : FIELDS P (h2 :: t2) = if NULL (SPLITP P (h2 :: t2)).2 then [(SPLITP P (h2 :: t2)).1]
          else (SPLITP P (h2 :: t2)).1 :: FIELDS P (TL (SPLITP P (h2 :: t2)).2) := by
        rw [FIELDS]; simp [SPLITP, hP2, NULL]
      by_cases hn : NULL (SPLITP P (h2 :: t2)).2
      · rw [if_pos hn] at e1 e2; exact ⟨_, _, e2, e1⟩
      · rw [if_neg hn] at e1 e2; exact ⟨_, _, e2, e1⟩

theorem Aux.testbit_single (b : Prop) (i : Nat) : testbit i [b] ↔ (i = 0 ∧ b) := by
  unfold testbit field
  have e : i + 1 - i = 1 := by omega
  rw [e]
  cases i with
  | zero =>
    simp [shiftr, fixwidth]
  | succ i =>
    simp [shiftr, fixwidth, zero_extend, PAD_LEFT, GENLIST, SNOC]

theorem Aux.FCP_bits_false (n : Nat) : FCP_bits n (fun _ => False) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [FCP_bits, ih]

theorem Aux.FCP_bits_zero (n : Nat) : FCP_bits (n + 1) (fun i => i = 0) = 1 := by
  induction n with
  | zero => simp [FCP_bits]
  | succ n ih => rw [FCP_bits, ih]; simp

/- HOL4:
Theorem append_aux_thm:
   !l xs. append_aux l xs = append_aux l [] ++ xs -/
theorem append_aux_thm {α : Type u} :
    ∀ (l : app_list α) (xs : List α), append_aux l xs = append_aux l [] ++ xs := by
  intro l
  induction l with
  | List ys => intro xs; simp [append_aux]
  | Append a b iha ihb =>
    intro xs
    simp only [append_aux]
    rw [iha, ihb, iha (append_aux b [])]
    simp
  | Nil => intro xs; simp [append_aux]

/- HOL4:
Theorem append_thm[simp]:
   append (Append l1 l2) = append l1 ++ append l2 /\
    append (List xs) = xs /\
    append Nil = []
   (the three conjuncts have independent HOL4 type variables) -/
theorem append_thm {α : Type u} {β : Type v} {γ : Type w}
    (l1 l2 : app_list α) (xs : List β) :
    append (app_list.Append l1 l2) = append l1 ++ append l2 ∧
    append (app_list.List xs) = xs ∧
    append (app_list.Nil : app_list γ) = [] := by
  refine ⟨?_, ?_, rfl⟩
  · simp only [append, append_aux]
    exact append_aux_thm _ _
  · simp [append, append_aux]

/- HOL4:
Definition SmartAppend_def[simp]:
  (SmartAppend Nil l2 = l2) ∧
  (SmartAppend l1 Nil = l1) ∧
  (SmartAppend l1 l2 = Append l1 l2)
End -/
def SmartAppend {α : Type u} : app_list α → app_list α → app_list α
  | .Nil, l2 => l2
  | l1, .Nil => l1
  | l1, l2 => .Append l1 l2

/- HOL4:
Theorem SmartAppend_thm:
   ∀l1 l2.
    SmartAppend l1 l2 =
      if l1 = Nil then l2 else
      if l2 = Nil then l1 else Append l1 l2 -/
theorem SmartAppend_thm {α : Type u} :
    ∀ (l1 l2 : app_list α),
      SmartAppend l1 l2 =
        if l1 = app_list.Nil then l2 else
        if l2 = app_list.Nil then l1 else app_list.Append l1 l2 := by
  intro l1 l2
  cases l1 <;> cases l2 <;> simp [SmartAppend]

/- HOL4:
Theorem append_SmartAppend[simp]:
   append (SmartAppend l1 l2) = append l1 ++ append l2 -/
theorem append_SmartAppend {α : Type u} (l1 l2 : app_list α) :
    append (SmartAppend l1 l2) = append l1 ++ append l2 := by
  rw [SmartAppend_thm]
  split
  · next h => subst h; simp [append, append_aux]
  · split
    · next h => subst h; simp [append, append_aux]
    · exact (append_thm (β := α) (γ := α) l1 l2 []).1

/- HOL4:
Theorem MAP_FST_I_PAIR_MAP[simp]:
   !xs. MAP FST (MAP (I ## f) xs) = MAP FST xs -/
theorem MAP_FST_I_PAIR_MAP {α : Type u} {β : Type v} {γ : Type w} (f : β → γ) :
    ∀ (xs : List (α × β)),
      List.map Prod.fst (List.map (PAIR_MAP I f) xs) = List.map Prod.fst xs := by
  intro xs
  rw [List.map_map]
  apply List.map_congr_left
  intro a _
  rfl

/- HOL4:
Theorem MAX_LIST_APPEND[simp]:
   MAX_LIST (xs++ys) = MAX (MAX_LIST xs) (MAX_LIST ys) -/
theorem MAX_LIST_APPEND (xs ys : List Nat) :
    MAX_LIST (xs ++ ys) = MAX (MAX_LIST xs) (MAX_LIST ys) := by
  induction xs with
  | nil => simp only [List.nil_append, MAX_LIST, MAX]; split <;> omega
  | cons a t ih =>
    simp only [List.cons_append, MAX_LIST, ih, MAX]
    repeat' split
    all_goals omega

/- HOL4:
Theorem MAX_LIST_SNOC[simp]:
   MAX_LIST (SNOC x xs) = MAX (MAX_LIST xs) x -/
theorem MAX_LIST_SNOC (x : Nat) (xs : List Nat) :
    MAX_LIST (SNOC x xs) = MAX (MAX_LIST xs) x := by
  induction xs with
  | nil =>
    simp only [SNOC, MAX_LIST, MAX]
    repeat' split
    all_goals omega
  | cons a t ih =>
    simp only [SNOC, MAX_LIST, ih, MAX]
    repeat' split
    all_goals omega

/- HOL4:
Definition max3_def[simp]:
  max3 (x:num) y z = if x > y then (if z > x then z else x)
                     else (if z > y then z else y)
End -/
def max3 (x y z : Nat) : Nat :=
  if x > y then (if z > x then z else x) else (if z > y then z else y)

/- HOL4:
Theorem domain_nat_set_from_list[simp]:
   ∀ls ns. domain (FOLDL (λs n. insert n () s) ns ls) = domain ns ∪ set ls -/
theorem domain_nat_set_from_list :
    ∀ (ls : List Nat) (ns : num_set),
      sptree.domain (List.foldl (fun s n => sptree.insert n () s) ns ls) =
        UNION (sptree.domain ns) (LIST_TO_SET ls) := by
  intro ls
  induction ls with
  | nil =>
    intro ns
    apply Aux.set_ext
    intro x
    simp [Aux.mem_UNION, Aux.mem_LIST_TO_SET]
  | cons a t ih =>
    intro ns
    simp only [List.foldl_cons, ih]
    apply Aux.set_ext
    intro x
    simp only [Aux.mem_UNION, Aux.mem_LIST_TO_SET, Aux.domain_insert, List.mem_cons]
    grind

/- HOL4:
Definition UPDATE_LIST_def:
  UPDATE_LIST = FOLDL (combin$C (UNCURRY UPDATE))
End
val _ = Parse.add_infix("=++",500,Parse.LEFT)
Overload "=++" = ``UPDATE_LIST``
   (`f =++ l` is written `UPDATE_LIST f l`) -/
def UPDATE_LIST {α : Type u} {β : Type v} : (α → β) → List (α × β) → (α → β) :=
  List.foldl (C (UNCURRY UPDATE))

/- HOL4:
Theorem UPDATE_LIST_THM:
   ∀f. (f =++ [] = f) ∧ ∀h t. (f =++ (h::t) = (FST h =+ SND h) f =++ t) -/
theorem UPDATE_LIST_THM {α : Type u} {β : Type v} :
    ∀ (f : α → β), (UPDATE_LIST f [] = f) ∧
      ∀ (h : α × β) (t : List (α × β)),
        UPDATE_LIST f (h :: t) = UPDATE_LIST (UPDATE h.1 h.2 f) t := by
  intro f
  exact ⟨rfl, fun _ _ => rfl⟩

/- HOL4:
Theorem APPLY_UPDATE_LIST_ALOOKUP:
   ∀ls f x. (f =++ ls) x = case ALOOKUP (REVERSE ls) x of NONE => f x | SOME y => y -/
theorem APPLY_UPDATE_LIST_ALOOKUP {α : Type u} {β : Type v} :
    ∀ (ls : List (α × β)) (f : α → β) (x : α),
      UPDATE_LIST f ls x =
        match ALOOKUP (List.reverse ls) x with
        | none => f x
        | some y => y := by
  intro ls
  induction ls with
  | nil => intro f x; simp [UPDATE_LIST, ALOOKUP]
  | cons p t ih =>
    intro f x
    rw [(UPDATE_LIST_THM f).2, ih, List.reverse_cons, Aux.ALOOKUP_append]
    obtain ⟨a, b⟩ := p
    cases h : ALOOKUP t.reverse x with
    | some y => simp
    | none => by_cases hx : a = x <;> simp [ALOOKUP, UPDATE, hx]

/- HOL4:
Definition find_index_def:
  (find_index _ [] _ = NONE) ∧
  (find_index y (x::xs) n = if x = y then SOME n else find_index y xs (n+1))
End -/
def find_index {α : Type u} : α → List α → Nat → Option Nat
  | _, [], _ => none
  | y, x :: xs, n => if x = y then some n else find_index y xs (n + 1)

/- HOL4:
Theorem find_index_ALL_DISTINCT_EL[simp]:
 ∀ls n m. ALL_DISTINCT ls ∧ n < LENGTH ls ⇒ (find_index (EL n ls) ls m = SOME (m + n)) -/
theorem find_index_ALL_DISTINCT_EL {α : Type u} [Nonempty α] :
    ∀ (ls : List α) (n m : Nat), ALL_DISTINCT ls ∧ n < ls.length →
      find_index (EL n ls) ls m = some (m + n) := by
  intro ls
  induction ls with
  | nil => intro n m ⟨_, h⟩; simp at h
  | cons a t ih =>
    intro n m ⟨hd, hn⟩
    simp only [ALL_DISTINCT] at hd
    cases n with
    | zero => simp [EL, HD_def, find_index]
    | succ n =>
      have hn' : n < t.length := by simpa using hn
      have hne : a ≠ EL n t := fun h => hd.1 (h ▸ Aux.EL_mem n t hn')
      simp only [EL, TL, find_index, hne, if_false]
      rw [ih n (m + 1) ⟨hd.2, hn'⟩]
      congr 1; omega

/- HOL4:
Theorem find_index_shift_0:
   ∀ls x k. find_index x ls k = OPTION_MAP (λx. x + k) (find_index x ls 0) -/
theorem find_index_shift_0 {α : Type u} :
    ∀ (ls : List α) (x : α) (k : Nat),
      find_index x ls k = Option.map (fun x => x + k) (find_index x ls 0) := by
  intro ls x
  induction ls with
  | nil => intro k; simp [find_index]
  | cons a t ih =>
    intro k
    by_cases h : a = x
    · simp [find_index, h]
    · simp only [find_index, h, if_false]
      rw [ih (k + 1), ih (0 + 1), Option.map_map]
      congr 1
      funext y
      simp only [Function.comp]
      omega

/- HOL4:
Theorem EVERY2_RC_same[simp]:
   EVERY2 (RC R) l l -/
theorem EVERY2_RC_same {α : Type u} (R : α → α → Prop) (l : List α) :
    EVERY2 (RC R) l l := by
  induction l with
  | nil => simp [LIST_REL]
  | cons a t ih => exact ⟨Or.inl rfl, ih⟩

/- HOL4:
Theorem I_PERMUTES[simp]:
   I PERMUTES s -/
theorem I_PERMUTES {α : Type u} (s : Set α) : PERMUTES I s := by
  exact ⟨⟨fun _ h => h, fun _ _ _ h => h⟩, fun _ h => h, fun x h => ⟨x, h, rfl⟩⟩

/- HOL4:
Theorem MAP_EQ_ID:
 !f ls. (MAP f ls = ls) = (!x. MEM x ls ==> (f x = x)) -/
theorem MAP_EQ_ID {α : Type u} :
    ∀ (f : α → α) (ls : List α), (List.map f ls = ls) = (∀ x, x ∈ ls → f x = x) := by
  intro f ls
  apply propext
  induction ls with
  | nil => simp
  | cons a t ih => simp [ih]

/- HOL4:
Theorem FUN_FMAP_FAPPLY_FEMPTY_FAPPLY[simp]:
 FINITE s ==> (FUN_FMAP ($FAPPLY FEMPTY) s ' x = FEMPTY ' x) -/
theorem FUN_FMAP_FAPPLY_FEMPTY_FAPPLY {α : Type u} {β : Type v} [Nonempty β]
    (s : Set α) (x : α) :
    FINITE s →
      FAPPLY (FUN_FMAP (FAPPLY (FEMPTY : fmap α β)) s) x = FAPPLY (FEMPTY : fmap α β) x := by
  intro hs
  have h := FUN_FMAP_DEF (FAPPLY (FEMPTY : fmap α β)) s hs
  by_cases hx : x ∈ s
  · exact h.2 x hx
  · have hr : (FUN_FMAP (FAPPLY (FEMPTY : fmap α β)) s).rep x = none := by
      apply Classical.byContradiction
      intro hne
      apply hx
      rw [← h.1]
      exact hne
    simp only [FAPPLY, hr]
    rfl

/- HOL4:
Theorem LESS_1[simp]:
 x < 1 ⇔ (x = 0:num) -/
theorem LESS_1 (x : Nat) : x < 1 ↔ x = 0 := by
  omega

/- HOL4:
Theorem num_from_hex_string_num_to_hex_string[simp]:
   num_from_hex_string (num_to_hex_string n) = n -/
theorem num_from_hex_string_num_to_hex_string (n : Nat) :
    num_from_hex_string (num_to_hex_string n) = n := by
  simp only [num_from_hex_string, num_to_hex_string, s2n, n2s, List.reverse_reverse, List.map_map]
  exact Aux.l2n_n2l n

/- HOL4:
Theorem MAPi_ID[simp]:
   MAPi (\x y. y) = I -/
theorem MAPi_ID {α : Type u} : MAPi (fun (_x : Nat) (y : α) => y) = (I : List α → List α) := by
  funext l
  induction l with
  | nil => rfl
  | cons a t ih => exact congrArg (a :: ·) ih

/- HOL4:
Theorem OPT_MMAP_SOME[simp]:
   OPT_MMAP SOME ls = SOME ls -/
theorem OPT_MMAP_SOME {α : Type u} (ls : List α) : OPT_MMAP some ls = some ls := by
  induction ls with
  | nil => rfl
  | cons a t ih => simp [OPT_MMAP, ih]

/- HOL4:
Theorem w2n_lt_256 =
  w2n_lt |> INST_TYPE [``:'a``|->``:8``]
         |> SIMP_RULE std_ss [EVAL ``dimword (:8)``]
   (wordsTheory.w2n_lt is `!w:'a word. w2n w < dimword(:'a)`, so the theorem is
   `!w:word8. w2n w < 256`) -/
theorem w2n_lt_256 : ∀ (w : word8), w2n w < 256 := by
  intro w
  exact w.isLt

theorem Aux.CHR_w2n_n2w_ORD (c : char) : CHR (w2n ((n2w : Nat → word8) (ORD c))) = c := by
  have h : w2n ((n2w : Nat → word8) (ORD c)) = ORD c := by
    have := c.ord_lt
    simp only [w2n, n2w, BitVec.toNat_ofNat, ORD]
    omega
  rw [h]
  exact CHR_of_lt c.ord_lt

theorem Aux.n2w_ORD_CHR_w2n (w : word8) : n2w (ORD (CHR (w2n w))) = w := by
  rw [CHR_of_lt (w2n_lt_256 w)]
  simp [ORD, n2w, w2n]

/- HOL4:
Theorem CHR_w2n_n2w_ORD:
   (CHR o w2n o (n2w:num->word8) o ORD) = I -/
theorem CHR_w2n_n2w_ORD : (CHR ∘ w2n ∘ (n2w : Nat → word8) ∘ ORD) = I := by
  funext c
  exact Aux.CHR_w2n_n2w_ORD c

/- HOL4:
Theorem n2w_ORD_CHR_w2n:
   ((n2w:num->word8) o ORD o CHR o w2n) = I -/
theorem n2w_ORD_CHR_w2n : ((n2w : Nat → word8) ∘ ORD ∘ CHR ∘ (w2n : word8 → Nat)) = I := by
  funext w
  exact Aux.n2w_ORD_CHR_w2n w

/- HOL4:
Theorem CHR_w2n_n2w_ORD_simp[simp]:
   !c. CHR(w2n((n2w:num->word8)(ORD c))) = c -/
theorem CHR_w2n_n2w_ORD_simp : ∀ (c : char), CHR (w2n ((n2w : Nat → word8) (ORD c))) = c := by
  exact Aux.CHR_w2n_n2w_ORD

/- HOL4:
Theorem n2w_ORD_CHR_w2n_simp[simp]:
   !w. n2w(ORD(CHR(w2n w))) = (w:word8) -/
theorem n2w_ORD_CHR_w2n_simp : ∀ (w : word8), n2w (ORD (CHR (w2n w))) = w := by
  exact Aux.n2w_ORD_CHR_w2n

/- HOL4:
Theorem LENGTH_FIELDS:
   ∀ls. LENGTH (FIELDS P ls) = LENGTH (FILTER P ls) + 1 -/
theorem LENGTH_FIELDS (P : char → Prop) :
    ∀ (ls : string), (FIELDS P ls).length = (FILTER P ls).length + 1 := by
  intro ls
  induction ls with
  | nil => simp [FIELDS, FILTER]
  | cons h t ih =>
    by_cases hP : P h
    · rw [Aux.FIELDS_cons_pos P h t hP]
      simp [FILTER, hP, ih]
    · obtain ⟨l, ls, e1, e2⟩ := Aux.FIELDS_cons_neg P h t hP
      rw [e2]
      rw [e1] at ih
      simp only [FILTER, hP, if_false]
      simpa using ih

/- HOL4:
Theorem FIELDS_NEQ_NIL[simp]:
   FIELDS P ls ≠ [] -/
theorem FIELDS_NEQ_NIL (P : char → Prop) (ls : string) : FIELDS P ls ≠ [] := by
  intro h
  have := LENGTH_FIELDS P ls
  rw [h] at this
  simp at this

/- HOL4:
Theorem FIELDS_next:
   ∀ls l1 l2.
   FIELDS P ls = l1::l2 ⇒
   LENGTH l1 < LENGTH ls ⇒
   FIELDS P (DROP (SUC (LENGTH l1)) ls) = l2 ∧
   (∃c. l1 ++ [c] ≼ ls ∧ P c) -/
theorem FIELDS_next (P : char → Prop) :
    ∀ (ls l1 : string) (l2 : List string),
      FIELDS P ls = l1 :: l2 →
      l1.length < ls.length →
      FIELDS P (ls.drop (l1.length + 1)) = l2 ∧
      (∃ c, isPREFIX (l1 ++ [c]) ls ∧ P c) := by
  intro ls
  induction ls with
  | nil => intro l1 l2 _ h; simp at h
  | cons h t ih =>
    intro l1 l2 hf hl
    by_cases hP : P h
    · rw [Aux.FIELDS_cons_pos P h t hP] at hf
      obtain ⟨rfl, rfl⟩ := List.cons.inj hf
      exact ⟨by simp, h, by simp [isPREFIX], hP⟩
    · obtain ⟨l, ls, e1, e2⟩ := Aux.FIELDS_cons_neg P h t hP
      rw [e2] at hf
      obtain ⟨rfl, rfl⟩ := List.cons.inj hf
      obtain ⟨h1, c, h2, h3⟩ := ih l ls e1 (by simpa using hl)
      exact ⟨by simpa using h1, c, ⟨rfl, h2⟩, h3⟩

/- HOL4:
Definition splitlines_def:
  splitlines ls =
  let lines = FIELDS ((=) #"\n") ls in
  (* discard trailing newline *)
  if NULL (LAST lines) then FRONT lines else lines
End -/
def splitlines (ls : string) : List string :=
  let lines := FIELDS (fun c => ch '\n' = c) ls
  if NULL (LAST lines) then FRONT lines else lines

/- HOL4:
Theorem splitlines_nil[simp] = EVAL“splitlines ""”
   (the theorem proved is `splitlines "" = []`) -/
theorem splitlines_nil : splitlines (str "") = [] := by
  have : str "" = [] := rfl
  rw [this]
  simp [splitlines, FIELDS, LAST_DEF, NULL, FRONT]

/- HOL4:
Theorem splitlines_eq_nil[simp]:
   splitlines ls = [] ⇔ (ls = []) -/
theorem splitlines_eq_nil (ls : string) : splitlines ls = [] ↔ ls = [] := by
  constructor
  · intro h
    cases ls with
    | nil => rfl
    | cons a t =>
      exfalso
      by_cases hP : ch '\n' = a
      · simp only [splitlines] at h
        rw [Aux.FIELDS_cons_pos (fun c => ch '\n' = c) a t hP] at h
        have hne := FIELDS_NEQ_NIL (fun c => ch '\n' = c) t
        split at h
        · simp [FRONT, hne] at h
        · simp at h
      · obtain ⟨l, ls, _, e2⟩ := Aux.FIELDS_cons_neg (fun c => ch '\n' = c) a t hP
        simp only [splitlines] at h
        rw [e2] at h
        split at h
        · next hn =>
          cases ls with
          | nil => simp [LAST_DEF, NULL] at hn
          | cons b s => simp [FRONT] at h
        · simp at h
  · rintro rfl
    simp [splitlines, FIELDS, LAST_DEF, NULL, FRONT]

/- HOL4:
Theorem irreflexive_inv_image:
   !R f. irreflexive R ==> irreflexive (inv_image R f) -/
theorem irreflexive_inv_image {α : Type u} {β : Type v} :
    ∀ (R : β → β → Prop) (f : α → β), irreflexive R → irreflexive (inv_image R f) := by
  intro R f h x
  exact h (f x)

/- HOL4:
Theorem trichotomous_inv_image:
   !R f. trichotomous R /\ (INJ f UNIV UNIV) ==> trichotomous (inv_image R f) -/
theorem trichotomous_inv_image {α : Type u} {β : Type v} :
    ∀ (R : β → β → Prop) (f : α → β),
      trichotomous R ∧ INJ f UNIV UNIV → trichotomous (inv_image R f) := by
  intro R f ⟨h, hi⟩ a b
  rcases h (f a) (f b) with h1 | h1 | h1
  · exact Or.inl h1
  · exact Or.inr (Or.inl h1)
  · exact Or.inr (Or.inr (hi.2 a b ⟨trivial, trivial⟩ h1))

/- HOL4:
Theorem plus_0_I[simp]:
   $+ 0n = I -/
theorem plus_0_I : (fun n : Nat => 0 + n) = (I : Nat → Nat) := by
  funext n
  exact Nat.zero_add n

/- HOL4:
Theorem OPTION_MAP_I[simp]:
   OPTION_MAP I x = x -/
theorem OPTION_MAP_I {α : Type u} (x : Option α) : Option.map I x = x := by
  cases x <;> rfl

/- HOL4:
Definition is_subseq_def:
  (is_subseq ls [] ⇔ T) ∧
  (is_subseq [] (x::xs) ⇔ F) ∧
  (is_subseq (y::ys) (x::xs) ⇔
   (x = y ∧ is_subseq ys xs) ∨
   (is_subseq ys (x::xs)))
End -/
def is_subseq {α : Type u} : List α → List α → Prop
  | _, [] => True
  | [], _ :: _ => False
  | y :: ys, x :: xs => (x = y ∧ is_subseq ys xs) ∨ is_subseq ys (x :: xs)

/- HOL4:
Theorem is_subseq_refl[simp]:
   ∀ls. is_subseq ls ls -/
theorem is_subseq_refl {α : Type u} : ∀ (ls : List α), is_subseq ls ls := by
  intro ls
  induction ls with
  | nil => simp [is_subseq]
  | cons a t ih => simp [is_subseq, ih]

/- HOL4:
Theorem is_subseq_nil[simp]:
   is_subseq [] ls ⇔ ls = [] -/
theorem is_subseq_nil {α : Type u} (ls : List α) : is_subseq [] ls ↔ ls = [] := by
  cases ls <;> simp [is_subseq]

/- HOL4:
Definition make_even_def:
  make_even n = if EVEN n then n else n+1
End -/
def make_even (n : Nat) : Nat := if EVEN n then n else n + 1

/- HOL4:
Theorem EVEN_make_even[simp]:
   EVEN (make_even x) -/
theorem EVEN_make_even (x : Nat) : EVEN (make_even x) := by
  unfold make_even
  by_cases h : EVEN x
  · simp [h]
  · simp only [h, if_false]
    rw [Aux.EVEN_iff] at h ⊢
    omega

/- HOL4:
Theorem v2w_32_F[simp]:
   (v2w [F] : word32) = 0w -/
theorem v2w_32_F : (v2w [False] : word32) = n2w 0 := by
  have : (fun i => testbit i [False]) = fun _ => False := by
    funext i; apply propext; rw [Aux.testbit_single]; simp
  simp only [v2w, FCP, n2w]
  rw [this, Aux.FCP_bits_false]

/- HOL4:
Theorem v2w_32_T[simp]:
   (v2w [T] : word32) = 1w -/
theorem v2w_32_T : (v2w [True] : word32) = n2w 1 := by
  have : (fun i => testbit i [True]) = fun i => i = 0 := by
    funext i; apply propext; rw [Aux.testbit_single]; simp
  simp only [v2w, FCP, n2w]
  rw [this, Aux.FCP_bits_zero 31]

/- HOL4:
Definition fmap_update_def[simp]:
  fmap_update f k v = f |+ (k,v)
End -/
def fmap_update {α : Type u} {β : Type v} (f : fmap α β) (k : α) (v : β) : fmap α β :=
  FUPDATE f (k, v)

end

end Candle
