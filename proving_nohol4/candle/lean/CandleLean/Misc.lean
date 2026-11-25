import CandleLean.Prelude
import CandleLean.Proofs.Base

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

/- HOL4:
Theorem append_aux_thm:
   !l xs. append_aux l xs = append_aux l [] ++ xs -/
theorem append_aux_thm {α : Type u} :
    ∀ (l : app_list α) (xs : List α), append_aux l xs = append_aux l [] ++ xs := by
  intro l
  induction l with
  | Nil => intro xs; simp [append_aux]
  | List ys => intro xs; simp [append_aux]
  | Append a b iha ihb =>
    intro xs
    simp only [append_aux]
    rw [iha (append_aux b xs), ihb xs, iha (append_aux b [])]
    simp

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
  refine ⟨?_, ?_, ?_⟩
  · simp only [append, append_aux]; rw [append_aux_thm]
  · simp [append, append_aux]
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
  by_cases h1 : l1 = app_list.Nil
  · subst h1; simp [append, append_aux]
  · by_cases h2 : l2 = app_list.Nil
    · subst h2; simp [h1, append, append_aux]
    · simp only [h1, h2, if_false]
      exact (append_thm l1 l2 ([] : List α) (γ := α)).1

/- HOL4:
Theorem MAP_FST_I_PAIR_MAP[simp]:
   !xs. MAP FST (MAP (I ## f) xs) = MAP FST xs -/
theorem MAP_FST_I_PAIR_MAP {α : Type u} {β : Type v} {γ : Type w} (f : β → γ) :
    ∀ (xs : List (α × β)),
      List.map Prod.fst (List.map (PAIR_MAP I f) xs) = List.map Prod.fst xs := by
  intro xs
  simp [Function.comp_def]

/- HOL4:
Theorem MAX_LIST_APPEND[simp]:
   MAX_LIST (xs++ys) = MAX (MAX_LIST xs) (MAX_LIST ys) -/
theorem MAX_LIST_APPEND (xs ys : List Nat) :
    MAX_LIST (xs ++ ys) = MAX (MAX_LIST xs) (MAX_LIST ys) := by
  induction xs with
  | nil => simp [MAX_LIST, Aux.MAX_eq]
  | cons a t ih => simp only [List.cons_append, MAX_LIST, ih, Aux.MAX_eq]; omega

/- HOL4:
Theorem MAX_LIST_SNOC[simp]:
   MAX_LIST (SNOC x xs) = MAX (MAX_LIST xs) x -/
theorem MAX_LIST_SNOC (x : Nat) (xs : List Nat) :
    MAX_LIST (SNOC x xs) = MAX (MAX_LIST xs) x := by
  rw [Aux.SNOC_eq, MAX_LIST_APPEND]
  simp [MAX_LIST, Aux.MAX_eq]

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
    apply Aux.set_ext
    intro x
    rw [List.foldl_cons, ih]
    simp only [Aux.mem_UNION, Aux.mem_LIST_TO_SET, Aux.mem_domain_insert, List.mem_cons]
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
  exact ⟨rfl, fun h t => rfl⟩

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
  | nil => intro f x; rfl
  | cons a t ih =>
    intro f x
    obtain ⟨a, b⟩ := a
    rw [(UPDATE_LIST_THM f).2, ih, List.reverse_cons, Aux.ALOOKUP_append]
    cases h : ALOOKUP t.reverse x with
    | some y => rfl
    | none => by_cases hx : a = x <;> simp [ALOOKUP, hx, UPDATE]

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
  | nil => intro n m h; simp at h
  | cons a t ih =>
    intro n m ⟨hd, hn⟩
    cases n with
    | zero => simp [EL, HD_def, find_index]
    | succ n =>
      have hn' : n < t.length := by simpa using hn
      have hmem : EL n t ∈ t := by rw [Aux.EL_eq n t hn']; exact List.getElem_mem hn'
      have hne : ¬ a = EL n t := fun e => hd.1 (e ▸ hmem)
      simp only [EL, TL, find_index, hne, if_false]
      rw [ih n (m + 1) ⟨hd.2, hn'⟩]
      congr 1; omega

/- HOL4:
Theorem find_index_shift_0:
   ∀ls x k. find_index x ls k = OPTION_MAP (λx. x + k) (find_index x ls 0) -/
theorem find_index_shift_0 {α : Type u} :
    ∀ (ls : List α) (x : α) (k : Nat),
      find_index x ls k = Option.map (fun x => x + k) (find_index x ls 0) := by
  intro ls
  induction ls with
  | nil => intro x k; rfl
  | cons a t ih =>
    intro x k
    by_cases h : a = x
    · simp [find_index, h]
    · simp only [find_index, h, if_false]
      rw [ih x (k + 1), ih x (0 + 1), Option.map_map]
      congr 1
      funext n
      simp only [Function.comp]
      omega

/- HOL4:
Theorem EVERY2_RC_same[simp]:
   EVERY2 (RC R) l l -/
theorem EVERY2_RC_same {α : Type u} (R : α → α → Prop) (l : List α) :
    EVERY2 (RC R) l l := by
  induction l with
  | nil => exact trivial
  | cons a t ih => exact ⟨Or.inl rfl, ih⟩

/- HOL4:
Theorem I_PERMUTES[simp]:
   I PERMUTES s -/
theorem I_PERMUTES {α : Type u} (s : Set α) : PERMUTES I s := by
  exact ⟨⟨fun x h => h, fun x y _ h => h⟩, ⟨fun x h => h, fun x h => ⟨x, h, rfl⟩⟩⟩

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
  obtain ⟨h1, h2⟩ := FUN_FMAP_DEF (FAPPLY (FEMPTY : fmap α β)) s hs
  by_cases hx : x ∈ s
  · exact h2 x hx
  · have hx' : ¬ x ∈ FDOM (FUN_FMAP (FAPPLY (FEMPTY : fmap α β)) s) := by rw [h1]; exact hx
    have hr : (FUN_FMAP (FAPPLY (FEMPTY : fmap α β)) s).rep x = none :=
      Classical.byContradiction fun h => hx' h
    have hg : ∀ g : fmap α β, g.rep x = none → FAPPLY g x = FAPPLY (FEMPTY : fmap α β) x := by
      intro g hg
      simp [FAPPLY, hg, FEMPTY]
    exact hg _ hr

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
  have : List.map (UNHEX ∘ HEX) (n2l 16 n) = n2l 16 n := by
    have h := Aux.n2l_lt 16 n (by omega)
    generalize n2l 16 n = l at h
    induction l with
    | nil => rfl
    | cons a t ih =>
      simp only [List.map_cons, Function.comp]
      rw [Aux.UNHEX_HEX a (h a List.mem_cons_self)]
      congr 1
      exact ih (fun d hd => h d (List.mem_cons_of_mem _ hd))
  rw [this, Aux.l2n_n2l 16 n (by omega)]

/- HOL4:
Theorem MAPi_ID[simp]:
   MAPi (\x y. y) = I -/
theorem MAPi_ID {α : Type u} : MAPi (fun (_x : Nat) (y : α) => y) = (I : List α → List α) := by
  funext l
  induction l with
  | nil => rfl
  | cons a t ih =>
    show a :: MAPi ((fun (_x : Nat) (y : α) => y) ∘ Nat.succ) t = a :: t
    exact congrArg (a :: ·) ih

/- HOL4:
Theorem OPT_MMAP_SOME[simp]:
   OPT_MMAP SOME ls = SOME ls -/
theorem OPT_MMAP_SOME {α : Type u} (ls : List α) : OPT_MMAP some ls = some ls := by
  induction ls with
  | nil => rfl
  | cons a t ih => simp [OPT_MMAP, ih]

/- HOL4:
Theorem w2n_lt_256 =
  [HOL4 proof text removed]
   (wordsTheory.w2n_lt is `!w:'a word. w2n w < dimword(:'a)`, so the theorem is
   `!w:word8. w2n w < 256`) -/
theorem w2n_lt_256 : ∀ (w : word8), w2n w < 256 := by
  intro w
  exact w.isLt

theorem Aux.CHR_w2n_n2w_ORD (c : char) : CHR (w2n ((n2w : Nat → word8) (ORD c))) = c := by
  have h : w2n ((n2w : Nat → word8) (ORD c)) = c.ord := by
    simp only [w2n, n2w, ORD, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt c.ord_lt
  rw [h, CHR_of_lt c.ord_lt]

theorem Aux.n2w_ORD_CHR_w2n (w : word8) : n2w (ORD (CHR (w2n w))) = w := by
  rw [CHR_of_lt (w2n_lt_256 w)]
  simp [n2w, w2n, ORD]

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
  | cons a t ih =>
    rw [Aux.FIELDS_cons]
    by_cases h : P a
    · simp [h, FILTER, ih]
    · simp only [h, FILTER, if_false]
      cases hf : FIELDS P t with
      | nil => rw [hf] at ih; simp at ih
      | cons f fs => rw [hf] at ih; simpa using ih

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
  | nil =>
    intro l1 l2 _ h
    simp at h
  | cons a t ih =>
    intro l1 l2 h hlen
    rw [Aux.FIELDS_cons] at h
    by_cases hp : P a
    · simp only [hp, if_true, List.cons.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨by simp, a, ⟨rfl, trivial⟩, hp⟩
    · simp only [hp, if_false] at h
      cases hf : FIELDS P t with
      | nil => exact absurd hf (FIELDS_NEQ_NIL P t)
      | cons f fs =>
        rw [hf] at h
        simp only [List.cons.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨h1, c, h2, h3⟩ := ih f fs hf (by simpa using hlen)
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
  [HOL4 proof text removed]
   (the theorem proved is `splitlines "" = []`) -/
theorem splitlines_nil : splitlines (str "") = [] := by
  have h : str "" = [] := by simp [str]
  simp [h, splitlines, FIELDS, LAST_DEF, NULL, FRONT]

/- HOL4:
Theorem splitlines_eq_nil[simp]:
   splitlines ls = [] ⇔ (ls = []) -/
theorem splitlines_eq_nil (ls : string) : splitlines ls = [] ↔ ls = [] := by
  constructor
  · intro h
    unfold splitlines at h
    dsimp only at h
    cases ls with
    | nil => rfl
    | cons a t =>
      exfalso
      rw [Aux.FIELDS_cons] at h
      have hne := FIELDS_NEQ_NIL (fun c => ch '\n' = c) t
      cases hf : FIELDS (fun c => ch '\n' = c) t with
      | nil => exact hne hf
      | cons f fs =>
        rw [hf] at h
        by_cases hp : ch '\n' = a
        · simp only [hp, if_true] at h
          split at h <;> simp [FRONT] at h
        · simp only [hp, if_false] at h
          split at h
          · rename_i hn
            simp only [FRONT] at h
            split at h
            · rename_i hfs
              subst hfs
              simp [LAST_DEF, NULL] at hn
            · simp at h
          · simp at h
  · intro h
    subst h
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
  rcases h (f a) (f b) with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (hi.2 a b ⟨trivial, trivial⟩ h))

/- HOL4:
Theorem plus_0_I[simp]:
   $+ 0n = I -/
theorem plus_0_I : (fun n : Nat => 0 + n) = (I : Nat → Nat) := by
  funext n
  simp

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
  · simp [h, EVEN]

/- HOL4:
Theorem v2w_32_F[simp]:
   (v2w [F] : word32) = 0w -/
theorem v2w_32_F : (v2w [False] : word32) = n2w 0 := by
  have h : (fun i => testbit i [False]) = fun _ => False := by
    funext i
    cases i <;> simp [testbit, field, fixwidth, shiftr, zero_extend, PAD_LEFT, GENLIST, SNOC]
  have h2 : ∀ n, FCP_bits n (fun _ => False) = 0 := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => simp [FCP_bits, ih]
  simp only [v2w, FCP, h, h2, n2w]

/- HOL4:
Theorem v2w_32_T[simp]:
   (v2w [T] : word32) = 1w -/
theorem v2w_32_T : (v2w [True] : word32) = n2w 1 := by
  have h : (fun i => testbit i [True]) = fun i => i = 0 := by
    funext i
    cases i <;> simp [testbit, field, fixwidth, shiftr, zero_extend, PAD_LEFT, GENLIST, SNOC]
  have h2 : ∀ n, FCP_bits (n + 1) (fun i => i = 0) = 1 := by
    intro n
    induction n with
    | zero => simp [FCP_bits]
    | succ n ih => rw [FCP_bits, ih]; simp
  simp only [v2w, FCP, h, h2 31, n2w]

/- HOL4:
Definition fmap_update_def[simp]:
  fmap_update f k v = f |+ (k,v)
End -/
def fmap_update {α : Type u} {β : Type v} (f : fmap α β) (k : α) (v : β) : fmap α β :=
  FUPDATE f (k, v)

end

end Candle
