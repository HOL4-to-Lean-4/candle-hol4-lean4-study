import CmlTS.Prelude.Set
import Batteries.Data.List.Basic
/-
  HOL4 library constants: `list`, `rich_list`, `alist`, `option`.
  (Constants that coincide with Lean core functions are used directly; see CONVENTIONS.md.)
-/
set_option autoImplicit false

namespace CmlTS
open Classical

universe u v w

/- HOL4: option$THE:  THE (SOME x) = x   (THE NONE is unspecified) -/
noncomputable def THE {α : Type u} [Nonempty α] : Option α → α
  | some x => x
  | none => ARB

/- HOL4: list$NULL:  (NULL [] = T) /\ (NULL (h::t) = F) -/
def NULL {α : Type u} : List α → Prop
  | [] => True
  | _ :: _ => False

/- HOL4: list$HD:  HD (h::t) = h    (HD [] = ARB) -/
noncomputable def HD {α : Type u} [Nonempty α] : List α → α
  | h :: _ => h
  | [] => ARB

/- HOL4: list$EL:  EL 0 l = (HD l:'a) /\ EL (SUC n) l = EL n (TL l) -/
noncomputable def EL {α : Type u} [Nonempty α] : Nat → List α → α
  | 0, l => HD l
  | n + 1, l => EL n l.tail

/- HOL4: list$EVERY:  (EVERY P [] <=> T) /\ (EVERY P (h::t) <=> P h /\ EVERY P t) -/
def EVERY {α : Type u} (P : α → Prop) : List α → Prop
  | [] => True
  | h :: t => P h ∧ EVERY P t

/- HOL4: list$EXISTS:  (EXISTS P [] <=> F) /\ (EXISTS P (h::t) <=> P h \/ EXISTS P t) -/
def EXISTS {α : Type u} (P : α → Prop) : List α → Prop
  | [] => False
  | h :: t => P h ∨ EXISTS P t

/- HOL4: list$LIST_REL (overloaded EVERY2):
   (LIST_REL R [] [] <=> T) /\ (LIST_REL R (a::as) [] <=> F) /\ (LIST_REL R [] (b::bs) <=> F) /\
   (LIST_REL R (a::as) (b::bs) <=> R a b /\ LIST_REL R as bs) -/
def LIST_REL {α : Type u} {β : Type v} (R : α → β → Prop) : List α → List β → Prop
  | [], [] => True
  | a :: as, b :: bs => R a b ∧ LIST_REL R as bs
  | _, _ => False

/-- HOL4: list$EVERY2 is an overload of LIST_REL. -/
abbrev EVERY2 {α : Type u} {β : Type v} (R : α → β → Prop) (l1 : List α) (l2 : List β) : Prop :=
  LIST_REL R l1 l2

/- HOL4: list$LIST_TO_SET (overloaded `set`); MEM x l = x IN LIST_TO_SET l -/
def LIST_TO_SET {α : Type u} (l : List α) : Set α := fun x => x ∈ l

/- HOL4: list$ALL_DISTINCT:
   (ALL_DISTINCT [] <=> T) /\ (ALL_DISTINCT (h::t) <=> ~MEM h t /\ ALL_DISTINCT t) -/
def ALL_DISTINCT {α : Type u} : List α → Prop
  | [] => True
  | h :: t => ¬ h ∈ t ∧ ALL_DISTINCT t

/- HOL4: list$REV:  (REV [] acc = acc) /\ (REV (h::t) acc = REV t (h::acc)) -/
def REV {α : Type u} : List α → List α → List α
  | [], acc => acc
  | h :: t, acc => REV t (h :: acc)

/- HOL4: rich_list$COUNT_LIST:
   (COUNT_LIST 0 = []) /\ (COUNT_LIST (SUC n) = 0::MAP SUC (COUNT_LIST n)) -/
def COUNT_LIST : Nat → List Nat
  | 0 => []
  | n + 1 => 0 :: (COUNT_LIST n).map Nat.succ

/- HOL4: rich_list$SPLITP:
   (SPLITP P [] = ([],[])) /\
   (SPLITP P (CONS x l) =
      if P x then ([], CONS x l) else (CONS x (FST (SPLITP P l)), SND (SPLITP P l))) -/
noncomputable def SPLITP {α : Type u} (P : α → Prop) : List α → List α × List α
  | [] => ([], [])
  | x :: l => if P x then ([], x :: l) else (x :: (SPLITP P l).1, (SPLITP P l).2)

/- HOL4: alist$ALOOKUP:
   (ALOOKUP [] q = NONE) /\ (ALOOKUP ((x,y)::t) q = if x = q then SOME y else ALOOKUP t q) -/
noncomputable def ALOOKUP {α : Type u} {β : Type v} : List (α × β) → α → Option β
  | [], _ => none
  | (x, y) :: t, q => if x = q then some y else ALOOKUP t q

/-! Support for recursion through `EVERY` in nested datatypes (no HOL4 counterpart;
    the analogue of HOL4's `EVERY_CONG`). -/

theorem EVERY_iff {α : Type u} {P : α → Prop} {l : List α} : EVERY P l ↔ ∀ x, x ∈ l → P x := by
  induction l with
  | nil => simp [EVERY]
  | cons h t ih => simp [EVERY, ih]

theorem EXISTS_iff {α : Type u} {P : α → Prop} {l : List α} : EXISTS P l ↔ ∃ x, x ∈ l ∧ P x := by
  induction l with
  | nil => simp [EXISTS]
  | cons h t ih => simp [EXISTS, ih]

theorem ALL_DISTINCT_iff {α : Type u} {l : List α} : ALL_DISTINCT l ↔ l.Nodup := by
  induction l with
  | nil => simp [ALL_DISTINCT]
  | cons h t ih => simp [ALL_DISTINCT, ih]

@[wf_preprocess] theorem EVERY_wfParam {α : Type u} {xs : List α} {P : α → Prop} :
    EVERY P (wfParam xs) = EVERY P xs.attach.unattach := by
  simp [wfParam]

@[wf_preprocess] theorem EVERY_unattach {α : Type u} {p : α → Prop} {xs : List (Subtype p)}
    {P : α → Prop} :
    EVERY P xs.unattach = EVERY (fun ⟨x, h⟩ =>
      binderNameHint x P <| binderNameHint h () <| P (wfParam x)) xs := by
  simp only [wfParam, binderNameHint, EVERY_iff, List.unattach, List.mem_map, Subtype.exists,
    exists_and_right, exists_eq_right, Subtype.forall, forall_exists_index]

theorem sizeOf_snd_lt_of_mem {α : Type u} {β : Type v} [SizeOf α] [SizeOf β]
    {x : α × β} {l : List (α × β)} (h : x ∈ l) : sizeOf x.2 < sizeOf l := by
  have := List.sizeOf_lt_of_mem h
  cases x
  simp at this ⊢
  omega

theorem sizeOf_snd_snd_lt_of_mem {α : Type u} {β : Type v} {γ : Type w}
    [SizeOf α] [SizeOf β] [SizeOf γ]
    {x : α × β × γ} {l : List (α × β × γ)} (h : x ∈ l) : sizeOf x.2.2 < sizeOf l := by
  have := List.sizeOf_lt_of_mem h
  obtain ⟨a, b, c⟩ := x
  simp at this ⊢
  omega

theorem sizeOf_list_reverse {α : Type u} [SizeOf α] (l : List α) :
    sizeOf l.reverse = sizeOf l := by
  have app : ∀ l1 l2 : List α, sizeOf (l1 ++ l2) + 1 = sizeOf l1 + sizeOf l2 := by
    intro l1 l2
    induction l1 with
    | nil => simp; omega
    | cons h t ih => simp at ih ⊢; omega
  induction l with
  | nil => simp
  | cons h t ih =>
    have := app t.reverse [h]
    simp at this ⊢
    omega

end CmlTS
