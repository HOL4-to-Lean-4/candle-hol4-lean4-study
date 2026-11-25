import CmlTS.Prelude.PredSet

/-
HOL4 library constants from `list`, `rich_list` and `alist` that are not
mapped to a Lean core function.
-/

namespace CmlTS

noncomputable section

open scoped Classical

variable {α β γ : Type}

/- HOL4: list$NULL   (NULL [] = T) /\ (NULL (h::t) = F) -/
def NULL : List α → Prop
  | [] => True
  | _ :: _ => False

/- HOL4: list$HD   HD (h::t) = h   (unspecified on []) -/
def HD [Nonempty α] : List α → α
  | h :: _ => h
  | [] => ARB

/- HOL4: list$TL   TL [] = [] /\ TL (h::t) = t -/
def TL : List α → List α
  | [] => []
  | _ :: t => t

/- HOL4: list$EL   EL 0 l = HD l /\ EL (SUC n) l = EL n (TL l) -/
def EL [Nonempty α] : Nat → List α → α
  | 0, l => HD l
  | n + 1, l => EL n (TL l)

/- HOL4: list$oEL
   (oEL n [] = NONE) /\
   (oEL n (x::xs) = if n = 0 then SOME x else oEL (n - 1) xs) -/
def oEL : Nat → List α → Option α
  | _, [] => none
  | n, x :: xs => if n = 0 then some x else oEL (n - 1) xs

/- HOL4: list$LUPDATE
   LUPDATE e n [] = [] /\
   LUPDATE e n (x::l) = if n = 0 then e :: l else x :: LUPDATE e (PRE n) l -/
def LUPDATE (e : α) : Nat → List α → List α
  | _, [] => []
  | n, x :: l => if n = 0 then e :: l else x :: LUPDATE e (n - 1) l

/- HOL4: list$EVERY   (EVERY P [] <=> T) /\ (EVERY P (h::t) <=> P h /\ EVERY P t) -/
def EVERY (P : α → Prop) : List α → Prop
  | [] => True
  | h :: t => P h ∧ EVERY P t

/- HOL4: list$EXISTS   (EXISTS P [] <=> F) /\ (EXISTS P (h::t) <=> P h \/ EXISTS P t) -/
def EXISTS (P : α → Prop) : List α → Prop
  | [] => False
  | h :: t => P h ∨ EXISTS P t

/- HOL4: list$LIST_REL (overloaded as EVERY2)
   (LIST_REL R []      []      <=> T) /\
   (LIST_REL R (a::as) []      <=> F) /\
   (LIST_REL R []      (b::bs) <=> F) /\
   (LIST_REL R (a::as) (b::bs) <=> R a b /\ LIST_REL R as bs) -/
def LIST_REL (R : α → β → Prop) : List α → List β → Prop
  | [], [] => True
  | _ :: _, [] => False
  | [], _ :: _ => False
  | a :: as, b :: bs => R a b ∧ LIST_REL R as bs

/- HOL4: list$ALL_DISTINCT
   (ALL_DISTINCT [] <=> T) /\ (ALL_DISTINCT (h::t) <=> ~MEM h t /\ ALL_DISTINCT t) -/
def ALL_DISTINCT : List α → Prop
  | [] => True
  | h :: t => ¬ h ∈ t ∧ ALL_DISTINCT t

/- HOL4: list$isPREFIX (infix `<<=`, written `≼`)
   (isPREFIX [] l = T) /\
   (isPREFIX (h::t) l = case l of [] => F
                                | h'::t' => (h = h') /\ isPREFIX t t') -/
def isPREFIX : List α → List α → Prop
  | [], _ => True
  | h :: t, l =>
    match l with
    | [] => False
    | h' :: t' => h = h' ∧ isPREFIX t t'

/- HOL4: rich_list, Overload IS_PREFIX = ``\x y. isPREFIX y x`` -/
def IS_PREFIX (x y : List α) : Prop := isPREFIX y x

/- HOL4: list$REV   (REV [] acc = acc) /\ (REV (h::t) acc = REV t (h::acc)) -/
def REV : List α → List α → List α
  | [], acc => acc
  | h :: t, acc => REV t (h :: acc)

/- HOL4: rich_list$SPLITP
   (SPLITP P [] = ([],[])) /\
   (SPLITP P (CONS x l) =
      if P x then ([], CONS x l)
      else (CONS x (FST (SPLITP P l)), SND (SPLITP P l))) -/
def SPLITP (P : α → Prop) : List α → List α × List α
  | [] => ([], [])
  | x :: l => if P x then ([], x :: l) else (x :: (SPLITP P l).1, (SPLITP P l).2)

/- HOL4: rich_list$COUNT_LIST
   (COUNT_LIST 0 = []) /\ (COUNT_LIST (SUC n) = 0::MAP SUC (COUNT_LIST n)) -/
def COUNT_LIST : Nat → List Nat
  | 0 => []
  | n + 1 => 0 :: (COUNT_LIST n).map Nat.succ

/- HOL4: alist$ALOOKUP
   (ALOOKUP [] q = NONE) /\
   (ALOOKUP ((x,y)::t) q = if x = q then SOME y else ALOOKUP t q) -/
def ALOOKUP : List (α × β) → α → Option β
  | [], _ => none
  | (x, y) :: t, q => if x = q then some y else ALOOKUP t q

/-! Helper lemmas (not HOL4 constants); the two `wf_preprocess` ones let Lean's
termination checker see through `EVERY` as it does through `List.map`. -/

theorem EVERY_iff_forall {P : α → Prop} {l : List α} : EVERY P l ↔ ∀ x, x ∈ l → P x := by
  induction l with
  | nil => simp [EVERY]
  | cons h t ih => simp [EVERY, ih]

theorem EVERY_map_aux {P : β → Prop} {f : α → β} {l : List α} :
    EVERY P (l.map f) ↔ EVERY (fun x => P (f x)) l := by
  simp [EVERY_iff_forall]

@[wf_preprocess] theorem EVERY_wfParam {xs : List α} {f : α → Prop} :
    EVERY f (wfParam xs) = EVERY f xs.attach.unattach := by
  simp [wfParam]

@[wf_preprocess] theorem EVERY_unattach {P : α → Prop} {xs : List (Subtype P)} {f : α → Prop} :
    EVERY f xs.unattach = EVERY (fun ⟨x, h⟩ =>
      binderNameHint x f <| binderNameHint h () <| f (wfParam x)) xs := by
  apply propext
  rw [List.unattach, EVERY_map_aux]
  simp [wfParam, binderNameHint]

theorem LIST_REL_iff_aux {R : α → β → Prop} {l1 : List α} {l2 : List β} :
    LIST_REL R l1 l2 ↔
      l1.length = l2.length ∧ ∀ (i : Nat) a b, l1[i]? = some a → l2[i]? = some b → R a b := by
  induction l1 generalizing l2 with
  | nil => cases l2 <;> simp [LIST_REL]
  | cons x xs ih =>
    cases l2 with
    | nil => simp [LIST_REL]
    | cons y ys =>
      simp only [LIST_REL, ih, List.length_cons, Nat.add_right_cancel_iff]
      constructor
      · rintro ⟨h1, h2, h3⟩
        refine ⟨h2, ?_⟩
        intro i a b ha hb
        cases i with
        | zero => simp at ha hb; subst ha; subst hb; exact h1
        | succ i => exact h3 i a b (by simpa using ha) (by simpa using hb)
      · rintro ⟨h1, h2⟩
        refine ⟨h2 0 x y (by simp) (by simp), h1, ?_⟩
        intro i a b ha hb
        exact h2 (i + 1) a b (by simpa using ha) (by simpa using hb)

theorem SPLITP_length_aux (P : α → Prop) (l : List α) : (SPLITP P l).2.length ≤ l.length := by
  induction l with
  | nil => simp [SPLITP]
  | cons x l ih =>
    simp only [SPLITP]
    split
    · simp
    · simp; omega

theorem TL_length_aux (l : List α) : (TL l).length = l.length - 1 := by
  cases l <;> simp [TL]

end

end CmlTS
