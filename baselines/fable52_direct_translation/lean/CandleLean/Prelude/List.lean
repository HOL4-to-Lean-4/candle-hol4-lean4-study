/-
  HOL4 library constants: list, rich_list, indexedLists, sorting, alist (ALOOKUP).

  HOL `'a list` is Lean `List α`; `[]`, `h::t`, `[a;b;c]` are `[]`, `h :: t`, `[a, b, c]`.
  HOL `l1 ++ l2` (`APPEND`) is Lean `l1 ++ l2`.
-/
import CandleLean.Prelude.PredSet

namespace Candle

noncomputable section
open Classical

/- HOL4: list$NULL_DEF  |- (NULL [] = T) /\ (NULL (h::t) = F) -/
def NULL {α : Type} : List α → Prop
  | [] => True
  | _ :: _ => False

/- HOL4: list$HD  |- HD (h::t) = h
   (`Definition` with a constructor argument and a missing clause goes through
   `Prim_rec.new_recursive_definition`: `HD []` is unspecified, so `HD` is an arbitrary
   function that satisfies the clause.) -/
def HD {α : Type} [Nonempty α] : List α → α :=
  select (fun f => ∀ h t, f (h :: t) = h)

/- HOL4: list$HD (the defining theorem of `HD`) -/
theorem HD_def {α : Type} [Nonempty α] (h : α) (t : List α) : HD (h :: t) = h :=
  select_spec (P := fun f : List α → α => ∀ h t, f (h :: t) = h)
    ⟨fun l => match l with | h :: _ => h | [] => ARB, fun _ _ => rfl⟩ h t

/- HOL4: list$TL_DEF  |- (TL [] = []) /\ (TL (h::t) = t) -/
def TL {α : Type} : List α → List α
  | [] => []
  | _ :: t => t

/- HOL4: list$APPEND_def  |- (APPEND [] l = l) /\ (APPEND (h::l1) l2 = h::APPEND l1 l2)
   (HOL `l1 ++ l2`; Lean `l1 ++ l2`) -/
abbrev APPEND {α : Type} (l1 l2 : List α) : List α := l1 ++ l2

/- HOL4: list$FLAT  |- (FLAT [] = []) /\ (FLAT (h::t) = APPEND h (FLAT t)) -/
abbrev FLAT {α : Type} (l : List (List α)) : List α := List.flatten l

/- HOL4: list$LENGTH  |- (LENGTH [] = 0) /\ (LENGTH (h::t) = SUC (LENGTH t)) -/
abbrev LENGTH {α : Type} (l : List α) : Nat := List.length l

/- HOL4: list$MAP  |- (!f. MAP f [] = []) /\ (!f h t. MAP f (h::t) = f h::MAP f t) -/
abbrev MAP {α β : Type} (f : α → β) (l : List α) : List β := List.map f l

/- HOL4: list$LIST_TO_SET_DEF
   |- (!x. LIST_TO_SET [] x <=> F) /\ (!h t x. LIST_TO_SET (h::t) x <=> (x = h) \/ LIST_TO_SET t x)
   (HOL `Overload set = “LIST_TO_SET”`.)  Stated with Lean's list membership, which satisfies
   exactly these two clauses (`List.not_mem_nil`, `List.mem_cons`). -/
def LIST_TO_SET {α : Type} (l : List α) : Set α := fun x => x ∈ l

/- HOL4: list  Overload set = “LIST_TO_SET” -/
abbrev set {α : Type} (l : List α) : Set α := LIST_TO_SET l

/- HOL4: list  Overload MEM = “\h:'a l:'a list. h IN LIST_TO_SET l”
   (`MEM x l` unfolds to Lean's `x ∈ l`, which is `x ∈ LIST_TO_SET l` by `Iff.rfl`.) -/
abbrev MEM {α : Type} (x : α) (l : List α) : Prop := x ∈ l

/- HOL4: list  Overload MEM (see above): `MEM x l` is `x IN LIST_TO_SET l`. -/
theorem MEM_def {α : Type} (x : α) (l : List α) : MEM x l ↔ x ∈ LIST_TO_SET l := Iff.rfl

/- HOL4: list$FILTER
   |- (FILTER P [] = []) /\ (FILTER P (h::t) = if P h then h::FILTER P t else FILTER P t) -/
def FILTER {α : Type} (P : α → Prop) : List α → List α
  | [] => []
  | h :: t => if P h then h :: FILTER P t else FILTER P t

/- HOL4: list$FOLDR  |- (FOLDR f e [] = e) /\ (FOLDR f e (x::l) = f x (FOLDR f e l)) -/
abbrev FOLDR {α β : Type} (f : α → β → β) (e : β) (l : List α) : β := List.foldr f e l

/- HOL4: list$FOLDL  |- (FOLDL f e [] = e) /\ (FOLDL f e (x::l) = FOLDL f (f e x) l) -/
abbrev FOLDL {α β : Type} (f : β → α → β) (e : β) (l : List α) : β := List.foldl f e l

/- HOL4: list$EVERY_DEF  |- (EVERY P [] <=> T) /\ (EVERY P (h::t) <=> P h /\ EVERY P t) -/
def EVERY {α : Type} (P : α → Prop) : List α → Prop
  | [] => True
  | h :: t => P h ∧ EVERY P t

/- HOL4: list$EXISTS_DEF  |- (EXISTS P [] <=> F) /\ (EXISTS P (h::t) <=> P h \/ EXISTS P t) -/
def EXISTS {α : Type} (P : α → Prop) : List α → Prop
  | [] => False
  | h :: t => P h ∨ EXISTS P t

/- HOL4: list$EL_def  |- (EL 0 l = HD l) /\ (EL (SUC n) l = EL n (TL l)) -/
def EL {α : Type} [Nonempty α] : Nat → List α → α
  | 0, l => HD l
  | n + 1, l => EL n (TL l)

/- HOL4: list$LIST_REL_def
   |- (LIST_REL R [] [] <=> T) /\ (LIST_REL R (a::as) [] <=> F) /\
      (LIST_REL R [] (b::bs) <=> F) /\ (LIST_REL R (a::as) (b::bs) <=> R a b /\ LIST_REL R as bs)
   (HOL `EVERY2` is an overload of `LIST_REL`) -/
def LIST_REL {α β : Type} (R : α → β → Prop) : List α → List β → Prop
  | [], [] => True
  | _ :: _, [] => False
  | [], _ :: _ => False
  | a :: as, b :: bs => R a b ∧ LIST_REL R as bs

/- HOL4: list  Overload EVERY2 = “LIST_REL” -/
abbrev EVERY2 {α β : Type} (R : α → β → Prop) (l1 : List α) (l2 : List β) : Prop :=
  LIST_REL R l1 l2

/- HOL4: list$ZIP_def
   |- (!l2. ZIP ([],l2) = []) /\ (!l1. ZIP (l1,[]) = []) /\
      (!x1 l1 x2 l2. ZIP (x1::l1,x2::l2) = (x1,x2)::ZIP (l1,l2)) -/
def ZIP {α β : Type} : List α × List β → List (α × β)
  | ([], _) => []
  | (_ :: _, []) => []
  | (x1 :: l1, x2 :: l2) => (x1, x2) :: ZIP (l1, l2)

/- HOL4: list$REVERSE_DEF  |- (REVERSE [] = []) /\ (REVERSE (h::t) = REVERSE t ++ [h]) -/
abbrev REVERSE {α : Type} (l : List α) : List α := List.reverse l

/- HOL4: list$REV_DEF  |- (REV [] acc = acc) /\ (REV (h::t) acc = REV t (h::acc)) -/
def REV {α : Type} : List α → List α → List α
  | [], acc => acc
  | h :: t, acc => REV t (h :: acc)

/- HOL4: list$LAST_DEF  |- LAST (h::t) = if t = [] then h else LAST t
   (`Prim_rec.new_recursive_definition` with a missing clause: `LAST []` is unspecified, so
   `LAST` is an arbitrary function that satisfies the clause.) -/
def LAST {α : Type} [Nonempty α] : List α → α :=
  select (fun f => ∀ h t, f (h :: t) = if t = [] then h else f t)

/-- Witness for the existence of `LAST`. -/
private def LAST_witness {α : Type} [Nonempty α] : List α → α
  | [] => ARB
  | [h] => h
  | _ :: h' :: t => LAST_witness (h' :: t)

/- HOL4: list$LAST_DEF (the defining theorem of `LAST`) -/
theorem LAST_DEF {α : Type} [Nonempty α] (h : α) (t : List α) :
    LAST (h :: t) = if t = [] then h else LAST t :=
  select_spec (P := fun f : List α → α => ∀ h t, f (h :: t) = if t = [] then h else f t)
    ⟨LAST_witness, fun h t => by cases t <;> simp [LAST_witness]⟩ h t

/- HOL4: list$FRONT_DEF
   |- (FRONT [] = []) /\ (FRONT (h::t) = if t = [] then [] else h::FRONT t) -/
def FRONT {α : Type} : List α → List α
  | [] => []
  | h :: t => if t = [] then [] else h :: FRONT t

/- HOL4: list$TAKE_def
   |- (TAKE n [] = []) /\ (TAKE n (x::xs) = if n = 0 then [] else x::TAKE (n - 1) xs) -/
abbrev TAKE {α : Type} (n : Nat) (l : List α) : List α := List.take n l

/- HOL4: list$DROP_def
   |- (DROP n [] = []) /\ (DROP n (x::xs) = if n = 0 then x::xs else DROP (n - 1) xs) -/
abbrev DROP {α : Type} (n : Nat) (l : List α) : List α := List.drop n l

/- HOL4: list$ALL_DISTINCT
   |- (ALL_DISTINCT [] <=> T) /\ (ALL_DISTINCT (h::t) <=> ~MEM h t /\ ALL_DISTINCT t) -/
def ALL_DISTINCT {α : Type} : List α → Prop
  | [] => True
  | h :: t => ¬ MEM h t ∧ ALL_DISTINCT t

/- HOL4: list$isPREFIX
   |- (isPREFIX [] l = T) /\
      (isPREFIX (h::t) l = case l of [] => F | h'::t' => (h = h') /\ isPREFIX t t')
   (HOL infix `l1 <<= l2`, `l1 ≼ l2`) -/
def isPREFIX {α : Type} : List α → List α → Prop
  | [], _ => True
  | h :: t, l => match l with
    | [] => False
    | h' :: t' => h = h' ∧ isPREFIX t t'

/- HOL4: list$SNOC  |- (SNOC x [] = [x]) /\ (SNOC x (x'::l) = x'::SNOC x l) -/
def SNOC {α : Type} (x : α) : List α → List α
  | [] => [x]
  | x' :: l => x' :: SNOC x l

/- HOL4: list$GENLIST  |- (GENLIST f 0 = []) /\ (GENLIST f (SUC n) = SNOC (f n) (GENLIST f n)) -/
def GENLIST {α : Type} (f : Nat → α) : Nat → List α
  | 0 => []
  | n + 1 => SNOC (f n) (GENLIST f n)

/- HOL4: list$PAD_LEFT  |- PAD_LEFT c n s = GENLIST (K c) (n - LENGTH s) ++ s -/
def PAD_LEFT {α : Type} (c : α) (n : Nat) (s : List α) : List α :=
  GENLIST (K c) (n - LENGTH s) ++ s

/- HOL4: list$LLEX_def
   |- (LLEX R [] l2 <=> l2 <> []) /\
      (LLEX R (h1::t1) l2 <=>
         case l2 of [] => F
                  | h2::t2 => if R h1 h2 then T else if h1 = h2 then LLEX R t1 t2 else F) -/
def LLEX {α : Type} (R : α → α → Prop) : List α → List α → Prop
  | [], l2 => l2 ≠ []
  | h1 :: t1, l2 => match l2 with
    | [] => False
    | h2 :: t2 => if R h1 h2 then True else if h1 = h2 then LLEX R t1 t2 else False

/- HOL4: list$OPT_MMAP_def
   |- (OPT_MMAP f [] = SOME []) /\
      (OPT_MMAP f (h0::t0) =
         OPTION_BIND (f h0) (\h. OPTION_BIND (OPT_MMAP f t0) (\t. SOME (h::t)))) -/
def OPT_MMAP {α β : Type} (f : α → Option β) : List α → Option (List β)
  | [] => some []
  | h0 :: t0 => OPTION_BIND (f h0) (fun h => OPTION_BIND (OPT_MMAP f t0) (fun t => some (h :: t)))

/- HOL4: rich_list$MAX_LIST_def
   |- (MAX_LIST [] = 0) /\ (MAX_LIST (h::t) = MAX h (MAX_LIST t)) -/
def MAX_LIST : List Nat → Nat
  | [] => 0
  | h :: t => MAX h (MAX_LIST t)

/- HOL4: rich_list$SEG
   |- (!k l. SEG 0 k l = []) /\
      (!m x l. SEG (SUC m) 0 (x::l) = x::SEG m 0 l) /\
      (!m k x l. SEG (SUC m) (SUC k) (x::l) = SEG (SUC m) k l)
   (`new_specification`: `SEG` is an arbitrary function that satisfies these clauses;
   `SEG (SUC m) k []` is unspecified.) -/
def SEG {α : Type} : Nat → Nat → List α → List α :=
  select (fun f =>
    (∀ k l, f 0 k l = []) ∧
    (∀ m x l, f (m + 1) 0 (x :: l) = x :: f m 0 l) ∧
    (∀ m k x l, f (m + 1) (k + 1) (x :: l) = f (m + 1) k l))

/- HOL4: rich_list$SEG (the defining theorem of `SEG`) -/
theorem SEG_def {α : Type} :
    (∀ k (l : List α), SEG 0 k l = []) ∧
    (∀ m x (l : List α), SEG (m + 1) 0 (x :: l) = x :: SEG m 0 l) ∧
    (∀ m k x (l : List α), SEG (m + 1) (k + 1) (x :: l) = SEG (m + 1) k l) :=
  select_spec (P := fun f : Nat → Nat → List α → List α =>
    (∀ k l, f 0 k l = []) ∧
    (∀ m x l, f (m + 1) 0 (x :: l) = x :: f m 0 l) ∧
    (∀ m k x l, f (m + 1) (k + 1) (x :: l) = f (m + 1) k l))
    ⟨fun m k l => List.take m (List.drop k l), by simp⟩

/- HOL4: rich_list$SPLITP
   |- (SPLITP P [] = ([],[])) /\
      (SPLITP P (x::l) = if P x then ([],x::l) else (x::FST (SPLITP P l),SND (SPLITP P l))) -/
def SPLITP {α : Type} (P : α → Prop) : List α → List α × List α
  | [] => ([], [])
  | x :: l => if P x then ([], x :: l) else (x :: FST (SPLITP P l), SND (SPLITP P l))

/- HOL4: indexedLists$MAPi_def
   |- (MAPi f [] = []) /\ (MAPi f (h::t) = f 0 h::MAPi (f o SUC) t) -/
def MAPi {α β : Type} : (Nat → α → β) → List α → List β
  | _, [] => []
  | f, h :: t => f 0 h :: MAPi (f ∘ SUC) t

/- HOL4: sorting$PERM_DEF  |- PERM L1 L2 <=> !x. FILTER ($= x) L1 = FILTER ($= x) L2 -/
def PERM {α : Type} (L1 L2 : List α) : Prop :=
  ∀ x, FILTER (fun y => x = y) L1 = FILTER (fun y => x = y) L2

/- HOL4: sorting$SORTED_DEF
   |- (SORTED R [] <=> T) /\ (SORTED R [x] <=> T) /\
      (SORTED R (x::y::rst) <=> R x y /\ SORTED R (y::rst)) -/
def SORTED {α : Type} (R : α → α → Prop) : List α → Prop
  | [] => True
  | [_] => True
  | x :: y :: rst => R x y ∧ SORTED R (y :: rst)

/- HOL4: alist$ALOOKUP_def
   |- (ALOOKUP [] q = NONE) /\ (ALOOKUP ((x,y)::t) q = if x = q then SOME y else ALOOKUP t q) -/
def ALOOKUP {α β : Type} : List (α × β) → α → Option β
  | [], _ => none
  | (x, y) :: t, q => if x = q then some y else ALOOKUP t q

end

end Candle
