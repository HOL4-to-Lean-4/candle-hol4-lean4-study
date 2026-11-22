/-
  HOL4 library constants from the theories `list`, `rich_list`, `indexedLists`,
  `alist`, `sorting`, `option`.

  HOL4 list constants that coincide exactly with Lean core functions are not
  redefined (see CONVENTIONS.md): `[]`, `h::t`, `++` (APPEND), `List.length`
  (LENGTH), `List.map` (MAP), `List.reverse` (REVERSE), `List.take` (TAKE),
  `List.drop` (DROP), `List.foldr` (FOLDR), `List.foldl` (FOLDL),
  `Option.map` (OPTION_MAP), `Option.bind` (OPTION_BIND).
-/
import CandleLean.Prelude.Set

open Classical

/- HOL4: list$LIST_TO_SET
   (!x. LIST_TO_SET [] x <=> F) /\
   (!h t x. LIST_TO_SET (h::t) x <=> (x = h) \/ LIST_TO_SET t x) -/
def LIST_TO_SET {α : Type u} : List α → Set α
  | [] => fun _ => False
  | h :: t => fun x => x = h ∨ LIST_TO_SET t x

/- HOL4: list `Overload set = “LIST_TO_SET”`
   In Lean `set` is notation (a macro) for `LIST_TO_SET`; a plain definition
   named `set` would be ambiguous with Lean's exported `MonadStateOf.set`. -/
macro "set" : term => `(LIST_TO_SET)

/- HOL4: list `Overload MEM = “\h:'a l:'a list. h IN LIST_TO_SET l”` -/
abbrev MEM {α : Type u} (h : α) (l : List α) : Prop := h ∈ LIST_TO_SET l

/- HOL4: list$NULL   (NULL [] = T) /\ (NULL (h::t) = F) -/
def NULL {α : Type u} : List α → Prop
  | [] => True
  | _ :: _ => False

/- HOL4: list$HD   `HD (h::t) = h`   (HD [] = ARB by pattern completion) -/
noncomputable def HD {α : Type u} [Nonempty α] : List α → α
  | h :: _ => h
  | [] => ARB

/- HOL4: list$TL   TL [] = [] /\ TL (h::t) = t -/
def TL {α : Type u} : List α → List α
  | [] => []
  | _ :: t => t

/- HOL4: list$EL   EL 0 l = (HD l:'a) /\ EL (SUC n) l = EL n (TL l) -/
noncomputable def EL {α : Type u} [Nonempty α] : Nat → List α → α
  | 0, l => HD l
  | n + 1, l => EL n (TL l)

/- HOL4: list$FLAT   FLAT [] = [] /\ FLAT (h::t) = APPEND h (FLAT t) -/
def FLAT {α : Type u} : List (List α) → List α
  | [] => []
  | h :: t => h ++ FLAT t

/- HOL4: list$FILTER
   FILTER P [] = [] /\
   FILTER P (h::t) = if P h then (h::FILTER P t) else FILTER P t -/
noncomputable def FILTER {α : Type u} (P : α → Prop) : List α → List α
  | [] => []
  | h :: t => if P h then h :: FILTER P t else FILTER P t

/- HOL4: list$EVERY   (EVERY P [] <=> T) /\ (EVERY P (h::t) <=> P h /\ EVERY P t) -/
def EVERY {α : Type u} (P : α → Prop) : List α → Prop
  | [] => True
  | h :: t => P h ∧ EVERY P t

/- HOL4: list$EXISTS   (EXISTS P [] <=> F) /\ (EXISTS P (h::t) <=> P h \/ EXISTS P t) -/
def EXISTS {α : Type u} (P : α → Prop) : List α → Prop
  | [] => False
  | h :: t => P h ∨ EXISTS P t

/- HOL4: list$ALL_DISTINCT
   (ALL_DISTINCT [] <=> T) /\ (ALL_DISTINCT (h::t) <=> ~MEM h t /\ ALL_DISTINCT t) -/
def ALL_DISTINCT {α : Type u} : List α → Prop
  | [] => True
  | h :: t => ¬ MEM h t ∧ ALL_DISTINCT t

/- HOL4: list$ZIP
   (!l2. ZIP ([], l2) = []) /\ (!l1. ZIP (l1, []) = []) /\
   (!x1 l1 x2 l2. ZIP ((CONS x1 l1), (CONS x2 l2)) = CONS (x1,x2) (ZIP (l1, l2)))
   (HOL4's ZIP takes a pair; it truncates exactly like `List.zip`.) -/
def ZIP {α : Type u} {β : Type v} : List α × List β → List (α × β)
  | ([], _) => []
  | (_ :: _, []) => []
  | (x1 :: l1, x2 :: l2) => (x1, x2) :: ZIP (l1, l2)

/- HOL4: list$LAST   `LAST (h::t) = if t = [] then h else LAST t`   (LAST [] = ARB) -/
noncomputable def LAST {α : Type u} [Nonempty α] : List α → α
  | [] => ARB
  | h :: t => if t = [] then h else LAST t

/- HOL4: list$FRONT   FRONT [] = [] /\ FRONT (h::t) = if t = [] then [] else h :: FRONT t -/
noncomputable def FRONT {α : Type u} : List α → List α
  | [] => []
  | h :: t => if t = [] then [] else h :: FRONT t

/- HOL4: list$SNOC   (SNOC x [] = [x]) /\ (SNOC x (CONS x' l) = CONS x' (SNOC x l)) -/
def SNOC {α : Type u} (x : α) : List α → List α
  | [] => [x]
  | x' :: l => x' :: SNOC x l

/- HOL4: list$GENLIST   GENLIST (f:num->'a) 0 = [] /\ GENLIST f (SUC n) = SNOC (f n) (GENLIST f n) -/
def GENLIST {α : Type u} (f : Nat → α) : Nat → List α
  | 0 => []
  | n + 1 => SNOC (f n) (GENLIST f n)

/- HOL4: list$REV   (REV [] acc = acc) /\ (REV (h::t) acc = REV t (h::acc)) -/
def REV {α : Type u} : List α → List α → List α
  | [], acc => acc
  | h :: t, acc => REV t (h :: acc)

/- HOL4: list$LIST_REL   (Overload EVERY2 = LIST_REL)
   (LIST_REL R [] [] <=> T) /\ (LIST_REL R (a::as) [] <=> F) /\
   (LIST_REL R [] (b::bs) <=> F) /\ (LIST_REL R (a::as) (b::bs) <=> R a b /\ LIST_REL R as bs) -/
def LIST_REL {α : Type u} {β : Type v} (R : α → β → Prop) : List α → List β → Prop
  | [], [] => True
  | _ :: _, [] => False
  | [], _ :: _ => False
  | a :: as, b :: bs => R a b ∧ LIST_REL R as bs

/- HOL4: list `EVERY2` is an overload of `LIST_REL` -/
abbrev EVERY2 {α : Type u} {β : Type v} (R : α → β → Prop) : List α → List β → Prop := LIST_REL R

/- HOL4: list$isPREFIX   (notation `l1 ≼ l2`, `<<=`)
   (isPREFIX [] l = T) /\
   (isPREFIX (h::t) l = case l of [] => F | h'::t' => (h = h') /\ isPREFIX t t') -/
def isPREFIX {α : Type u} : List α → List α → Prop
  | [], _ => True
  | _ :: _, [] => False
  | h :: t, h' :: t' => h = h' ∧ isPREFIX t t'

/- HOL4: list$LLEX
   (LLEX R [] l2 <=> l2 <> []) /\
   (LLEX R (h1::t1) l2 <=> case l2 of [] => F
                          | h2::t2 => if R h1 h2 then T else if h1 = h2 then LLEX R t1 t2 else F) -/
noncomputable def LLEX {α : Type u} (R : α → α → Prop) : List α → List α → Prop
  | [], l2 => l2 ≠ []
  | _ :: _, [] => False
  | h1 :: t1, h2 :: t2 => if R h1 h2 then True else if h1 = h2 then LLEX R t1 t2 else False

/- HOL4: list$OPT_MMAP
   (OPT_MMAP f [] = SOME []) /\
   (OPT_MMAP f (h0::t0) = OPTION_BIND (f h0) (\h. OPTION_BIND (OPT_MMAP f t0) (\t. SOME (h::t)))) -/
def OPT_MMAP {α : Type u} {β : Type v} (f : α → Option β) : List α → Option (List β)
  | [] => some []
  | h0 :: t0 => (f h0).bind (fun h => (OPT_MMAP f t0).bind (fun t => some (h :: t)))

/- HOL4: rich_list$SPLITP
   (SPLITP P [] = ([],[])) /\
   (SPLITP P (CONS x l) = if P x then ([], CONS x l)
                          else (CONS x (FST (SPLITP P l)), SND (SPLITP P l))) -/
noncomputable def SPLITP {α : Type u} (P : α → Prop) : List α → List α × List α
  | [] => ([], [])
  | x :: l => if P x then ([], x :: l) else (x :: (SPLITP P l).1, (SPLITP P l).2)

/- HOL4: rich_list$SEG  (new_specification)
   ?SEG. (!k (l:'a list). SEG 0 k l = []) /\
         (!m x l. SEG (SUC m) 0 (CONS x l) = CONS x (SEG m 0 l)) /\
         (!m k x l. SEG (SUC m) (SUC k) (CONS x l) = SEG (SUC m) k l)
   `SEG (SUC m) k []` is unspecified: encoded as a choice over all functions
   satisfying the specification. -/
noncomputable def SEG {α : Type u} : Nat → Nat → List α → List α :=
  Classical.epsilon (fun SEG : Nat → Nat → List α → List α =>
    (∀ k l, SEG 0 k l = []) ∧
    (∀ m x l, SEG (m + 1) 0 (x :: l) = x :: SEG m 0 l) ∧
    (∀ m k x l, SEG (m + 1) (k + 1) (x :: l) = SEG (m + 1) k l))

/- HOL4: rich_list$MAX_LIST   (MAX_LIST [] = 0) /\ (MAX_LIST (h::t) = MAX h (MAX_LIST t)) -/
def MAX_LIST : List Nat → Nat
  | [] => 0
  | h :: t => MAX h (MAX_LIST t)

/- HOL4: indexedLists$MAPi
   (MAPi f [] = []) /\ (MAPi f (h::t) = f 0 h :: MAPi (f o SUC) t) -/
def MAPi {α : Type u} {β : Type v} : (Nat → α → β) → List α → List β
  | _, [] => []
  | f, h :: t => f 0 h :: MAPi (f ∘ Nat.succ) t

/- HOL4: alist$ALOOKUP
   (ALOOKUP [] q = NONE) /\ (ALOOKUP ((x,y)::t) q = if x = q then SOME y else ALOOKUP t q) -/
noncomputable def ALOOKUP {α : Type u} {β : Type v} : List (α × β) → α → Option β
  | [], _ => none
  | (x, y) :: t, q => if x = q then some y else ALOOKUP t q

/- HOL4: sorting$PERM   `PERM L1 L2 = !x. FILTER ($= x) L1 = FILTER ($= x) L2` -/
def PERM {α : Type u} (L1 L2 : List α) : Prop :=
  ∀ x, FILTER (fun y => x = y) L1 = FILTER (fun y => x = y) L2

/- HOL4: sorting$SORTED
   (SORTED R [] = T) /\ (SORTED R [x] = T) /\
   (SORTED R (x::y::rst) <=> R x y /\ SORTED R (y::rst)) -/
def SORTED {α : Type u} (R : α → α → Prop) : List α → Prop
  | [] => True
  | [_] => True
  | x :: y :: rst => R x y ∧ SORTED R (y :: rst)

/-! Well-founded-recursion preprocessing for `EVERY` (not HOL4 constants; needed
so that definitions recursing through `EVERY f args` on nested datatypes are
accepted, in the same way Lean core handles `List.map`). -/

theorem EVERY_attach_unattach {α : Type u} {Q : α → Prop} (P : α → Prop) :
    ∀ xs : List (Subtype Q), EVERY P xs.unattach = EVERY (fun x => P x.1) xs
  | [] => rfl
  | x :: xs => by
    simp only [List.unattach_cons, EVERY]
    rw [EVERY_attach_unattach P xs]

@[wf_preprocess] theorem EVERY_wfParam {α : Type u} {xs : List α} {P : α → Prop} :
    EVERY P (wfParam xs) = EVERY P xs.attach.unattach := by
  simp [wfParam]

@[wf_preprocess] theorem EVERY_unattach {α : Type u} {Q : α → Prop} {xs : List (Subtype Q)}
    {P : α → Prop} :
    EVERY P xs.unattach = EVERY (fun ⟨x, h⟩ =>
      binderNameHint x P <| binderNameHint h () <| P (wfParam x)) xs := by
  rw [EVERY_attach_unattach]; simp [wfParam, binderNameHint]
