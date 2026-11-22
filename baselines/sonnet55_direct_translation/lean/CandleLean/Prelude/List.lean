import CandleLean.Prelude.Basic
/-
  HOL4 library constants, part 2: lists (listTheory, rich_listTheory, sortingTheory,
  indexedListsTheory, alistTheory).  Namespace `HOL`, HOL4 names.
  Partial HOL4 functions (HD, LAST, EL, ...) take an `[Inhabited α]` and return `default`
  (= `ARB`) outside their specified domain.
-/
namespace HOL

universe u v w

open Classical

noncomputable section

variable {α : Type u} {β : Type v} {γ : Type w}

/- HOL4: listTheory LENGTH, MAP, APPEND (infix ++), FLAT, REVERSE, FOLDR, FOLDL
   are plain structural recursions that agree with the Lean core functions. -/
abbrev LENGTH : List α → Nat := List.length
abbrev MAP : (α → β) → List α → List β := List.map
abbrev APPEND : List α → List α → List α := List.append
abbrev FLAT : List (List α) → List α := List.flatten
abbrev REVERSE : List α → List α := List.reverse
/- HOL4: FOLDR f e [] = e; FOLDR f e (x::l) = f x (FOLDR f e l) -/
abbrev FOLDR (f : α → β → β) (e : β) (l : List α) : β := List.foldr f e l
/- HOL4: FOLDL f e [] = e; FOLDL f e (x::l) = FOLDL f (f e x) l -/
abbrev FOLDL (f : β → α → β) (e : β) (l : List α) : β := List.foldl f e l

/- HOL4: LIST_TO_SET_DEF: LIST_TO_SET [] = {}; LIST_TO_SET (h::t) = h INSERT LIST_TO_SET t
   (HOL4 `Overload set = LIST_TO_SET`; the Lean name is `LIST_TO_SET`, because `set` is taken by
   `MonadStateOf.set`) -/
def LIST_TO_SET (l : List α) : Set α := fun x => x ∈ l
/- HOL4: Overload MEM = λh l. h IN LIST_TO_SET l -/
def MEM (x : α) (l : List α) : Prop := x ∈ LIST_TO_SET l

theorem MEM_iff (x : α) (l : List α) : MEM x l ↔ x ∈ l := Iff.rfl
@[simp] theorem MEM_nil (x : α) : MEM x ([] : List α) ↔ False := by
  rw [MEM_iff]; simp
@[simp] theorem MEM_cons (x a : α) (l : List α) : MEM x (a :: l) ↔ x = a ∨ MEM x l := by
  rw [MEM_iff, MEM_iff]; simp

/- HOL4: NULL_DEF -/
def NULL : List α → Prop
  | [] => True
  | _ :: _ => False

/- HOL4: HD (h::t) = h  (HD [] unspecified) -/
def HD [Inhabited α] : List α → α
  | [] => ARB
  | h :: _ => h
/- HOL4: TL (h::t) = t  (TL [] unspecified; here []) -/
def TL : List α → List α
  | [] => []
  | _ :: t => t

/- HOL4: FILTER P [] = []; FILTER P (h::t) = if P h then h::FILTER P t else FILTER P t -/
def FILTER (P : α → Prop) : List α → List α
  | [] => []
  | h :: t => if P h then h :: FILTER P t else FILTER P t

theorem MEM_FILTER (P : α → Prop) (l : List α) (x : α) : MEM x (FILTER P l) ↔ MEM x l ∧ P x := by
  induction l with
  | nil => simp [FILTER]
  | cons h t ih =>
    unfold FILTER
    by_cases hp : P h
    · simp only [hp, if_true, MEM_cons, ih]
      constructor
      · rintro (rfl | ⟨h1, h2⟩)
        · exact ⟨Or.inl rfl, hp⟩
        · exact ⟨Or.inr h1, h2⟩
      · rintro ⟨h1 | h1, h2⟩
        · subst h1; exact Or.inl rfl
        · exact Or.inr ⟨h1, h2⟩
    · simp only [hp, if_false, MEM_cons, ih]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨Or.inr h1, h2⟩
      · rintro ⟨h1 | h1, h2⟩
        · subst h1; exact absurd h2 hp
        · exact ⟨h1, h2⟩

/- HOL4: EVERY_DEF -/
def EVERY (P : α → Prop) : List α → Prop
  | [] => True
  | h :: t => P h ∧ EVERY P t
/- HOL4: EXISTS_DEF -/
def EXISTS (P : α → Prop) : List α → Prop
  | [] => False
  | h :: t => P h ∨ EXISTS P t

/- HOL4: EL 0 l = HD l; EL (SUC n) l = EL n (TL l) -/
def EL [Inhabited α] : Nat → List α → α
  | 0, l => HD l
  | n + 1, l => EL n (TL l)

/- HOL4: LAST (h::t) = if t = [] then h else LAST t   (LAST [] unspecified) -/
def LAST [Inhabited α] : List α → α
  | [] => ARB
  | h :: t => if t = [] then h else LAST t
/- HOL4: FRONT [] = []; FRONT (h::t) = if t = [] then [] else h :: FRONT t -/
def FRONT : List α → List α
  | [] => []
  | h :: t => if t = [] then [] else h :: FRONT t

/- HOL4: TAKE_def: TAKE n [] = []; TAKE n (x::xs) = if n = 0 then [] else x :: TAKE (n-1) xs -/
def TAKE : Nat → List α → List α
  | _, [] => []
  | n, x :: xs => if n = 0 then [] else x :: TAKE (n - 1) xs
/- HOL4: DROP_def: DROP n [] = []; DROP n (x::xs) = if n = 0 then x::xs else DROP (n-1) xs -/
def DROP : Nat → List α → List α
  | _, [] => []
  | n, x :: xs => if n = 0 then x :: xs else DROP (n - 1) xs

/- HOL4: SNOC x [] = [x]; SNOC x (x'::l) = x' :: SNOC x l -/
def SNOC (x : α) : List α → List α
  | [] => [x]
  | x' :: l => x' :: SNOC x l

/- HOL4: GENLIST f 0 = []; GENLIST f (SUC n) = SNOC (f n) (GENLIST f n) -/
def GENLIST (f : Nat → α) : Nat → List α
  | 0 => []
  | n + 1 => SNOC (f n) (GENLIST f n)

/- HOL4: rich_listTheory REPLICATE -/
def REPLICATE : Nat → α → List α
  | 0, _ => []
  | n + 1, x => x :: REPLICATE n x

/- HOL4: ZIP ([],l2) = []; ZIP (l1,[]) = []; ZIP (x1::l1, x2::l2) = (x1,x2)::ZIP (l1,l2)
   (HOL4's ZIP takes a pair of lists.) -/
def ZIP : List α × List β → List (α × β)
  | ([], _) => []
  | (_ :: _, []) => []
  | (x1 :: l1, x2 :: l2) => (x1, x2) :: ZIP (l1, l2)
/- HOL4: UNZIP -/
def UNZIP : List (α × β) → List α × List β
  | [] => ([], [])
  | x :: l => (x.1 :: (UNZIP l).1, x.2 :: (UNZIP l).2)

/- HOL4: ALL_DISTINCT [] = T; ALL_DISTINCT (h::t) = ¬MEM h t ∧ ALL_DISTINCT t -/
def ALL_DISTINCT : List α → Prop
  | [] => True
  | h :: t => ¬ MEM h t ∧ ALL_DISTINCT t

/- HOL4: SUM -/
def SUM : List Nat → Nat
  | [] => 0
  | h :: t => h + SUM t
/- HOL4: rich_listTheory MAX_LIST -/
def MAX_LIST : List Nat → Nat
  | [] => 0
  | h :: t => MAX h (MAX_LIST t)

/- HOL4: SEG_def: SEG 0 k l = []; SEG (SUC m) 0 (x::l) = x :: SEG m 0 l;
   SEG (SUC m) (SUC k) (x::l) = SEG (SUC m) k l   (SEG (SUC m) k [] unspecified; here []) -/
def SEG : Nat → Nat → List α → List α
  | 0, _, _ => []
  | _ + 1, _, [] => []
  | m + 1, 0, x :: l => x :: SEG m 0 l
  | m + 1, k + 1, _ :: l => SEG (m + 1) k l

/- HOL4: listTheory LIST_REL (overload EVERY2) -/
def LIST_REL (R : α → β → Prop) : List α → List β → Prop
  | [], [] => True
  | _ :: _, [] => False
  | [], _ :: _ => False
  | a :: as, b :: bs => R a b ∧ LIST_REL R as bs
abbrev EVERY2 := @LIST_REL

/- HOL4: indexedListsTheory MAPi_def: MAPi f [] = []; MAPi f (h::t) = f 0 h :: MAPi (f o SUC) t -/
def MAPi (f : Nat → α → β) : List α → List β
  | [] => []
  | h :: t => f 0 h :: MAPi (fun n => f (n + 1)) t

/- HOL4: listTheory OPT_MMAP -/
def OPT_MMAP (f : α → Option β) : List α → Option (List β)
  | [] => some []
  | h0 :: t0 => OPTION_BIND (f h0) (fun h => OPTION_BIND (OPT_MMAP f t0) (fun t => some (h :: t)))

/- HOL4: rich_listTheory SPLITP -/
def SPLITP (P : α → Prop) : List α → List α × List α
  | [] => ([], [])
  | x :: l => if P x then ([], x :: l) else (x :: (SPLITP P l).1, (SPLITP P l).2)

/- HOL4: listTheory isPREFIX (infix ≼ / <<=) -/
def isPREFIX : List α → List α → Prop
  | [], _ => True
  | _ :: _, [] => False
  | h :: t, h' :: t' => h = h' ∧ isPREFIX t t'

/- HOL4: listTheory LLEX_def -/
def LLEX (R : α → α → Prop) : List α → List α → Prop
  | [], l2 => l2 ≠ []
  | h1 :: t1, [] => False
  | h1 :: t1, h2 :: t2 => if R h1 h2 then True else if h1 = h2 then LLEX R t1 t2 else False

/- HOL4: sortingTheory PERM_DEF: PERM L1 L2 = ∀x. FILTER ($= x) L1 = FILTER ($= x) L2 -/
def PERM (L1 L2 : List α) : Prop := ∀ x, FILTER (fun y => x = y) L1 = FILTER (fun y => x = y) L2

/- HOL4: sortingTheory SORTED: SORTED R [] = T; SORTED R [x] = T; SORTED R (x::y::rst) = R x y ∧ SORTED R (y::rst) -/
def SORTED (R : α → α → Prop) : List α → Prop
  | [] => True
  | [_] => True
  | x :: y :: rst => R x y ∧ SORTED R (y :: rst)

/- HOL4: alistTheory ALOOKUP_def -/
def ALOOKUP : List (α × β) → α → Option β
  | [], _ => none
  | (x, y) :: t, q => if x = q then some y else ALOOKUP t q

/- HOL4: listTheory REV_DEF: REV [] acc = acc; REV (h::t) acc = REV t (h::acc) -/
def REV : List α → List α → List α
  | [], acc => acc
  | h :: t, acc => REV t (h :: acc)

end

end HOL
