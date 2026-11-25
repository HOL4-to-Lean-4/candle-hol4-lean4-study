import CmlTS.Prelude.Basic

/-!
# HOL4 library prelude: lists, options, characters, strings, integers, words, ordering

HOL4 constants keep their HOL4 names (root namespace).
-/

universe u v w

noncomputable section

open Classical

/-! ## list theory -/

/- HOL4: list theory, `LIST_TO_SET [] = {}`, `LIST_TO_SET (h::t) = h INSERT LIST_TO_SET t`
   (overloaded as `set`) -/
def LIST_TO_SET {α : Type u} : List α → Set α
  | [] => ∅
  | h :: t => insert h (LIST_TO_SET t)

/- HOL4: list theory, `MEM h l = h IN LIST_TO_SET l` -/
def MEM {α : Type u} (h : α) (l : List α) : Prop := h ∈ LIST_TO_SET l

/- HOL4: list theory, `LENGTH`, `MAP`, `REVERSE`, `FLAT`, `FOLDL`, `FOLDR`, `TAKE`, `DROP`,
   `REPLICATE`, `MAP2` : same recursion equations as the Lean core functions -/
abbrev LENGTH {α : Type u} (l : List α) : Nat := l.length
abbrev MAP {α : Type u} {β : Type v} (f : α → β) (l : List α) : List β := l.map f
abbrev REVERSE {α : Type u} (l : List α) : List α := l.reverse
abbrev FLAT {α : Type u} (l : List (List α)) : List α := l.flatten
abbrev FOLDL {α : Type u} {β : Type v} (f : β → α → β) (e : β) (l : List α) : β := l.foldl f e
abbrev FOLDR {α : Type u} {β : Type v} (f : α → β → β) (e : β) (l : List α) : β := l.foldr f e
/- HOL4: list theory, `TAKE n [] = []`, `TAKE n (x::xs) = if n = 0 then [] else x :: TAKE (n-1) xs` -/
abbrev TAKE {α : Type u} (n : Nat) (l : List α) : List α := l.take n
/- HOL4: list theory, `DROP n [] = []`, `DROP n (x::xs) = if n = 0 then x::xs else DROP (n-1) xs` -/
abbrev DROP {α : Type u} (n : Nat) (l : List α) : List α := l.drop n
/- HOL4: rich_list theory, `REPLICATE 0 x = []`, `REPLICATE (SUC n) x = x :: REPLICATE n x` -/
abbrev REPLICATE {α : Type u} (n : Nat) (x : α) : List α := List.replicate n x
/- HOL4: list theory, `MAP2 f (h1::t1) (h2::t2) = f h1 h2 :: MAP2 f t1 t2`, `MAP2 f x y = []`
   (truncates to the shorter list) -/
abbrev MAP2 {α : Type u} {β : Type v} {γ : Type w} (f : α → β → γ) (l1 : List α) (l2 : List β) :
    List γ := List.zipWith f l1 l2
/- HOL4: list theory, `ZIP (l1, l2)` (truncates to the shorter list; takes a pair) -/
def ZIP {α : Type u} {β : Type v} (p : List α × List β) : List (α × β) := List.zip p.1 p.2

/- HOL4: list theory, `NULL [] = T`, `NULL (h::t) = F` -/
def NULL {α : Type u} : List α → Prop
  | [] => True
  | _ :: _ => False

/- HOL4: list theory, `HD (h::t) = h` (`HD []` is unspecified) -/
def HD {α : Type u} [Nonempty α] : List α → α
  | h :: _ => h
  | [] => ARB

/- HOL4: list theory, `TL [] = []`, `TL (h::t) = t` -/
def TL {α : Type u} : List α → List α
  | [] => []
  | _ :: t => t

/- HOL4: list theory, `EL 0 l = HD l`, `EL (SUC n) l = EL n (TL l)` (out of range: `HD []`) -/
def EL {α : Type u} [Nonempty α] : Nat → List α → α
  | 0, l => HD l
  | n + 1, l => EL n (TL l)

/- HOL4: list theory, `EVERY P [] = T`, `EVERY P (h::t) = P h /\ EVERY P t` -/
def EVERY {α : Type u} (P : α → Prop) : List α → Prop
  | [] => True
  | h :: t => P h ∧ EVERY P t

/- HOL4: list theory, `EXISTS P [] = F`, `EXISTS P (h::t) = P h \/ EXISTS P t` -/
def EXISTS {α : Type u} (P : α → Prop) : List α → Prop
  | [] => False
  | h :: t => P h ∨ EXISTS P t

/- HOL4: list theory, `ALL_DISTINCT [] = T`, `ALL_DISTINCT (h::t) = ~MEM h t /\ ALL_DISTINCT t` -/
def ALL_DISTINCT {α : Type u} : List α → Prop
  | [] => True
  | h :: t => ¬ MEM h t ∧ ALL_DISTINCT t

/- HOL4: list theory, `LUPDATE e n [] = []`,
   `LUPDATE e n (x::l) = if n = 0 then e :: l else x :: LUPDATE e (PRE n) l` -/
def LUPDATE {α : Type u} (e : α) : Nat → List α → List α
  | _, [] => []
  | n, x :: l => if n = 0 then e :: l else x :: LUPDATE e (n - 1) l

/- HOL4: list theory, `REV [] acc = acc`, `REV (h::t) acc = REV t (h::acc)` -/
def REV {α : Type u} : List α → List α → List α
  | [], acc => acc
  | h :: t, acc => REV t (h :: acc)

/- HOL4: rich_list theory, `COUNT_LIST 0 = []`, `COUNT_LIST (SUC n) = 0 :: MAP SUC (COUNT_LIST n)` -/
def COUNT_LIST : Nat → List Nat
  | 0 => []
  | n + 1 => 0 :: (COUNT_LIST n).map (· + 1)

/- HOL4: list theory, `LIST_REL R [] [] = T`, `LIST_REL R (a::as) [] = F`,
   `LIST_REL R [] (b::bs) = F`, `LIST_REL R (a::as) (b::bs) = R a b /\ LIST_REL R as bs`
   (also written `EVERY2`) -/
def LIST_REL {α : Type u} {β : Type v} (R : α → β → Prop) : List α → List β → Prop
  | [], [] => True
  | _ :: _, [] => False
  | [], _ :: _ => False
  | a :: as, b :: bs => R a b ∧ LIST_REL R as bs

/- HOL4: list theory, `oEL n [] = NONE`, `oEL n (x::xs) = if n = 0 then SOME x else oEL (n-1) xs` -/
def oEL {α : Type u} : Nat → List α → Option α
  | _, [] => none
  | n, x :: xs => if n = 0 then some x else oEL (n - 1) xs

/- HOL4: list theory, `isPREFIX [] l = T`,
   `isPREFIX (h::t) l = case l of [] => F | h'::t' => (h = h') /\ isPREFIX t t'` -/
def isPREFIX {α : Type u} : List α → List α → Prop
  | [], _ => True
  | _ :: _, [] => False
  | h :: t, h' :: t' => h = h' ∧ isPREFIX t t'

/-- HOL4 `l1 ≼ l2` / `l1 <<= l2` is `isPREFIX l1 l2` -/
infix:50 " ≼ " => isPREFIX

/- HOL4: rich_list theory, `IS_PREFIX = \x y. isPREFIX y x` -/
def IS_PREFIX {α : Type u} (x y : List α) : Prop := isPREFIX y x

/- HOL4: list theory, `OPT_MMAP f [] = SOME []`,
   `OPT_MMAP f (h0::t0) = OPTION_BIND (f h0) (\h. OPTION_BIND (OPT_MMAP f t0) (\t. SOME (h::t)))` -/
def OPT_MMAP {α : Type u} {β : Type v} (f : α → Option β) : List α → Option (List β)
  | [] => some []
  | h0 :: t0 => (f h0).bind fun h => (OPT_MMAP f t0).bind fun t => some (h :: t)

/- HOL4: rich_list theory, `SPLITP P [] = ([],[])`,
   `SPLITP P (x::l) = if P x then ([], x::l) else (x :: FST (SPLITP P l), SND (SPLITP P l))` -/
def SPLITP {α : Type u} (P : α → Prop) : List α → List α × List α
  | [] => ([], [])
  | x :: l => if P x then ([], x :: l) else (x :: (SPLITP P l).1, (SPLITP P l).2)

theorem SPLITP_snd_length {α : Type u} (P : α → Prop) (l : List α) :
    (SPLITP P l).2.length ≤ l.length := by
  induction l with
  | nil => simp [SPLITP]
  | cons x l ih =>
    unfold SPLITP
    by_cases h : P x <;> simp [h] <;> omega

theorem SPLITP_null {α : Type u} (P : α → Prop) (x : α) (l : List α)
    (h : NULL (SPLITP P (x :: l)).1) : (SPLITP P (x :: l)).2 = x :: l := by
  unfold SPLITP at h ⊢
  by_cases hp : P x <;> simp [hp, NULL] at h ⊢

theorem SPLITP_not_null {α : Type u} (P : α → Prop) (x : α) (l : List α)
    (h : ¬ NULL (SPLITP P (x :: l)).1) : (SPLITP P (x :: l)).2.length < (x :: l).length := by
  have := SPLITP_snd_length P l
  unfold SPLITP at h ⊢
  by_cases hp : P x
  · simp [hp, NULL] at h
  · simp [hp] at h ⊢
    omega

/- HOL4: string theory (list-based strings):
   `TOKENS P [] = []`,
   `TOKENS P (h::t) = let (l,r) = SPLITP P (h::t) in if NULL l then TOKENS P (TL r) else l::TOKENS P r`
   (termination: `measure (LENGTH o SND)`).  Defined here for arbitrary element types. -/
def TOKENS {α : Type u} (P : α → Prop) : List α → List (List α)
  | [] => []
  | h :: t =>
    if NULL (SPLITP P (h :: t)).1 then TOKENS P (TL (SPLITP P (h :: t)).2)
    else (SPLITP P (h :: t)).1 :: TOKENS P (SPLITP P (h :: t)).2
termination_by l => l.length
decreasing_by
  · rename_i hn
    rw [SPLITP_null P h t hn]
    simp [TL]
  · rename_i hn
    exact SPLITP_not_null P h t hn

/-! ## alist -/

/- HOL4: alist theory, type `('a, 'b) alist = ('a # 'b) list` -/
abbrev alist (α : Type u) (β : Type v) : Type (max u v) := List (α × β)

/- HOL4: alist theory, `ALOOKUP [] q = NONE`,
   `ALOOKUP ((x,y)::t) q = if x = q then SOME y else ALOOKUP t q` -/
def ALOOKUP {α : Type u} {β : Type v} : List (α × β) → α → Option β
  | [], _ => none
  | (x, y) :: t, q => if x = q then some y else ALOOKUP t q

end
