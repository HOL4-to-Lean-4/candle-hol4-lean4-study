/-
  HOL4 theory `holSyntaxLib` (candle/syntax-lib/holSyntaxLibScript.sml).
-/
import CandleLean.Mlstring

namespace Candle

noncomputable section
open Classical

/- HOL4:
Definition ALPHAVARS_def:
  (ALPHAVARS [] tmp ⇔ (FST tmp = SND tmp)) ∧
  (ALPHAVARS (tp::oenv) tmp ⇔
    (tmp = tp) ∨
    (FST tp ≠ FST tmp) ∧ (SND tp ≠ SND tmp) ∧ ALPHAVARS oenv tmp)
End -/
def ALPHAVARS {α : Type} : List (α × α) → α × α → Prop
  | [], tmp => FST tmp = SND tmp
  | tp :: oenv, tmp =>
    tmp = tp ∨ (FST tp ≠ FST tmp ∧ SND tp ≠ SND tmp ∧ ALPHAVARS oenv tmp)

/- HOL4:
Definition REV_ASSOCD_def:
  (REV_ASSOCD a [] d = d) ∧
  (REV_ASSOCD a (p::t) d = if SND p = a then FST p else REV_ASSOCD a t d)
End -/
def REV_ASSOCD {α β : Type} : α → List (β × α) → β → β
  | _, [], d => d
  | a, p :: t, d => if SND p = a then FST p else REV_ASSOCD a t d

/- HOL4:
Datatype:
  result = Clash 'a | Result 'a
End -/
inductive result (α : Type) where
  | Clash : α → result α
  | Result : α → result α

export result (Clash Result)

instance {α : Type} [Nonempty α] : Nonempty (result α) := ‹Nonempty α›.elim fun a => ⟨Clash a⟩

/- HOL4:
Definition IS_RESULT_def[simp]:
  IS_RESULT(Clash _) = F ∧
  IS_RESULT(Result _) = T
End -/
def IS_RESULT {α : Type} : result α → Prop
  | Clash _ => False
  | Result _ => True

/- HOL4:
Definition IS_CLASH_def[simp]:
  IS_CLASH(Clash _) = T ∧
  IS_CLASH(Result _) = F
End -/
def IS_CLASH {α : Type} : result α → Prop
  | Clash _ => True
  | Result _ => False

/- HOL4:
Definition RESULT_def[simp]:
  RESULT(Result t) = t
End
   (a constructor pattern with a missing clause: defined by
   `Prim_rec.new_recursive_definition`, so `RESULT (Clash t)` is unspecified and `RESULT` is
   an arbitrary function that satisfies the clause.) -/
def RESULT {α : Type} [Nonempty α] : result α → α :=
  select (fun f => ∀ t, f (Result t) = t)

/- HOL4: RESULT_def (the defining theorem of `RESULT`)  |- RESULT (Result t) = t -/
theorem RESULT_def {α : Type} [Nonempty α] (t : α) : RESULT (Result t) = t :=
  select_spec (P := fun f : result α → α => ∀ t, f (Result t) = t)
    ⟨fun r => match r with | Result t => t | Clash _ => ARB, fun _ => rfl⟩ t

/- HOL4:
Definition CLASH_def[simp]:
  CLASH(Clash t) = t
End
   (as for `RESULT`: `CLASH (Result t)` is unspecified.) -/
def CLASH {α : Type} [Nonempty α] : result α → α :=
  select (fun f => ∀ t, f (Clash t) = t)

/- HOL4: CLASH_def (the defining theorem of `CLASH`)  |- CLASH (Clash t) = t -/
theorem CLASH_def {α : Type} [Nonempty α] (t : α) : CLASH (Clash t) = t :=
  select_spec (P := fun f : result α → α => ∀ t, f (Clash t) = t)
    ⟨fun r => match r with | Clash t => t | Result _ => ARB, fun _ => rfl⟩ t

/- HOL4:
Definition LIST_INSERT_def:
  LIST_INSERT x xs = if MEM x xs then xs else x::xs
End -/
def LIST_INSERT {α : Type} (x : α) (xs : List α) : List α :=
  if MEM x xs then xs else x :: xs

/- HOL4:
Definition LIST_UNION_def:
  LIST_UNION xs ys = FOLDR LIST_INSERT ys xs
End -/
def LIST_UNION {α : Type} (xs ys : List α) : List α := FOLDR LIST_INSERT ys xs

/- HOL4:
Definition INORDER_INSERT_def:
  INORDER_INSERT x xs =
    APPEND (FILTER (λy. string_lt y x) xs)
   (APPEND [x] (FILTER (λy. string_lt x y) xs))
End -/
def INORDER_INSERT (x : string) (xs : List string) : List string :=
  APPEND (FILTER (fun y => string_lt y x) xs)
    (APPEND [x] (FILTER (fun y => string_lt x y) xs))

/- HOL4:
Definition STRING_SORT_def:
  STRING_SORT xs = FOLDR INORDER_INSERT [] xs
End -/
def STRING_SORT (xs : List string) : List string := FOLDR INORDER_INSERT [] xs

end

end Candle

/-! ## Stage 2: the target theorems of the HOL4 theory `holSyntaxLib` (statements only, proofs `sorry`) -/

namespace Candle

noncomputable section
open Classical
set_option autoImplicit false

/- HOL4:
Theorem ALPHAVARS_REFL:
   ∀env t. EVERY (UNCURRY $=) env ==> ALPHAVARS env (t,t)
-/
theorem ALPHAVARS_REFL {α : Type} [Nonempty α] :
    ∀ (env : List (α × α)) (t : α),
      EVERY (UNCURRY (fun x y => x = y)) env → ALPHAVARS env (t, t) := by
  sorry

/- HOL4:
Theorem ALPHAVARS_MEM:
   ∀env tp. ALPHAVARS env tp ⇒ MEM tp env ∨ (FST tp = SND tp)
-/
theorem ALPHAVARS_MEM {α : Type} [Nonempty α] :
    ∀ (env : List (α × α)) (tp : α × α),
      ALPHAVARS env tp → MEM tp env ∨ (FST tp = SND tp) := by
  sorry

/- HOL4:
Theorem REV_ASSOCD:
   (∀a d. REV_ASSOCD a [] d = d) ∧
    (∀a x y t d. REV_ASSOCD a ((x,y)::t) d =
                 if y = a then x else REV_ASSOCD a t d)
-/
theorem REV_ASSOCD_thm {α β γ δ : Type} [Nonempty α] [Nonempty β] [Nonempty γ] [Nonempty δ] :
    (∀ (a : α) (d : β), REV_ASSOCD a [] d = d) ∧
    (∀ (a : γ) (x : δ) (y : γ) (t : List (δ × γ)) (d : δ),
      REV_ASSOCD a ((x, y) :: t) d =
        if y = a then x else REV_ASSOCD a t d) := by
  sorry

/- HOL4:
Theorem REV_ASSOCD_ALOOKUP:
   ∀ls x d. REV_ASSOCD x ls d = case ALOOKUP (MAP (λ(x,y). (y,x)) ls) x of NONE => d | SOME y => y
-/
theorem REV_ASSOCD_ALOOKUP {α β : Type} [Nonempty α] [Nonempty β] :
    ∀ (ls : List (β × α)) (x : α) (d : β),
      REV_ASSOCD x ls d =
        match ALOOKUP (MAP (fun (x, y) => (y, x)) ls) x with
        | none => d
        | some y => y := by
  sorry

/- HOL4:
Theorem PRIMED_INFINITE:
   INFINITE (IMAGE (λn. APPEND x (GENLIST (K #"'") n)) UNIV)
-/
theorem PRIMED_INFINITE (x : string) :
    INFINITE (IMAGE (fun n => APPEND x (GENLIST (K chr!"'") n)) (UNIV : Set Nat)) := by
  sorry

/- HOL4:
Theorem REV_ASSOCD_FILTER:
   ∀l a b d.
      REV_ASSOCD a (FILTER (λ(y,x). P x) l) b =
        if P a then REV_ASSOCD a l b else b
-/
theorem REV_ASSOCD_FILTER {α β γ : Type} [Nonempty α] [Nonempty β] [Nonempty γ] (P : α → Prop) :
    ∀ (l : List (β × α)) (a : α) (b : β) (d : γ),
      REV_ASSOCD a (FILTER (fun (y, x) => P x) l) b =
        if P a then REV_ASSOCD a l b else b := by
  sorry

/- HOL4:
Theorem REV_ASSOCD_MEM:
   ∀l x d. MEM (REV_ASSOCD x l d,x) l ∨ (REV_ASSOCD x l d = d)
-/
theorem REV_ASSOCD_MEM {α β : Type} [Nonempty α] [Nonempty β] :
    ∀ (l : List (β × α)) (x : α) (d : β),
      MEM (REV_ASSOCD x l d, x) l ∨ (REV_ASSOCD x l d = d) := by
  sorry

/- HOL4:
Theorem MEM_LIST_INSERT:
   ∀l x. set (LIST_INSERT x l) = x INSERT set l
-/
theorem MEM_LIST_INSERT {α : Type} [Nonempty α] :
    ∀ (l : List α) (x : α), set (LIST_INSERT x l) = INSERT x (set l) := by
  sorry

/- HOL4:
Theorem MEM_LIST_UNION:
   ∀l1 l2. set (LIST_UNION l1 l2) = set l1 ∪ set l2
-/
theorem MEM_LIST_UNION {α : Type} [Nonempty α] :
    ∀ (l1 l2 : List α), set (LIST_UNION l1 l2) = set l1 ∪ set l2 := by
  sorry

/- HOL4:
Theorem MEM_FOLDR_LIST_UNION:
   ∀ls x f b. MEM x (FOLDR (λx y. LIST_UNION (f x) y) b ls) ⇔ MEM x b ∨ ∃y. MEM y ls ∧ MEM x (f y)
-/
theorem MEM_FOLDR_LIST_UNION {α β : Type} [Nonempty α] [Nonempty β] :
    ∀ (ls : List β) (x : α) (f : β → List α) (b : List α),
      MEM x (FOLDR (fun x y => LIST_UNION (f x) y) b ls) ↔
        MEM x b ∨ ∃ y, MEM y ls ∧ MEM x (f y) := by
  sorry

/- HOL4:
Theorem LIST_UNION_NIL[simp]:
   ∀l2. (LIST_UNION [] l2 = l2)
-/
theorem LIST_UNION_NIL {α : Type} [Nonempty α] :
    ∀ (l2 : List α), (LIST_UNION [] l2 = l2) := by
  sorry

/- HOL4:
Theorem set_LIST_UNION[simp]:
   ∀l1 l2. set (LIST_UNION l1 l2) = set l1 ∪ set l2
-/
theorem set_LIST_UNION {α : Type} [Nonempty α] :
    ∀ (l1 l2 : List α), set (LIST_UNION l1 l2) = set l1 ∪ set l2 := by
  sorry

/- HOL4:
Theorem MEM_FOLDR_INORDER_INSERT[simp]:
   !xs x. MEM x (FOLDR INORDER_INSERT [] xs) = MEM x xs
-/
theorem MEM_FOLDR_INORDER_INSERT :
    ∀ (xs : List string) (x : string),
      MEM x (FOLDR INORDER_INSERT [] xs) ↔ MEM x xs := by
  sorry

/- HOL4:
Theorem PERM_STRING_SORT:
   ∀ls. ALL_DISTINCT ls ⇒ PERM ls (STRING_SORT ls)
-/
theorem PERM_STRING_SORT :
    ∀ (ls : List string), ALL_DISTINCT ls → PERM ls (STRING_SORT ls) := by
  sorry

/- HOL4:
Theorem LENGTH_STRING_SORT[simp]:
   ∀ls. ALL_DISTINCT ls ⇒ (LENGTH (STRING_SORT ls) = LENGTH ls)
-/
theorem LENGTH_STRING_SORT :
    ∀ (ls : List string), ALL_DISTINCT ls → (LENGTH (STRING_SORT ls) = LENGTH ls) := by
  sorry

/- HOL4:
Theorem MEM_STRING_SORT[simp]:
   ∀ls. set (STRING_SORT ls) = set ls
-/
theorem MEM_STRING_SORT :
    ∀ (ls : List string), set (STRING_SORT ls) = set ls := by
  sorry

/- HOL4:
Theorem ALL_DISTINCT_STRING_SORT[simp]:
   !xs. ALL_DISTINCT (STRING_SORT xs)
-/
theorem ALL_DISTINCT_STRING_SORT :
    ∀ (xs : List string), ALL_DISTINCT (STRING_SORT xs) := by
  sorry

/- HOL4:
Theorem ALL_DISTINCT_LIST_UNION:
   ∀l1 l2. ALL_DISTINCT l2 ⇒ ALL_DISTINCT (LIST_UNION l1 l2)
-/
theorem ALL_DISTINCT_LIST_UNION {α : Type} [Nonempty α] :
    ∀ (l1 l2 : List α), ALL_DISTINCT l2 → ALL_DISTINCT (LIST_UNION l1 l2) := by
  sorry

end

end Candle
