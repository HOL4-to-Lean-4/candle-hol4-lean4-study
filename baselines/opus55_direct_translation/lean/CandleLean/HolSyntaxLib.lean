import CandleLean.Mlstring

/-!
# holSyntaxLib (CakeML `candle/syntax-lib/holSyntaxLibScript.sml`)
-/

universe u v

namespace Candle

open HOL Classical

noncomputable section

/- HOL4:
Definition ALPHAVARS_def:
  (ALPHAVARS [] tmp ⇔ (FST tmp = SND tmp)) ∧
  (ALPHAVARS (tp::oenv) tmp ⇔
    (tmp = tp) ∨
    (FST tp ≠ FST tmp) ∧ (SND tp ≠ SND tmp) ∧ ALPHAVARS oenv tmp)
End -/
def ALPHAVARS {α : Type u} : List (α × α) → α × α → Prop
  | [], tmp => tmp.1 = tmp.2
  | tp :: oenv, tmp => tmp = tp ∨ (tp.1 ≠ tmp.1 ∧ tp.2 ≠ tmp.2 ∧ ALPHAVARS oenv tmp)

/- HOL4:
Definition REV_ASSOCD_def:
  (REV_ASSOCD a [] d = d) ∧
  (REV_ASSOCD a (p::t) d = if SND p = a then FST p else REV_ASSOCD a t d)
End -/
def REV_ASSOCD {α : Type u} {β : Type v} (a : β) : List (α × β) → α → α
  | [], d => d
  | p :: t, d => if p.2 = a then p.1 else REV_ASSOCD a t d

/- HOL4:
Datatype:
  result = Clash 'a | Result 'a
End -/
inductive result (α : Type u) where
  | Clash : α → result α
  | Result : α → result α
  deriving Inhabited

export result (Clash Result)

/- HOL4:
Definition IS_RESULT_def[simp]:
  IS_RESULT(Clash _) = F ∧
  IS_RESULT(Result _) = T
End -/
def IS_RESULT {α : Type u} : result α → Prop
  | Clash _ => False
  | Result _ => True

/- HOL4:
Definition IS_CLASH_def[simp]:
  IS_CLASH(Clash _) = T ∧
  IS_CLASH(Result _) = F
End -/
def IS_CLASH {α : Type u} : result α → Prop
  | Clash _ => True
  | Result _ => False

/- HOL4:
Definition RESULT_def[simp]:
  RESULT(Result t) = t
End
   (pattern completion: RESULT (Clash t) = ARB) -/
def RESULT {α : Type u} : result α → α
  | Result t => t
  | Clash t => @ARB α ⟨t⟩

/- HOL4:
Definition CLASH_def[simp]:
  CLASH(Clash t) = t
End
   (pattern completion: CLASH (Result t) = ARB) -/
def CLASH {α : Type u} : result α → α
  | Clash t => t
  | Result t => @ARB α ⟨t⟩

/- HOL4:
Definition LIST_INSERT_def:
  LIST_INSERT x xs = if MEM x xs then xs else x::xs
End -/
def LIST_INSERT {α : Type u} (x : α) (xs : List α) : List α :=
  if x ∈ xs then xs else x :: xs

/- HOL4:
Definition LIST_UNION_def:
  LIST_UNION xs ys = FOLDR LIST_INSERT ys xs
End -/
def LIST_UNION {α : Type u} (xs ys : List α) : List α := xs.foldr LIST_INSERT ys

/- HOL4:
Definition INORDER_INSERT_def:
  INORDER_INSERT x xs =
    APPEND (FILTER (λy. string_lt y x) xs)
   (APPEND [x] (FILTER (λy. string_lt x y) xs))
End -/
def INORDER_INSERT (x : string) (xs : List string) : List string :=
  FILTER (fun y => string_lt y x) xs ++ ([x] ++ FILTER (fun y => string_lt x y) xs)

/- HOL4:
Definition STRING_SORT_def:
  STRING_SORT xs = FOLDR INORDER_INSERT [] xs
End -/
def STRING_SORT (xs : List string) : List string := xs.foldr INORDER_INSERT []

/-! Auxiliary lemmas (namespace `Candle.Aux`; used for the proof of `instance_def`). -/

theorem Aux.mem_LIST_INSERT {α : Type u} (x y : α) (xs : List α) :
    y ∈ LIST_INSERT x xs ↔ y = x ∨ y ∈ xs := by
  unfold LIST_INSERT
  by_cases h : x ∈ xs
  · simp only [h, if_true]
    constructor
    · exact Or.inr
    · rintro (h' | h') <;> [exact h' ▸ h; exact h']
  · simp [h]

theorem Aux.mem_LIST_UNION {α : Type u} (y : α) (xs ys : List α) :
    y ∈ LIST_UNION xs ys ↔ y ∈ xs ∨ y ∈ ys := by
  unfold LIST_UNION
  induction xs with
  | nil => simp
  | cons a t ih =>
    simp only [List.foldr_cons, Aux.mem_LIST_INSERT, ih, List.mem_cons]
    constructor
    · rintro (h | h | h) <;> simp [h]
    · rintro ((h | h) | h) <;> simp [h]

theorem Aux.mem_FILTER_imp' {α : Type u} (P : α → Prop) :
    ∀ (l : List α) (x : α), x ∈ FILTER P l → x ∈ l
  | [], x, h => by simp [FILTER] at h
  | y :: l, x, h => by
    unfold FILTER at h
    by_cases hy : P y
    · simp only [hy, if_true, List.mem_cons] at h
      rcases h with h | h
      · exact h ▸ List.mem_cons_self
      · exact List.mem_cons_of_mem _ (Aux.mem_FILTER_imp' P l x h)
    · simp only [hy, if_false] at h
      exact List.mem_cons_of_mem _ (Aux.mem_FILTER_imp' P l x h)

theorem Aux.mem_STRING_SORT (x : string) :
    ∀ (xs : List string), x ∈ STRING_SORT xs → x ∈ xs
  | [], h => by simp [STRING_SORT] at h
  | a :: t, h => by
    simp only [STRING_SORT, List.foldr_cons, INORDER_INSERT, List.mem_append] at h
    rcases h with h | h | h
    · exact List.mem_cons_of_mem _ (Aux.mem_STRING_SORT x t (Aux.mem_FILTER_imp' _ _ _ h))
    · simp at h; exact h ▸ List.mem_cons_self
    · exact List.mem_cons_of_mem _ (Aux.mem_STRING_SORT x t (Aux.mem_FILTER_imp' _ _ _ h))

/-! ## Theorems (stage 2) -/

/- HOL4:
Theorem ALPHAVARS_REFL:
   ∀env t. EVERY (UNCURRY $=) env ==> ALPHAVARS env (t,t)
-/
theorem ALPHAVARS_REFL {α : Type u} :
    ∀ (env : List (α × α)) (t : α), EVERY (UNCURRY (fun a b => a = b)) env → ALPHAVARS env (t, t) := by
  sorry

/- HOL4:
Theorem ALPHAVARS_MEM:
   ∀env tp. ALPHAVARS env tp ⇒ MEM tp env ∨ (FST tp = SND tp)
-/
theorem ALPHAVARS_MEM {α : Type u} :
    ∀ (env : List (α × α)) (tp : α × α), ALPHAVARS env tp → tp ∈ env ∨ tp.1 = tp.2 := by
  sorry

/- HOL4:
Theorem REV_ASSOCD:
   (∀a d. REV_ASSOCD a [] d = d) ∧
    (∀a x y t d. REV_ASSOCD a ((x,y)::t) d =
                 if y = a then x else REV_ASSOCD a t d)
   (Lean name `REV_ASSOCD_thm`: the name `Candle.REV_ASSOCD` is the definition) -/
theorem REV_ASSOCD_thm {α : Type u} {β : Type v} :
    (∀ (a : β) (d : α), REV_ASSOCD a [] d = d) ∧
    (∀ (a : β) (x : α) (y : β) (t : List (α × β)) (d : α),
      REV_ASSOCD a ((x, y) :: t) d = if y = a then x else REV_ASSOCD a t d) := by
  sorry

/- HOL4:
Theorem REV_ASSOCD_ALOOKUP:
   ∀ls x d. REV_ASSOCD x ls d = case ALOOKUP (MAP (λ(x,y). (y,x)) ls) x of NONE => d | SOME y => y
-/
theorem REV_ASSOCD_ALOOKUP {α : Type u} {β : Type v} :
    ∀ (ls : List (α × β)) (x : β) (d : α),
      REV_ASSOCD x ls d =
        match ALOOKUP (ls.map (fun (x, y) => (y, x))) x with
        | none => d
        | some y => y := by
  sorry

/- HOL4:
Theorem PRIMED_INFINITE:
   INFINITE (IMAGE (λn. APPEND x (GENLIST (K #"'") n)) UNIV)
-/
theorem PRIMED_INFINITE (x : string) :
    INFINITE (IMAGE (fun n => x ++ GENLIST (K (ch '\'')) n) UNIV) := by
  sorry

universe w

/- HOL4:
Theorem REV_ASSOCD_FILTER:
   ∀l a b d.
      REV_ASSOCD a (FILTER (λ(y,x). P x) l) b =
        if P a then REV_ASSOCD a l b else b
   (`d` does not occur in the body; its HOL4 type is an independent type variable) -/
theorem REV_ASSOCD_FILTER {α : Type u} {β : Type v} {γ : Type w} (P : β → Prop) :
    ∀ (l : List (α × β)) (a : β) (b : α) (d : γ),
      REV_ASSOCD a (FILTER (fun (y, x) => P x) l) b =
        if P a then REV_ASSOCD a l b else b := by
  sorry

/- HOL4:
Theorem REV_ASSOCD_MEM:
   ∀l x d. MEM (REV_ASSOCD x l d,x) l ∨ (REV_ASSOCD x l d = d)
-/
theorem REV_ASSOCD_MEM {α : Type u} {β : Type v} :
    ∀ (l : List (α × β)) (x : β) (d : α),
      (REV_ASSOCD x l d, x) ∈ l ∨ REV_ASSOCD x l d = d := by
  sorry

/- HOL4:
Theorem MEM_LIST_INSERT:
   ∀l x. set (LIST_INSERT x l) = x INSERT set l
-/
theorem MEM_LIST_INSERT {α : Type u} :
    ∀ (l : List α) (x : α), LIST_TO_SET (LIST_INSERT x l) = INSERT x (LIST_TO_SET l) := by
  sorry

/- HOL4:
Theorem MEM_LIST_UNION:
   ∀l1 l2. set (LIST_UNION l1 l2) = set l1 ∪ set l2
-/
theorem MEM_LIST_UNION {α : Type u} :
    ∀ (l1 l2 : List α),
      LIST_TO_SET (LIST_UNION l1 l2) = UNION (LIST_TO_SET l1) (LIST_TO_SET l2) := by
  sorry

/- HOL4:
Theorem MEM_FOLDR_LIST_UNION:
   ∀ls x f b. MEM x (FOLDR (λx y. LIST_UNION (f x) y) b ls) ⇔ MEM x b ∨ ∃y. MEM y ls ∧ MEM x (f y)
-/
theorem MEM_FOLDR_LIST_UNION {α : Type u} {β : Type v} :
    ∀ (ls : List α) (x : β) (f : α → List β) (b : List β),
      x ∈ List.foldr (fun x y => LIST_UNION (f x) y) b ls ↔ x ∈ b ∨ ∃ y, y ∈ ls ∧ x ∈ f y := by
  sorry

/- HOL4:
Theorem LIST_UNION_NIL[simp]:
   ∀l2. (LIST_UNION [] l2 = l2)
-/
theorem LIST_UNION_NIL {α : Type u} : ∀ (l2 : List α), LIST_UNION [] l2 = l2 := by
  sorry

/- HOL4:
Theorem set_LIST_UNION[simp]:
   ∀l1 l2. set (LIST_UNION l1 l2) = set l1 ∪ set l2
-/
theorem set_LIST_UNION {α : Type u} :
    ∀ (l1 l2 : List α),
      LIST_TO_SET (LIST_UNION l1 l2) = UNION (LIST_TO_SET l1) (LIST_TO_SET l2) := by
  sorry

/- HOL4:
Theorem MEM_FOLDR_INORDER_INSERT[simp]:
   !xs x. MEM x (FOLDR INORDER_INSERT [] xs) = MEM x xs
-/
theorem MEM_FOLDR_INORDER_INSERT :
    ∀ (xs : List string) (x : string), (x ∈ List.foldr INORDER_INSERT [] xs) = (x ∈ xs) := by
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
    ∀ (ls : List string), ALL_DISTINCT ls → (STRING_SORT ls).length = ls.length := by
  sorry

/- HOL4:
Theorem MEM_STRING_SORT[simp]:
   ∀ls. set (STRING_SORT ls) = set ls
-/
theorem MEM_STRING_SORT :
    ∀ (ls : List string), LIST_TO_SET (STRING_SORT ls) = LIST_TO_SET ls := by
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
theorem ALL_DISTINCT_LIST_UNION {α : Type u} :
    ∀ (l1 l2 : List α), ALL_DISTINCT l2 → ALL_DISTINCT (LIST_UNION l1 l2) := by
  sorry

end

end Candle
