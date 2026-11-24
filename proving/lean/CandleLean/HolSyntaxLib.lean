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
   (`RESULT (Clash t)` is unspecified) -/
private opaque RESULT_pkg {α : Type u} : {f : result α → α // ∀ t, f (Result t) = t} :=
  ⟨fun r => match r with | Result t => t | Clash t => t, fun _ => rfl⟩

def RESULT {α : Type u} : result α → α := RESULT_pkg.1

theorem RESULT_def {α : Type u} (t : α) : RESULT (Result t) = t := RESULT_pkg.2 t

/- HOL4:
Definition CLASH_def[simp]:
  CLASH(Clash t) = t
End
   (`CLASH (Result t)` is unspecified) -/
private opaque CLASH_pkg {α : Type u} : {f : result α → α // ∀ t, f (Clash t) = t} :=
  ⟨fun r => match r with | Clash t => t | Result t => t, fun _ => rfl⟩

def CLASH {α : Type u} : result α → α := CLASH_pkg.1

theorem CLASH_def {α : Type u} (t : α) : CLASH (Clash t) = t := CLASH_pkg.2 t

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

theorem Aux.EVERY_iff {α : Type u} (P : α → Prop) (l : List α) : EVERY P l ↔ ∀ x, x ∈ l → P x := by
  induction l with
  | nil => simp [EVERY]
  | cons a t ih => simp [EVERY, ih]

theorem Aux.EXISTS_iff {α : Type u} (P : α → Prop) (l : List α) : EXISTS P l ↔ ∃ x, x ∈ l ∧ P x := by
  induction l with
  | nil => simp [EXISTS]
  | cons a t ih => simp [EXISTS, ih]

theorem Aux.FILTER_eq_filter {α : Type u} (P : α → Prop) (l : List α) :
    FILTER P l = l.filter (fun x => decide (P x)) := by
  induction l with
  | nil => rfl
  | cons a t ih => by_cases h : P a <;> simp [FILTER, h, ih]

theorem Aux.mem_FILTER {α : Type u} (P : α → Prop) (l : List α) (x : α) :
    x ∈ FILTER P l ↔ x ∈ l ∧ P x := by
  rw [Aux.FILTER_eq_filter]; simp

theorem Aux.exists_length_bound {α : Type u} (l : List (List α)) :
    ∃ n, ∀ y, y ∈ l → y.length ≤ n := by
  induction l with
  | nil => exact ⟨0, by simp⟩
  | cons a t ih =>
    obtain ⟨n, hn⟩ := ih
    refine ⟨max a.length n, fun y hy => ?_⟩
    rcases List.mem_cons.mp hy with rfl | hy
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (hn y hy) (Nat.le_max_right _ _)

theorem Aux.length_SNOC {α : Type u} (x : α) (l : List α) : (SNOC x l).length = l.length + 1 := by
  induction l with
  | nil => rfl
  | cons a t ih => simp [SNOC, ih]

theorem Aux.length_GENLIST {α : Type u} (f : Nat → α) (n : Nat) : (GENLIST f n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [GENLIST, Aux.length_SNOC, ih]

theorem Aux.mem_INORDER_INSERT (a x : string) (l : List string) :
    x ∈ INORDER_INSERT a l ↔ x = a ∨ x ∈ l := by
  simp only [INORDER_INSERT, List.mem_append, Aux.mem_FILTER, List.mem_singleton]
  have := Aux.string_lt_tri x a
  grind

theorem Aux.mem_STRING_SORT_iff (x : string) (xs : List string) : x ∈ STRING_SORT xs ↔ x ∈ xs := by
  induction xs with
  | nil => simp [STRING_SORT]
  | cons a t ih =>
    have : STRING_SORT (a :: t) = INORDER_INSERT a (STRING_SORT t) := rfl
    rw [this, Aux.mem_INORDER_INSERT, ih, List.mem_cons]

theorem Aux.filter_split_perm (a : string) (s : List string) (h : ¬ a ∈ s) :
    (FILTER (fun y => string_lt y a) s ++ FILTER (fun y => string_lt a y) s).Perm s := by
  induction s with
  | nil => simp [FILTER]
  | cons b t ih =>
    simp only [List.mem_cons, not_or] at h
    simp only [FILTER]
    by_cases h1 : string_lt b a
    · have h2 : ¬ string_lt a b := fun h2 =>
        Aux.string_lt_irrefl _ (Aux.string_lt_trans _ _ _ h1 h2)
      rw [if_pos h1, if_neg h2]
      exact (ih h.2).cons b
    · have h2 : string_lt a b := by
        rcases Aux.string_lt_tri a b with h' | h' | h'
        · exact h'
        · exact absurd h' h1
        · exact absurd h' h.1
      rw [if_neg h1, if_pos h2]
      exact List.perm_middle.trans ((ih h.2).cons b)

theorem Aux.STRING_SORT_perm (ls : List string) (h : ALL_DISTINCT ls) : ls.Perm (STRING_SORT ls) := by
  induction ls with
  | nil => exact List.Perm.refl _
  | cons a t ih =>
    have e : STRING_SORT (a :: t) = INORDER_INSERT a (STRING_SORT t) := rfl
    rw [e]
    have hn : ¬ a ∈ STRING_SORT t := fun h' => h.1 ((Aux.mem_STRING_SORT_iff a t).mp h')
    have h1 := Aux.filter_split_perm a _ hn
    exact (((ih h.2).trans h1.symm).cons a).trans List.perm_middle.symm

/-! ## Theorems (stage 2) -/

/- HOL4:
Theorem ALPHAVARS_REFL:
   ∀env t. EVERY (UNCURRY $=) env ==> ALPHAVARS env (t,t)
-/
theorem ALPHAVARS_REFL {α : Type u} :
    ∀ (env : List (α × α)) (t : α), EVERY (UNCURRY (fun a b => a = b)) env → ALPHAVARS env (t, t) := by
  intro env t h
  induction env with
  | nil => rfl
  | cons p env ih =>
    obtain ⟨a, b⟩ := p
    obtain ⟨hab, he⟩ := h
    have hab' : a = b := hab
    subst hab'
    by_cases hat : a = t
    · subst hat; exact Or.inl rfl
    · exact Or.inr ⟨hat, hat, ih he⟩

/- HOL4:
Theorem ALPHAVARS_MEM:
   ∀env tp. ALPHAVARS env tp ⇒ MEM tp env ∨ (FST tp = SND tp)
-/
theorem ALPHAVARS_MEM {α : Type u} :
    ∀ (env : List (α × α)) (tp : α × α), ALPHAVARS env tp → tp ∈ env ∨ tp.1 = tp.2 := by
  intro env tp h
  induction env with
  | nil => exact Or.inr h
  | cons p env ih =>
    rcases h with h | ⟨_, _, h⟩
    · exact Or.inl (h ▸ List.mem_cons_self)
    · rcases ih h with h | h
      · exact Or.inl (List.mem_cons_of_mem _ h)
      · exact Or.inr h

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
  exact ⟨fun _ _ => rfl, fun _ _ _ _ _ => rfl⟩

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
  intro ls x d
  induction ls with
  | nil => rfl
  | cons p t ih =>
    obtain ⟨a, b⟩ := p
    by_cases h : b = x <;> simp [REV_ASSOCD, ALOOKUP, h, ih]

/- HOL4:
Theorem PRIMED_INFINITE:
   INFINITE (IMAGE (λn. APPEND x (GENLIST (K #"'") n)) UNIV)
-/
theorem PRIMED_INFINITE (x : string) :
    INFINITE (IMAGE (fun n => x ++ GENLIST (K (ch '\'')) n) UNIV) := by
  intro hf
  obtain ⟨l, hl⟩ := Aux.FINITE_list_bound _ hf
  obtain ⟨n, hn⟩ := Aux.exists_length_bound l
  have h1 := hn _ (hl (x ++ GENLIST (K (ch '\'')) (n + 1))
    ((Aux.mem_IMAGE _ _ _).mpr ⟨n + 1, rfl, trivial⟩))
  rw [List.length_append, Aux.length_GENLIST] at h1
  omega

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
  intro l a b _
  induction l with
  | nil => simp [FILTER, REV_ASSOCD]
  | cons p t ih =>
    obtain ⟨y, x⟩ := p
    simp only [FILTER]
    by_cases h1 : P x
    · rw [if_pos h1]
      simp only [REV_ASSOCD]
      by_cases h2 : x = a
      · subst h2; simp [h1]
      · simp only [h2, if_false, ih]
    · rw [if_neg h1, ih]
      by_cases h2 : x = a
      · subst h2; simp [h1]
      · simp only [REV_ASSOCD, h2, if_false]

/- HOL4:
Theorem REV_ASSOCD_MEM:
   ∀l x d. MEM (REV_ASSOCD x l d,x) l ∨ (REV_ASSOCD x l d = d)
-/
theorem REV_ASSOCD_MEM {α : Type u} {β : Type v} :
    ∀ (l : List (α × β)) (x : β) (d : α),
      (REV_ASSOCD x l d, x) ∈ l ∨ REV_ASSOCD x l d = d := by
  intro l x d
  induction l with
  | nil => exact Or.inr rfl
  | cons p t ih =>
    simp only [REV_ASSOCD]
    by_cases h : p.2 = x
    · simp only [h, if_true]; exact Or.inl (h ▸ List.mem_cons_self)
    · simp only [h, if_false]
      rcases ih with h' | h'
      · exact Or.inl (List.mem_cons_of_mem _ h')
      · exact Or.inr h'

/- HOL4:
Theorem MEM_LIST_INSERT:
   ∀l x. set (LIST_INSERT x l) = x INSERT set l
-/
theorem MEM_LIST_INSERT {α : Type u} :
    ∀ (l : List α) (x : α), LIST_TO_SET (LIST_INSERT x l) = INSERT x (LIST_TO_SET l) := by
  intro l x
  apply Aux.set_ext
  intro y
  rw [Aux.mem_LIST_TO_SET, Aux.mem_LIST_INSERT, Aux.mem_INSERT, Aux.mem_LIST_TO_SET]

theorem Aux.MEM_LIST_UNION {α : Type u} (l1 l2 : List α) :
    LIST_TO_SET (LIST_UNION l1 l2) = UNION (LIST_TO_SET l1) (LIST_TO_SET l2) := by
  apply Aux.set_ext
  intro y
  rw [Aux.mem_LIST_TO_SET, Aux.mem_LIST_UNION, Aux.mem_UNION, Aux.mem_LIST_TO_SET,
    Aux.mem_LIST_TO_SET]

/- HOL4:
Theorem MEM_LIST_UNION:
   ∀l1 l2. set (LIST_UNION l1 l2) = set l1 ∪ set l2
-/
theorem MEM_LIST_UNION {α : Type u} :
    ∀ (l1 l2 : List α),
      LIST_TO_SET (LIST_UNION l1 l2) = UNION (LIST_TO_SET l1) (LIST_TO_SET l2) := by
  exact Aux.MEM_LIST_UNION

/- HOL4:
Theorem MEM_FOLDR_LIST_UNION:
   ∀ls x f b. MEM x (FOLDR (λx y. LIST_UNION (f x) y) b ls) ⇔ MEM x b ∨ ∃y. MEM y ls ∧ MEM x (f y)
-/
theorem MEM_FOLDR_LIST_UNION {α : Type u} {β : Type v} :
    ∀ (ls : List α) (x : β) (f : α → List β) (b : List β),
      x ∈ List.foldr (fun x y => LIST_UNION (f x) y) b ls ↔ x ∈ b ∨ ∃ y, y ∈ ls ∧ x ∈ f y := by
  intro ls x f b
  induction ls with
  | nil => simp
  | cons a t ih =>
    simp only [List.foldr_cons, Aux.mem_LIST_UNION, ih, List.mem_cons]
    grind

/- HOL4:
Theorem LIST_UNION_NIL[simp]:
   ∀l2. (LIST_UNION [] l2 = l2)
-/
theorem LIST_UNION_NIL {α : Type u} : ∀ (l2 : List α), LIST_UNION [] l2 = l2 := by
  intro l2
  rfl

/- HOL4:
Theorem set_LIST_UNION[simp]:
   ∀l1 l2. set (LIST_UNION l1 l2) = set l1 ∪ set l2
-/
theorem set_LIST_UNION {α : Type u} :
    ∀ (l1 l2 : List α),
      LIST_TO_SET (LIST_UNION l1 l2) = UNION (LIST_TO_SET l1) (LIST_TO_SET l2) := by
  exact Aux.MEM_LIST_UNION

/- HOL4:
Theorem MEM_FOLDR_INORDER_INSERT[simp]:
   !xs x. MEM x (FOLDR INORDER_INSERT [] xs) = MEM x xs
-/
theorem MEM_FOLDR_INORDER_INSERT :
    ∀ (xs : List string) (x : string), (x ∈ List.foldr INORDER_INSERT [] xs) = (x ∈ xs) := by
  intro xs x
  exact propext (Aux.mem_STRING_SORT_iff x xs)

/- HOL4:
Theorem PERM_STRING_SORT:
   ∀ls. ALL_DISTINCT ls ⇒ PERM ls (STRING_SORT ls)
-/
theorem PERM_STRING_SORT :
    ∀ (ls : List string), ALL_DISTINCT ls → PERM ls (STRING_SORT ls) := by
  intro ls h
  exact Aux.PERM_of_perm (Aux.STRING_SORT_perm ls h)

/- HOL4:
Theorem LENGTH_STRING_SORT[simp]:
   ∀ls. ALL_DISTINCT ls ⇒ (LENGTH (STRING_SORT ls) = LENGTH ls)
-/
theorem LENGTH_STRING_SORT :
    ∀ (ls : List string), ALL_DISTINCT ls → (STRING_SORT ls).length = ls.length := by
  intro ls h
  exact (Aux.STRING_SORT_perm ls h).length_eq.symm

/- HOL4:
Theorem MEM_STRING_SORT[simp]:
   ∀ls. set (STRING_SORT ls) = set ls
-/
theorem MEM_STRING_SORT :
    ∀ (ls : List string), LIST_TO_SET (STRING_SORT ls) = LIST_TO_SET ls := by
  intro ls
  apply Aux.set_ext
  intro x
  rw [Aux.mem_LIST_TO_SET, Aux.mem_LIST_TO_SET, Aux.mem_STRING_SORT_iff]

/- HOL4:
Theorem ALL_DISTINCT_STRING_SORT[simp]:
   !xs. ALL_DISTINCT (STRING_SORT xs)
-/
theorem ALL_DISTINCT_STRING_SORT :
    ∀ (xs : List string), ALL_DISTINCT (STRING_SORT xs) := by
  intro xs
  rw [Aux.ALL_DISTINCT_iff_nodup]
  induction xs with
  | nil => simp [STRING_SORT]
  | cons a t ih =>
    have e : STRING_SORT (a :: t) = INORDER_INSERT a (STRING_SORT t) := rfl
    rw [e, INORDER_INSERT, List.nodup_append, List.nodup_append]
    refine ⟨?_, ⟨by simp, ?_, ?_⟩, ?_⟩
    · rw [Aux.FILTER_eq_filter]; exact ih.filter _
    · rw [Aux.FILTER_eq_filter]; exact ih.filter _
    · intro x hx y hy hxy
      simp only [List.mem_singleton] at hx
      rw [Aux.mem_FILTER] at hy
      subst hx; subst hxy
      exact Aux.string_lt_irrefl _ hy.2
    · intro x hx y hy hxy
      rw [Aux.mem_FILTER] at hx
      simp only [List.mem_append, List.mem_singleton, Aux.mem_FILTER] at hy
      subst hxy
      rcases hy with rfl | hy
      · exact Aux.string_lt_irrefl _ hx.2
      · exact Aux.string_lt_irrefl _ (Aux.string_lt_trans _ _ _ hx.2 hy.2)

/- HOL4:
Theorem ALL_DISTINCT_LIST_UNION:
   ∀l1 l2. ALL_DISTINCT l2 ⇒ ALL_DISTINCT (LIST_UNION l1 l2)
-/
theorem ALL_DISTINCT_LIST_UNION {α : Type u} :
    ∀ (l1 l2 : List α), ALL_DISTINCT l2 → ALL_DISTINCT (LIST_UNION l1 l2) := by
  intro l1 l2 h
  induction l1 with
  | nil => exact h
  | cons a t ih =>
    have e : LIST_UNION (a :: t) l2 = LIST_INSERT a (LIST_UNION t l2) := rfl
    rw [e, LIST_INSERT]
    by_cases hm : a ∈ LIST_UNION t l2
    · rw [if_pos hm]; exact ih
    · rw [if_neg hm]; exact ⟨hm, ih⟩

end

end Candle
