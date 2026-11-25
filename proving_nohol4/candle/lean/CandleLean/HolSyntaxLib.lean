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

/-! ## Theorems (stage 2) -/

/- HOL4:
Theorem ALPHAVARS_REFL:
   ∀env t. EVERY (UNCURRY $=) env ==> ALPHAVARS env (t,t)
-/
theorem ALPHAVARS_REFL {α : Type u} :
    ∀ (env : List (α × α)) (t : α), EVERY (UNCURRY (fun a b => a = b)) env → ALPHAVARS env (t, t) := by
  intro env t
  induction env with
  | nil => intro _; rfl
  | cons p env ih =>
    obtain ⟨a, b⟩ := p
    rintro ⟨h1, h2⟩
    have h1 : a = b := h1
    subst h1
    by_cases h : t = a
    · left; rw [h]
    · right; exact ⟨fun e => h e.symm, fun e => h e.symm, ih h2⟩

/- HOL4:
Theorem ALPHAVARS_MEM:
   ∀env tp. ALPHAVARS env tp ⇒ MEM tp env ∨ (FST tp = SND tp)
-/
theorem ALPHAVARS_MEM {α : Type u} :
    ∀ (env : List (α × α)) (tp : α × α), ALPHAVARS env tp → tp ∈ env ∨ tp.1 = tp.2 := by
  intro env tp
  induction env with
  | nil => intro h; exact Or.inr h
  | cons p env ih =>
    rintro (h | ⟨_, _, h⟩)
    · left; rw [h]; exact List.mem_cons_self
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
  intro h
  obtain ⟨l, hl⟩ := Aux.FINITE_iff.mp h
  have hb : ∀ l : List string, ∃ N, ∀ y, y ∈ l → y.length < N := by
    intro l
    induction l with
    | nil => exact ⟨0, by simp⟩
    | cons a t ih =>
      obtain ⟨N, hN⟩ := ih
      refine ⟨N + a.length + 1, fun y hy => ?_⟩
      rcases List.mem_cons.mp hy with h | h
      · subst h; omega
      · have := hN y h; omega
  obtain ⟨N, hN⟩ := hb l
  have hm := hN _ (hl (x ++ GENLIST (K (ch '\'')) N) (Aux.mem_IMAGE.mpr ⟨N, rfl, trivial⟩))
  rw [Aux.GENLIST_K] at hm
  simp at hm
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
    by_cases hx : P x
    · by_cases h : x = a
      · subst h; simp [FILTER, REV_ASSOCD, hx]
      · simp [FILTER, REV_ASSOCD, hx, h, ih]
    · by_cases h : x = a
      · subst h; simp [FILTER, hx, ih]
      · simp [FILTER, REV_ASSOCD, hx, h, ih]

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
    obtain ⟨a, b⟩ := p
    by_cases h : b = x
    · left; simp [REV_ASSOCD, h]
    · simp only [REV_ASSOCD, h, if_false]
      rcases ih with h | h
      · exact Or.inl (List.mem_cons_of_mem _ h)
      · exact Or.inr h

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

/- HOL4:
Theorem MEM_LIST_UNION:
   ∀l1 l2. set (LIST_UNION l1 l2) = set l1 ∪ set l2
-/
theorem MEM_LIST_UNION {α : Type u} :
    ∀ (l1 l2 : List α),
      LIST_TO_SET (LIST_UNION l1 l2) = UNION (LIST_TO_SET l1) (LIST_TO_SET l2) := by
  intro l1 l2
  apply Aux.set_ext
  intro y
  rw [Aux.mem_LIST_TO_SET, Aux.mem_LIST_UNION, Aux.mem_UNION, Aux.mem_LIST_TO_SET,
    Aux.mem_LIST_TO_SET]

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
    rw [List.foldr_cons, Aux.mem_LIST_UNION, ih]
    simp only [List.mem_cons]
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
  exact MEM_LIST_UNION

theorem Aux.mem_INORDER_INSERT (a x : string) (l : List string) :
    x ∈ INORDER_INSERT a l ↔ x = a ∨ x ∈ l := by
  simp only [INORDER_INSERT, List.mem_append, Aux.mem_FILTER, List.mem_singleton]
  have := Aux.string_lt_trichotomous x a
  grind

theorem Aux.mem_STRING_SORT_iff (x : string) (xs : List string) :
    x ∈ STRING_SORT xs ↔ x ∈ xs := by
  induction xs with
  | nil => simp [STRING_SORT]
  | cons a t ih =>
    show x ∈ INORDER_INSERT a (STRING_SORT t) ↔ _
    rw [Aux.mem_INORDER_INSERT, ih, List.mem_cons]

/- HOL4:
Theorem MEM_FOLDR_INORDER_INSERT[simp]:
   !xs x. MEM x (FOLDR INORDER_INSERT [] xs) = MEM x xs
-/
theorem MEM_FOLDR_INORDER_INSERT :
    ∀ (xs : List string) (x : string), (x ∈ List.foldr INORDER_INSERT [] xs) = (x ∈ xs) := by
  intro xs x
  exact propext (Aux.mem_STRING_SORT_iff x xs)

theorem Aux.INORDER_INSERT_perm (a : string) (l : List string) (h : ¬ a ∈ l) :
    (INORDER_INSERT a l).Perm (a :: l) := by
  unfold INORDER_INSERT
  refine List.perm_middle.trans (List.Perm.cons a ?_)
  rw [Aux.FILTER_eq, Aux.FILTER_eq]
  have : l.filter (fun y => decide (string_lt a y)) =
      l.filter (fun y => ! decide (string_lt y a)) := by
    apply List.filter_congr
    intro y hy
    have h1 := Aux.string_lt_trichotomous a y
    have h2 : ¬ a = y := fun e => h (e ▸ hy)
    have h3 : ¬ (string_lt a y ∧ string_lt y a) :=
      fun e => Aux.string_lt_irrefl _ (Aux.string_lt_trans _ _ _ e.1 e.2)
    by_cases h4 : string_lt a y <;> by_cases h5 : string_lt y a <;> simp_all
  rw [this]
  exact List.filter_append_perm _ l

/- HOL4:
Theorem PERM_STRING_SORT:
   ∀ls. ALL_DISTINCT ls ⇒ PERM ls (STRING_SORT ls)
-/
theorem PERM_STRING_SORT :
    ∀ (ls : List string), ALL_DISTINCT ls → PERM ls (STRING_SORT ls) := by
  intro ls h
  rw [Aux.PERM_iff]
  induction ls with
  | nil => exact List.Perm.refl _
  | cons a t ih =>
    have hn : ¬ a ∈ STRING_SORT t := by rw [Aux.mem_STRING_SORT_iff]; exact h.1
    exact ((ih h.2).cons a).trans (Aux.INORDER_INSERT_perm a _ hn).symm

/- HOL4:
Theorem LENGTH_STRING_SORT[simp]:
   ∀ls. ALL_DISTINCT ls ⇒ (LENGTH (STRING_SORT ls) = LENGTH ls)
-/
theorem LENGTH_STRING_SORT :
    ∀ (ls : List string), ALL_DISTINCT ls → (STRING_SORT ls).length = ls.length := by
  intro ls h
  exact (Aux.PERM_iff.mp (PERM_STRING_SORT ls h)).length_eq.symm

/- HOL4:
Theorem MEM_STRING_SORT[simp]:
   ∀ls. set (STRING_SORT ls) = set ls
-/
theorem MEM_STRING_SORT :
    ∀ (ls : List string), LIST_TO_SET (STRING_SORT ls) = LIST_TO_SET ls := by
  intro ls
  apply Aux.set_ext
  intro y
  rw [Aux.mem_LIST_TO_SET, Aux.mem_LIST_TO_SET, Aux.mem_STRING_SORT_iff]

/- HOL4:
Theorem ALL_DISTINCT_STRING_SORT[simp]:
   !xs. ALL_DISTINCT (STRING_SORT xs)
-/
theorem ALL_DISTINCT_STRING_SORT :
    ∀ (xs : List string), ALL_DISTINCT (STRING_SORT xs) := by
  intro xs
  induction xs with
  | nil => exact trivial
  | cons a t ih =>
    show ALL_DISTINCT (INORDER_INSERT a (STRING_SORT t))
    generalize STRING_SORT t = l at ih
    rw [Aux.ALL_DISTINCT_iff] at ih ⊢
    have hf : ∀ P : string → Prop, (FILTER P l).Nodup := by
      intro P; rw [Aux.FILTER_eq]; exact ih.filter _
    have hi := Aux.string_lt_irrefl
    have ht := Aux.string_lt_trans
    unfold INORDER_INSERT
    rw [List.nodup_append]
    refine ⟨hf _, ?_, ?_⟩
    · rw [List.singleton_append, List.nodup_cons]
      refine ⟨?_, hf _⟩
      rw [Aux.mem_FILTER]
      exact fun h => hi a h.2
    · intro x hx y hy e
      subst e
      rw [Aux.mem_FILTER] at hx
      rw [List.singleton_append, List.mem_cons, Aux.mem_FILTER] at hy
      rcases hy with h | ⟨_, h⟩
      · subst h; exact hi _ hx.2
      · exact hi _ (ht _ _ _ hx.2 h)

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
    show ALL_DISTINCT (LIST_INSERT a (LIST_UNION t l2))
    unfold LIST_INSERT
    split
    · exact ih
    · rename_i hn; exact ⟨hn, ih⟩

end

end Candle
