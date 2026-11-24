import CandleLean.Prelude.Basic

/-!
# HOL4 library: pred_set

HOL4 `'a set` is the type `'a -> bool` of predicates; here `HOL.Set α := α → Prop`.
Sets may be infinite.  `x ∈ s` (Lean `Membership`) is HOL4 `x IN s`.
-/

universe u v

namespace HOL

open Classical

noncomputable section

/- HOL4: pred_set$set    'a set = 'a -> bool   (type abbreviation) -/
def Set (α : Type u) : Type u := α → Prop

/- HOL4: bool$IN    IN x s = s x   (IN_DEF) -/
def IN {α : Type u} (x : α) (s : Set α) : Prop := s x

instance {α : Type u} : Membership α (Set α) := ⟨fun s x => IN x s⟩

theorem Aux.mem_def {α : Type u} (x : α) (s : Set α) : (x ∈ s) = s x := rfl

/-- Set comprehension `{x | P x}` (HOL4 `GSPEC (\x. (x, P x))`); written `setOf P`. -/
def setOf {α : Type u} (P : α → Prop) : Set α := P

/- HOL4: pred_set$GSPEC (new_specification)
     GSPECIFICATION: !f v. v IN (GSPEC f) = ?x. (v,T) = f x
   HOL4 `{e x | P x}` is `GSPEC (\x. (e x, P x))`. -/
def GSPEC {α : Type u} {β : Type v} (f : β → α × Prop) : Set α :=
  fun v => ∃ x, (v, True) = f x

/- HOL4: pred_set$EMPTY    EMPTY = (\x:'a.F) -/
def EMPTY {α : Type u} : Set α := fun _ => False

/- HOL4: pred_set$UNIV    UNIV = (\x:'a.T) -/
def UNIV {α : Type u} : Set α := fun _ => True

/- HOL4: pred_set$UNION    UNION s t = {x:'a | x IN s \/ x IN t} -/
def UNION {α : Type u} (s t : Set α) : Set α := setOf fun x => x ∈ s ∨ x ∈ t

/- HOL4: pred_set$INTER    INTER s t = {x:'a | x IN s /\ x IN t} -/
def INTER {α : Type u} (s t : Set α) : Set α := setOf fun x => x ∈ s ∧ x ∈ t

/- HOL4: pred_set$DIFF    DIFF s t = {x:'a | x IN s /\ ~(x IN t)} -/
def DIFF {α : Type u} (s t : Set α) : Set α := setOf fun x => x ∈ s ∧ ¬ x ∈ t

/- HOL4: pred_set$INSERT    INSERT (x:'a) s = {y | (y = x) \/ y IN s} -/
def INSERT {α : Type u} (x : α) (s : Set α) : Set α := setOf fun y => y = x ∨ y ∈ s

/- HOL4: pred_set$SUBSET    SUBSET s t = !x:'a. x IN s ==> x IN t -/
def SUBSET {α : Type u} (s t : Set α) : Prop := ∀ x, x ∈ s → x ∈ t

/- HOL4: pred_set$DISJOINT    DISJOINT (s:'a set) t = ((s INTER t) = EMPTY) -/
def DISJOINT {α : Type u} (s t : Set α) : Prop := INTER s t = EMPTY

instance {α : Type u} : EmptyCollection (Set α) := ⟨EMPTY⟩
instance {α : Type u} : Union (Set α) := ⟨UNION⟩
instance {α : Type u} : Inter (Set α) := ⟨INTER⟩
instance {α : Type u} : SDiff (Set α) := ⟨DIFF⟩
instance {α : Type u} : Insert α (Set α) := ⟨INSERT⟩
instance {α : Type u} : Singleton α (Set α) := ⟨fun x => INSERT x EMPTY⟩
instance {α : Type u} : HasSubset (Set α) := ⟨SUBSET⟩

/- HOL4: pred_set$FINITE
     !s:'a set. FINITE s = !P. P EMPTY /\ (!s. P s ==> !e. P (e INSERT s)) ==> P s -/
def FINITE {α : Type u} (s : Set α) : Prop :=
  ∀ P : Set α → Prop, P EMPTY ∧ (∀ s, P s → ∀ e, P (INSERT e s)) → P s

/- HOL4: pred_set$INFINITE (overload)    INFINITE = \s. ~FINITE s -/
@[reducible] def INFINITE {α : Type u} (s : Set α) : Prop := ¬ FINITE s

/- HOL4: pred_set$IMAGE    IMAGE (f:'a->'b) s = {f x | x IN s} -/
def IMAGE {α : Type u} {β : Type v} (f : α → β) (s : Set α) : Set β :=
  GSPEC fun x => (f x, x ∈ s)

/- HOL4: pred_set$INJ
     INJ (f:'a->'b) s t <=>
       (!x. x IN s ==> (f x) IN t) /\
       (!x y. (x IN s /\ y IN s) ==> (f x = f y) ==> (x = y)) -/
def INJ {α : Type u} {β : Type v} (f : α → β) (s : Set α) (t : Set β) : Prop :=
  (∀ x, x ∈ s → f x ∈ t) ∧ (∀ x y, (x ∈ s ∧ y ∈ s) → f x = f y → x = y)

/- HOL4: pred_set$SURJ
     SURJ (f:'a->'b) s t <=>
       (!x. x IN s ==> (f x) IN t) /\
       (!x. (x IN t) ==> ?y. y IN s /\ (f y = x)) -/
def SURJ {α : Type u} {β : Type v} (f : α → β) (s : Set α) (t : Set β) : Prop :=
  (∀ x, x ∈ s → f x ∈ t) ∧ (∀ x, x ∈ t → ∃ y, y ∈ s ∧ f y = x)

/- HOL4: pred_set$BIJ    BIJ (f:'a->'b) s t <=> INJ f s t /\ SURJ f s t -/
def BIJ {α : Type u} {β : Type v} (f : α → β) (s : Set α) (t : Set β) : Prop :=
  INJ f s t ∧ SURJ f s t

/- HOL4: pred_set$PERMUTES (overload, infix)    PERMUTES = \f s. BIJ f s s -/
@[reducible] def PERMUTES {α : Type u} (f : α → α) (s : Set α) : Prop := BIJ f s s

/-! ### Small lemmas used to build finite maps (not HOL4 targets) -/

/-- A set contained in (the elements of) a list is `FINITE`. -/
theorem Aux.FINITE_of_list_bound {α : Type u} (l : List α) :
    ∀ s : Set α, (∀ x, x ∈ s → x ∈ l) → FINITE s := by
  induction l with
  | nil =>
    intro s hs P ⟨h0, _⟩
    have : s = EMPTY := funext fun x => propext ⟨fun hx => by simpa using hs x hx, False.elim⟩
    exact this ▸ h0
  | cons a l ih =>
    intro s hs P hP
    have hs' : FINITE (fun x => x ∈ s ∧ x ≠ a) :=
      ih _ (fun x ⟨hx, hne⟩ => by
        rcases List.mem_cons.mp (hs x hx) with h | h
        · exact absurd h hne
        · exact h)
    have hP' := hs' P hP
    by_cases ha : a ∈ s
    · have : s = INSERT a (fun x => x ∈ s ∧ x ≠ a) := by
        funext x
        apply propext
        show x ∈ s ↔ (x = a ∨ (x ∈ s ∧ x ≠ a))
        constructor
        · intro hx; by_cases h : x = a
          · exact Or.inl h
          · exact Or.inr ⟨hx, h⟩
        · rintro (h | ⟨h, _⟩)
          · exact h ▸ ha
          · exact h
      rw [this]; exact hP.2 _ hP' a
    · have : s = (fun x => x ∈ s ∧ x ≠ a) := by
        funext x
        apply propext
        constructor
        · intro hx; exact ⟨hx, fun h => ha (h ▸ hx)⟩
        · intro h; exact h.1
      rw [this]; exact hP'

/-- Every `FINITE` set is contained in (the elements of) some list. -/
theorem Aux.FINITE_list_bound {α : Type u} (s : Set α) (h : FINITE s) :
    ∃ l : List α, ∀ x, x ∈ s → x ∈ l := by
  refine h (fun s => ∃ l : List α, ∀ x, x ∈ s → x ∈ l) ⟨⟨[], fun _ h => False.elim h⟩, ?_⟩
  rintro s ⟨l, hl⟩ e
  refine ⟨e :: l, fun x hx => ?_⟩
  rcases hx with h | h
  · exact h ▸ List.mem_cons_self
  · exact List.mem_cons_of_mem _ (hl x h)

end

end HOL
