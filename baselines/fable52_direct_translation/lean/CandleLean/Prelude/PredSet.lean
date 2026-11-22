/-
  HOL4 library constants: pred_set.

  HOL `'a set` (= `'a -> bool`) is `Candle.Set α` (= `α → Prop`).
-/
import CandleLean.Prelude.Basic

namespace Candle

noncomputable section
open Classical

/- HOL4: pred_set  Type `:'a set` = `:'a -> bool` -/
def Set (α : Type) : Type := α → Prop

/- HOL4: bool$IN_DEF  |- $IN = (\x f. f x)       (`x IN s` is Lean `x ∈ s`, `x NOTIN s` is `x ∉ s`) -/
instance {α : Type} : Membership α (Set α) := ⟨fun s x => s x⟩

/- HOL4: pred_set$GSPECIFICATION (simple form)  `{x | P x}`: the set of all `x` with `P x`.
   Lean notation `{x | P x}` and `{x : τ | P x}` (below). -/
def setOf {α : Type} (P : α → Prop) : Set α := P

syntax:max (priority := high) "{" ident " | " term "}" : term
syntax:max (priority := high) "{" ident " : " term " | " term "}" : term
macro_rules
  | `({ $x:ident | $p }) => `(Candle.setOf fun $x => $p)
  | `({ $x:ident : $t | $p }) => `(Candle.setOf fun ($x : $t) => $p)

/- HOL4: pred_set$GSPECIFICATION  |- !f v. v IN GSPEC f <=> ?x. (v,T) = f x
   (general set comprehension `{t x | P x}` = `GSPEC (\x. (t x, P x))`) -/
def GSPEC {α β : Type} (f : β → α × Prop) : Set α :=
  fun v => ∃ x, (v, True) = f x

/- HOL4: pred_set$EMPTY_DEF  |- EMPTY = (\x. F)      (`{}`, `∅`; Lean notation `∅`) -/
def EMPTY {α : Type} : Set α := fun _ => False

instance {α : Type} : EmptyCollection (Set α) := ⟨EMPTY⟩

/- HOL4: pred_set$UNIV_DEF  |- UNIV = (\x. T) -/
def UNIV {α : Type} : Set α := fun _ => True

/- HOL4: pred_set$SUBSET_DEF  |- s SUBSET t <=> !x. x IN s ==> x IN t    (Lean notation `s ⊆ t`) -/
def SUBSET {α : Type} (s t : Set α) : Prop := ∀ x, x ∈ s → x ∈ t

instance {α : Type} : HasSubset (Set α) := ⟨SUBSET⟩

/- HOL4: pred_set$UNION_DEF  |- s UNION t = {x | x IN s \/ x IN t}    (Lean notation `s ∪ t`) -/
def UNION {α : Type} (s t : Set α) : Set α := {x | x ∈ s ∨ x ∈ t}

instance {α : Type} : Union (Set α) := ⟨UNION⟩

/- HOL4: pred_set$INTER_DEF  |- s INTER t = {x | x IN s /\ x IN t}    (Lean notation `s ∩ t`) -/
def INTER {α : Type} (s t : Set α) : Set α := {x | x ∈ s ∧ x ∈ t}

instance {α : Type} : Inter (Set α) := ⟨INTER⟩

/- HOL4: pred_set$DIFF_DEF  |- s DIFF t = {x | x IN s /\ ~(x IN t)}    (Lean notation `s \ t`) -/
def DIFF {α : Type} (s t : Set α) : Set α := {x | x ∈ s ∧ ¬ (x ∈ t)}

instance {α : Type} : SDiff (Set α) := ⟨DIFF⟩

/- HOL4: pred_set$INSERT_DEF  |- x INSERT s = {y | (y = x) \/ y IN s}
   (HOL `x INSERT s` is `INSERT x s`; HOL `{a; b}` is Lean `{a, b}`, HOL `{a}` is Lean `{a}`) -/
def INSERT {α : Type} (x : α) (s : Set α) : Set α := {y | y = x ∨ y ∈ s}

instance {α : Type} : Insert α (Set α) := ⟨INSERT⟩
instance {α : Type} : Singleton α (Set α) := ⟨fun x => INSERT x EMPTY⟩

/- HOL4: pred_set$DISJOINT_DEF  |- DISJOINT s t <=> (s INTER t = EMPTY) -/
def DISJOINT {α : Type} (s t : Set α) : Prop := s ∩ t = ∅

/- HOL4: pred_set$IMAGE_DEF  |- IMAGE f s = {f x | x IN s} -/
def IMAGE {α β : Type} (f : α → β) (s : Set α) : Set β := {y | ∃ x, y = f x ∧ x ∈ s}

/- HOL4: pred_set$INJ_DEF
   |- INJ f s t <=> (!x. x IN s ==> f x IN t) /\
                    (!x y. x IN s /\ y IN s ==> (f x = f y) ==> (x = y)) -/
def INJ {α β : Type} (f : α → β) (s : Set α) (t : Set β) : Prop :=
  (∀ x, x ∈ s → f x ∈ t) ∧ (∀ x y, x ∈ s ∧ y ∈ s → f x = f y → x = y)

/- HOL4: pred_set$SURJ_DEF
   |- SURJ f s t <=> (!x. x IN s ==> f x IN t) /\ (!x. x IN t ==> ?y. y IN s /\ (f y = x)) -/
def SURJ {α β : Type} (f : α → β) (s : Set α) (t : Set β) : Prop :=
  (∀ x, x ∈ s → f x ∈ t) ∧ (∀ x, x ∈ t → ∃ y, y ∈ s ∧ f y = x)

/- HOL4: pred_set$BIJ_DEF  |- BIJ f s t <=> INJ f s t /\ SURJ f s t -/
def BIJ {α β : Type} (f : α → β) (s : Set α) (t : Set β) : Prop := INJ f s t ∧ SURJ f s t

/- HOL4: pred_set  Overload PERMUTES = ``\f s. BIJ f s s``    (HOL infix `f PERMUTES s`) -/
abbrev PERMUTES {α : Type} (f : α → α) (s : Set α) : Prop := BIJ f s s

/- HOL4: pred_set$FINITE_DEF
   |- !s. FINITE s <=> !P. P EMPTY /\ (!s. P s ==> !e. P (e INSERT s)) ==> P s -/
def FINITE {α : Type} (s : Set α) : Prop :=
  ∀ P : Set α → Prop, P ∅ ∧ (∀ s, P s → ∀ e, P (INSERT e s)) → P s

/- HOL4: pred_set  Overload INFINITE = ``\s. ~FINITE s`` -/
abbrev INFINITE {α : Type} (s : Set α) : Prop := ¬ FINITE s

end

end Candle
