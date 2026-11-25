/-!
# HOL4 library prelude: basics

`ARB`, pairs, combinators, `pred_set` (sets as predicates), `relation` (`RTC`).
HOL4's `bool` is modelled by Lean's `Prop` everywhere (also when it is used as data,
e.g. in `Eq_val : bool -> eq_result`); this is the exact HOL4 reading (`bool` is the type of
propositions and `T = True`, `F = False`).
-/

universe u v w

noncomputable section

open Classical

/- HOL4: bool theory, constant `ARB` : 'a  (an arbitrary but fixed element; every HOL4 type is
   inhabited, in Lean we ask for `Nonempty`). -/
def ARB {α : Sort u} [Nonempty α] : α := Classical.choice inferInstance

/- HOL4: combin theory, `UPDATE a b = \f c. if a = c then b else f c` -/
def UPDATE {α : Type u} {β : Type v} (a : α) (b : β) (f : α → β) : α → β :=
  fun c => if a = c then b else f c

/- HOL4: pair theory, `FST`, `SND`, `UNCURRY`, `CURRY` -/
def FST {α : Type u} {β : Type v} (p : α × β) : α := p.1
def SND {α : Type u} {β : Type v} (p : α × β) : β := p.2
def UNCURRY {α : Type u} {β : Type v} {γ : Sort w} (f : α → β → γ) : α × β → γ :=
  fun p => f p.1 p.2
def CURRY {α : Type u} {β : Type v} {γ : Sort w} (f : α × β → γ) : α → β → γ :=
  fun a b => f (a, b)

/-! ## pred_set: sets are predicates -/

/- HOL4: pred_set theory, type `'a set` = `'a -> bool` -/
def Set (α : Type u) : Type u := α → Prop

namespace Set
instance {α : Type u} : Inhabited (Set α) := ⟨fun _ => False⟩
instance {α : Type u} : Membership α (Set α) := ⟨fun s a => s a⟩
instance {α : Type u} : EmptyCollection (Set α) := ⟨fun _ => False⟩
instance {α : Type u} : Singleton α (Set α) := ⟨fun a => fun x => x = a⟩
instance {α : Type u} : Insert α (Set α) := ⟨fun a s => fun x => x = a ∨ s x⟩
instance {α : Type u} : Union (Set α) := ⟨fun s t => fun x => s x ∨ t x⟩
instance {α : Type u} : Inter (Set α) := ⟨fun s t => fun x => s x ∧ t x⟩
instance {α : Type u} : HasSubset (Set α) := ⟨fun s t => ∀ x, s x → t x⟩
/-- `{x | p x}` (HOL4 `GSPEC`) is written `setOf (fun x => p x)` -/
def setOf {α : Type u} (p : α → Prop) : Set α := p
theorem ext {α : Type u} {s t : Set α} (h : ∀ x, s x ↔ t x) : s = t :=
  funext fun x => propext (h x)
end Set

/- HOL4: pred_set, `UNIV` (written 𝕌(:'a)) -/
def UNIV {α : Type u} : Set α := fun _ => True
/- HOL4: pred_set, `x IN s` -/
def IN {α : Type u} (x : α) (s : Set α) : Prop := s x
/- HOL4: pred_set, `DIFF` : `s DIFF t = {x | x IN s /\ x NOTIN t}` -/
def DIFF {α : Type u} (s t : Set α) : Set α := fun x => s x ∧ ¬ t x
/- HOL4: pred_set, `DISJOINT s t = (s INTER t = {})` -/
def DISJOINT {α : Type u} (s t : Set α) : Prop := s ∩ t = ∅
/- HOL4: pred_set, `IMAGE f s = {f x | x IN s}` -/
def IMAGE {α : Type u} {β : Type v} (f : α → β) (s : Set α) : Set β :=
  fun y => ∃ x, s x ∧ f x = y
/- HOL4: pred_set, `BIGUNION P = {x | ?s. s IN P /\ x IN s}` -/
def BIGUNION {α : Type u} (P : Set (Set α)) : Set α := fun x => ∃ s, P s ∧ s x
/- HOL4: pred_set, `FINITE` (inductive: empty set and `FINITE s ==> FINITE (e INSERT s)`).
   Here: contained in a finite list (equivalent). -/
def FINITE {α : Type u} (s : Set α) : Prop := ∃ l : List α, ∀ x, s x → x ∈ l
/- HOL4: pred_set, `CARD s = if FINITE s then ITSET (\x n. SUC n) s 0 else 0`;
   for finite `s` this is the number of elements. -/
def CARD {α : Type u} (s : Set α) : Nat :=
  if FINITE s then
    Classical.epsilon (fun n : Nat => ∃ l : List α, l.Nodup ∧ (∀ x, x ∈ l ↔ s x) ∧ l.length = n)
  else 0
/- HOL4: pred_set, `INJ f s t` -/
def INJ {α : Type u} {β : Type v} (f : α → β) (s : Set α) (t : Set β) : Prop :=
  (∀ x, s x → t (f x)) ∧ ∀ x y, s x → s y → f x = f y → x = y
/- HOL4: pred_set, `SURJ f s t` -/
def SURJ {α : Type u} {β : Type v} (f : α → β) (s : Set α) (t : Set β) : Prop :=
  (∀ x, s x → t (f x)) ∧ ∀ x, t x → ∃ y, s y ∧ f y = x
/- HOL4: pred_set, `BIJ f s t = INJ f s t /\ SURJ f s t` -/
def BIJ {α : Type u} {β : Type v} (f : α → β) (s : Set α) (t : Set β) : Prop :=
  INJ f s t ∧ SURJ f s t

/-! ## relation -/

/- HOL4: relation theory, `RTC R` the reflexive transitive closure, inductively defined by
   `RTC R x x` and `R x y /\ RTC R y z ==> RTC R x z`. -/
inductive RTC {α : Type u} (R : α → α → Prop) : α → α → Prop
  | refl (x : α) : RTC R x x
  | step (x y z : α) : R x y → RTC R y z → RTC R x z

end
