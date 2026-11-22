/-
  HOL4 library constants, part 1: sets, options, pairs, combinators,
  relations, arithmetic, choice.
  Everything here lives in namespace `HOL` and keeps the HOL4 name.
  HOL4 `bool` is modelled by Lean `Prop` (classical logic, `Classical.propDecidable`).
-/
namespace HOL

universe u v w

open Classical

noncomputable section

/- HOL4: ARB (boolTheory): an arbitrary (unspecified) element. Types are non-empty in HOL4;
   in Lean we require `Inhabited` where HOL4 uses `ARB`. -/
def ARB {α : Sort u} [Inhabited α] : α := default

/-- HOL4 Hilbert choice operator `@x. P x`. (`Classical.epsilon`). -/
abbrev ε {α : Sort u} [Nonempty α] (P : α → Prop) : α := Classical.epsilon P

/-! ## Sets (pred_setTheory) -/

/- HOL4: type_abbrev "set" ``:'a -> bool``  (pred_set). Here a one-field wrapper-free `def`. -/
def Set (α : Type u) : Type u := α → Prop

namespace Set
protected def mem {α : Type u} (s : Set α) (a : α) : Prop := s a
end Set

instance {α : Type u} : Membership α (Set α) := ⟨Set.mem⟩

/-- `{x | P x}` (HOL4: `{x | P x}`, i.e. `GSPEC`). -/
def setOf {α : Type u} (p : α → Prop) : Set α := p

syntax "{" ident " | " term "}" : term
macro_rules
  | `({ $x:ident | $p }) => `(HOL.setOf (fun $x => $p))

theorem mem_setOf_eq {α : Type u} {p : α → Prop} {a : α} : (a ∈ setOf p) = p a := rfl
theorem mem_def {α : Type u} {s : Set α} {a : α} : (a ∈ s) = s a := rfl

/-- Extensionality for sets (HOL4: EXTENSION). -/
theorem Set.ext {α : Type u} {s t : Set α} (h : ∀ x, x ∈ s ↔ x ∈ t) : s = t :=
  funext fun x => propext (h x)

/- HOL4: pred_set EMPTY_DEF: {} = (λx. F) -/
instance {α : Type u} : EmptyCollection (Set α) := ⟨fun _ => False⟩
/- HOL4: UNIV_DEF: UNIV = (λx. T) -/
def UNIV {α : Type u} : Set α := fun _ => True
/- HOL4: INSERT_DEF: x INSERT s = {y | y = x ∨ y ∈ s} -/
instance {α : Type u} : Insert α (Set α) := ⟨fun a s => fun y => y = a ∨ y ∈ s⟩
instance {α : Type u} : Singleton α (Set α) := ⟨fun a => fun y => y = a⟩
/- HOL4: UNION_DEF, INTER_DEF, DIFF_DEF, SUBSET_DEF -/
instance {α : Type u} : Union (Set α) := ⟨fun s t => fun x => x ∈ s ∨ x ∈ t⟩
instance {α : Type u} : Inter (Set α) := ⟨fun s t => fun x => x ∈ s ∧ x ∈ t⟩
instance {α : Type u} : SDiff (Set α) := ⟨fun s t => fun x => x ∈ s ∧ x ∉ t⟩
instance {α : Type u} : HasSubset (Set α) := ⟨fun s t => ∀ x, x ∈ s → x ∈ t⟩

/- HOL4: DISJOINT_DEF: DISJOINT s t = (s ∩ t = {}) -/
def DISJOINT {α : Type u} (s t : Set α) : Prop := s ∩ t = ∅

/- HOL4: IMAGE_DEF: IMAGE f s = {f x | x ∈ s} -/
def IMAGE {α : Type u} {β : Type v} (f : α → β) (s : Set α) : Set β := fun y => ∃ x, x ∈ s ∧ y = f x

/- HOL4: FINITE_DEF (inductive): FINITE s = ∀P. P {} ∧ (∀s. P s ⇒ ∀e. e ∉ s ⇒ P (e INSERT s)) ⇒ P s.
   Equivalent formulation used here: s is contained in some list. -/
def FINITE {α : Type u} (s : Set α) : Prop := ∃ l : List α, ∀ x, x ∈ s → x ∈ l
/- HOL4: INFINITE s = ¬FINITE s -/
def INFINITE {α : Type u} (s : Set α) : Prop := ¬ FINITE s

/- HOL4: INJ_DEF: INJ f s t = (∀x. x ∈ s ⇒ f x ∈ t) ∧ ∀x y. x ∈ s ∧ y ∈ s ∧ f x = f y ⇒ x = y -/
def INJ {α : Type u} {β : Type v} (f : α → β) (s : Set α) (t : Set β) : Prop :=
  (∀ x, x ∈ s → f x ∈ t) ∧ ∀ x y, x ∈ s → y ∈ s → f x = f y → x = y
/- HOL4: SURJ_DEF: SURJ f s t = (∀x. x ∈ s ⇒ f x ∈ t) ∧ ∀x. x ∈ t ⇒ ∃y. y ∈ s ∧ f y = x -/
def SURJ {α : Type u} {β : Type v} (f : α → β) (s : Set α) (t : Set β) : Prop :=
  (∀ x, x ∈ s → f x ∈ t) ∧ ∀ x, x ∈ t → ∃ y, y ∈ s ∧ f y = x
/- HOL4: BIJ_DEF: BIJ f s t = INJ f s t ∧ SURJ f s t -/
def BIJ {α : Type u} {β : Type v} (f : α → β) (s : Set α) (t : Set β) : Prop :=
  INJ f s t ∧ SURJ f s t
/- HOL4: PERMUTES_DEF (pred_set): f PERMUTES s = (∀x. x ∉ s ⇒ f x = x) ∧ BIJ f s s -/
def PERMUTES {α : Type u} (f : α → α) (s : Set α) : Prop :=
  (∀ x, x ∉ s → f x = x) ∧ BIJ f s s

/-! ## Options, pairs, combinators -/

/- HOL4: optionTheory OPTION_MAP, OPTION_BIND -/
abbrev OPTION_MAP {α : Type u} {β : Type v} (f : α → β) (o : Option α) : Option β := Option.map f o
abbrev OPTION_BIND {α : Type u} {β : Type v} (o : Option α) (f : α → Option β) : Option β := Option.bind o f
/- HOL4: THE-like total function from misc; (`the_def`) is in Candle.Misc -/

/- HOL4: pairTheory FST, SND, UNCURRY, CURRY -/
abbrev FST {α : Type u} {β : Type v} (p : α × β) : α := p.1
abbrev SND {α : Type u} {β : Type v} (p : α × β) : β := p.2
abbrev UNCURRY {α : Type u} {β : Type v} {γ : Sort w} (f : α → β → γ) (p : α × β) : γ := f p.1 p.2
abbrev CURRY {α : Type u} {β : Type v} {γ : Sort w} (f : α × β → γ) (a : α) (b : β) : γ := f (a, b)
/- HOL4: pairTheory PAIR_MAP (infix ##): (f ## g) p = (f (FST p), g (SND p)) -/
def PAIR_MAP {α : Type u} {β : Type v} {γ : Type w} {δ : Type _} (f : α → γ) (g : β → δ) (p : α × β) : γ × δ :=
  (f p.1, g p.2)
scoped infixr:90 " ## " => PAIR_MAP

/- HOL4: combinTheory I, K, o, C, S, UPDATE -/
def I {α : Sort u} (x : α) : α := x
def K {α : Sort u} {β : Sort v} (x : α) (_ : β) : α := x
def C {α : Sort u} {β : Sort v} {γ : Sort w} (f : α → β → γ) (x : β) (y : α) : γ := f y x
/- HOL4: combinTheory.UPDATE_def: (a =+ b) f = λc. if a = c then b else f c -/
def UPDATE {α : Type u} {β : Sort v} (a : α) (b : β) (f : α → β) : α → β :=
  fun c => if a = c then b else f c
/-- `(a =+ b)` is `UPDATE a b` (HOL4: infix `=+`). -/
scoped infix:300 " =+ " => UPDATE

/- HOL4: boolTheory EXISTS_UNIQUE_DEF: ?!x. P x = (∃x. P x) ∧ ∀x y. P x ∧ P y ⇒ x = y -/
def EXISTS_UNIQUE {α : Sort u} (P : α → Prop) : Prop := (∃ x, P x) ∧ ∀ x y, P x ∧ P y → x = y

/-! ## Relations (relationTheory, pairTheory, listTheory) -/

section rel
variable {α : Type u} {β : Type v}
/- HOL4: relationTheory -/
def reflexive (R : α → α → Prop) : Prop := ∀ x, R x x
def irreflexive (R : α → α → Prop) : Prop := ∀ x, ¬ R x x
def transitive (R : α → α → Prop) : Prop := ∀ x y z, R x y ∧ R y z → R x z
def symmetric (R : α → α → Prop) : Prop := ∀ x y, R x y = R y x
def antisymmetric (R : α → α → Prop) : Prop := ∀ x y, R x y ∧ R y x → x = y
def trichotomous (R : α → α → Prop) : Prop := ∀ a b, R a b ∨ R b a ∨ a = b
def StrongOrder (Z : α → α → Prop) : Prop := irreflexive Z ∧ transitive Z
def StrongLinearOrder (R : α → α → Prop) : Prop := StrongOrder R ∧ trichotomous R
/- HOL4: RC_DEF: RC R x y ⇔ x = y ∨ R x y -/
def RC (R : α → α → Prop) (x y : α) : Prop := x = y ∨ R x y
/- HOL4: RTC_DEF: RTC R x y = ∀P. (∀x. P x x) ∧ (∀x y z. R x y ∧ P y z ⇒ P x z) ⇒ P x y.
   Encoded as the (equivalent) inductive definition of the reflexive transitive closure. -/
inductive RTC (R : α → α → Prop) : α → α → Prop
  | refl (x : α) : RTC R x x
  | step {x y z : α} : R x y → RTC R y z → RTC R x z
/- HOL4: relationTheory.inv_image: inv_image R f x y = R (f x) (f y) -/
def inv_image (R : β → β → Prop) (f : α → β) (x y : α) : Prop := R (f x) (f y)
/- HOL4: pairTheory LEX_DEF: (R1 LEX R2) (s,t) (u,v) = R1 s u ∨ (s = u ∧ R2 t v) -/
def LEX (R1 : α → α → Prop) (R2 : β → β → Prop) : α × β → α × β → Prop :=
  fun p q => R1 p.1 q.1 ∨ (p.1 = q.1 ∧ R2 p.2 q.2)
end rel

/-! ## Arithmetic (arithmeticTheory) -/

/- HOL4: MAX_DEF: MAX m n = if m < n then n else m -/
def MAX (m n : Nat) : Nat := if m < n then n else m
/- HOL4: MIN_DEF: MIN m n = if m < n then m else n -/
def MIN (m n : Nat) : Nat := if m < n then m else n
/- HOL4: EVEN (arithmeticTheory): EVEN n ⇔ ∃m. n = 2*m -/
def EVEN (n : Nat) : Prop := ∃ m, n = 2 * m
/- HOL4: ODD n ⇔ ∃m. n = SUC (2*m) -/
def ODD (n : Nat) : Prop := ∃ m, n = (2 * m).succ
/- HOL4: DIV2_def: DIV2 n = n DIV 2 -/
def DIV2 (n : Nat) : Nat := n / 2

/-! ## Ordering (ternaryComparisons / comparison) -/

/- HOL4: `ordering` = LESS | EQUAL | GREATER is `Ordering` = lt | eq | gt -/
abbrev ordering := Ordering
abbrev LESS : Ordering := Ordering.lt
abbrev EQUAL : Ordering := Ordering.eq
abbrev GREATER : Ordering := Ordering.gt
/- HOL4: ternaryComparisons.invert_comparison (Overload flip_ord in holSyntaxExtra/mlstring) -/
def invert_comparison : Ordering → Ordering
  | .gt => .lt
  | .lt => .gt
  | .eq => .eq
abbrev flip_ord := invert_comparison

/- HOL4: totoTheory.TotOrd -/
def TotOrd {α : Type u} (c : α → α → Ordering) : Prop :=
  (∀ x y, (c x y = EQUAL) ↔ (x = y)) ∧
  (∀ x y, (c x y = GREATER) ↔ (c y x = LESS)) ∧
  (∀ x y z, c x y = LESS ∧ c y z = LESS → c x z = LESS)
/- HOL4: totoTheory.TO_of_LinearOrder -/
def TO_of_LinearOrder {α : Type u} (r : α → α → Prop) (x y : α) : Ordering :=
  if x = y then EQUAL else if r x y then LESS else GREATER

/- HOL4: numeralTheory/primWFTheory LEAST_DEF: (LEAST) P = (@n. P n ∧ ∀n'. n' < n ⇒ ¬P n') -/
def LEAST (P : Nat → Prop) : Nat := Classical.epsilon (fun n => P n ∧ ∀ n', n' < n → ¬ P n')

end

end HOL
