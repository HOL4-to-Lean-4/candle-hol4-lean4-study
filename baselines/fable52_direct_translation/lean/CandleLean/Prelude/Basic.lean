/-
  HOL4 library constants: bool, combin, pair, option, sum, arithmetic,
  relation, ternaryComparisons, toto.

  Conventions (see CONVENTIONS.md): HOL `bool` is Lean `Prop`, HOL is classical
  (`open Classical`), every HOL type is non-empty (`[Nonempty α]` where a
  definition needs it).
-/
namespace Candle

noncomputable section
open Classical

/-! ## bool -/

/- HOL4: bool$@ (Hilbert choice), `@x. P x`.
   `select P` is some `x` with `P x` if one exists, and an unspecified element otherwise. -/
def select {α : Type} [Nonempty α] (P : α → Prop) : α := Classical.epsilon P

/- HOL4: bool$SELECT_AX  |- !P x. P x ==> P ($@ P)   (the only property of `@`) -/
theorem select_spec {α : Type} [Nonempty α] {P : α → Prop} (h : ∃ x, P x) :
    P (select P) := Classical.epsilon_spec h

/- HOL4: bool$ARB_DEF  |- ARB = @x. T -/
def ARB {α : Type} [Nonempty α] : α := select (fun _ => True)

/- HOL4: bool$EXISTS_UNIQUE_DEF  |- $?! = (\P. $? P /\ !x y. P x /\ P y ==> (x = y))
   `?!x. P x` is written `EXISTS_UNIQUE (fun x => P x)`. -/
def EXISTS_UNIQUE {α : Type} (P : α → Prop) : Prop :=
  (∃ x, P x) ∧ ∀ x y, P x ∧ P y → x = y

/-! ## combin -/

/- HOL4: combin$K_DEF  |- K = (\x y. x) -/
abbrev K {α β : Type} (x : α) (_y : β) : α := x

/- HOL4: combin$S_DEF  |- S = (\f g x. f x (g x)) -/
abbrev S {α β γ : Type} (f : α → β → γ) (g : α → β) (x : α) : γ := f x (g x)

/- HOL4: combin$I_DEF  |- I = S K K      (so `I x = x`) -/
abbrev I {α : Type} (x : α) : α := x

/- HOL4: combin$C_DEF  |- C = (\f x y. f y x) -/
abbrev C {α β γ : Type} (f : α → β → γ) (x : β) (y : α) : γ := f y x

/- HOL4: combin$o_DEF  |- f o g = (\x. f (g x))
   HOL `f o g` is Lean `f ∘ g` (`Function.comp`); no new constant. -/

/- HOL4: combin$UPDATE_def  |- UPDATE a b = (\f c. if a = c then b else f c)
   HOL notation `(a =+ b) f` is `UPDATE a b f`. -/
def UPDATE {α β : Type} (a : α) (b : β) : (α → β) → α → β :=
  fun f c => if a = c then b else f c

/-! ## pair -/

/- HOL4: pair$FST  |- FST (x,y) = x -/
abbrev FST {α β : Type} (p : α × β) : α := p.1

/- HOL4: pair$SND  |- SND (x,y) = y -/
abbrev SND {α β : Type} (p : α × β) : β := p.2

/- HOL4: pair$UNCURRY  |- UNCURRY f v = f (FST v) (SND v) -/
def UNCURRY {α β γ : Type} (f : α → β → γ) (v : α × β) : γ := f (FST v) (SND v)

/- HOL4: pair$PAIR_MAP  |- (f ## g) p = (f (FST p), g (SND p))      (infixr 490) -/
def PAIR_MAP {α β γ δ : Type} (f : α → γ) (g : β → δ) (p : α × β) : γ × δ :=
  (f (FST p), g (SND p))

infixr:80 " ## " => PAIR_MAP

/- HOL4: pair$LEX_DEF  |- R1 LEX R2 = (\(s,t) (u,v). R1 s u \/ (s = u) /\ R2 t v)
   HOL infix `R1 LEX R2` is `LEX R1 R2`. -/
def LEX {α β : Type} (R1 : α → α → Prop) (R2 : β → β → Prop) : α × β → α × β → Prop :=
  fun p q => R1 p.1 q.1 ∨ p.1 = q.1 ∧ R2 p.2 q.2

/-! ## option -/

/- HOL4: option$OPTION_MAP_DEF
   |- (OPTION_MAP f (SOME x) = SOME (f x)) /\ (OPTION_MAP f NONE = NONE) -/
def OPTION_MAP {α β : Type} (f : α → β) : Option α → Option β
  | some x => some (f x)
  | none => none

/- HOL4: option$OPTION_BIND_def
   |- (OPTION_BIND NONE f = NONE) /\ (OPTION_BIND (SOME x) f = f x) -/
def OPTION_BIND {α β : Type} : Option α → (α → Option β) → Option β
  | none, _ => none
  | some x, f => f x

/-! ## sum -/

/- HOL4: sum$ISL  |- ISL (INL x) = T /\ ISL (INR y) = F -/
def ISL {α β : Type} : Sum α β → Prop
  | .inl _ => True
  | .inr _ => False

/- HOL4: sum$OUTL  |- OUTL (INL x) = x
   (`new_recursive_definition` with a missing clause: `OUTL (INR y)` is unspecified, so `OUTL`
   is an arbitrary function that satisfies the clause.) -/
def OUTL {α β : Type} [Nonempty α] : Sum α β → α :=
  select (fun f => ∀ x, f (.inl x) = x)

/- HOL4: sum$OUTL (the defining theorem of `OUTL`) -/
theorem OUTL_def {α β : Type} [Nonempty α] (x : α) : OUTL (.inl x : Sum α β) = x :=
  select_spec (P := fun f : Sum α β → α => ∀ x, f (.inl x) = x)
    ⟨fun s => match s with | .inl x => x | .inr _ => ARB, fun _ => rfl⟩ x

/-! ## arithmetic (`num` is `Nat`; `-`, `DIV`, `MOD` agree with Lean's on all inputs:
    in this HOL4, `DIV_def |- m DIV n = if n = 0 then 0 else ...` and
    `MOD_def |- m MOD n = if n = 0 then m else ...`). -/

/- HOL4: num$SUC -/
abbrev SUC (n : Nat) : Nat := n + 1

/- HOL4: arithmetic$MAX_DEF  |- MAX m n = if m < n then n else m -/
def MAX (m n : Nat) : Nat := if m < n then n else m

/- HOL4: arithmetic$EVEN  |- (EVEN 0 = T) /\ (EVEN (SUC n) = ~EVEN n) -/
def EVEN : Nat → Prop
  | 0 => True
  | n + 1 => ¬ EVEN n

/- HOL4: arithmetic$DIV2_def  |- DIV2 n = n DIV 2 -/
def DIV2 (n : Nat) : Nat := n / 2

/-! ## relation -/

/- HOL4: relation$transitive_def  |- transitive R = !x y z. R x y /\ R y z ==> R x z -/
def transitive {α : Type} (R : α → α → Prop) : Prop := ∀ x y z, R x y ∧ R y z → R x z

/- HOL4: relation$reflexive_def  |- reflexive R = !x. R x x -/
def reflexive {α : Type} (R : α → α → Prop) : Prop := ∀ x, R x x

/- HOL4: relation$irreflexive_def  |- irreflexive R = !x. ~R x x -/
def irreflexive {α : Type} (R : α → α → Prop) : Prop := ∀ x, ¬ R x x

/- HOL4: relation$trichotomous  |- trichotomous R = !a b. R a b \/ R b a \/ (a = b) -/
def trichotomous {α : Type} (R : α → α → Prop) : Prop := ∀ a b, R a b ∨ R b a ∨ a = b

/- HOL4: relation$RC_DEF  |- RC R x y <=> (x = y) \/ R x y -/
def RC {α : Type} (R : α → α → Prop) (x y : α) : Prop := x = y ∨ R x y

/- HOL4: relation$RTC
   Inductive RTC: (!x. RTC R x x) /\ (!x y z. R x y /\ RTC R y z ==> RTC R x z) End -/
inductive RTC {α : Type} (R : α → α → Prop) : α → α → Prop
  | refl (x : α) : RTC R x x
  | step (x y z : α) : R x y → RTC R y z → RTC R x z

/- HOL4: relation$inv_image_def  |- inv_image R f = (\x y. R (f x) (f y)) -/
def inv_image {α β : Type} (R : β → β → Prop) (f : α → β) : α → α → Prop :=
  fun x y => R (f x) (f y)

/- HOL4: relation$StrongOrder  |- StrongOrder Z <=> irreflexive Z /\ transitive Z -/
def StrongOrder {α : Type} (Z : α → α → Prop) : Prop := irreflexive Z ∧ transitive Z

/- HOL4: relation$StrongLinearOrder
   |- StrongLinearOrder R <=> StrongOrder R /\ trichotomous R -/
def StrongLinearOrder {α : Type} (R : α → α → Prop) : Prop := StrongOrder R ∧ trichotomous R

/-! ## ternaryComparisons, toto -/

/- HOL4: ternaryComparisons  Datatype: ordering = LESS | EQUAL | GREATER End -/
inductive ordering where
  | LESS
  | EQUAL
  | GREATER
deriving DecidableEq, Repr, Inhabited

export ordering (LESS EQUAL GREATER)

/- HOL4: ternaryComparisons$invert_comparison_def
   |- (invert_comparison GREATER = LESS) /\ (invert_comparison LESS = GREATER) /\
      (invert_comparison EQUAL = EQUAL)
   (mlstring: `Overload flip_ord = ``invert_comparison```) -/
def invert_comparison : ordering → ordering
  | GREATER => LESS
  | LESS => GREATER
  | EQUAL => EQUAL

/- HOL4: mlstring  Overload flip_ord = ``invert_comparison`` -/
abbrev flip_ord (c : ordering) : ordering := invert_comparison c

/- HOL4: toto$TotOrd
   |- TotOrd c <=> (!x y. (c x y = EQUAL) <=> (x = y)) /\
                   (!x y. (c x y = GREATER) <=> (c y x = LESS)) /\
                   (!x y z. (c x y = LESS) /\ (c y z = LESS) ==> (c x z = LESS)) -/
def TotOrd {α : Type} (c : α → α → ordering) : Prop :=
  (∀ x y, c x y = EQUAL ↔ x = y) ∧
  (∀ x y, c x y = GREATER ↔ c y x = LESS) ∧
  (∀ x y z, c x y = LESS ∧ c y z = LESS → c x z = LESS)

/- HOL4: toto$TO_of_LinearOrder
   |- TO_of_LinearOrder r x y = if x = y then EQUAL else if r x y then LESS else GREATER -/
def TO_of_LinearOrder {α : Type} (r : α → α → Prop) (x y : α) : ordering :=
  if x = y then EQUAL else if r x y then LESS else GREATER

end

end Candle
