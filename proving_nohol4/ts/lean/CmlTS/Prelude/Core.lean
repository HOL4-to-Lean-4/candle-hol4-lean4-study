/-
HOL4 library constants from `bool`, `combin`, `pair`, `option`, `relation`
and `ternaryComparisons`.
-/

namespace CmlTS

noncomputable section

open scoped Classical

/- HOL4: bool$ARB  (the unspecified element of a type; `ARB` is also the value
   HOL4 gives to the missing cases of an incomplete set of equations) -/
def ARB {α : Type} [Nonempty α] : α := Classical.choice inferInstance

/- HOL4: min$@  (Hilbert choice, `@x. P x`) -/
def select {α : Type} [Nonempty α] (P : α → Prop) : α := Classical.epsilon P

/- HOL4: combin$I   I = S K K, i.e. `I x = x` -/
def I {α : Type} (x : α) : α := x

/- HOL4: combin$K   K = \x y. x -/
def K {α β : Type} (x : α) (_ : β) : α := x

/- HOL4: combin$C   C = \f x y. f y x -/
def C {α β γ : Type} (f : α → β → γ) (x : β) (y : α) : γ := f y x

/- HOL4: combin$UPDATE   UPDATE a b = \f c. if a = c then b else f c -/
def UPDATE {α β : Type} (a : α) (b : β) : (α → β) → α → β :=
  fun f c => if a = c then b else f c

/- HOL4: pair$UNCURRY   UNCURRY f v = f (FST v) (SND v) -/
def UNCURRY {α β γ : Type} (f : α → β → γ) (v : α × β) : γ := f v.1 v.2

/- HOL4: option$THE   THE (SOME x) = x  (unspecified on NONE) -/
def THE {α : Type} [Nonempty α] : Option α → α
  | some x => x
  | none => ARB

/- HOL4: relation$RTC
   Inductive RTC:
     (!x. RTC R x x) /\
     (!x y z. R x y /\ RTC R y z ==> RTC R x z)
   End -/
inductive RTC {α : Type} (R : α → α → Prop) : α → α → Prop
  | refl (x : α) : RTC R x x
  | step (x y z : α) : R x y → RTC R y z → RTC R x z

/- HOL4: ternaryComparisons$ordering
   Datatype: ordering = LESS | EQUAL | GREATER -/
inductive ordering
  | LESS
  | EQUAL
  | GREATER

end

end CmlTS
