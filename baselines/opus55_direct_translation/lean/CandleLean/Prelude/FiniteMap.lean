import CandleLean.Prelude.List

/-!
# HOL4 library: finite_map, alist

HOL4 `'a |-> 'b` is a type definition over `'a -> 'b + one` restricted to the functions built
from `\a. INR one` by finitely many updates (`is_fmap`).  It is modelled by the structure
`HOL.fmap α β`: a function `α → Option β` (`none` plays the role of `INR one`) together with a
proof that its support is contained in some finite list (equivalent to `is_fmap`).
Two finite maps are equal iff their underlying functions are equal (as in HOL4).
-/

universe u v

namespace HOL

open Classical

noncomputable section

/- HOL4: finite_map$fmap
     Hol_reln `is_fmap (\a. INR one)
          /\ (!f a b. is_fmap f ==> is_fmap (\x. if x=a then INL b else f x))`;
     val fmap_TY_DEF = new_type_definition("fmap", EXISTENCE_THM);   (infix type |->) -/
structure fmap (α : Type u) (β : Type v) where
  /-- HOL4 `fmap_REP`, with `INL b` as `some b` and `INR one` as `none` -/
  rep : α → Option β
  finite_support : ∃ l : List α, ∀ a, rep a ≠ none → a ∈ l

/- HOL4: finite_map$FEMPTY    (FEMPTY:'a |-> 'b) = fmap_ABS (\a. INR one) -/
def FEMPTY {α : Type u} {β : Type v} : fmap α β :=
  ⟨fun _ => none, ⟨[], fun _ h => absurd rfl h⟩⟩

instance {α : Type u} {β : Type v} : Nonempty (fmap α β) := ⟨FEMPTY⟩

/- HOL4: finite_map$FUPDATE (overloaded as |+)
     FUPDATE (f:'a |-> 'b) (x,y) = fmap_ABS (\a. if a=x then INL y else fmap_REP f a) -/
def FUPDATE {α : Type u} {β : Type v} (f : fmap α β) (p : α × β) : fmap α β :=
  ⟨fun a => if a = p.1 then some p.2 else f.rep a, by
    obtain ⟨l, hl⟩ := f.finite_support
    refine ⟨p.1 :: l, fun a ha => ?_⟩
    by_cases h : a = p.1
    · exact h ▸ List.mem_cons_self
    · simp only [h, if_false] at ha
      exact List.mem_cons_of_mem _ (hl a ha)⟩

/- HOL4: finite_map$FAPPLY (overloaded as ')    FAPPLY (f:'a |-> 'b) x = OUTL (fmap_REP f x)
   (`OUTL (INR _)` is unspecified in HOL4: here `ARB`, the same value for every map and key,
   as in HOL4 where it is the fixed value `OUTL (INR one)`) -/
def FAPPLY {α : Type u} {β : Type v} [Nonempty β] (f : fmap α β) (x : α) : β :=
  match f.rep x with
  | some y => y
  | none => ARB

/- HOL4: finite_map$FDOM    FDOM (f:'a |-> 'b) x = ISL (fmap_REP f x) -/
def FDOM {α : Type u} {β : Type v} (f : fmap α β) : Set α := fun x => f.rep x ≠ none

/- HOL4: finite_map$FLOOKUP    FLOOKUP f x = if x IN FDOM f then SOME (FAPPLY f x) else NONE -/
def FLOOKUP {α : Type u} {β : Type v} [Nonempty β] (f : fmap α β) (x : α) : Option β :=
  if x ∈ FDOM f then some (FAPPLY f x) else none

/- HOL4: finite_map$FEVERY    FEVERY P f = !x. x IN FDOM f ==> P (x, FAPPLY f x) -/
def FEVERY {α : Type u} {β : Type v} [Nonempty β] (P : α × β → Prop) (f : fmap α β) : Prop :=
  ∀ x, x ∈ FDOM f → P (x, FAPPLY f x)

/- HOL4: finite_map$FRANGE    FRANGE f = { y | ?x. x IN FDOM f /\ (FAPPLY f x = y)} -/
def FRANGE {α : Type u} {β : Type v} [Nonempty β] (f : fmap α β) : Set β :=
  setOf fun y => ∃ x, x ∈ FDOM f ∧ FAPPLY f x = y

/- HOL4: finite_map$FUN_FMAP (new_specification)
     FUN_FMAP_DEF: !f P. FINITE P ==>
                     (FDOM (FUN_FMAP f P) = P) /\ !x. x IN P ==> (FAPPLY (FUN_FMAP f P) x = f x)
   Encoded as Hilbert choice of a function satisfying the specification. -/
def FUN_FMAP_spec {α : Type u} {β : Type v} [Nonempty β]
    (F : (α → β) → Set α → fmap α β) : Prop :=
  ∀ f P, FINITE P → FDOM (F f P) = P ∧ ∀ x, x ∈ P → FAPPLY (F f P) x = f x

def FUN_FMAP {α : Type u} {β : Type v} [Nonempty β] : (α → β) → Set α → fmap α β :=
  Classical.epsilon (FUN_FMAP_spec (α := α) (β := β))

/-- The HOL4 defining theorem `FUN_FMAP_DEF`. -/
theorem FUN_FMAP_DEF {α : Type u} {β : Type v} [Nonempty β] :
    FUN_FMAP_spec (FUN_FMAP (α := α) (β := β)) := by
  apply Classical.epsilon_spec (p := FUN_FMAP_spec (α := α) (β := β))
  refine ⟨fun f P => if h : FINITE P then
      ⟨fun x => if P x then some (f x) else none, by
        obtain ⟨l, hl⟩ := Aux.FINITE_list_bound P h
        exact ⟨l, fun a ha => hl a (by
          by_cases hp : P a
          · exact hp
          · simp [hp] at ha)⟩⟩
    else FEMPTY, ?_⟩
  intro f P hP
  simp only [hP, dif_pos]
  constructor
  · funext x
    apply propext
    show (if P x then some (f x) else none) ≠ none ↔ P x
    by_cases hp : P x <;> simp [hp]
  · intro x hx
    have hx' : P x := hx
    simp [FAPPLY, hx']

/- HOL4: alist$ALOOKUP
     (ALOOKUP [] q = NONE) /\
     (ALOOKUP ((x,y)::t) q = if x = q then SOME y else ALOOKUP t q) -/
def ALOOKUP {α : Type u} {β : Type v} : List (α × β) → α → Option β
  | [], _ => none
  | (x, y) :: t, q => if x = q then some y else ALOOKUP t q

/- HOL4: alist$alist_to_fmap    alist_to_fmap s = FOLDR (\(k,v) f.f|+(k,v)) FEMPTY s -/
def alist_to_fmap {α : Type u} {β : Type v} (s : List (α × β)) : fmap α β :=
  s.foldr (fun kv f => FUPDATE f (kv.1, kv.2)) FEMPTY

end

end HOL
