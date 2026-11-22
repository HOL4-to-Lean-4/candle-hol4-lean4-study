/-
  HOL4 library constants from the theories `finite_map` and `alist`.

  HOL4 `'a |-> 'b` (type `fmap`) is defined as the functions `'a -> 'b + one`
  satisfying `is_fmap`; we use the same representation (`one` = `Unit`).
-/
import CandleLean.Prelude.List

open Classical

/- HOL4: finite_map$is_fmap
   Hol_reln `is_fmap (\a. INR one)
      /\ (!f a b. is_fmap f ==> is_fmap (\x. if x=a then INL b else f x))` -/
inductive is_fmap {α : Type u} {β : Type v} : (α → β ⊕ Unit) → Prop
  | empty : is_fmap (fun _ => .inr ())
  | update (f : α → β ⊕ Unit) (a : α) (b : β) :
      is_fmap f → is_fmap (fun x => if x = a then .inl b else f x)

/- HOL4: finite_map$fmap   `val fmap_TY_DEF = new_type_definition("fmap", EXISTENCE_THM)`
   (HOL4 notation `'a |-> 'b`; `fmap_REP` is `Subtype.val`) -/
def fmap (α : Type u) (β : Type v) : Type (max u v) := {f : α → β ⊕ Unit // is_fmap f}

/- HOL4: finite_map$fmap_REP (representation function of the type definition) -/
def fmap_REP {α : Type u} {β : Type v} (f : fmap α β) : α → β ⊕ Unit := f.1

/- HOL4: finite_map$FEMPTY   `(FEMPTY:'a |-> 'b) = fmap_ABS (\a. INR one)` -/
def FEMPTY {α : Type u} {β : Type v} : fmap α β := ⟨fun _ => .inr (), is_fmap.empty⟩

instance {α : Type u} {β : Type v} : Inhabited (fmap α β) := ⟨FEMPTY⟩

/- HOL4: finite_map$FUPDATE   (HOL4 notation `f |+ (x,y)`)
   FUPDATE (f:'a |-> 'b) (x,y) = fmap_ABS (\a. if a=x then INL y else fmap_REP f a) -/
noncomputable def FUPDATE {α : Type u} {β : Type v} (f : fmap α β) (p : α × β) : fmap α β :=
  ⟨fun a => if a = p.1 then .inl p.2 else fmap_REP f a, is_fmap.update _ _ _ f.2⟩

/- HOL4: finite_map$FAPPLY   (HOL4 notation `f ' x`)
   FAPPLY (f:'a |-> 'b) x = OUTL (fmap_REP f x) -/
noncomputable def FAPPLY {α : Type u} {β : Type v} [Nonempty β] (f : fmap α β) (x : α) : β :=
  OUTL (fmap_REP f x)

/- HOL4: finite_map$FDOM   `FDOM (f:'a |-> 'b) x = ISL (fmap_REP f x)` -/
def FDOM {α : Type u} {β : Type v} (f : fmap α β) : Set α := fun x => ISL (fmap_REP f x)

/- HOL4: finite_map$FLOOKUP
   FLOOKUP f x = if x IN FDOM f then SOME (FAPPLY f x) else NONE -/
noncomputable def FLOOKUP {α : Type u} {β : Type v} [Nonempty β] (f : fmap α β) (x : α) : Option β :=
  if x ∈ FDOM f then some (FAPPLY f x) else none

/- HOL4: finite_map$FEVERY   `FEVERY P f = !x. x IN FDOM f ==> P (x, FAPPLY f x)` -/
def FEVERY {α : Type u} {β : Type v} [Nonempty β] (P : α × β → Prop) (f : fmap α β) : Prop :=
  ∀ x, x ∈ FDOM f → P (x, FAPPLY f x)

/- HOL4: finite_map$FRANGE   `FRANGE f = { y | ?x. x IN FDOM f /\ (FAPPLY f x = y)}` -/
noncomputable def FRANGE {α : Type u} {β : Type v} [Nonempty β] (f : fmap α β) : Set β :=
  {y | ∃ x, x ∈ FDOM f ∧ FAPPLY f x = y}

/- HOL4: finite_map$FUN_FMAP  (new_specification FUN_FMAP_DEF)
   !f P. FINITE P ==> (FDOM (FUN_FMAP f P) = P) /\
                      (!x. x IN P ==> (FAPPLY (FUN_FMAP f P) x = f x))
   Unspecified for infinite `P`: encoded as a choice over all functions
   satisfying the specification. -/
noncomputable def FUN_FMAP {α : Type u} {β : Type v} [Nonempty β] : (α → β) → Set α → fmap α β :=
  Classical.epsilon (fun FUN_FMAP : (α → β) → Set α → fmap α β =>
    ∀ f P, FINITE P → FDOM (FUN_FMAP f P) = P ∧ (∀ x, x ∈ P → FAPPLY (FUN_FMAP f P) x = f x))

/- HOL4: alist$alist_to_fmap   `alist_to_fmap s = FOLDR (\(k,v) f.f|+(k,v)) FEMPTY s` -/
noncomputable def alist_to_fmap {α : Type u} {β : Type v} (s : List (α × β)) : fmap α β :=
  s.foldr (fun kv f => FUPDATE f (kv.1, kv.2)) FEMPTY
