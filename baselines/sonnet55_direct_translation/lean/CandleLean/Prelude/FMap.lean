import CandleLean.Prelude.List
/-
  HOL4 library constants, part 3: finite maps (finite_mapTheory, alistTheory).
  `'a |-> 'b` is modelled as a function to `Option` with finite support.
  (Lean has no finite map type in core/Batteries with the same extensional behaviour.)
-/
namespace HOL

universe u v w

open Classical

noncomputable section

/- HOL4: finite_mapTheory type `'a |-> 'b` (`fmap`). A finite map is a partial function
   whose domain is finite. Two finite maps are equal iff their lookup functions are equal
   (extensionality, `FMap.ext`). -/
structure FMap (α : Type u) (β : Type v) where
  lookup : α → Option β
  finite : ∃ l : List α, ∀ a, (lookup a).isSome → a ∈ l

@[ext] theorem FMap.ext {α : Type u} {β : Type v} {f g : FMap α β} (h : f.lookup = g.lookup) : f = g := by
  cases f; cases g; simp at h; subst h; rfl

namespace FMap
variable {α : Type u} {β : Type v}
end FMap

variable {α : Type u} {β : Type v}

/- HOL4: FEMPTY_DEF -/
def FEMPTY : FMap α β := ⟨fun _ => none, ⟨[], fun a h => by simp at h⟩⟩

/- HOL4: FDOM_DEF: FDOM f x = ISL (fmap_REP f x). `FDOM f` is a set. -/
def FDOM (f : FMap α β) : Set α := fun x => (f.lookup x).isSome

/- HOL4: FLOOKUP_DEF: FLOOKUP f x = if x ∈ FDOM f then SOME (f ' x) else NONE -/
def FLOOKUP (f : FMap α β) (x : α) : Option β := f.lookup x

/- HOL4: FAPPLY_DEF (infix ' ): f ' x = OUTL (fmap_REP f x); unspecified outside FDOM f -/
def FAPPLY [Inhabited β] (f : FMap α β) (x : α) : β :=
  match f.lookup x with
  | some y => y
  | none => ARB

/- HOL4: FUPDATE_DEF (infix |+): f |+ (x,y) -/
def FUPDATE (f : FMap α β) (p : α × β) : FMap α β :=
  ⟨fun a => if a = p.1 then some p.2 else f.lookup a,
   by
     obtain ⟨l, hl⟩ := f.finite
     refine ⟨p.1 :: l, fun a h => ?_⟩
     by_cases ha : a = p.1
     · simp [ha]
     · simp [ha] at h
       exact List.mem_cons_of_mem _ (hl a h)⟩
scoped infixl:600 " |+ " => FUPDATE

/- HOL4: FUNION_DEF (infixl ⊌): FDOM (f ⊌ g) = FDOM f ∪ FDOM g;
   (f ⊌ g) ' x = if x ∈ FDOM f then f ' x else g ' x -/
def FUNION (f g : FMap α β) : FMap α β :=
  ⟨fun a => match f.lookup a with | some y => some y | none => g.lookup a,
   by
     obtain ⟨l1, h1⟩ := f.finite
     obtain ⟨l2, h2⟩ := g.finite
     refine ⟨l1 ++ l2, fun a h => ?_⟩
     cases hf : f.lookup a with
     | some y => simp [hf] at h; exact List.mem_append_left _ (h1 a (by simp [hf]))
     | none => simp [hf] at h; exact List.mem_append_right _ (h2 a h)⟩

/- HOL4: FRANGE_DEF: FRANGE f = {y | ∃x. x ∈ FDOM f ∧ f ' x = y} -/
def FRANGE (f : FMap α β) : Set β := fun y => ∃ x, f.lookup x = some y

/- HOL4: FEVERY_DEF: FEVERY P f = ∀x. x ∈ FDOM f ⇒ P (x, f ' x) -/
def FEVERY (P : α × β → Prop) (f : FMap α β) : Prop :=
  ∀ x y, f.lookup x = some y → P (x, y)

/- HOL4: alistTheory alist_to_fmap_def: alist_to_fmap s = FOLDR (λ(k,v) f. f |+ (k,v)) FEMPTY s -/
def alist_to_fmap (s : List (α × β)) : FMap α β :=
  s.foldr (fun kv f => f |+ kv) FEMPTY

/- HOL4: FUN_FMAP_DEF (new_specification):
   FINITE P ⇒ FDOM (FUN_FMAP f P) = P ∧ ∀x. x ∈ P ⇒ FUN_FMAP f P ' x = f x.
   For infinite P the HOL4 value is unspecified; here FEMPTY. -/
def FUN_FMAP (f : α → β) (P : Set α) : FMap α β :=
  if h : FINITE P then
    ⟨fun a => if a ∈ P then some (f a) else none,
     by
       obtain ⟨l, hl⟩ := h
       exact ⟨l, fun a ha => by
         by_cases hp : a ∈ P
         · exact hl a hp
         · simp [hp] at ha⟩⟩
  else FEMPTY

end

end HOL
