import CmlTS.Prelude.List
/-
  HOL4 library constants: `finite_map` (and `alist$alist_to_fmap`).
-/
set_option autoImplicit false

namespace CmlTS
open Classical

universe u v w

/- HOL4: finite_map, ('a,'b) fmap, written 'a |-> 'b.
   "The representation is the type 'a -> ('b + one) where only a finite number of the 'a map to a
   'b and the rest map to one."  Here `INL y` is `some y` and `INR one` is `none`. -/
structure fmap (α : Type u) (β : Type v) : Type (max u v) where
  /-- HOL4: finite_map$FLOOKUP -/
  FLOOKUP : α → Option β
  finite : ∃ l : List α, ∀ a, FLOOKUP a ≠ none → a ∈ l

/- HOL4: finite_map$FLOOKUP:  FLOOKUP f x = if x IN FDOM f then SOME (FAPPLY f x) else NONE -/
export fmap (FLOOKUP)

namespace fmap
variable {α : Type u} {β : Type v}

theorem ext {f g : fmap α β} (h : ∀ a, f.FLOOKUP a = g.FLOOKUP a) : f = g := by
  cases f; cases g; simp at h; congr; exact funext h

end fmap

section
variable {α : Type u} {β : Type v} {γ : Type w}

/- HOL4: finite_map$FEMPTY:  FEMPTY = fmap_ABS (\a. INR one) -/
def FEMPTY : fmap α β := ⟨fun _ => none, ⟨[], by simp⟩⟩

instance : Inhabited (fmap α β) := ⟨FEMPTY⟩

/- HOL4: finite_map$FUPDATE (infix |+):
   FUPDATE f (x,y) = fmap_ABS (\a. if a=x then INL y else fmap_REP f a) -/
noncomputable def FUPDATE (f : fmap α β) (p : α × β) : fmap α β :=
  ⟨fun a => if a = p.1 then some p.2 else FLOOKUP f a, by
    obtain ⟨l, hl⟩ := f.finite
    refine ⟨p.1 :: l, fun a ha => ?_⟩
    by_cases h : a = p.1
    · simp [h]
    · simp only [h, if_false] at ha
      exact List.mem_cons_of_mem _ (hl a ha)⟩

/- HOL4: finite_map$FDOM:  FDOM f x = ISL (fmap_REP f x) -/
def FDOM (f : fmap α β) : Set α := {x | FLOOKUP f x ≠ none}

/- HOL4: finite_map$FAPPLY (infix '):  FAPPLY f x = OUTL (fmap_REP f x) -/
noncomputable def FAPPLY [Nonempty β] (f : fmap α β) (x : α) : β := THE (FLOOKUP f x)

/- HOL4: finite_map$FUPDATE_LIST (infix |++):  FUPDATE_LIST = FOLDL FUPDATE -/
noncomputable def FUPDATE_LIST (f : fmap α β) (l : List (α × β)) : fmap α β :=
  List.foldl FUPDATE f l

/- HOL4: finite_map$SUBMAP:
   $SUBMAP f g = !x. x IN FDOM f ==> x IN FDOM g /\ (FAPPLY f x = FAPPLY g x)
   Stated with FLOOKUP (HOL4 theorem FLOOKUP_SUBMAP / SUBMAP_FLOOKUP_EQN), so that no `Nonempty`
   instance is needed. -/
def SUBMAP (f g : fmap α β) : Prop := ∀ x y, FLOOKUP f x = some y → FLOOKUP g x = some y

/- HOL4: finite_map$FUNION (new_specification):
   (FDOM (FUNION f g) = FDOM f UNION FDOM g) /\
   (!x. FUNION f g ' x = if x IN FDOM f then f ' x else g ' x) -/
def FUNION (f g : fmap α β) : fmap α β :=
  ⟨fun a => match FLOOKUP f a with
      | none => FLOOKUP g a
      | some y => some y, by
    obtain ⟨l, hl⟩ := f.finite
    obtain ⟨m, hm⟩ := g.finite
    refine ⟨l ++ m, fun a ha => ?_⟩
    rw [List.mem_append]
    by_cases h : f.FLOOKUP a = none
    · simp only [h] at ha
      exact Or.inr (hm a ha)
    · exact Or.inl (hl a h)⟩

/- HOL4: finite_map$o_f:  f o_f g  (f applied to every value in the range of g):
   (FDOM (f o_f g) = FDOM g) /\ (!x. x IN FDOM (f o_f g) ==> ((f o_f g) ' x = f (g ' x))) -/
def o_f (f : β → γ) (g : fmap α β) : fmap α γ :=
  ⟨fun a => (FLOOKUP g a).map f, by
    obtain ⟨l, hl⟩ := g.finite
    refine ⟨l, fun a ha => hl a ?_⟩
    intro h
    simp [h] at ha⟩

/- HOL4: finite_map$FRANGE:  FRANGE f = { y | ?x. x IN FDOM f /\ (FAPPLY f x = y)}
   Stated with FLOOKUP. -/
def FRANGE (f : fmap α β) : Set β := {y | ∃ x, FLOOKUP f x = some y}

/- HOL4: finite_map$FEVERY:  FEVERY P f = !x. x IN FDOM f ==> P (x, FAPPLY f x)
   Stated with FLOOKUP. -/
def FEVERY (P : α × β → Prop) (f : fmap α β) : Prop := ∀ x y, FLOOKUP f x = some y → P (x, y)

/- HOL4: alist$alist_to_fmap:  alist_to_fmap s = FOLDR (\(k,v) f. f|+(k,v)) FEMPTY s -/
noncomputable def alist_to_fmap (s : List (α × β)) : fmap α β :=
  List.foldr (fun p f => FUPDATE f p) FEMPTY s

end

/-- HOL4 infixes `|+` and `|++` (both `Infixl 600`) and `⊌` (`Infixl 500`).
    `SUBMAP`/`⊑` and `o_f` are written prefix in Lean. -/
infixl:65 " |+ " => FUPDATE
infixl:65 " |++ " => FUPDATE_LIST
infixl:60 " ⊌ " => FUNION

end CmlTS
