import CmlTS.Prelude.Num

/-!
# HOL4 library prelude: finite maps (`finite_map`, `alist`)

`('a, 'b) fmap` is modelled as a partial function `'a -> 'b option` with finite domain; this has the
same extensional equality as HOL4's `fmap` (two maps are equal iff they have the same domain and
values).
-/

universe u v w

noncomputable section

open Classical

/- HOL4: finite_map theory, type `('a, 'b) fmap` (written `'a |-> 'b`) -/
def FMap (α : Type u) (β : Type v) : Type (max u v) :=
  { f : α → Option β // ∃ l : List α, ∀ a, (f a).isSome → a ∈ l }

namespace FMap

theorem ext {α : Type u} {β : Type v} {f g : FMap α β} (h : ∀ x, f.1 x = g.1 x) : f = g :=
  Subtype.ext (funext h)

end FMap

/- HOL4: finite_map theory, `FEMPTY` -/
def FEMPTY {α : Type u} {β : Type v} : FMap α β := ⟨fun _ => none, [], by simp⟩

/- HOL4: finite_map theory, `FLOOKUP f x = if x IN FDOM f then SOME (FAPPLY f x) else NONE` -/
def FLOOKUP {α : Type u} {β : Type v} (f : FMap α β) (x : α) : Option β := f.1 x

/- HOL4: finite_map theory, `FDOM f` -/
def FDOM {α : Type u} {β : Type v} (f : FMap α β) : Set α := fun x => (f.1 x).isSome

/- HOL4: finite_map theory, `FAPPLY f x` (written `f ' x`); unspecified outside `FDOM f` -/
def FAPPLY {α : Type u} {β : Type v} [Nonempty β] (f : FMap α β) (x : α) : β :=
  match f.1 x with
  | some v => v
  | none => ARB

/- HOL4: finite_map theory, `FUPDATE f (k, v)` (written `f |+ (k, v)`) -/
def FUPDATE {α : Type u} {β : Type v} (f : FMap α β) (p : α × β) : FMap α β :=
  ⟨fun x => if x = p.1 then some p.2 else f.1 x, by
    obtain ⟨l, hl⟩ := f.2
    refine ⟨p.1 :: l, fun a ha => ?_⟩
    by_cases h : a = p.1
    · simp [h]
    · simp only [h, if_false] at ha
      exact List.mem_cons_of_mem _ (hl a ha)⟩

/- HOL4: finite_map theory, `FUPDATE_LIST = FOLDL FUPDATE` (written `f |++ l`) -/
def FUPDATE_LIST {α : Type u} {β : Type v} (f : FMap α β) (l : List (α × β)) : FMap α β :=
  FOLDL FUPDATE f l

/- HOL4: finite_map theory, `FUNION f g` (written `f ⊌ g`): domain is the union, values of `f`
   take priority. -/
def FUNION {α : Type u} {β : Type v} (f g : FMap α β) : FMap α β :=
  ⟨fun x => match f.1 x with
    | some v => some v
    | none => g.1 x, by
    obtain ⟨l1, h1⟩ := f.2
    obtain ⟨l2, h2⟩ := g.2
    refine ⟨l1 ++ l2, fun a ha => ?_⟩
    simp only at ha
    rcases hf : f.1 a with _ | v
    · rw [hf] at ha
      exact List.mem_append_right _ (h2 a (by simpa using ha))
    · exact List.mem_append_left _ (h1 a (by simp [hf]))⟩

/- HOL4: finite_map theory, `FRANGE f = {y | ?x. x IN FDOM f /\ FAPPLY f x = y}` -/
def FRANGE {α : Type u} {β : Type v} (f : FMap α β) : Set β := fun y => ∃ x, f.1 x = some y

/- HOL4: finite_map theory, `FEVERY P f = !x. x IN FDOM f ==> P (x, FAPPLY f x)` -/
def FEVERY {α : Type u} {β : Type v} (P : α × β → Prop) (f : FMap α β) : Prop :=
  ∀ x v, f.1 x = some v → P (x, v)

/- HOL4: finite_map theory, `(f o_f m)`: applies `f` to every value of `m`
   (`FDOM (f o_f m) = FDOM m`, `(f o_f m) ' x = f (m ' x)`) -/
def o_f {α : Type u} {β : Type v} {γ : Type w} (f : β → γ) (m : FMap α β) : FMap α γ :=
  ⟨fun x => (m.1 x).map f, by
    obtain ⟨l, hl⟩ := m.2
    exact ⟨l, fun a ha => hl a (by simpa using ha)⟩⟩

/- HOL4: finite_map theory, `f SUBMAP g = !x. x IN FDOM f ==> x IN FDOM g /\ f ' x = g ' x`
   (written `f ⊑ g`) -/
def SUBMAP {α : Type u} {β : Type v} (f g : FMap α β) : Prop :=
  ∀ x v, f.1 x = some v → g.1 x = some v

/- HOL4: alist theory, `alist_to_fmap s = FOLDR (\(k,v) f. f |+ (k,v)) FEMPTY s` -/
def alist_to_fmap {α : Type u} {β : Type v} (s : List (α × β)) : FMap α β :=
  FOLDR (fun p f => FUPDATE f (p.1, p.2)) FEMPTY s

/-- HOL4 `f |+ (k, v)` -/
infixl:480 " |+ " => FUPDATE
/-- HOL4 `f |++ l` -/
infixl:480 " |++ " => FUPDATE_LIST
/-- HOL4 `f ⊌ g` -/
infixl:480 " ⊌ " => FUNION
/-- HOL4 `f ⊑ g` -/
infix:450 " ⊑ " => SUBMAP

end
