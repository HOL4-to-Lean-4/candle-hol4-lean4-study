import CmlTS.Prelude.ListLib

/-
HOL4 library constants from `finite_map` (and `alist_to_fmap` of `alist`).
-/

namespace CmlTS

noncomputable section

open scoped Classical

variable {α β γ : Type}

/- HOL4: finite_map$fmap, written `'a |-> 'b`.
   In HOL4 the type is the subset of `'a -> 'b + one` closed under
   `\a. INR one` and pointwise update, i.e. the functions that differ from
   `INR one` at finitely many points.  Here: option-valued functions with
   finite support.  Equality is extensional in both. -/
structure fmap (α β : Type) where
  rep : α → Option β
  finite : ∃ l : List α, ∀ a, rep a ≠ none → a ∈ l

/- HOL4: finite_map$FEMPTY   FEMPTY = fmap_ABS (\a. INR one) -/
def FEMPTY : fmap α β := ⟨fun _ => none, [], fun _ h => absurd rfl h⟩

instance : Nonempty (fmap α β) := ⟨FEMPTY⟩

/- HOL4: finite_map$FUPDATE (infix `|+`)
   FUPDATE f (x,y) = fmap_ABS (\a. if a = x then INL y else fmap_REP f a) -/
def FUPDATE (f : fmap α β) (xy : α × β) : fmap α β :=
  ⟨fun a => if a = xy.1 then some xy.2 else f.rep a, by
    obtain ⟨l, hl⟩ := f.finite
    refine ⟨xy.1 :: l, fun a h => ?_⟩
    by_cases hx : a = xy.1
    · simp [hx]
    · simp only [hx, if_false] at h
      exact List.mem_cons_of_mem _ (hl a h)⟩

/- HOL4: finite_map$FAPPLY (infix `'`)   FAPPLY f x = OUTL (fmap_REP f x)
   (unspecified outside the domain) -/
def FAPPLY [Nonempty β] (f : fmap α β) (x : α) : β :=
  match f.rep x with
  | some y => y
  | none => ARB

/- HOL4: finite_map$FDOM   FDOM f x = ISL (fmap_REP f x) -/
def FDOM (f : fmap α β) : Set α := setOf fun x => f.rep x ≠ none

/- HOL4: finite_map$FLOOKUP
   FLOOKUP f x = if x IN FDOM f then SOME (FAPPLY f x) else NONE -/
def FLOOKUP (f : fmap α β) (x : α) : Option β := f.rep x

/- HOL4: finite_map$SUBMAP (infix, also `⊑`)
   $SUBMAP f g = !x. x IN FDOM f ==> x IN FDOM g /\ (FAPPLY f x = FAPPLY g x) -/
def SUBMAP (f g : fmap α β) : Prop :=
  ∀ x, x ∈ FDOM f → x ∈ FDOM g ∧ FLOOKUP f x = FLOOKUP g x

/- HOL4: finite_map$FUNION (infix `⊌`), the specification
   (FDOM (FUNION f g) = FDOM f UNION FDOM g) /\
   (!x. FAPPLY (FUNION f g) x = if x IN FDOM f then FAPPLY f x else FAPPLY g x) -/
def FUNION (f g : fmap α β) : fmap α β :=
  ⟨fun x => if x ∈ FDOM f then f.rep x else g.rep x, by
    obtain ⟨l1, h1⟩ := f.finite
    obtain ⟨l2, h2⟩ := g.finite
    refine ⟨l1 ++ l2, fun a h => ?_⟩
    by_cases hx : a ∈ FDOM f
    · simp only [hx, if_true] at h
      exact List.mem_append_left _ (h1 a h)
    · simp only [hx, if_false] at h
      exact List.mem_append_right _ (h2 a h)⟩

/- HOL4: finite_map$FEVERY   FEVERY P f = !x. x IN FDOM f ==> P (x, FAPPLY f x) -/
def FEVERY (P : α × β → Prop) (f : fmap α β) : Prop :=
  ∀ x y, FLOOKUP f x = some y → P (x, y)

/- HOL4: finite_map$o_f (infix), the specification
   (FDOM (f o_f g) = FDOM g) /\
   (!x. x IN FDOM (f o_f g) ==> (FAPPLY (f o_f g) x = f (FAPPLY g x))) -/
def o_f (f : β → γ) (g : fmap α β) : fmap α γ :=
  ⟨fun x => (g.rep x).map f, by
    obtain ⟨l, hl⟩ := g.finite
    refine ⟨l, fun a h => hl a fun hn => h ?_⟩
    simp [hn]⟩

/- HOL4: finite_map$FRANGE   FRANGE f = { y | ?x. x IN FDOM f /\ (FAPPLY f x = y)} -/
def FRANGE (f : fmap α β) : Set β := setOf fun y => ∃ x, FLOOKUP f x = some y

/- HOL4: finite_map$FUPDATE_LIST (infix `|++`)   FUPDATE_LIST = FOLDL FUPDATE -/
def FUPDATE_LIST : fmap α β → List (α × β) → fmap α β := List.foldl FUPDATE

/- HOL4: alist$alist_to_fmap
   alist_to_fmap s = FOLDR (\(k,v) f. f|+(k,v)) FEMPTY s -/
def alist_to_fmap (s : List (α × β)) : fmap α β :=
  s.foldr (fun (k, v) f => FUPDATE f (k, v)) FEMPTY

end

end CmlTS
