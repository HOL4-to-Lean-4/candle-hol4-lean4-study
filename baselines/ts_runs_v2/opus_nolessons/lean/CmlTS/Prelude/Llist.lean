import CmlTS.Prelude.List
/-
  HOL4 library constants: `llist` (lazy lists).
-/
set_option autoImplicit false

namespace CmlTS
open Classical

universe u

/- HOL4: llist$llist is the type of `f : num -> 'a option` with `lrep_ok f`, where
   lrep_ok f = (!n. IS_SOME (f (SUC n)) ==> IS_SOME (f n))      (theorem lrep_ok_alt) -/
structure llist (α : Type u) : Type u where
  llist_rep : Nat → Option α
  lrep_ok : ∀ n, (llist_rep (n + 1)).isSome → (llist_rep n).isSome

section
variable {α : Type u}

theorem llist.ext {a b : llist α} (h : ∀ n, a.llist_rep n = b.llist_rep n) : a = b := by
  cases a; cases b; simp at h; congr; exact funext h

/- HOL4: llist$LNIL:  LNIL = llist_abs (λn. NONE) -/
def LNIL : llist α := ⟨fun _ => none, by simp⟩

instance : Inhabited (llist α) := ⟨LNIL⟩

/- HOL4: llist$LCONS:  LCONS h t = llist_abs (λn. if n = 0 then SOME h else llist_rep t (n - 1)) -/
def LCONS (h : α) (t : llist α) : llist α :=
  ⟨fun n => if n = 0 then some h else t.llist_rep (n - 1), by
    intro n hn
    cases n with
    | zero => simp
    | succ m => simpa using t.lrep_ok m (by simpa using hn)⟩

/- HOL4: llist$LHD:  LHD ll = llist_rep ll 0 -/
def LHD (ll : llist α) : Option α := ll.llist_rep 0

/- HOL4: llist$LTL:
   LTL ll = case LHD ll of NONE => NONE | SOME _ => SOME (llist_abs (\n. llist_rep ll (n + 1))) -/
def LTL (ll : llist α) : Option (llist α) :=
  match LHD ll with
  | none => none
  | some _ => some ⟨fun n => ll.llist_rep (n + 1), fun n => ll.lrep_ok (n + 1)⟩

/- HOL4: llist$LTAKE:
   (LTAKE 0 ll = SOME []) /\
   (LTAKE (SUC n) ll =
      case LHD ll of
          NONE => NONE
        | SOME hd => case LTAKE n (THE (LTL ll)) of NONE => NONE | SOME tl => SOME (hd::tl)) -/
noncomputable def LTAKE : Nat → llist α → Option (List α)
  | 0, _ => some []
  | n + 1, ll =>
    match LHD ll with
    | none => none
    | some hd =>
      match LTAKE n (THE (LTL ll)) with
      | none => none
      | some tl => some (hd :: tl)

/- HOL4: llist$LFINITE:  LFINITE [||] /\ (!h t. LFINITE t ==> LFINITE (h:::t)) -/
inductive LFINITE : llist α → Prop
  | nil : LFINITE LNIL
  | cons (h : α) (t : llist α) : LFINITE t → LFINITE (LCONS h t)

/- HOL4: llist$llength_rel:
   llength_rel [||] 0 /\ (!h n t. llength_rel t n ==> llength_rel (h:::t) (SUC n)) -/
inductive llength_rel : llist α → Nat → Prop
  | nil : llength_rel LNIL 0
  | cons (h : α) (n : Nat) (t : llist α) : llength_rel t n → llength_rel (LCONS h t) (n + 1)

/- HOL4: llist$LLENGTH:  LLENGTH ll = if LFINITE ll then SOME (@n. llength_rel ll n) else NONE -/
noncomputable def LLENGTH (ll : llist α) : Option Nat :=
  if LFINITE ll then some (SELECT fun n => llength_rel ll n) else none

/- HOL4: llist$toList:  toList ll = if LFINITE ll then LTAKE (THE (LLENGTH ll)) ll else NONE
   (`llist_toList`, because `toList` is also an `sptree` constant) -/
noncomputable def llist_toList (ll : llist α) : Option (List α) :=
  if LFINITE ll then LTAKE (THE (LLENGTH ll)) ll else none

/- HOL4: llist$fromList:  (fromList [] = LNIL) /\ (fromList (h::t) = LCONS h (fromList t)) -/
def fromList : List α → llist α
  | [] => LNIL
  | h :: t => LCONS h (fromList t)

/- HOL4: llist$LPREFIX:
   LPREFIX l1 l2 =
     case toList l1 of
     | NONE => (l1 = l2)
     | SOME xs =>
         case toList l2 of
         | NONE => LTAKE (LENGTH xs) l2 = SOME xs
         | SOME ys => isPREFIX xs ys -/
def LPREFIX (l1 l2 : llist α) : Prop :=
  match llist_toList l1 with
  | none => l1 = l2
  | some xs =>
    match llist_toList l2 with
    | none => LTAKE xs.length l2 = some xs
    | some ys => xs <+: ys

end

end CmlTS
