import CmlTS.Prelude.FMap

/-!
# HOL4 library prelude: `sptree` (num-keyed tries) and `llist` (lazy lists)
-/

universe u v w

noncomputable section

open Classical

/-! ## sptree -/

/- HOL4: sptree theory, `Datatype: spt = LN | LS 'a | BN spt spt | BS spt 'a spt` -/
inductive spt (α : Type u) : Type u where
  | LN : spt α
  | LS (a : α) : spt α
  | BN (t1 t2 : spt α) : spt α
  | BS (t1 : spt α) (a : α) (t2 : spt α) : spt α

/- HOL4: sptree theory, `Type num_map = ':'a spt'`, `Type num_set = ':unit spt'` -/
abbrev num_map (α : Type u) : Type u := spt α
abbrev num_set : Type := spt Unit

namespace sptree

/- HOL4: sptree theory,
   `lookup k LN = NONE`, `lookup k (LS a) = if k = 0 then SOME a else NONE`,
   `lookup k (BN t1 t2) = if k = 0 then NONE else lookup ((k - 1) DIV 2) (if EVEN k then t1 else t2)`,
   `lookup k (BS t1 a t2) = if k = 0 then SOME a else lookup ((k - 1) DIV 2) (if EVEN k then t1 else t2)` -/
def lookup {α : Type u} : Nat → spt α → Option α
  | _, .LN => none
  | k, .LS a => if k = 0 then some a else none
  | k, .BN t1 t2 =>
    if k = 0 then none else lookup ((k - 1) / 2) (if k % 2 = 0 then t1 else t2)
  | k, .BS t1 a t2 =>
    if k = 0 then some a else lookup ((k - 1) / 2) (if k % 2 = 0 then t1 else t2)
termination_by k => k
decreasing_by
  all_goals first | omega | (rename_i h; omega)

/- HOL4: sptree theory, `domain LN = {}`, `domain (LS _) = {0}`,
   `domain (BN t1 t2) = IMAGE (\n. 2 * n + 2) (domain t1) UNION IMAGE (\n. 2 * n + 1) (domain t2)`,
   `domain (BS t1 _ t2) = {0} UNION IMAGE (\n. 2 * n + 2) (domain t1) UNION IMAGE (\n. 2 * n + 1) (domain t2)` -/
def domain {α : Type u} : spt α → Set Nat
  | .LN => ∅
  | .LS _ => ({0} : Set Nat)
  | .BN t1 t2 => IMAGE (fun n => 2 * n + 2) (domain t1) ∪ IMAGE (fun n => 2 * n + 1) (domain t2)
  | .BS t1 _ t2 =>
    ({0} : Set Nat) ∪ IMAGE (fun n => 2 * n + 2) (domain t1) ∪
      IMAGE (fun n => 2 * n + 1) (domain t2)

/- HOL4: sptree theory, `toListA acc LN = acc`, `toListA acc (LS a) = a::acc`,
   `toListA acc (BN t1 t2) = toListA (toListA acc t2) t1`,
   `toListA acc (BS t1 a t2) = toListA (a :: toListA acc t2) t1` -/
def toListA {α : Type u} : List α → spt α → List α
  | acc, .LN => acc
  | acc, .LS a => a :: acc
  | acc, .BN t1 t2 => toListA (toListA acc t2) t1
  | acc, .BS t1 a t2 => toListA (a :: toListA acc t2) t1

/- HOL4: sptree theory, `toList m = toListA [] m` -/
def toList {α : Type u} (m : spt α) : List α := toListA [] m

end sptree

/-! ## llist -/

/- HOL4: llist theory, type `'a llist`: a function `num -> 'a option` with
   `!n. IS_SOME (f (SUC n)) ==> IS_SOME (f n)` (`lrep_ok_alt`) -/
def llist (α : Type u) : Type u :=
  { f : Nat → Option α // ∀ n, (f (n + 1)).isSome → (f n).isSome }

/- HOL4: llist theory, `LNIL` (written `[||]`) -/
def LNIL {α : Type u} : llist α := ⟨fun _ => none, by simp⟩

/- HOL4: llist theory, `LNTH n ll` -/
def LNTH {α : Type u} (n : Nat) (ll : llist α) : Option α := ll.1 n

/- HOL4: llist theory, `fromList [] = LNIL`, `fromList (h::t) = LCONS h (fromList t)`;
   the n-th element of `fromList l` is `l[n]`. -/
def fromList {α : Type u} (l : List α) : llist α :=
  ⟨fun n => l[n]?, by
    intro n h
    have h : (l[n + 1]?).isSome = true := h
    show (l[n]?).isSome = true
    cases h0 : l[n]? with
    | some _ => rfl
    | none =>
      have h1 := List.getElem?_eq_none_iff.mp h0
      have h2 : l[n + 1]? = none := List.getElem?_eq_none_iff.mpr (by omega)
      simp [h2] at h⟩

/- HOL4: llist theory, `LFINITE ll` (there is a position without element) -/
def LFINITE {α : Type u} (ll : llist α) : Prop := ∃ n, ll.1 n = none

/- HOL4: llist theory, `llength_rel ll n` (`n` is the length of `ll`: the first missing position) -/
def llength_rel {α : Type u} (ll : llist α) (n : Nat) : Prop :=
  ll.1 n = none ∧ ∀ i, i < n → (ll.1 i).isSome

/- HOL4: llist theory, `LLENGTH ll = if LFINITE ll then SOME (@n. llength_rel ll n) else NONE` -/
def LLENGTH {α : Type u} (ll : llist α) : Option Nat :=
  if LFINITE ll then some (Classical.epsilon (fun n => llength_rel ll n)) else none

/- HOL4: llist theory, `LTAKE 0 ll = SOME []`,
   `LTAKE (SUC n) ll = case LHD ll of NONE => NONE | SOME hd => case LTAKE n (THE (LTL ll)) of NONE => NONE | SOME tl => SOME (hd::tl)`;
   i.e. the list of the first `n` elements if there are that many. -/
def LTAKE {α : Type u} (n : Nat) (ll : llist α) : Option (List α) :=
  if ∀ i, i < n → (ll.1 i).isSome then some ((List.range n).filterMap ll.1) else none

/- HOL4: llist theory, `toList ll = if LFINITE ll then LTAKE (THE (LLENGTH ll)) ll else NONE` -/
def llist.toList {α : Type u} (ll : llist α) : Option (List α) :=
  if LFINITE ll then LTAKE ((LLENGTH ll).getD 0) ll else none

/- HOL4: llist theory,
   `LPREFIX l1 l2 = case toList l1 of NONE => (l1 = l2)
                    | SOME xs => case toList l2 of NONE => LTAKE (LENGTH xs) l2 = SOME xs
                                 | SOME ys => isPREFIX xs ys` -/
def LPREFIX {α : Type u} (l1 l2 : llist α) : Prop :=
  match llist.toList l1 with
  | none => l1 = l2
  | some xs =>
    match llist.toList l2 with
    | none => LTAKE xs.length l2 = some xs
    | some ys => isPREFIX xs ys

end
