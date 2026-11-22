/-
  HOL4 library constants: finite_map, alist (alist_to_fmap), sptree.

  HOL `'a |-> 'b` is `fmap α β`.  As in HOL4, a finite map is a function
  `α → β + one` (`α → Sum β Unit`) with finite support.
-/
import CandleLean.Prelude.List

namespace Candle

noncomputable section
open Classical

/-! ## finite_map -/

/- HOL4: finite_map
   Hol_reln `is_fmap (\a. INR one) /\
             (!f a b. is_fmap f ==> is_fmap (\x. if x=a then INL b else f x))` -/
inductive is_fmap {α β : Type} : (α → Sum β Unit) → Prop
  | empty : is_fmap (fun _ => .inr ())
  | update (f : α → Sum β Unit) (a : α) (b : β) :
      is_fmap f → is_fmap (fun x => if x = a then .inl b else f x)

/- HOL4: finite_map  `fmap`  (infix type `'a |-> 'b`)
   val fmap_TY_DEF = new_type_definition("fmap", EXISTENCE_THM)   (|- ?x. is_fmap x)
   with bijections fmap_ABS / fmap_REP.  `fmap.mk` is `fmap_ABS` (on `is_fmap` functions). -/
structure fmap (α β : Type) where
  fmap_REP : α → Sum β Unit
  is_fmap_REP : is_fmap fmap_REP

/- HOL4: finite_map  `fmap_REP` -/
abbrev fmap_REP {α β : Type} (f : fmap α β) : α → Sum β Unit := f.fmap_REP

/- HOL4: finite_map$FEMPTY_DEF  |- FEMPTY = fmap_ABS (\a. INR one) -/
def FEMPTY {α β : Type} : fmap α β := ⟨fun _ => .inr (), is_fmap.empty⟩

instance {α β : Type} : Inhabited (fmap α β) := ⟨FEMPTY⟩

/- HOL4: finite_map$FUPDATE_DEF
   |- FUPDATE f (x,y) = fmap_ABS (\a. if a = x then INL y else fmap_REP f a)
   (HOL infix `f |+ (x,y)` is `FUPDATE f (x, y)`) -/
def FUPDATE {α β : Type} (f : fmap α β) (xy : α × β) : fmap α β :=
  ⟨fun a => if a = xy.1 then .inl xy.2 else fmap_REP f a,
   is_fmap.update _ _ _ f.is_fmap_REP⟩

/- HOL4: finite_map$FAPPLY_DEF  |- FAPPLY f x = OUTL (fmap_REP f x)
   (HOL infix `f ' x` is `FAPPLY f x`; unspecified when `x` is not in `FDOM f`) -/
def FAPPLY {α β : Type} [Nonempty β] (f : fmap α β) (x : α) : β := OUTL (fmap_REP f x)

/- HOL4: finite_map$FDOM_DEF  |- FDOM f x = ISL (fmap_REP f x) -/
def FDOM {α β : Type} (f : fmap α β) : Set α := fun x => ISL (fmap_REP f x)

/- HOL4: finite_map$FLOOKUP_DEF
   |- FLOOKUP f x = if x IN FDOM f then SOME (FAPPLY f x) else NONE -/
def FLOOKUP {α β : Type} [Nonempty β] (f : fmap α β) (x : α) : Option β :=
  if x ∈ FDOM f then some (FAPPLY f x) else none

/- HOL4: finite_map$FEVERY_DEF  |- FEVERY P f <=> !x. x IN FDOM f ==> P (x,FAPPLY f x) -/
def FEVERY {α β : Type} [Nonempty β] (P : α × β → Prop) (f : fmap α β) : Prop :=
  ∀ x, x ∈ FDOM f → P (x, FAPPLY f x)

/- HOL4: finite_map$FRANGE_DEF  |- FRANGE f = {y | ?x. x IN FDOM f /\ (FAPPLY f x = y)} -/
def FRANGE {α β : Type} [Nonempty β] (f : fmap α β) : Set β :=
  {y | ∃ x, x ∈ FDOM f ∧ FAPPLY f x = y}

/- HOL4: finite_map$FUN_FMAP_DEF
   |- !f P. FINITE P ==>
            (FDOM (FUN_FMAP f P) = P) /\ !x. x IN P ==> (FAPPLY (FUN_FMAP f P) x = f x)
   (`new_specification`: `FUN_FMAP` is an arbitrary function that satisfies this;
   `FUN_FMAP f P` is unspecified for infinite `P`.) -/
def FUN_FMAP {α β : Type} [Nonempty β] : (α → β) → Set α → fmap α β :=
  select (fun F => ∀ (f : α → β) (P : Set α), FINITE P →
    FDOM (F f P) = P ∧ ∀ x, x ∈ P → FAPPLY (F f P) x = f x)

/-! ## alist -/

/- HOL4: alist$alist_to_fmap_def  |- alist_to_fmap s = FOLDR (\(k,v) f. f |+ (k,v)) FEMPTY s -/
def alist_to_fmap {α β : Type} (s : List (α × β)) : fmap α β :=
  FOLDR (fun (kv : α × β) f => FUPDATE f (kv.1, kv.2)) FEMPTY s

/-! ## sptree -/

/- HOL4: sptree  Datatype: spt = LN | LS 'a | BN spt spt | BS spt 'a spt End -/
inductive spt (α : Type) where
  | LN : spt α
  | LS : α → spt α
  | BN : spt α → spt α → spt α
  | BS : spt α → α → spt α → spt α

export spt (LN LS BN BS)

instance {α : Type} : Inhabited (spt α) := ⟨LN⟩

/- HOL4: sptree (and misc)  Type num_set = “:unit spt” -/
abbrev num_set : Type := spt Unit

/- HOL4: sptree (and misc)  Type num_map = “:'a spt” -/
abbrev num_map (α : Type) : Type := spt α

namespace sptree

/- HOL4: sptree$insert_def
   |- (insert k a LN = if k = 0 then LS a
                       else if EVEN k then BN (insert ((k-1) DIV 2) a LN) LN
                       else BN LN (insert ((k-1) DIV 2) a LN)) /\
      (insert k a (LS a') =
         if k = 0 then LS a
         else if EVEN k then BS (insert ((k-1) DIV 2) a LN) a' LN
         else BS LN a' (insert ((k-1) DIV 2) a LN)) /\
      (insert k a (BN t1 t2) =
         if k = 0 then BS t1 a t2
         else if EVEN k then BN (insert ((k - 1) DIV 2) a t1) t2
         else BN t1 (insert ((k - 1) DIV 2) a t2)) /\
      (insert k a (BS t1 a' t2) =
         if k = 0 then BS t1 a t2
         else if EVEN k then BS (insert ((k - 1) DIV 2) a t1) a' t2
         else BS t1 a' (insert ((k - 1) DIV 2) a t2))
   Termination: WF_REL_TAC `measure FST` -/
def insert {α : Type} (k : Nat) (a : α) : spt α → spt α
  | LN => if k = 0 then LS a
          else if EVEN k then BN (insert ((k - 1) / 2) a LN) LN
          else BN LN (insert ((k - 1) / 2) a LN)
  | LS a' =>
          if k = 0 then LS a
          else if EVEN k then BS (insert ((k - 1) / 2) a LN) a' LN
          else BS LN a' (insert ((k - 1) / 2) a LN)
  | BN t1 t2 =>
          if k = 0 then BS t1 a t2
          else if EVEN k then BN (insert ((k - 1) / 2) a t1) t2
          else BN t1 (insert ((k - 1) / 2) a t2)
  | BS t1 a' t2 =>
          if k = 0 then BS t1 a t2
          else if EVEN k then BS (insert ((k - 1) / 2) a t1) a' t2
          else BS t1 a' (insert ((k - 1) / 2) a t2)
termination_by k
decreasing_by all_goals omega

/- HOL4: sptree$domain_def
   |- (domain LN = {}) /\ (domain (LS _) = {0}) /\
      (domain (BN t1 t2) =
         IMAGE (\n. 2 * n + 2) (domain t1) UNION IMAGE (\n. 2 * n + 1) (domain t2)) /\
      (domain (BS t1 _ t2) =
         {0} UNION IMAGE (\n. 2 * n + 2) (domain t1) UNION IMAGE (\n. 2 * n + 1) (domain t2)) -/
def domain {α : Type} : spt α → Set Nat
  | LN => ∅
  | LS _ => {0}
  | BN t1 t2 => IMAGE (fun n => 2 * n + 2) (domain t1) ∪ IMAGE (fun n => 2 * n + 1) (domain t2)
  | BS t1 _ t2 =>
      {0} ∪ IMAGE (fun n => 2 * n + 2) (domain t1) ∪ IMAGE (fun n => 2 * n + 1) (domain t2)

end sptree

end

end Candle
