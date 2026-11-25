import CmlTS.Prelude.List
/-
  HOL4 library constants: `sptree`.
-/
set_option autoImplicit false

namespace CmlTS
open Classical

universe u

/- HOL4: sptree
   Datatype: spt = LN | LS 'a | BN spt spt | BS spt 'a spt End -/
inductive spt (α : Type u) : Type u
  | LN
  | LS (a : α)
  | BN (t1 t2 : spt α)
  | BS (t1 : spt α) (a : α) (t2 : spt α)
  deriving Inhabited

export spt (LN LS BN BS)

section
variable {α : Type u}

/- HOL4: sptree$lookup
   (lookup k LN = NONE) /\
   (lookup k (LS a) = if k = 0 then SOME a else NONE) /\
   (lookup k (BN t1 t2) =
      if k = 0 then NONE else lookup ((k - 1) DIV 2) (if EVEN k then t1 else t2)) /\
   (lookup k (BS t1 a t2) =
      if k = 0 then SOME a else lookup ((k - 1) DIV 2) (if EVEN k then t1 else t2)) -/
def lookup (k : Nat) : spt α → Option α
  | .LN => none
  | .LS a => if k = 0 then some a else none
  | .BN t1 t2 => if k = 0 then none else lookup ((k - 1) / 2) (if EVEN k then t1 else t2)
  | .BS t1 a t2 => if k = 0 then some a else lookup ((k - 1) / 2) (if EVEN k then t1 else t2)
termination_by k
decreasing_by all_goals omega

/- HOL4: sptree$domain
   domain LN = {} /\
   domain (LS _) = {0} /\
   domain (BN t1 t2) = IMAGE (\n. 2 * n + 2) (domain t1) UNION IMAGE (\n. 2 * n + 1) (domain t2) /\
   domain (BS t1 _ t2) =
      {0} UNION IMAGE (\n. 2 * n + 2) (domain t1) UNION IMAGE (\n. 2 * n + 1) (domain t2) -/
def domain : spt α → Set Nat
  | .LN => ∅
  | .LS _ => {0}
  | .BN t1 t2 => IMAGE (fun n => 2 * n + 2) (domain t1) ∪ IMAGE (fun n => 2 * n + 1) (domain t2)
  | .BS t1 _ t2 =>
    {0} ∪ IMAGE (fun n => 2 * n + 2) (domain t1) ∪ IMAGE (fun n => 2 * n + 1) (domain t2)

/- HOL4: sptree$toListA
   (toListA acc LN = acc) /\
   (toListA acc (LS a) = a::acc) /\
   (toListA acc (BN t1 t2) = toListA (toListA acc t2) t1) /\
   (toListA acc (BS t1 a t2) = toListA (a :: toListA acc t2) t1) -/
def toListA (acc : List α) : spt α → List α
  | .LN => acc
  | .LS a => a :: acc
  | .BN t1 t2 => toListA (toListA acc t2) t1
  | .BS t1 a t2 => toListA (a :: toListA acc t2) t1

/- HOL4: sptree$toList:  toList m = toListA [] m -/
def toList (m : spt α) : List α := toListA [] m

end

end CmlTS
