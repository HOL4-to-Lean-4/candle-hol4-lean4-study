import CmlTS.Prelude.ListLib

/-
HOL4 library constants from `sptree`.
-/

namespace CmlTS

noncomputable section

open scoped Classical

variable {α : Type}

/- HOL4: sptree$spt
   Datatype: spt = LN | LS 'a | BN spt spt | BS spt 'a spt -/
inductive spt (α : Type)
  | LN
  | LS (a : α)
  | BN (t1 t2 : spt α)
  | BS (t1 : spt α) (a : α) (t2 : spt α)

/- HOL4: sptree$lookup
   (lookup k LN = NONE) /\
   (lookup k (LS a) = if k = 0 then SOME a else NONE) /\
   (lookup k (BN t1 t2) =
      if k = 0 then NONE
      else lookup ((k - 1) DIV 2) (if EVEN k then t1 else t2)) /\
   (lookup k (BS t1 a t2) =
      if k = 0 then SOME a
      else lookup ((k - 1) DIV 2) (if EVEN k then t1 else t2))
   (The recursive call is pushed into the two branches of `if EVEN k` so that
   the recursion is structural in the tree.) -/
def lookup : Nat → spt α → Option α
  | _, spt.LN => none
  | k, spt.LS a => if k = 0 then some a else none
  | k, spt.BN t1 t2 =>
    if k = 0 then none
    else if k % 2 = 0 then lookup ((k - 1) / 2) t1 else lookup ((k - 1) / 2) t2
  | k, spt.BS t1 a t2 =>
    if k = 0 then some a
    else if k % 2 = 0 then lookup ((k - 1) / 2) t1 else lookup ((k - 1) / 2) t2

/- HOL4: sptree$domain
   domain LN = {} /\
   domain (LS _) = {0} /\
   domain (BN t1 t2) =
      IMAGE (\n. 2 * n + 2) (domain t1) UNION
      IMAGE (\n. 2 * n + 1) (domain t2) /\
   domain (BS t1 _ t2) =
      {0} UNION IMAGE (\n. 2 * n + 2) (domain t1) UNION
      IMAGE (\n. 2 * n + 1) (domain t2) -/
def domain : spt α → Set Nat
  | spt.LN => ∅
  | spt.LS _ => {0}
  | spt.BN t1 t2 =>
    IMAGE (fun n => 2 * n + 2) (domain t1) ∪ IMAGE (fun n => 2 * n + 1) (domain t2)
  | spt.BS t1 _ t2 =>
    {0} ∪ IMAGE (fun n => 2 * n + 2) (domain t1) ∪ IMAGE (fun n => 2 * n + 1) (domain t2)

/- HOL4: sptree$toListA
   (toListA acc LN = acc) /\
   (toListA acc (LS a) = a::acc) /\
   (toListA acc (BN t1 t2) = toListA (toListA acc t2) t1) /\
   (toListA acc (BS t1 a t2) = toListA (a :: toListA acc t2) t1) -/
def toListA : List α → spt α → List α
  | acc, spt.LN => acc
  | acc, spt.LS a => a :: acc
  | acc, spt.BN t1 t2 => toListA (toListA acc t2) t1
  | acc, spt.BS t1 a t2 => toListA (a :: toListA acc t2) t1

/- HOL4: sptree$toList   toList m = toListA [] m -/
def spt_toList (m : spt α) : List α := toListA [] m

end

end CmlTS
