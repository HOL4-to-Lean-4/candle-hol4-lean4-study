import CandleLean.Prelude.PredSet

/-!
# HOL4 library: sptree (only what the targets need)

The names `insert`, `domain`, `lookup` live in the namespace `HOL.sptree`
(write `sptree.insert`, `sptree.domain`, ... after `open HOL`).
-/

universe u

namespace HOL

open Classical

noncomputable section

/- HOL4: sptree$spt    Datatype: spt = LN | LS 'a | BN spt spt | BS spt 'a spt End -/
inductive spt (α : Type u) where
  | LN : spt α
  | LS : α → spt α
  | BN : spt α → spt α → spt α
  | BS : spt α → α → spt α → spt α
  deriving DecidableEq, Inhabited

export spt (LN LS BN BS)

/- HOL4: sptree$num_map    Type num_map = “:'a spt” -/
abbrev num_map (α : Type u) := spt α

/- HOL4: sptree$num_set    Type num_set = “:unit spt” -/
abbrev num_set := spt Unit

namespace sptree

/- HOL4: sptree$lookup
     (lookup k LN = NONE) /\
     (lookup k (LS a) = if k = 0 then SOME a else NONE) /\
     (lookup k (BN t1 t2) =
        if k = 0 then NONE
        else lookup ((k - 1) DIV 2) (if EVEN k then t1 else t2)) /\
     (lookup k (BS t1 a t2) =
        if k = 0 then SOME a
        else lookup ((k - 1) DIV 2) (if EVEN k then t1 else t2)) -/
def lookup {α : Type u} (k : Nat) : spt α → Option α
  | LN => none
  | LS a => if k = 0 then some a else none
  | BN t1 t2 => if k = 0 then none else lookup ((k - 1) / 2) (if EVEN k then t1 else t2)
  | BS t1 a t2 => if k = 0 then some a else lookup ((k - 1) / 2) (if EVEN k then t1 else t2)
termination_by k
decreasing_by all_goals omega

/- HOL4: sptree$insert
     (insert k a LN = if k = 0 then LS a
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
        else BS t1 a' (insert ((k - 1) DIV 2) a t2)) -/
def insert {α : Type u} (k : Nat) (a : α) : spt α → spt α
  | LN => if k = 0 then LS a
          else if EVEN k then BN (insert ((k - 1) / 2) a LN) LN
          else BN LN (insert ((k - 1) / 2) a LN)
  | LS a' => if k = 0 then LS a
             else if EVEN k then BS (insert ((k - 1) / 2) a LN) a' LN
             else BS LN a' (insert ((k - 1) / 2) a LN)
  | BN t1 t2 => if k = 0 then BS t1 a t2
                else if EVEN k then BN (insert ((k - 1) / 2) a t1) t2
                else BN t1 (insert ((k - 1) / 2) a t2)
  | BS t1 a' t2 => if k = 0 then BS t1 a t2
                   else if EVEN k then BS (insert ((k - 1) / 2) a t1) a' t2
                   else BS t1 a' (insert ((k - 1) / 2) a t2)
termination_by k
decreasing_by all_goals omega

/- HOL4: sptree$domain
     domain LN = {} /\
     domain (LS _) = {0} /\
     domain (BN t1 t2) =
        IMAGE (\n. 2 * n + 2) (domain t1) UNION
        IMAGE (\n. 2 * n + 1) (domain t2) /\
     domain (BS t1 _ t2) =
        {0} UNION IMAGE (\n. 2 * n + 2) (domain t1) UNION
        IMAGE (\n. 2 * n + 1) (domain t2) -/
def domain {α : Type u} : spt α → Set Nat
  | LN => EMPTY
  | LS _ => INSERT 0 EMPTY
  | BN t1 t2 => UNION (IMAGE (fun n => 2 * n + 2) (domain t1)) (IMAGE (fun n => 2 * n + 1) (domain t2))
  | BS t1 _ t2 =>
    UNION (UNION (INSERT 0 EMPTY) (IMAGE (fun n => 2 * n + 2) (domain t1)))
      (IMAGE (fun n => 2 * n + 1) (domain t2))

end sptree

end

end HOL
