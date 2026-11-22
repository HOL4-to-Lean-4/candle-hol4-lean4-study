/-
  HOL4 library constants from the theory `sptree` (namespace `sptree`, because
  `domain` and `insert` clash with other names).
-/
import CandleLean.Prelude.Set

open Classical

namespace sptree

/- HOL4: sptree$spt   `Datatype: spt = LN | LS 'a | BN spt spt | BS spt 'a spt End` -/
inductive spt (α : Type u) where
  | LN : spt α
  | LS : α → spt α
  | BN : spt α → spt α → spt α
  | BS : spt α → α → spt α → spt α
  deriving Inhabited

export spt (LN LS BN BS)

/- HOL4: sptree `Type num_map = “:'a spt”`, `Type num_set = “:unit spt”` -/
abbrev num_map (α : Type u) := spt α
abbrev num_set := spt Unit

/- HOL4: sptree$insert
   (insert k a LN = if k = 0 then LS a
                    else if EVEN k then BN (insert ((k-1) DIV 2) a LN) LN
                    else BN LN (insert ((k-1) DIV 2) a LN)) /\
   (insert k a (LS a') = if k = 0 then LS a
                         else if EVEN k then BS (insert ((k-1) DIV 2) a LN) a' LN
                         else BS LN a' (insert ((k-1) DIV 2) a LN)) /\
   (insert k a (BN t1 t2) = if k = 0 then BS t1 a t2
                            else if EVEN k then BN (insert ((k - 1) DIV 2) a t1) t2
                            else BN t1 (insert ((k - 1) DIV 2) a t2)) /\
   (insert k a (BS t1 a' t2) = if k = 0 then BS t1 a t2
                               else if EVEN k then BS (insert ((k - 1) DIV 2) a t1) a' t2
                               else BS t1 a' (insert ((k - 1) DIV 2) a t2))
   Termination: WF_REL_TAC `measure FST` -/
noncomputable def insert {α : Type u} (k : Nat) (a : α) : spt α → spt α
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
   domain (BN t1 t2) = IMAGE (\n. 2 * n + 2) (domain t1) UNION IMAGE (\n. 2 * n + 1) (domain t2) /\
   domain (BS t1 _ t2) = {0} UNION IMAGE (\n. 2 * n + 2) (domain t1) UNION
                         IMAGE (\n. 2 * n + 1) (domain t2) -/
def domain {α : Type u} : spt α → Set Nat
  | LN => EMPTY
  | LS _ => {0}
  | BN t1 t2 => IMAGE (fun n => 2 * n + 2) (domain t1) ∪ IMAGE (fun n => 2 * n + 1) (domain t2)
  | BS t1 _ t2 => {0} ∪ IMAGE (fun n => 2 * n + 2) (domain t1) ∪ IMAGE (fun n => 2 * n + 1) (domain t2)

end sptree
