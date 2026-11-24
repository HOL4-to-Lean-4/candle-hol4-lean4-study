import CandleLean
open HOL Classical
noncomputable section
namespace Mut
open spt
def insert {α : Type u} (k : Nat) (a : α) : spt α → spt α
  | LN => if k = 0 then LS a
          else if EVEN k then BN (insert ((k - 1) / 2) a LN) LN
          else BN LN (insert ((k - 1) / 2) a LN)
  | LS a' => if k = 0 then LS a
             else if EVEN k then BS (insert ((k - 1) / 2) a LN) a' LN
             else BS LN a' (insert ((k - 1) / 2) a LN)
  | BN t1 t2 => if k = 0 then BS t1 a t2
                else if EVEN k then BN (insert ((k - 1) / 2) a t1) t2
                else BN t1 (insert ((k - 1) / 3) a t2)
  | BS t1 a' t2 => if k = 0 then BS t1 a t2
                   else if EVEN k then BS (insert ((k - 1) / 2) a t1) a' t2
                   else BS t1 a' (insert ((k - 1) / 2) a t2)
termination_by k
decreasing_by all_goals omega
end Mut

open spt in
theorem witness : ∃ (k : Nat) (a : Nat) (t : spt Nat), Mut.insert k a t ≠ HOL.sptree.insert k a t := by
  refine ⟨3, 7, BN LN LN, ?_⟩
  have e : EVEN 3 = False := by simp [EVEN]
  have e1 : EVEN 1 = False := by simp [EVEN]
  simp [Mut.insert, HOL.sptree.insert, e, e1]

#print axioms witness
