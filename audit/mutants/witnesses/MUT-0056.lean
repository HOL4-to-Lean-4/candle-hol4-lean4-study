import CandleLean
open HOL Classical
noncomputable section
namespace Mut
open spt
def lookup {α : Type u} (k : Nat) : spt α → Option α
  | LN => none
  | LS a => if k = 0 then some a else none
  | BN t1 t2 => if k = 0 then none else lookup ((k - 1) / 2) (if EVEN k then t1 else t2)
  | BS t1 a t2 => if k = 0 then some a else lookup ((k - 1) / 2) (if ODD k then t1 else t2)
termination_by k
decreasing_by all_goals omega
end Mut

open spt in
theorem witness : ∃ (k : Nat) (t : spt Nat), Mut.lookup k t ≠ HOL.sptree.lookup k t := by
  refine ⟨1, BS (LS 5) 0 LN, ?_⟩
  have e : EVEN 1 = False := by simp [EVEN]
  have o : ODD 1 = True := by simp [ODD]
  simp [Mut.lookup, HOL.sptree.lookup, e, o]

#print axioms witness
