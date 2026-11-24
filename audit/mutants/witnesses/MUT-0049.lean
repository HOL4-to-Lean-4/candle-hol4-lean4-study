import CandleLean
open HOL Candle Classical
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
universe u
noncomputable section

namespace Mut
def lookup {α : Type u} (k : Nat) : spt α → Option α
  | LN => none
  | LS a => if k = 0 then some a else none
  | BN t1 t2 => if k = 0 then none else lookup ((k - 1) / 2) (if EVEN k then t2 else t1)
  | BS t1 a t2 => if k = 0 then some a else lookup ((k - 1) / 2) (if EVEN k then t1 else t2)
termination_by k
decreasing_by all_goals omega
end Mut

theorem witness : ∃ (k : Nat) (t : spt Nat), Mut.lookup k t ≠ HOL.sptree.lookup k t := by
  refine ⟨1, BN (LS 5) LN, ?_⟩
  have hodd : ¬ EVEN 1 := by simp [EVEN]
  have h10 : ¬ (1:Nat) = 0 := by omega
  have e1 : Mut.lookup 1 (BN (LS 5) LN) = some 5 := by
    rw [Mut.lookup, if_neg h10]
    show Mut.lookup 0 (if EVEN 1 then LN else LS 5) = _
    rw [if_neg hodd, Mut.lookup]; simp
  have e2 : HOL.sptree.lookup 1 (BN (LS 5) LN) = none := by
    rw [HOL.sptree.lookup, if_neg h10]
    show HOL.sptree.lookup 0 (if EVEN 1 then LS 5 else LN) = _
    rw [if_neg hodd, HOL.sptree.lookup]
  rw [e1, e2]; intro h; cases h

#print axioms witness
