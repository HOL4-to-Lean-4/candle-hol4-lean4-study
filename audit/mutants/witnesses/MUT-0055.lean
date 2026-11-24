import CandleLean
open HOL Candle Classical
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
universe u
noncomputable section

namespace Mut
def insert {α : Type u} (k : Nat) (a : α) : spt α → spt α
  | LN => if k = 0 then LS a
          else if EVEN k then BN (insert ((k - 1) / 2) a LN) LN
          else BN LN (insert ((k - 1) / 2) a LN)
  | LS a' => if k = 0 then LS a
             else if EVEN k then BS (insert ((k - 1) / 1) a LN) a' LN
             else BS LN a' (insert ((k - 1) / 2) a LN)
  | BN t1 t2 => if k = 0 then BS t1 a t2
                else if EVEN k then BN (insert ((k - 1) / 2) a t1) t2
                else BN t1 (insert ((k - 1) / 2) a t2)
  | BS t1 a' t2 => if k = 0 then BS t1 a t2
                   else if EVEN k then BS (insert ((k - 1) / 2) a t1) a' t2
                   else BS t1 a' (insert ((k - 1) / 2) a t2)
termination_by k
decreasing_by all_goals omega
end Mut

theorem witness : ∃ (k a : Nat) (t : spt Nat), Mut.insert k a t ≠ HOL.sptree.insert k a t := by
  refine ⟨2, 7, LS 3, ?_⟩
  have h20 : ¬ (2:Nat) = 0 := by omega
  have h10 : ¬ (1:Nat) = 0 := by omega
  have hev2 : EVEN 2 := by simp [EVEN]
  have hodd : ¬ EVEN 1 := by simp [EVEN]
  have e0 : HOL.sptree.insert 0 7 (LN : spt Nat) = LS 7 := by
    rw [HOL.sptree.insert]; simp
  have e1 : HOL.sptree.insert 1 7 (LN : spt Nat) = BN LN (LS 7) := by
    rw [HOL.sptree.insert, if_neg h10, if_neg hodd]
    show BN LN (HOL.sptree.insert ((1 - 1) / 2) 7 LN) = _
    rw [show (1 - 1) / 2 = 0 by omega, e0]
  have eb : HOL.sptree.insert 2 7 (LS 3) = BS (LS 7) 3 LN := by
    rw [HOL.sptree.insert, if_neg h20, if_pos hev2]
    show BS (HOL.sptree.insert ((2 - 1) / 2) 7 LN) 3 LN = _
    rw [show (2 - 1) / 2 = 0 by omega, e0]
  have em : Mut.insert 2 7 (LS 3) = BS (BN LN (LS 7)) 3 LN := by
    rw [Mut.insert, if_neg h20, if_pos hev2]
    show BS (Mut.insert ((2 - 1) / 1) 7 LN) 3 LN = _
    have : Mut.insert ((2 - 1) / 1) 7 (LN : spt Nat) = BN LN (LS 7) := by
      rw [show (2 - 1) / 1 = 1 by omega, Mut.insert, if_neg h10, if_neg hodd]
      show BN LN (Mut.insert ((1 - 1) / 2) 7 LN) = _
      rw [show (1 - 1) / 2 = 0 by omega, Mut.insert]; simp
    rw [this]
  rw [eb, em]
  intro h; cases h

#print axioms witness
