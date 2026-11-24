import CandleLean

universe u v

open HOL Candle Classical

noncomputable section

namespace Mut

def HEX (n : Nat) : char :=
  if n < 10 then CHR (ORD (ch '0') + n) else
  if n < 17 then CHR (ORD (ch 'A') + (n - 10)) else CHR 0

theorem witness : ∃ n, Mut.HEX n ≠ HOL.HEX n := by
  refine ⟨16, ?_⟩
  intro h
  simp [Mut.HEX, HOL.HEX] at h
  have e1 : CHR (ORD (ch 'A') + 6) = ⟨71, by decide⟩ := by
    have : ORD (ch 'A') + 6 = 71 := by simp [ORD, ch]
    rw [this]; exact CHR_of_lt (by decide)
  have e2 : CHR 0 = ⟨0, by decide⟩ := CHR_of_lt (by decide)
  rw [e1, e2] at h
  cases h

end Mut

#print axioms Mut.witness
