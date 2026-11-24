import CandleLean

universe u v

open HOL Candle Classical

noncomputable section

namespace Mut

def make_even (n : Nat) : Nat := if ODD n then n else n + 1

theorem witness : ∃ n, Mut.make_even n ≠ Candle.make_even n :=
  ⟨0, by simp [Mut.make_even, Candle.make_even, ODD, EVEN]⟩

end Mut

#print axioms Mut.witness
