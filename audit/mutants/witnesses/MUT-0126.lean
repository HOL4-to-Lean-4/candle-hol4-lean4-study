import CandleLean
open Candle HOL Classical

noncomputable section
namespace Mut
def make_even (n : Nat) : Nat := if EVEN n then n else n + 2
end Mut
end

/-- n = 1: base 2, mutant 3 -/
theorem witness : ∃ n, Mut.make_even n ≠ make_even n := by
  refine ⟨1, ?_⟩
  have h : ¬ EVEN 1 := by simp [EVEN]
  simp [Mut.make_even, make_even, h]

#print axioms witness
