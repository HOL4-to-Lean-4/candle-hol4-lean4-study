import CandleLean
open Candle HOL Classical

noncomputable section
namespace Mut
def UNHEX (c : char) : Nat :=
  let n := ORD c
  if ORD (ch '0') ≤ n ∧ n ≤ ORD (ch '0') then n - ORD (ch '0') else
  if ORD (ch 'a') ≤ n ∧ n ≤ ORD (ch 'f') then 10 + n - ORD (ch 'a') else
  if ORD (ch 'A') ≤ n ∧ n ≤ ORD (ch 'F') then 10 + n - ORD (ch 'A') else 0
end Mut
end

/-- the digit '5': base 5, mutant 0 -/
theorem witness : ∃ c, Mut.UNHEX c ≠ UNHEX c := by
  refine ⟨ch '5', ?_⟩
  simp [Mut.UNHEX, UNHEX, ORD, ch]

#print axioms witness
