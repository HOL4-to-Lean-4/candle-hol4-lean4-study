import CandleLean
open HOL Classical
noncomputable section
namespace Mut
def UNHEX (c : char) : Nat :=
  let n := ORD c
  if ORD (ch '0') ≤ n ∧ n ≤ ORD (ch '9') then n - ORD (ch '0') else
  if ORD (ch 'a') ≤ n ∧ n ≤ ORD (ch 'f') then 10 + n - ORD (ch 'a') else
  if ORD (ch 'A') ≤ n ∧ n ≤ ORD (ch 'F') then 10 + n - ORD (ch 'B') else 0
end Mut

theorem witness : ∃ c, Mut.UNHEX c ≠ HOL.UNHEX c := by
  refine ⟨ch 'A', ?_⟩
  simp [Mut.UNHEX, HOL.UNHEX, ORD, ch]

#print axioms witness
