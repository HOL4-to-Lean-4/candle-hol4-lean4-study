import CandleLean
open Candle HOL Classical

noncomputable section
namespace Mut
def FCP_bits : (n : Nat) → (Nat → Prop) → Nat
  | 0, _ => 0
  | k + 1, f => FCP_bits k f + (if f k then 2 ^ k else 1)
end Mut
end

/-- f = False, n = 1: base 0, mutant 1 -/
theorem witness : ∃ n f, Mut.FCP_bits n f ≠ FCP_bits n f := by
  refine ⟨1, fun _ => False, ?_⟩
  simp [Mut.FCP_bits, FCP_bits]

#print axioms witness
