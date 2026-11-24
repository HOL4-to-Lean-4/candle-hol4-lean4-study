import CandleLean

open HOL Classical

namespace Mut
noncomputable section

def FCP_bits : (n : Nat) → (Nat → Prop) → Nat
  | 0, _ => 0
  | k + 1, f => FCP_bits k f + (if f k then 0 else 2 ^ k)

end
end Mut

theorem witness : ∃ (n : Nat) (f : Nat → Prop), Mut.FCP_bits n f ≠ HOL.FCP_bits n f := by
  refine ⟨1, fun _ => True, ?_⟩
  simp [Mut.FCP_bits, HOL.FCP_bits]

#print axioms witness
