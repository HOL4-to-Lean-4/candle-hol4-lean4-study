import CandleLean
open Candle HOL Classical

namespace Mut
universe u
def ALL_DISTINCT {α : Type u} : List α → Prop
  | [] => True
  | h :: t => ¬ h ∈ t ∨ ALL_DISTINCT t
end Mut

/-- [0, 0]: the mutant accepts it (second disjunct, since ALL_DISTINCT [0] holds), base rejects it -/
theorem witness : ∃ l : List Nat, Mut.ALL_DISTINCT l ∧ ¬ ALL_DISTINCT l := by
  refine ⟨[0, 0], ?_, ?_⟩
  · simp [Mut.ALL_DISTINCT]
  · simp [ALL_DISTINCT]

#print axioms witness
