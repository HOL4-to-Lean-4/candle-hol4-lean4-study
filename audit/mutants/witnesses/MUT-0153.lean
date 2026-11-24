import CandleLean

open Candle HOL Classical

universe u

namespace Mut
noncomputable section

def find_index {α : Type u} : α → List α → Nat → Option Nat
  | _, [], _ => none
  | y, x :: xs, n => if x = y then find_index y xs (n + 1) else some n

end
end Mut

theorem witness : ∃ (y : Nat) (l : List Nat) (n : Nat),
    Mut.find_index y l n ≠ Candle.find_index y l n := by
  refine ⟨1, [1], 0, ?_⟩
  simp [Mut.find_index, Candle.find_index]

#print axioms witness
