import CandleLean

open Candle HOL Classical

namespace Mut
noncomputable section

def compare (s1 s2 : mlstring) : ordering :=
  if strlen s1 < strlen s2 then compare_aux s1 s2 LESS 0 (strlen s1)
  else if strlen s2 < strlen s1 then compare_aux s1 s2 LESS 0 (strlen s2)
  else compare_aux s1 s2 EQUAL 0 (strlen s2)

end
end Mut

-- s1 = "a" (one char), s2 = "": the base returns GREATER, the mutant LESS.
theorem witness : ∃ s1 s2 : mlstring, Mut.compare s1 s2 ≠ Candle.compare s1 s2 := by
  refine ⟨Candle.implode [⟨97, by decide⟩], Candle.implode [], ?_⟩
  have h1 : Candle.compare (Candle.implode [⟨97, by decide⟩]) (Candle.implode []) = GREATER := by
    simp [Candle.compare, strlen, compare_aux]
  have h2 : Mut.compare (Candle.implode [⟨97, by decide⟩]) (Candle.implode []) = LESS := by
    simp [Mut.compare, strlen, compare_aux]
  rw [h1, h2]
  intro h
  cases h

#print axioms witness
