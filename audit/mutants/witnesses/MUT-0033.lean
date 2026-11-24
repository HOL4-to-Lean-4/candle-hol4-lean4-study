import CandleLean

open Candle HOL Classical

namespace Mut
noncomputable section

def INORDER_INSERT (x : string) (xs : List string) : List string :=
  FILTER (fun y => string_lt x y) xs ++ ([x] ++ FILTER (fun y => string_lt x y) xs)

end
end Mut

-- x = "b", xs = ["a"] (ASCII 98, 97): base gives ["a","b"], mutant gives ["b"].
theorem witness : ∃ (x : string) (xs : List string),
    Mut.INORDER_INSERT x xs ≠ Candle.INORDER_INSERT x xs := by
  let a : char := ⟨97, by decide⟩
  let b : char := ⟨98, by decide⟩
  have hab : char_lt a b := by simp [char_lt, ORD, a, b]
  have hba : ¬ char_lt b a := by simp [char_lt, ORD, a, b]
  have hs1 : string_lt [a] [b] := Or.inl hab
  have hs2 : ¬ string_lt [b] [a] := by
    rintro (h | ⟨h, _⟩)
    · exact hba h
    · exact hba (by simp [char_lt, ORD, a, b] at h ⊢)
  refine ⟨[b], [[a]], ?_⟩
  intro h
  have h1 : Candle.INORDER_INSERT [b] [[a]] = [[a], [b]] := by
    simp [Candle.INORDER_INSERT, FILTER, hs1, hs2]
  have h2 : Mut.INORDER_INSERT [b] [[a]] = [[b]] := by
    simp [Mut.INORDER_INSERT, FILTER, hs2]
  rw [h1, h2] at h
  simp at h

#print axioms witness
