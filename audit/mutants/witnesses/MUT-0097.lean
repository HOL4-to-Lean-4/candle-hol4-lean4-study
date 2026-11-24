import CandleLean
open HOL Candle Classical
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
universe u
noncomputable section

namespace Mut
def splitlines (ls : string) : List string :=
  let lines := FIELDS (fun c => ch '\n' = c) ls
  if NULL (LAST lines) then lines else FRONT lines
end Mut

theorem witness : ∃ ls : string, Mut.splitlines ls ≠ Candle.splitlines ls := by
  refine ⟨[], ?_⟩
  have hl : FIELDS (fun c => ch '\n' = c) [] = [[]] := by rw [FIELDS]
  have hlast : LAST ([[]] : List string) = [] := by rw [LAST_DEF]; simp
  have hnull : NULL (LAST ([[]] : List string)) := by rw [hlast]; exact trivial
  have hm : Mut.splitlines [] = [[]] := by
    unfold Mut.splitlines; simp only [hl]; rw [if_pos hnull]
  have hb : Candle.splitlines [] = [] := by
    unfold Candle.splitlines; simp only [hl]; rw [if_pos hnull]; simp [FRONT]
  rw [hm, hb]; intro h; cases h

#print axioms witness
