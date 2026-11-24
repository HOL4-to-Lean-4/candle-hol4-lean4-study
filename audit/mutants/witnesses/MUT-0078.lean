import CandleLean
open Candle HOL Classical

noncomputable section
namespace Mut
def splitlines (ls : string) : List string :=
  let lines := FIELDS (fun c => ch '\n' = c) ls
  if NULL (HD lines) then FRONT lines else lines
end Mut
end

/-- ls = "a\n": FIELDS gives [["a"], []]; the base tests `NULL (LAST lines)` (true) and returns `[["a"]]`,
    the mutant tests `NULL (HD lines)` (false) and returns both fields. -/
theorem witness : ∃ ls : string, Mut.splitlines ls ≠ splitlines ls := by
  refine ⟨[ch 'a', ch '\n'], ?_⟩
  have hne : ch '\n' ≠ ch 'a' := by decide
  have hF : FIELDS (fun c => ch '\n' = c) [ch 'a', ch '\n'] = [[ch 'a'], []] := by
    rw [FIELDS]
    simp [SPLITP, hne, NULL, TL, FIELDS]
  intro h
  simp only [Mut.splitlines, splitlines, hF] at h
  simp [LAST_DEF, HD_def, NULL, FRONT] at h

#print axioms witness
