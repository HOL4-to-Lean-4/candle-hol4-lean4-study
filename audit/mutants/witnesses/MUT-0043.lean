import CandleLean
open HOL Candle Classical
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
noncomputable section

namespace Mut
def compare (s1 s2 : mlstring) : ordering :=
  if strlen s1 < strlen s2 then compare_aux s2 s1 LESS 0 (strlen s1)
  else if strlen s2 < strlen s1 then compare_aux s1 s2 GREATER 0 (strlen s2)
  else compare_aux s1 s2 EQUAL 0 (strlen s2)
end Mut

theorem witness : ∃ s1 s2 : mlstring, Mut.compare s1 s2 ≠ Candle.compare s1 s2 := by
  refine ⟨implode [ch 'a'], implode [ch 'b', ch 'b'], ?_⟩
  have e1 : strlen (implode [ch 'a']) = 1 := rfl
  have e2 : strlen (implode [ch 'b', ch 'b']) = 2 := rfl
  have h1 : char_lt (ch 'a') (ch 'b') := by unfold char_lt ORD ch; decide
  have h2 : ¬ char_lt (ch 'b') (ch 'a') := by unfold char_lt ORD ch; decide
  have s1 : strsub (implode [ch 'a']) 0 = ch 'a' := by simp [strsub, EL, HD_def]
  have s2 : strsub (implode [ch 'b', ch 'b']) 0 = ch 'b' := by simp [strsub, EL, HD_def]
  have hb : Candle.compare (implode [ch 'a']) (implode [ch 'b', ch 'b']) = LESS := by
    unfold Candle.compare
    rw [if_pos (by rw [e1, e2]; decide), e1, compare_aux, if_neg (by decide), s1, s2, if_neg h2, if_pos h1]
  have hm : Mut.compare (implode [ch 'a']) (implode [ch 'b', ch 'b']) = GREATER := by
    unfold Mut.compare
    rw [if_pos (by rw [e1, e2]; decide), e1, compare_aux, if_neg (by decide), s1, s2, if_pos h1]
  rw [hb, hm]
  intro h; cases h

#print axioms witness
