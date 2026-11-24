import CandleLean

universe u v

open HOL Candle Classical

noncomputable section

namespace Mut

def type_ok (tysig : tysig) : type → Prop
  | Tyvar _ => True
  | Tyapp name args => EVERY (type_ok tysig) args

theorem witness : ¬ ∀ tysig ty, (Mut.type_ok tysig ty ↔ Candle.type_ok tysig ty) := by
  intro h
  have h2 := (h FEMPTY (Tyapp (mls "c") [])).1 (by simp [Mut.type_ok, EVERY])
  unfold Candle.type_ok at h2
  obtain ⟨hl, _⟩ := h2
  unfold FLOOKUP at hl
  split at hl
  · rename_i hm
    exact hm rfl
  · cases hl

end Mut

#print axioms Mut.witness
