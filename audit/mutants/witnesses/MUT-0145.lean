import CandleLean
open HOL Candle Classical
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
universe u
noncomputable section

namespace Mut
def term_ok (sig : sig) : term → Prop
  | Var _ ty => type_ok (tysof sig) ty
  | Const name ty =>
    ∃ ty0, FLOOKUP (tmsof sig) name = some ty0 ∨ type_ok (tysof sig) ty ∧ is_instance ty0 ty
  | Comb tm1 tm2 => term_ok sig tm1 ∧ term_ok sig tm2 ∧ welltyped (Comb tm1 tm2)
  | Abs v tm => ∃ x ty, v = Var x ty ∧ type_ok (tysof sig) ty ∧ term_ok sig tm
end Mut

theorem witness : ∃ (sig : sig) (t : term), Mut.term_ok sig t ∧ ¬ Candle.term_ok sig t := by
  refine ⟨(FEMPTY, FEMPTY), Const (mls "c") (Tyvar (mls "a")), ?_, ?_⟩
  · refine ⟨Tyvar (mls "a"), Or.inr ⟨by simp [type_ok], [], ?_⟩⟩
    simp [TYPE_SUBST, REV_ASSOCD]
  · rintro ⟨ty0, h, _⟩
    have : FLOOKUP (tmsof ((FEMPTY : tysig), (FEMPTY : tmsig))) (mls "c") = none := by
      unfold FLOOKUP
      rw [if_neg]
      intro h; exact h rfl
    simp only [term_ok] at *
    rw [this] at h
    cases h

#print axioms witness
