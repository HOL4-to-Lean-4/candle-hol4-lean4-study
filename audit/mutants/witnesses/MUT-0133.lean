import CandleLean
open HOL Candle Classical
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
universe u
variable {U : Type u}
noncomputable section

namespace Mut
def is_structure0 [Nonempty U] (mem : U → U → Prop) (sig : sig) (int : interpretation U)
    (val : valuation U) : Prop :=
  is_std_sig sig ∧
  is_std_interpretation0 mem int ∧
  is_interpretation0 mem sig int ∨
  is_valuation0 mem (tysof sig) (tyaof int) val
end Mut

theorem flookup_empty {α : Type} {β : Type} [Nonempty β] (x : α) :
    FLOOKUP (FEMPTY : fmap α β) x = none := by
  unfold FLOOKUP
  rw [if_neg]
  intro h
  exact h rfl

/-- empty signature, trivial membership: the valuation clause holds, the standard-signature clause does not -/
theorem witness : ∃ (mem : Nat → Nat → Prop) (sig : sig) (int : interpretation Nat) (val : valuation Nat),
    Mut.is_structure0 mem sig int val ∧ ¬ Candle.is_structure0 mem sig int val := by
  refine ⟨fun _ _ => True, (FEMPTY, FEMPTY), (fun _ _ => 0, fun _ _ => 0), (fun _ => 0, fun _ => 0), ?_, ?_⟩
  · right
    refine ⟨fun x => ⟨0, trivial⟩, fun v ty _ => trivial⟩
  · intro h
    have h3 := h.1.1
    have h4 : FLOOKUP (tysof ((FEMPTY : tysig), (FEMPTY : tmsig))) (mls "fun") = none := flookup_empty _
    rw [h4] at h3
    cases h3

#print axioms witness
