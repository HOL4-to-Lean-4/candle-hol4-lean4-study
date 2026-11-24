import CandleLean
open HOL Candle
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Mut
universe u
/-- mutated statement of `Candle.ASSUME_correct` (premise `theory_ok thy ∧ has_type p BoolTy ∧ term_ok (sigof thy) p` dropped) -/
def ASSUME_correct_stmt : Prop :=
  ∀ (U : Type u) [Nonempty U] (mem : U → U → Prop),
    ∀ (thy : thy) (p : term), entails0 mem (thy, [p]) p
end Mut

theorem flookup_empty {α : Type} {β : Type} [Nonempty β] (x : α) :
    FLOOKUP (FEMPTY : fmap α β) x = none := by
  unfold FLOOKUP
  rw [if_neg]
  intro h
  exact h rfl

/-- the empty signature is not a standard signature, so `entails0` fails -/
theorem witness : ¬ Mut.ASSUME_correct_stmt.{0} := by
  intro h
  have := h Nat (fun _ _ => False) ((FEMPTY, FEMPTY), fun _ => False) (Var (mls "x") (Tyvar (mls "a")))
  have h3 := this.1.2.2.1
  have h4 : FLOOKUP (tysof (sigof (((FEMPTY : tysig), (FEMPTY : tmsig)), (fun _ => False : Set term)))) (mls "fun") = none :=
    flookup_empty _
  rw [h4] at h3
  cases h3

#print axioms witness
