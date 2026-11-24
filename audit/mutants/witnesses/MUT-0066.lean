import CandleLean
open Candle HOL Classical

noncomputable section
namespace Mut
def alpha_lt (t1 t2 : term) : Prop := orda [] t2 t1 = LESS
end Mut
end

/-- t1 = Var, t2 = Const: base `orda [] (Var ..) (Const ..) = LESS` (Var < anything),
    mutant needs `orda [] (Const ..) (Var ..) = LESS` but that is GREATER. -/
theorem witness : ∃ t1 t2 : term, Mut.alpha_lt t1 t2 ∧ ¬ alpha_lt t1 t2 := by
  refine ⟨Const (mls "c") BoolTy, Var (mls "a") BoolTy, ?_⟩
  constructor
  · unfold Mut.alpha_lt
    rw [orda]
    simp
    all_goals (intro _ _ h; cases h)
  · unfold alpha_lt
    rw [orda]
    simp
    all_goals (intro _ _ h; cases h)

#print axioms witness
