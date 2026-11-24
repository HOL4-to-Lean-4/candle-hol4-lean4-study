import CandleLean
open HOL Candle Classical
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
noncomputable section

namespace Mut
def append_aux {α : Type u} : app_list α → List α → List α
  | .Nil, aux => aux
  | .List xs, aux => xs ++ xs
  | .Append l1 l2, aux => append_aux l1 (append_aux l2 aux)
end Mut

/-- `List [0]` with aux `[1]`: the mutant gives `[0,0]`, the base `[0,1]`. -/
theorem witness : ∃ (l : app_list Nat) (aux : List Nat), Mut.append_aux l aux ≠ Candle.append_aux l aux := by
  refine ⟨.List [0], [1], ?_⟩
  simp [Mut.append_aux, Candle.append_aux]

#print axioms witness
