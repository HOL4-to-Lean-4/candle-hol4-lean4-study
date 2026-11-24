import CandleLean
open HOL Candle Classical
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
universe u
noncomputable section

namespace Mut
def types_in : term → Set type
  | Var _ ty => INSERT ty EMPTY
  | Const _ ty => INSERT ty EMPTY
  | Comb t1 t2 => UNION (types_in t1) (types_in t2)
  | Abs v t => UNION (types_in t) (types_in v)
end Mut

theorem equiv : ∀ t : term, Mut.types_in t = Candle.types_in t := by
  intro t
  induction t with
  | Var x ty => simp [Mut.types_in, Candle.types_in]
  | Const x ty => simp [Mut.types_in, Candle.types_in]
  | Comb t1 t2 ih1 ih2 => simp only [Mut.types_in, Candle.types_in, ih1, ih2]
  | Abs v t ih1 ih2 =>
    simp only [Mut.types_in, Candle.types_in, ih1, ih2]
    unfold UNION setOf
    funext x
    apply propext
    exact or_comm

#print axioms equiv
