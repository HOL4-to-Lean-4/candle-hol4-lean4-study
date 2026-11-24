import CandleLean

universe u v

open HOL Candle Classical

noncomputable section

namespace Mut

def term_remove (t : term) (l : List term) : List term :=
  match l with
  | [] => l
  | s :: ss =>
    let c := orda [] t s
    if c = GREATER then
      let ss' := term_remove t ss
      if ss' = ss then l else s :: ss'
    else if c = EQUAL then l else ss

theorem witness : ∃ t l, Mut.term_remove t l ≠ Candle.term_remove t l := by
  refine ⟨Var (mls "x") BoolTy, [Var (mls "x") BoolTy], ?_⟩
  simp [Mut.term_remove, Candle.term_remove, orda]

end Mut

#print axioms Mut.witness
