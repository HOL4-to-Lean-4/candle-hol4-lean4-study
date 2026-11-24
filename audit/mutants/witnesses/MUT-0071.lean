import CandleLean

universe u v

open HOL Candle Classical

noncomputable section

namespace Mut

def sizeof : term → Nat
  | Var _ _ => 2
  | Const _ _ => 1
  | Comb s t => 1 + sizeof s + sizeof t
  | Abs _ t => 2 + sizeof t

theorem witness : ∃ t, Mut.sizeof t ≠ Candle.sizeof t :=
  ⟨Var (mls "x") BoolTy, by simp [Mut.sizeof, Candle.sizeof]⟩

end Mut

#print axioms Mut.witness
