import CandleLean
open Candle HOL Classical
noncomputable section
namespace Mut
def sizeof : term → Nat
  | Var _ _ => 1
  | Const _ _ => 1
  | Comb s t => 1 + sizeof s + sizeof t
  | Abs _ t => 1 + sizeof t
end Mut

theorem witness : ∃ t, Mut.sizeof t ≠ Candle.sizeof t := by
  refine ⟨Abs (Var (mls "x") (Tyvar (mls "a"))) (Var (mls "x") (Tyvar (mls "a"))), ?_⟩
  simp [Mut.sizeof, Candle.sizeof]

#print axioms witness
