import CandleLean

universe u v

open HOL Candle Classical

noncomputable section

namespace Mut

def VFREE_IN (v : term) : term → Prop
  | Var x ty => Var x ty = v
  | Const x ty => Const x ty = v
  | Comb s t => VFREE_IN v s ∨ VFREE_IN v t
  | Abs w t => w = v ∧ VFREE_IN v t

theorem witness : ¬ ∀ v t, (Mut.VFREE_IN v t ↔ Candle.VFREE_IN v t) := by
  intro h
  have := (h (Var (mls "x") BoolTy) (Abs (Var (mls "x") BoolTy) (Var (mls "x") BoolTy))).1
    (by simp [Mut.VFREE_IN])
  simp [Candle.VFREE_IN] at this

end Mut

#print axioms Mut.witness
