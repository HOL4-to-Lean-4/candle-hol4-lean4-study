import CandleLean
open HOL Candle Classical
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
noncomputable section

namespace Mut
inductive has_type : term → type → Prop where
  | Var {n : mlstring} {ty : type} : has_type (Var n ty) ty
  | Const {n : mlstring} {ty : type} : has_type (Const n ty) ty
  | Comb {s t : term} {dty rty : type} :
      has_type s (Fun dty rty) → has_type t dty → has_type (Comb s t) rty
  | Abs {n : mlstring} {dty rty : type} {t : term} :
      has_type (Abs (Var n dty) t) (Fun dty rty)
end Mut

/-- In the mutant `λ(x:bool). (y:a)` has type `bool → bool`; in the base it cannot. -/
theorem witness : ∃ (t : term) (ty : type), Mut.has_type t ty ∧ ¬ Candle.has_type t ty := by
  refine ⟨Abs (Var (mls "x") BoolTy) (Var (mls "y") (Tyvar (mls "a"))), Fun BoolTy BoolTy,
    Mut.has_type.Abs, ?_⟩
  intro h
  cases h with
  | Abs h2 => cases h2

#print axioms witness
