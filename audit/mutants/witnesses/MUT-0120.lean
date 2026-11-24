import CandleLean
open Candle HOL Classical

namespace Mut
inductive RACONV : List (term × term) → term × term → Prop where
  | Var {env : List (term × term)} {x1 : mlstring} {ty1 : type} {x2 : mlstring} {ty2 : type} :
      ALPHAVARS env (Var x1 ty1, Var x2 ty2) → RACONV env (Var x1 ty1, Var x2 ty2)
  | Const {env : List (term × term)} {x : mlstring} {ty : type} :
      RACONV env (Const x ty, Const x ty)
  | Comb {env : List (term × term)} {s1 s2 t1 t2 : term} :
      RACONV env (t1, t2) → RACONV env (Comb s1 t1, Comb s2 t2)
  | Abs {env : List (term × term)} {v1 v2 t1 t2 : term} :
      typeof v1 = typeof v2 → RACONV ((v1, v2) :: env) (t1, t2) →
      RACONV env (Abs v1 t1, Abs v2 t2)
end Mut

/-- `Comb (Var a) c` vs `Comb (Const a) c`: the mutant ignores the function parts; the base needs RACONV (Var, Const), impossible. -/
theorem witness : ¬ ∀ (env : List (term × term)) (p : term × term), (Mut.RACONV env p ↔ RACONV env p) := by
  intro h
  have hm : Mut.RACONV [] (Comb (Var (mls "a") BoolTy) (Const (mls "c") BoolTy),
      Comb (Const (mls "a") BoolTy) (Const (mls "c") BoolTy)) := Mut.RACONV.Comb Mut.RACONV.Const
  have hb := (h _ _).1 hm
  cases hb with
  | Comb h1 h2 => cases h1

#print axioms witness
