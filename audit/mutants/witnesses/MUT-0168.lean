import CandleLean
open Candle HOL Classical

namespace Mut
def domain (ty : type) : type :=
  match ty with
  | _ => ty
end Mut

/-- `domain (Fun bool bool) = bool` in the base, but the mutant is the identity -/
theorem witness : ∃ ty, Mut.domain ty ≠ domain ty := by
  refine ⟨Fun BoolTy BoolTy, ?_⟩
  intro h
  simp [Mut.domain, domain, Fun, BoolTy] at h

#print axioms witness
