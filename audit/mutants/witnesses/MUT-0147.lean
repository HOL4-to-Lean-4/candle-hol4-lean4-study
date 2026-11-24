import CandleLean

open Candle HOL Classical

universe u

namespace Mut
noncomputable section

variable {U : Type u}

def is_term_valuation0 (mem : U → U → Prop) (tysig : tysig) (δ : tyass U) (τ : tyval U)
    (σ : tmval U) : Prop :=
  ∃ v ty, type_ok tysig ty → mem (σ (v, ty)) (typesem δ τ ty)

end
end Mut

-- mem = False, empty type signature.  Base: fails at ty = Tyvar a (type_ok holds, mem fails).
-- Mutant: holds, witnessed by an ill-formed type `Tyapp x []` (type_ok false, implication vacuous).
theorem witness : ∃ (mem : Nat → Nat → Prop) (tysig : tysig) (δ : tyass Nat) (τ : tyval Nat)
    (σ : tmval Nat), Mut.is_term_valuation0 mem tysig δ τ σ ∧ ¬ is_term_valuation0 mem tysig δ τ σ := by
  refine ⟨fun _ _ => False, FEMPTY, fun _ _ => 0, fun _ => 0, fun _ => 0, ?_, ?_⟩
  · refine ⟨mls "v", Tyapp (mls "x") [], ?_⟩
    intro h
    exfalso
    simp [type_ok, FLOOKUP, FDOM, FEMPTY, Aux.mem_def] at h
  · intro h
    exact h (mls "v") (Tyvar (mls "a")) (by simp [type_ok])

#print axioms witness
