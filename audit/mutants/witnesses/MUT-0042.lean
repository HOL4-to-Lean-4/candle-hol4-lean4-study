import CandleLean
open Candle HOL Classical

namespace Mut
universe u
def interprets0 {U : Type u} (mem : U → U → Prop) (γ : tmass U) (name : mlstring) (vs : List mlstring)
    (f : List U → U) : Prop :=
  ∀ τ : tyval U, vs ≠ [] → is_type_valuation0 mem τ → γ name (vs.map τ) = f (vs.map τ)
end Mut

/-- U = Nat, mem = always true, vs = []: the mutant holds vacuously, while the base demands `γ name [] = f []`, false for γ = 0, f = 1. -/
theorem witness : ∃ (mem : Nat → Nat → Prop) (γ : tmass Nat) (name : mlstring) (vs : List mlstring) (f : List Nat → Nat),
    Mut.interprets0 mem γ name vs f ∧ ¬ interprets0 mem γ name vs f := by
  refine ⟨fun _ _ => True, fun _ _ => 0, mls "c", [], fun _ => 1, ?_, ?_⟩
  · intro τ h; exact absurd rfl h
  · intro h
    have := h (fun _ => 0) (fun _ => ⟨0, trivial⟩)
    simp at this

#print axioms witness
