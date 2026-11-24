import CandleLean
open Candle HOL Classical
noncomputable section
namespace Mut
def is_std_type_assignment0 [Nonempty U] (mem : U → U → Prop) (δ : tyass U) : Prop :=
  (∀ dom rng, δ (mls "fun") [dom, rng] = funspace mem dom rng) ∧
  δ (mls "boom") [] = boolset mem
end Mut

-- U = Bool, mem arbitrary; δ follows the base clauses and returns the negation of `boolset` elsewhere.
theorem witness : ∃ (mem : Bool → Bool → Prop) (δ : tyass Bool),
    Candle.is_std_type_assignment0 mem δ ∧ ¬ Mut.is_std_type_assignment0 mem δ := by
  refine ⟨fun _ _ => False,
    fun n l => if n = mls "bool" ∧ l = [] then boolset (fun _ _ : Bool => False)
      else if n = mls "fun" then (match l with | [d, r] => funspace (fun _ _ : Bool => False) d r | _ => true)
      else !(boolset (fun _ _ : Bool => False)), ?_, ?_⟩
  · refine ⟨fun dom rng => ?_, ?_⟩
    · simp
    · simp
  · rintro ⟨_, h⟩
    have hb : mls "boom" ≠ mls "bool" := by simp [mls, str]; decide
    have hf : mls "boom" ≠ mls "fun" := by simp [mls, str]; decide
    revert h
    simp [hb, hf]

#print axioms witness
