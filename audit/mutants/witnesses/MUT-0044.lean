import CandleLean
open Candle HOL Classical
noncomputable section
namespace Mut
def models0 [Nonempty U] (mem : U → U → Prop) (i : interpretation U) (thy : thy) : Prop :=
  is_interpretation0 mem (sigof thy) i ∨
  is_std_interpretation0 mem i ∧
  ∀ p, p ∈ axsof thy → satisfies0 mem i (sigof thy, [], p)
end Mut

-- U = Bool, empty signature (so any interpretation is an interpretation), but the type assignment does not
-- interpret "bool" as boolset: the mutant (a disjunction) accepts it, the base (needs the standard interpretation) does not.
theorem witness : ¬ ∀ (mem : Bool → Bool → Prop) (i : interpretation Bool) (t : thy),
    (Mut.models0 mem i t ↔ Candle.models0 mem i t) := by
  intro h
  let mem : Bool → Bool → Prop := fun _ _ => False
  let i : interpretation Bool := (fun _ _ => !(boolset mem), fun _ _ => true)
  let t : thy := ((FEMPTY, FEMPTY), fun _ => False)
  have h1 : Mut.models0 mem i t := by
    left
    refine ⟨?_, ?_⟩
    · intro x hx
      exact absurd rfl hx
    · intro x hx
      exact absurd rfl hx
  have h2 := ((h mem i t).1 h1).2.1.1.2
  revert h2
  simp [i]
  cases boolset mem <;> simp

#print axioms witness
