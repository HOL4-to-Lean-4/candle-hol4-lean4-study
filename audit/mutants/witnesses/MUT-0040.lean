import CandleLean
open HOL Candle Classical
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
noncomputable section

namespace Mut
/-- mutated `satisfies0` (valuation and hypothesis premises dropped) -/
def satisfies0 {U : Type u} [Nonempty U] (mem : U → U → Prop) (i : interpretation U)
    (shc : sig × List term × term) : Prop :=
  ∀ v, termsem0 mem (tmsof shc.1) i v shc.2.2 = true_ mem
end Mut

/-- With the empty membership relation on `Nat` there are no valuations, so the base is vacuously true; the mutant would
need every valuation to send `x` to the same element `true_`, which two valuations (constant `0`, constant `1`) cannot. -/
theorem witness : ∃ (mem : Nat → Nat → Prop) (i : interpretation Nat) (shc : sig × List term × term),
    satisfies0 mem i shc ∧ ¬ Mut.satisfies0 mem i shc := by
  let i : interpretation Nat := (fun _ _ => 0, fun _ _ => 0)
  refine ⟨fun _ _ => False, i, (((FEMPTY : tysig), (FEMPTY : tmsig)), [], Var (mls "x") (Tyvar (mls "a"))), ?_, ?_⟩
  · intro v hv
    obtain ⟨⟨h1, _⟩, _⟩ := hv
    obtain ⟨a, ha⟩ := h1 (mls "x")
    exact ha.elim
  · intro h
    have h0 := h ((fun _ => 0), (fun _ => 0))
    have h1 := h ((fun _ => 1), (fun _ => 1))
    rw [(termsem0_def _ _ _).1] at h0 h1
    exact absurd (h0.trans h1.symm) (by decide)

#print axioms witness
