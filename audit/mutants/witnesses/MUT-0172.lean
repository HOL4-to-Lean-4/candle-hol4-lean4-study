import CandleLean
open HOL Candle Classical
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
noncomputable section

namespace Mut
/-- mutated `RESULT_pkg`: `opaque` replaced by `def`, so the value on `Clash t` is now known -/
private def RESULT_pkg {α : Type u} : {f : result α → α // ∀ t, f (Result t) = t} :=
  ⟨fun r => match r with | Result t => t | Clash t => t, fun _ => rfl⟩

def RESULT {α : Type u} : result α → α := RESULT_pkg.1
end Mut

/-- U1 witness. In the mutant, `RESULT (Clash t) = t` is provable (by `rfl`).
HOL4 clause that leaves it open: `holSyntaxLib$RESULT_def`, `RESULT (Result t) = t` (nothing about `Clash`).
Two models of that clause (functions on `result Bool`) disagree on `RESULT (Clash true)`. -/
theorem witness : ∀ {α : Type} (t : α), Mut.RESULT (Clash t) = t := fun _ => rfl

/-- the saved clause has models that disagree on `RESULT (Clash true)` (so the equation is not in Φ) -/
theorem models_disagree :
    ∃ f g : {f : result Bool → Bool // ∀ t, f (Result t) = t}, f.1 (Clash true) ≠ g.1 (Clash true) :=
  ⟨⟨fun r => match r with | Result t => t | Clash t => t, fun _ => rfl⟩,
   ⟨fun r => match r with | Result t => t | Clash t => !t, fun _ => rfl⟩, by decide⟩

#print axioms models_disagree
#print axioms witness
