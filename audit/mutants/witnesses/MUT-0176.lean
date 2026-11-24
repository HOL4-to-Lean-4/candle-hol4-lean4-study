import CandleLean
open Candle HOL Classical
noncomputable section
namespace Mut
private def CLASH_pkg {α : Type u} : {f : result α → α // ∀ t, f (Clash t) = t} :=
  ⟨fun r => match r with | Clash t => t | Result t => t, fun _ => rfl⟩

def CLASH {α : Type u} : result α → α := CLASH_pkg.1

theorem CLASH_def {α : Type u} (t : α) : CLASH (Clash t) = t := CLASH_pkg.2 t
end Mut

/-- U1 (V-C). HOL4 clause (saved theorem `CLASH_def` in holSyntaxLib): `CLASH (Clash t) = t`; nothing is saved for `CLASH (Result t)`.
    (1) In the mutant the equation `CLASH (Result t) = t` is provable (by `rfl`).
    (2) The clause leaves it open: two functions satisfy `f (Clash t) = t` and disagree on `Result true`
        (so no equation about `CLASH (Result _)` follows from the clause alone). -/
theorem witness :
    (∀ {α : Type u} (t : α), Mut.CLASH (Result t) = t) ∧
    ∃ f g : result Bool → Bool, (∀ t, f (Clash t) = t) ∧ (∀ t, g (Clash t) = t) ∧
      f (Result true) ≠ g (Result true) := by
  refine ⟨fun t => rfl, ?_⟩
  refine ⟨fun r => match r with | Clash t => t | Result t => t,
          fun r => match r with | Clash t => t | Result t => !t, fun _ => rfl, fun _ => rfl, ?_⟩
  simp

#print axioms witness
