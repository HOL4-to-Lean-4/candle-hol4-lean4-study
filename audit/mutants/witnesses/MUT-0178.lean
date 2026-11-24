import CandleLean
open HOL Candle Classical
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
noncomputable section

namespace Mut
/-- mutated `HD_pkg`: `opaque` replaced by `def`, so `HD []` is now known to be `Classical.choice _` -/
private def HD_pkg {α : Type u} [Nonempty α] : {f : List α → α // ∀ h t, f (h :: t) = h} :=
  ⟨fun l => match l with | h :: _ => h | [] => Classical.choice inferInstance, fun _ _ => rfl⟩

def HD {α : Type u} [Nonempty α] : List α → α := HD_pkg.1
end Mut

theorem epsilon_false {α : Type u} [Nonempty α] : (Classical.epsilon (fun _ : α => False)) = Classical.choice inferInstance := by
  unfold Classical.epsilon Classical.strongIndefiniteDescription
  rw [dif_neg (fun ⟨_, h⟩ => h)]

/-- the saved HOL4 clause (`list$HD`, only `HD (h::t) = h`) has models that disagree on `HD []` -/
theorem models_disagree :
    ∃ f g : {f : List Bool → Bool // ∀ h t, f (h :: t) = h}, f.1 [] ≠ g.1 [] :=
  ⟨⟨fun l => match l with | h :: _ => h | [] => true, fun _ _ => rfl⟩,
   ⟨fun l => match l with | h :: _ => h | [] => false, fun _ _ => rfl⟩, by decide⟩

/-- U1 witness. In the mutant, `HD [] = @x. F` is provable (`@x. F` is `Classical.epsilon (fun _ => False)`, which is
`Classical.choice`). HOL4 clause that leaves it open: `list$HD` defining theorem `HD (h::t) = h` (nothing about `HD []`);
`models_disagree` gives two models of the clause with different `HD []`. -/
theorem witness : ∀ {α : Type} [Nonempty α], Mut.HD ([] : List α) = Classical.epsilon (fun _ : α => False) := by
  intro α _
  rw [epsilon_false]
  rfl

#print axioms witness
