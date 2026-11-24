import CandleLean

open HOL Classical

universe u v

namespace Mut
noncomputable section

def SURJ {α : Type u} {β : Type v} (f : α → β) (s : Set α) (t : Set β) : Prop :=
  (∀ x, x ∈ s → f x ∈ t) ∧ (∀ x, x ∈ t → ∃ y, y ∈ s ∨ f y = x)

end
end Mut

-- s = ∅, t = {0}, f = id: the mutated SURJ holds (y = 0 satisfies `f y = 0`), the base one does not.
theorem witness : ∃ (f : Nat → Nat) (s t : HOL.Set Nat), Mut.SURJ f s t ∧ ¬ HOL.SURJ f s t := by
  refine ⟨id, (fun _ => False), (fun x => x = 0), ?_, ?_⟩
  · refine ⟨fun x (hx : False) => hx.elim, fun x _ => ⟨x, Or.inr rfl⟩⟩
  · rintro ⟨_, h⟩
    obtain ⟨y, hy, _⟩ := h 0 (show 0 = 0 from rfl)
    exact (hy : False)

#print axioms witness
