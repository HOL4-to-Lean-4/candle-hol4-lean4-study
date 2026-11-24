import CandleLean
open Candle HOL Classical

namespace Mut
universe u v
def INJ {α : Type u} {β : Type v} (f : α → β) (s : Set α) (t : Set β) : Prop :=
  ∀ x, x ∈ s → f x ∈ t ∧ (∀ x y, (x ∈ s ∧ y ∈ s) → f x = f y → x = y)
end Mut

/-- The mutant moves the injectivity conjunct under `∀ x ∈ s`. Its own hypothesis `x ∈ s` is not used by the injectivity
    part, which carries its own `x ∈ s ∧ y ∈ s` premise, so the two definitions are provably equivalent (for s = ∅ both are true). -/
theorem equiv {α : Type u} {β : Type v} (f : α → β) (s : Set α) (t : Set β) :
    Mut.INJ f s t ↔ INJ f s t := by
  unfold Mut.INJ INJ
  constructor
  · intro h
    exact ⟨fun x hx => (h x hx).1, fun x y hxy => (h x hxy.1).2 x y hxy⟩
  · intro h x hx
    exact ⟨h.1 x hx, h.2⟩

#print axioms equiv
