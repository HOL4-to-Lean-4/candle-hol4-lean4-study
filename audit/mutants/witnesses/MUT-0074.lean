import CandleLean
open HOL Classical
noncomputable section
namespace Mut
def BIJ {α : Type u} {β : Type v} (f : α → β) (s : Set α) (t : Set β) : Prop :=
  INJ f s t ∨ SURJ f s t
end Mut

-- f = id, s = ∅, t = everything: injective (vacuously) but not onto t.
theorem witness : ¬ ∀ (f : Nat → Nat) (s t : Set Nat), (Mut.BIJ f s t ↔ HOL.BIJ f s t) := by
  intro h
  have h1 := (h (fun x => x) (fun _ => False) (fun _ => True)).1
    (Or.inl ⟨fun x hx => by exact absurd hx (by simp [Membership.mem, IN]), fun x y hxy => by
      exact absurd hxy.1 (by simp [Membership.mem, IN])⟩)
  obtain ⟨_, hs⟩ := h1.2
  obtain ⟨y, hy, _⟩ := hs 0 (by simp [Membership.mem, IN])
  simp [Membership.mem, IN] at hy

#print axioms witness
