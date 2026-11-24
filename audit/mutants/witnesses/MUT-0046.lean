import CandleLean
open HOL Candle Classical
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
noncomputable section
theorem mem_IMAGE' {α β : Type} (f : α → β) (s : Set α) (y : β) :
    y ∈ IMAGE f s ↔ ∃ x, f x = y ∧ x ∈ s := by
  unfold IMAGE GSPEC
  show (∃ x, (y, True) = (f x, x ∈ s)) ↔ _
  constructor
  · rintro ⟨x, hx⟩
    simp only [Prod.mk.injEq] at hx
    exact ⟨x, hx.1.symm, by rw [← hx.2]; trivial⟩
  · rintro ⟨x, hx, hs⟩
    exact ⟨x, by simp [hx, hs]⟩
theorem mem_UNION' {α : Type} (s t : Set α) (y : α) : y ∈ UNION s t ↔ y ∈ s ∨ y ∈ t := Iff.rfl
theorem mem_INSERT' {α : Type} (x : α) (s : Set α) (y : α) : y ∈ INSERT x s ↔ y = x ∨ y ∈ s := Iff.rfl
theorem mem_EMPTY' {α : Type} (y : α) : y ∈ (EMPTY : Set α) ↔ False := Iff.rfl


namespace Mut
def domain {α : Type u} : spt α → Set Nat
  | LN => EMPTY
  | LS _ => INSERT 0 EMPTY
  | BN t1 t2 => UNION (IMAGE (fun n => 2 * n + 2) (domain t1)) (IMAGE (fun n => 2 * n + 1) (domain t2))
  | BS t1 _ t2 =>
    UNION (UNION (INSERT 0 EMPTY) (IMAGE (fun n => 2 * n - 2) (domain t1)))
      (IMAGE (fun n => 2 * n + 1) (domain t2))
end Mut

/-- t = BS (LS ()) () LN has domain {0,2} in the base and {0} in the mutant (2*0-2 = 0 in Nat). -/
theorem witness : ∃ t : spt Unit, Mut.domain t ≠ sptree.domain t := by
  refine ⟨BS (LS ()) () LN, ?_⟩
  intro h
  have h2 : (2 ∈ Mut.domain (BS (LS ()) () LN)) ↔ (2 ∈ sptree.domain (BS (LS ()) () LN)) := by
    rw [h]
  have r : 2 ∈ sptree.domain (BS (LS ()) () LN) := by
    simp only [sptree.domain, mem_UNION', mem_IMAGE', mem_INSERT', mem_EMPTY']
    exact Or.inl (Or.inr ⟨0, rfl, Or.inl rfl⟩)
  have l := h2.mpr r
  simp only [Mut.domain, mem_UNION', mem_IMAGE', mem_INSERT', mem_EMPTY'] at l
  rcases l with ((h | h) | ⟨x, hx, hx2 | hx2⟩) | ⟨x, hx, hx2⟩
  · omega
  · exact h
  · omega
  · exact hx2
  · exact hx2

#print axioms witness
