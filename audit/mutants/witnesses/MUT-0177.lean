import CandleLean

open HOL Classical

universe u

namespace Mut
noncomputable section

private def LAST_wit {α : Type u} [Nonempty α] : List α → α
  | [] => Classical.choice inferInstance
  | h :: t => if t = [] then h else LAST_wit t

private def LAST_pkg {α : Type u} [Nonempty α] :
    {f : List α → α // ∀ h t, f (h :: t) = if t = [] then h else f t} :=
  ⟨LAST_wit, fun _ _ => by simp [LAST_wit]⟩

def LAST {α : Type u} [Nonempty α] : List α → α := LAST_pkg.1

end
end Mut

/-- Models of the HOL4 defining clause `list$LAST_DEF`:
    `LAST (h::t) = if t = [] then h else LAST t`. -/
def LAST_clause {α : Type u} (f : List α → α) : Prop :=
  ∀ h t, f (h :: t) = if t = [] then h else f t

/-- A model of the clause that returns `d` on `[]`. -/
def lastD {α : Type u} (d : α) : List α → α
  | [] => d
  | h :: t => if t = [] then h else lastD d t

-- (1) In the mutant, `LAST []` is provably the Hilbert-choice element (a mapped-constant equation).
-- (2) The clause `LAST_DEF` leaves `LAST []` open: for every value c there is a model of the clause
--     with `f [] ≠ c`, so (1) is not in Φ and the base (opaque `LAST_pkg`) cannot prove it.
theorem witness :
    (Mut.LAST ([] : List Nat) = Classical.choice (inferInstance : Nonempty Nat)) ∧
    (∀ c : Nat, ∃ f : List Nat → Nat, LAST_clause f ∧ f [] ≠ c) := by
  refine ⟨rfl, fun c => ?_⟩
  have hcl : ∀ d : Nat, LAST_clause (lastD d) := fun d h t => by simp [lastD]
  by_cases hc : c = 0
  · exact ⟨lastD 1, hcl 1, by simp [lastD, hc]⟩
  · exact ⟨lastD 0, hcl 0, by simp [lastD]; omega⟩

#print axioms witness
