import CandleLean
open HOL Candle Classical
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
noncomputable section

namespace Mut
/-- mutated statement of `REV_ASSOCD_ALOOKUP` (the swapped list is reversed before the lookup),
for all types in `Type` -/
def REV_ASSOCD_ALOOKUP_stmt : Prop :=
    ∀ {α β : Type} (ls : List (α × β)) (x : β) (d : α),
      REV_ASSOCD x ls d =
        match ALOOKUP (List.reverse (ls.map (fun (x, y) => (y, x)))) x with
        | none => d
        | some y => y
end Mut

/-- ls = [(0,5),(1,5)], x = 5: the first match gives 0, the reversed lookup gives 1. -/
theorem witness : ¬ Mut.REV_ASSOCD_ALOOKUP_stmt := by
  intro h
  have := h (α := Nat) (β := Nat) [(0, 5), (1, 5)] 5 7
  simp [REV_ASSOCD, ALOOKUP] at this

#print axioms witness
