import CandleLean

open HOL Classical

universe u

namespace Mut
noncomputable section

def sort3_tail {α : Type u} (neg : Prop) (R : α → α → Prop) (x y z : α) : List α :=
  if R x y ≠ neg then
    if R y z ≠ neg then [x, y, z]
    else if R x z ≠ neg then [z, x, y] else [x, z, y]
  else if R y z ≠ neg then
    if R x z ≠ neg then [y, x, z]
    else [y, z, x]
  else [z, y, x]

end
end Mut

-- neg = True, R a b := (a = 1 ∧ b = 2): R 0 1, R 0 2 are False (so ≠ neg), R 1 2 is True (= neg).
-- (x,y,z) = (0,1,2): base [0,2,1], mutant [2,0,1].
theorem witness : ∃ (neg : Prop) (R : Nat → Nat → Prop) (x y z : Nat),
    Mut.sort3_tail neg R x y z ≠ HOL.sort3_tail neg R x y z := by
  refine ⟨True, fun a b => a = 1 ∧ b = 2, 0, 1, 2, ?_⟩
  simp [Mut.sort3_tail, HOL.sort3_tail]

#print axioms witness
