import CandleLean
example : HD ([] : List Nat) = ARB := by first | rfl | simp [HD]
example : LAST ([] : List Nat) = ARB := by first | rfl | simp [LAST]
example : HD ([] : List Nat) = LAST [] := by first | rfl | simp [HD, LAST]
example (a : mlstring) (t : type) : dest_var (term.Const a t) = ARB := by first | rfl | simp [dest_var]
example (s t : Nat) : RESULT (result.Clash s) = RESULT (result.Clash t) := by first | rfl | simp [RESULT]
example (s t : Nat) : CLASH (result.Result s) = RESULT (result.Clash t) := by first | rfl | simp [RESULT, CLASH]
-- tier 2
example : (SEG : Nat → Nat → List Nat → List Nat) = Classical.epsilon (fun SEG : Nat → Nat → List Nat → List Nat => (∀ k l, SEG 0 k l = []) ∧ (∀ m x l, SEG (m + 1) 0 (x :: l) = x :: SEG m 0 l) ∧ (∀ m k x l, SEG (m + 1) (k + 1) (x :: l) = SEG (m + 1) k l)) := rfl
