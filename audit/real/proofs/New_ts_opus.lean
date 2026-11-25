import CmlTS
open CmlTS
theorem select_false_eq_ARB : select (fun _ : Bool => False) = (ARB : Bool) := by
  unfold select ARB; unfold Classical.epsilon Classical.strongIndefiniteDescription; simp
#print axioms select_false_eq_ARB
