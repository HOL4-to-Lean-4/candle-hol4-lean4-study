import CmlTS
open Classical
theorem fapply_arb : FAPPLY (FEMPTY : FMap Nat Nat) 0 = ARB := by unfold FAPPLY FEMPTY; simp
