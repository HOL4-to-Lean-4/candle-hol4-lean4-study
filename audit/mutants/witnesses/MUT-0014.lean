import CandleLean
open HOL Classical
noncomputable section
namespace Mut
def field (h l : Nat) (v : bitstring) : bitstring := fixwidth (h + 2 - l) (shiftr v l)
end Mut

theorem witness : ∃ h l v, Mut.field h l v ≠ HOL.field h l v := by
  refine ⟨0, 0, [], ?_⟩
  intro h
  have := congrArg List.length h
  simp [Mut.field, HOL.field, fixwidth, shiftr, zero_extend, PAD_LEFT, GENLIST, SNOC] at this

#print axioms witness
