import CandleLean

universe u v

open HOL Candle Classical

noncomputable section

namespace Mut

def field (h l : Nat) (v : bitstring) : bitstring := fixwidth (h + 0 - l) (shiftr v l)

theorem witness : ∃ h l v, Mut.field h l v ≠ HOL.field h l v :=
  ⟨0, 0, [], by simp [Mut.field, HOL.field, fixwidth, shiftr, zero_extend, PAD_LEFT, GENLIST, K, SNOC]⟩

end Mut

#print axioms Mut.witness
