import CandleLean
open HOL Candle.HolSemantics Candle.HolSyntax Candle.Mlstring
-- instance_ is fixed for an undeclared constant
example {U : Type} (i : interpretation U) (name : mlstring) (ty : type) :
    instance_ FEMPTY i name ty = fun _ => tmaof i name [] := by
  unfold instance_
  rw [dif_neg]
  rintro ⟨ty0, tyin, h, _⟩
  exact absurd h (by simp [FLOOKUP, FEMPTY])
-- termsem of an abstraction with a constant binder is the default value
example (mem : Nat → Nat → Prop) (tm : Candle.HolSyntax.tmsig) (i : interpretation Nat) (v : valuation Nat) (n : mlstring) (ty : type) (b : term) :
    termsem mem tm i v (.Abs (.Const n ty) b) = 0 := by
  rw [termsem]
  · rfl
  · intros; simp_all
-- FAPPLY of the empty map
example : FAPPLY (FEMPTY : FMap Nat Nat) 3 = 0 := rfl
-- PERMUTES is not BIJ f s s : the constant function is BIJ on {0} and HOL4 proves it PERMUTES {0}
example (s : HOL.Set Nat) (hs : ∀ x, x ∈ s ↔ x = 0) : ¬ PERMUTES (fun _ : Nat => 0) s := by
  intro h
  exact absurd (h.1 1 (by rw [hs]; decide)) (by decide)
example (s : HOL.Set Nat) (hs : ∀ x, x ∈ s ↔ x = 0) : BIJ (fun _ : Nat => 0) s s := by
  simp [BIJ, INJ, SURJ, hs]
