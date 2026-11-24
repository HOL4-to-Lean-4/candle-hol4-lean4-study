import CandleLean
open Candle HOL Classical
noncomputable section
namespace Mut
def satisfies0 [Nonempty U] (mem : U → U → Prop) (i : interpretation U)
    (shc : sig × List term × term) : Prop :=
  ∀ v, EVERY (fun t => termsem0 mem (tmsof shc.1) i v t = true_ mem) shc.2.1 →
    termsem0 mem (tmsof shc.1) i v shc.2.2 = true_ mem
end Mut

-- U = Bool and mem = (fun _ _ => False): no valuation is a valuation (types have no inhabitants), so the base holds
-- vacuously, while the mutant (no is_valuation0 guard) must hold for the junk valuation sending every variable to `not True`.
theorem witness : ¬ ∀ (mem : Bool → Bool → Prop) (i : interpretation Bool) (shc : sig × List term × term),
    (Mut.satisfies0 mem i shc ↔ Candle.satisfies0 mem i shc) := by
  intro h
  let mem : Bool → Bool → Prop := fun _ _ => False
  let i : interpretation Bool := (fun _ _ => true, fun _ _ => true)
  let shc : sig × List term × term := ((FEMPTY, FEMPTY), [], Var (mls "x") (Tyvar (mls "a")))
  have hb : Candle.satisfies0 mem i shc := by
    intro v ⟨hv, _⟩
    obtain ⟨y, hy⟩ := hv.1 (mls "a")
    exact absurd hy (by simp [mem])
  have hm := (h mem i shc).2 hb ((fun _ => true), (fun _ => !(true_ mem)))
  have := hm (by simp [EVERY, shc])
  rw [(termsem0_def mem (tmsof shc.1) i).1] at this
  revert this
  simp
  cases true_ mem <;> simp

#print axioms witness
