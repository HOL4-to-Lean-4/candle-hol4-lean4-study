import CandleLean
open Candle
example {U : Type} [Nonempty U] (mem : U → U → Prop) (tmsig : Candle.tmsig) (i : interpretation U) (v : valuation U) (n : mlstring) (ty : type) (b : term) :
    termsem0 mem tmsig i v (.Abs (.Const n ty) b) = ARB := by
  rw [termsem0]; simp
