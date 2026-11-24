import CandleLean

universe u v

open HOL Candle Classical

noncomputable section

namespace Mut

inductive subtype1 : type → type → Prop where
  | rule {a : type} {args : List type} {name : mlstring} :
      subtype1 a (Tyapp name args)

theorem witness : ¬ ∀ a b, (Mut.subtype1 a b ↔ Candle.subtype1 a b) := by
  intro h
  have h1 : Mut.subtype1 (Tyvar (mls "x")) (Tyapp (mls "c") []) := Mut.subtype1.rule
  have h2 := (h _ _).1 h1
  cases h2 with
  | rule hm => simp at hm

end Mut

#print axioms Mut.witness
