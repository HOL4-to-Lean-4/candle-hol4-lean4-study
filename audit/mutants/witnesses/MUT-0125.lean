import CandleLean

universe u v

open HOL Candle Classical

noncomputable section

namespace Mut

def term_union (l1 l2 : List term) : List term :=
  match l1, l2 with
  | [], l2 => l1
  | l1, [] => l2
  | h1 :: t1, h2 :: t2 =>
    let c := orda [] h1 h2
    if c = EQUAL then h1 :: term_union t1 t2
    else if c = LESS then h1 :: term_union t1 (h2 :: t2)
    else h2 :: term_union (h1 :: t1) t2
termination_by l1.length + l2.length

theorem witness : ∃ l1 l2, Mut.term_union l1 l2 ≠ Candle.term_union l1 l2 := by
  refine ⟨[], [Var (mls "x") BoolTy], ?_⟩
  simp [Mut.term_union, Candle.term_union]

end Mut

#print axioms Mut.witness
