import CandleLean

open Candle HOL Classical

namespace Mut
noncomputable section

def term_union (l1 l2 : List term) : List term :=
  match l1, l2 with
  | [], l2 => l2
  | l1, [] => l1
  | h1 :: t1, h2 :: t2 =>
    let c := orda [] h1 h2
    if c = EQUAL then h1 :: term_union t1 t2
    else if c = LESS then h1 :: term_union t1 (t2 ++ [h2])
    else h2 :: term_union (h1 :: t1) t2
termination_by l1.length + l2.length

end
end Mut

-- h1 = Var, h2 = Const (so orda [] h1 h2 = LESS), l2 = [h2, k]:
-- base [h1, h2, k], mutant [h1, k, h2].
theorem witness : ∃ l1 l2 : List term, Mut.term_union l1 l2 ≠ Candle.term_union l1 l2 := by
  let ty : type := Tyvar (mls "a")
  let h1 : term := Var (mls "a") ty
  let h2 : term := Const (mls "c") ty
  let k : term := Var (mls "e") ty
  have hlt : orda [] h1 h2 = LESS := by
    simp [orda, h1, h2]
  have hne : orda [] h1 h2 ≠ EQUAL := by rw [hlt]; intro h; cases h
  refine ⟨[h1], [h2, k], ?_⟩
  have e1 : Candle.term_union [h1] [h2, k] = [h1, h2, k] := by
    rw [Candle.term_union]
    simp only [hlt]
    simp [Candle.term_union]
  have e2 : Mut.term_union [h1] [h2, k] = [h1, k, h2] := by
    rw [Mut.term_union]
    simp only [hlt]
    simp [Mut.term_union]
  rw [e1, e2]
  intro h
  simp [h2, k] at h

#print axioms witness
