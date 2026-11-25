import CmlTS.Proofs.Lib

/-! Auxiliary lemmas about `TOKENS`. -/

set_option linter.unusedSimpArgs false

namespace CmlTS

noncomputable section

open scoped Classical

def Aux.tok (P : char → Prop) : List char → string → List string
  | [], l => TOKENS P l
  | h :: t, [] => [(h :: t).reverse]
  | h :: t, x :: l =>
    if P x then (h :: t).reverse :: TOKENS P (x :: l)
    else ((h :: t).reverse ++ HD (TOKENS P (x :: l))) :: TL (TOKENS P (x :: l))

theorem Aux.TOKENS_nil (P : char → Prop) : TOKENS P [] = [] := by rw [TOKENS]

theorem Aux.TOKENS_pos {P : char → Prop} {x : char} {l : string} (h : P x) :
    TOKENS P (x :: l) = TOKENS P l := by
  rw [TOKENS]
  simp [SPLITP, h, NULL, TL]

theorem Aux.TOKENS_neg {P : char → Prop} {x : char} {l : string} (h : ¬ P x) :
    TOKENS P (x :: l) = (x :: (SPLITP P l).1) :: TOKENS P (SPLITP P l).2 := by
  rw [TOKENS]
  simp [SPLITP, h, NULL]

theorem Aux.TOKENS_tok {P : char → Prop} {x : char} {l : string} (h : ¬ P x) :
    TOKENS P (x :: l) = Aux.tok P [x] l := by
  rw [Aux.TOKENS_neg h]
  cases l with
  | nil => simp [SPLITP, Aux.tok, Aux.TOKENS_nil]
  | cons y l =>
    by_cases hy : P y
    · simp [SPLITP, Aux.tok, hy]
    · simp [SPLITP, Aux.tok, hy, Aux.TOKENS_neg hy, HD, TL]

theorem Aux.tok_step {P : char → Prop} {x : char} {l : string} {ss : List char} (h : ¬ P x) :
    Aux.tok P ss (x :: l) = Aux.tok P (x :: ss) l := by
  cases ss with
  | nil => exact Aux.TOKENS_tok h
  | cons a ss =>
    simp only [Aux.tok, if_neg h, Aux.TOKENS_tok h]
    cases l with
    | nil => simp [Aux.tok, HD, TL]
    | cons y l =>
      by_cases hy : P y
      · simp [Aux.tok, hy, HD, TL]
      · simp [Aux.tok, hy, HD, TL]

end

end CmlTS
