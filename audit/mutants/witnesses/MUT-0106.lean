import CandleLean
open HOL Candle Classical
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
noncomputable section

namespace Mut
def term_image (f : term → term) (l : List term) : List term :=
  match l with
  | [] => l
  | h :: t =>
    let h' := f h
    let t' := term_image f t
    if h' = h ∧ t' = t then term_union [h'] t' else l
end Mut

/-- `f` constantly `y`, `l = [x]`: the base returns `[y]`, the mutant returns `[x]`. -/
theorem witness : ∃ (f : term → term) (l : List term), Mut.term_image f l ≠ Candle.term_image f l := by
  have hxy : mls "x" ≠ mls "y" := by decide
  have hyx : mls "y" ≠ mls "x" := by decide
  refine ⟨fun _ => Var (mls "y") (Tyvar (mls "a")), [Var (mls "x") (Tyvar (mls "a"))], ?_⟩
  intro h
  simp [Mut.term_image, Candle.term_image, term_union, hxy, hyx] at h

#print axioms witness
