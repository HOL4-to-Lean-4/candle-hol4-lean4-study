import CandleLean
open Candle HOL Classical

noncomputable section
namespace Mut
def is_std_sig (sig : sig) : Prop :=
  FLOOKUP (tysof sig) (mls "gun") = some 2 ∧
  FLOOKUP (tysof sig) (mls "bool") = some 0 ∧
  FLOOKUP (tmsof sig) (mls "=") = some (Fun (Tyvar (mls "A")) (Fun (Tyvar (mls "A")) BoolTy))
end Mut

theorem flookup_empty {α β : Type} [Nonempty β] (k : α) : FLOOKUP (FEMPTY : fmap α β) k = none := by
  unfold FLOOKUP
  rw [if_neg]
  intro h
  exact (h : (FEMPTY : fmap α β).rep k ≠ none) rfl

theorem flookup_upd {α β : Type} [Nonempty β] (f : fmap α β) (k k' : α) (v : β) :
    FLOOKUP (FUPDATE f (k, v)) k' = if k' = k then some v else FLOOKUP f k' := by
  by_cases h : k' = k
  · subst h
    have hd : k' ∈ FDOM (FUPDATE f (k', v)) := by
      show (FUPDATE f (k', v)).rep k' ≠ none
      simp [FUPDATE]
    rw [FLOOKUP, if_pos hd]
    simp [FAPPLY, FUPDATE]
  · rw [if_neg h]
    have hm : k' ∈ FDOM (FUPDATE f (k, v)) ↔ k' ∈ FDOM f := by
      show (FUPDATE f (k, v)).rep k' ≠ none ↔ f.rep k' ≠ none
      simp [FUPDATE, h]
    have ha : FAPPLY (FUPDATE f (k, v)) k' = FAPPLY f k' := by
      simp [FAPPLY, FUPDATE, h]
    unfold FLOOKUP
    rw [ha]
    by_cases hf : k' ∈ FDOM f
    · rw [if_pos (hm.2 hf), if_pos hf]
    · rw [if_neg (fun h' => hf (hm.1 h')), if_neg hf]

/-- a standard signature with `fun`, `bool`, `=` (and no `gun`) satisfies the base predicate but not the mutant. -/
theorem witness : ∃ s : sig, is_std_sig s ∧ ¬ Mut.is_std_sig s := by
  let tys : tysig := FUPDATE (FUPDATE FEMPTY (mls "fun", 2)) (mls "bool", 0)
  let tms : tmsig := FUPDATE FEMPTY (mls "=", Fun (Tyvar (mls "A")) (Fun (Tyvar (mls "A")) BoolTy))
  have hfb : mls "fun" ≠ mls "bool" := by
    simp only [mls, ne_eq, mlstring.implode.injEq]; decide
  have hgb : mls "gun" ≠ mls "bool" := by
    simp only [mls, ne_eq, mlstring.implode.injEq]; decide
  have hgf : mls "gun" ≠ mls "fun" := by
    simp only [mls, ne_eq, mlstring.implode.injEq]; decide
  refine ⟨(tys, tms), ⟨?_, ?_, ?_⟩, ?_⟩
  · show FLOOKUP (FUPDATE (FUPDATE FEMPTY (mls "fun", 2)) (mls "bool", 0)) (mls "fun") = some 2
    rw [flookup_upd, if_neg hfb, flookup_upd, if_pos rfl]
  · show FLOOKUP (FUPDATE (FUPDATE FEMPTY (mls "fun", 2)) (mls "bool", 0)) (mls "bool") = some 0
    rw [flookup_upd, if_pos rfl]
  · show FLOOKUP (FUPDATE FEMPTY (mls "=", Fun (Tyvar (mls "A")) (Fun (Tyvar (mls "A")) BoolTy))) (mls "=") = _
    rw [flookup_upd, if_pos rfl]
  · intro h
    have h1 := h.1
    change FLOOKUP (FUPDATE (FUPDATE FEMPTY (mls "fun", 2)) (mls "bool", 0)) (mls "gun") = some 2 at h1
    rw [flookup_upd, if_neg hgb, flookup_upd, if_neg hgf, flookup_empty] at h1
    exact absurd h1 (by simp)

#print axioms witness
