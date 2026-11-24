import CandleLean
open HOL Candle Classical
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
universe u
noncomputable section

namespace Mut
def type_ok (tysig : tysig) : type → Prop
  | Tyvar _ => True
  | Tyapp name args => FLOOKUP tysig name = some args.length
end Mut

theorem flookup_upd_self {β : Type} [Nonempty β] (m : fmap mlstring β) (k : mlstring) (v : β) :
    FLOOKUP (FUPDATE m (k, v)) k = some v := by
  unfold FLOOKUP
  have hd : k ∈ FDOM (FUPDATE m (k, v)) := by
    show (FUPDATE m (k, v)).rep k ≠ none
    simp [FUPDATE]
  rw [if_pos hd]
  have : (FUPDATE m (k, v)).rep k = some v := by simp [FUPDATE]
  unfold FAPPLY
  rw [this]

theorem flookup_empty {α : Type} {β : Type} [Nonempty β] (x : α) :
    FLOOKUP (FEMPTY : fmap α β) x = none := by
  unfold FLOOKUP
  rw [if_neg]
  intro h
  exact h rfl

theorem flookup_upd_ne {β : Type} [Nonempty β] (m : fmap mlstring β) (k k' : mlstring) (v : β) (h : k' ≠ k) :
    FLOOKUP (FUPDATE m (k, v)) k' = FLOOKUP m k' := by
  unfold FLOOKUP
  have e : (FUPDATE m (k, v)).rep k' = m.rep k' := by simp [FUPDATE, h]
  have e2 : k' ∈ FDOM (FUPDATE m (k, v)) ↔ k' ∈ FDOM m := by
    show (FUPDATE m (k, v)).rep k' ≠ none ↔ m.rep k' ≠ none
    rw [e]
  by_cases hm : k' ∈ FDOM m
  · rw [if_pos hm, if_pos (e2.2 hm)]
    unfold FAPPLY; rw [e]
  · rw [if_neg hm, if_neg (fun hh => hm (e2.1 hh))]

/-- signature with `fun : 1`; `Tyapp fun [Tyapp q []]` is accepted by the mutant but `q` is undeclared -/
theorem witness : ∃ (tysig : tysig) (t : type), Mut.type_ok tysig t ∧ ¬ Candle.type_ok tysig t := by
  have hne : mls "q" ≠ mls "fun" := by
    intro h
    simp only [mls, str, mlstring.implode.injEq] at h
    have h' := congrArg List.length h
    simp only [List.length_map] at h'
    revert h'; decide
  refine ⟨FUPDATE FEMPTY (mls "fun", 1), Tyapp (mls "fun") [Tyapp (mls "q") []], ?_, ?_⟩
  · simp only [Mut.type_ok]
    rw [flookup_upd_self]; rfl
  · intro h
    simp only [Candle.type_ok] at h
    have h2 := h.2
    simp only [EVERY] at h2
    have h3 := h2.1
    simp only [Candle.type_ok] at h3
    have h4 := h3.1
    rw [flookup_upd_ne _ _ _ _ hne, flookup_empty] at h4
    cases h4

#print axioms witness
