import CandleLean
open HOL Candle
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Mut
/-- mutated statement of `Candle.term_ok_raconv` (the EVERY hypothesis on `env` is dropped) -/
def term_ok_raconv_stmt : Prop :=
    ∀ (env : List (term × term)) (tp : term × term), RACONV env tp →
        ∀ (sig : sig),
        term_ok sig tp.1 ∧ welltyped tp.2 → term_ok sig tp.2
end Mut

theorem flookup_empty {α : Type} {β : Type} [Nonempty β] (x : α) :
    FLOOKUP (FEMPTY : fmap α β) x = none := by
  unfold FLOOKUP
  rw [if_neg]
  intro h
  exact h rfl

/-- env = [(x:a, y:foo)] has ill-matched types; with the empty signature `x:a` is term_ok but `y:foo` is not. -/
theorem witness : ¬ Mut.term_ok_raconv_stmt := by
  intro h
  have key := h [(Var (mls "x") (Tyvar (mls "a")), Var (mls "y") (Tyapp (mls "foo") []))]
    (Var (mls "x") (Tyvar (mls "a")), Var (mls "y") (Tyapp (mls "foo") []))
    (RACONV.Var (Or.inl rfl)) ((FEMPTY : tysig), (FEMPTY : tmsig))
    ⟨by simp [term_ok, type_ok, tysof], ⟨_, has_type.Var⟩⟩
  have h4 : FLOOKUP (tysof (((FEMPTY : tysig), (FEMPTY : tmsig)) : sig)) (mls "foo") = none :=
    flookup_empty _
  have h3 : type_ok (tysof (((FEMPTY : tysig), (FEMPTY : tmsig)) : sig)) (Tyapp (mls "foo") []) := key
  simp only [type_ok] at h3
  rw [h4] at h3
  cases h3.1

#print axioms witness
