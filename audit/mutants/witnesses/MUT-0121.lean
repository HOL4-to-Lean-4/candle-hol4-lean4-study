import CandleLean
open HOL Candle Classical
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
universe u
variable {U : Type u}
noncomputable section

namespace Mut
def type_lt (a b : type) : Prop :=
  ∀ type_lt' : type → type → Prop,
    ((∀ x1 x2, mlstring_lt x1 x2 → type_lt' (Tyvar x1) (Tyvar x2)) ∧
     (∀ x1 x2 args2, type_lt' (Tyvar x1) (Tyapp x2 args2)) ∧
     (∀ x1 args1 x2 args2,
        type_lt' (Tyapp x1 args1) (Tyapp x2 args2))) →
    type_lt' a b
end Mut

/-- a relation closed under the base rules that does not relate `Tyapp "b" []` to `Tyapp "a" []` -/
def R : type → type → Prop
  | Tyvar x1, Tyvar x2 => mlstring_lt x1 x2
  | Tyvar _, Tyapp _ _ => True
  | Tyapp x1 _, Tyapp x2 _ => mlstring_lt x1 x2 ∨ x1 = x2
  | Tyapp _ _, Tyvar _ => False

theorem witness : ∃ a b : type, Mut.type_lt a b ∧ ¬ Candle.type_lt a b := by
  have e1 : strlen (implode [ch 'b']) = 1 := rfl
  have e2 : strlen (implode [ch 'a']) = 1 := rfl
  have h1 : char_lt (ch 'a') (ch 'b') := by unfold char_lt ORD ch; decide
  have s1 : strsub (implode [ch 'b']) 0 = ch 'b' := by simp [strsub, EL, HD_def]
  have s2 : strsub (implode [ch 'a']) 0 = ch 'a' := by simp [strsub, EL, HD_def]
  have hn : ¬ mlstring_lt (implode [ch 'b']) (implode [ch 'a']) := by
    unfold mlstring_lt Candle.compare
    rw [e1, e2, if_neg (by omega), if_neg (by omega), compare_aux, if_neg (by omega), s1, s2, if_pos h1]
    intro h; cases h
  have hne : implode [ch 'b'] ≠ implode [ch 'a'] := by
    intro h
    have := mlstring.implode.inj h
    simp [ch] at this
  refine ⟨Tyapp (implode [ch 'b']) [], Tyapp (implode [ch 'a']) [], ?_, ?_⟩
  · intro T hT
    exact hT.2.2 _ _ _ _
  · intro h
    have := h R ⟨fun _ _ hh => hh, fun _ _ _ => trivial, fun x1 args1 x2 args2 hl => ?_⟩
    · rcases this with hh | hh
      · exact hn hh
      · exact hne hh
    · rcases hl with hl | hl
      · exact Or.inl hl
      · exact Or.inr hl.1

#print axioms witness
