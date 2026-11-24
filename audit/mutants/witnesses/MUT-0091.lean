import CandleLean
open HOL Candle Classical
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
universe u
variable {U : Type u}
noncomputable section

namespace Mut
def is_structure0 [Nonempty U] (mem : U → U → Prop) (sig : sig) (int : interpretation U)
    (val : valuation U) : Prop :=
  is_std_interpretation0 mem int ∧
  is_interpretation0 mem sig int ∧
  is_valuation0 mem (tysof sig) (tyaof int) val
end Mut

theorem flookup_empty {α : Type} {β : Type} [Nonempty β] (x : α) :
    FLOOKUP (FEMPTY : fmap α β) x = none := by
  unfold FLOOKUP
  rw [if_neg]
  intro h
  exact h rfl

theorem mls_ne_of_length (a b : String) (h : a.length ≠ b.length) : mls a ≠ mls b := by
  intro hh
  simp only [mls, str, mlstring.implode.injEq] at hh
  have h' := congrArg List.length hh
  simp only [List.length_map] at h'
  exact h (by simpa using h')

/-- the standard interpretation over any `mem`, defined by cases on the names `fun`, `bool`, `=` -/
def stdint (mem : Nat → Nat → Prop) : interpretation Nat :=
  (fun name l => if name = mls "fun" then funspace mem (l.getD 0 0) (l.getD 1 0)
                 else if name = mls "bool" then boolset mem else 0,
   fun name l => if name = mls "=" then
       abstract mem (HD l) (funspace mem (HD l) (boolset mem))
         (fun x => abstract mem (HD l) (boolset mem) (fun y => boolean mem (x = y)))
     else 0)

/-- the empty signature is not standard, yet it carries a standard interpretation and a valuation -/
theorem witness : ∃ (mem : Nat → Nat → Prop) (sig : sig) (int : interpretation Nat) (val : valuation Nat),
    Mut.is_structure0 mem sig int val ∧ ¬ Candle.is_structure0 mem sig int val := by
  have hfb : mls "bool" ≠ mls "fun" := mls_ne_of_length _ _ (by decide)
  refine ⟨fun _ _ => True, (FEMPTY, FEMPTY), stdint (fun _ _ => True), (fun _ => 0, fun _ => 0), ?_, ?_⟩
  · refine ⟨⟨⟨fun dom rng => ?_, ?_⟩, ?_⟩, ⟨?_, ?_⟩, ⟨fun x => ⟨0, trivial⟩, fun v ty _ => trivial⟩⟩
    · simp [stdint, tyaof, tmaof]
    · simp [stdint, tyaof, tmaof, hfb]
    · intro τ _
      simp [stdint, tyaof, tmaof]
    · intro x hx; exact absurd rfl hx
    · intro x hx; exact absurd rfl hx
  · intro h
    have h3 := h.1.1
    have h4 : FLOOKUP (tysof ((FEMPTY : tysig), (FEMPTY : tmsig))) (mls "fun") = none := flookup_empty _
    rw [h4] at h3
    cases h3

#print axioms witness
