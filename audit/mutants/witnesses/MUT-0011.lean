import CandleLean

universe u v

open HOL Candle Classical

noncomputable section

namespace Mut

/-- The mutated statement of `RACONV_dbterm` (`∃` instead of `∀` for `env` and `tp`) -/
def Smut : Prop :=
    ∃ (env : List (term × term)) (tp : term × term), RACONV env tp →
      welltyped tp.1 ∧ welltyped tp.2 ∧
      (∀ (vp : term × term), vp ∈ env → (∃ (x : mlstring) (ty : type), vp.1 = Var x ty) ∧
        (∃ (x : mlstring) (ty : type), vp.2 = Var x ty))
       → dbterm (env.map (dest_var ∘ Prod.fst)) tp.1 = dbterm (env.map (dest_var ∘ Prod.snd)) tp.2

/-- Vacuous: the mutated statement holds whatever the conclusion is, because the premise
`welltyped tp.1` fails for the chosen `tp`. -/
theorem witness : ∀ (C : List (term × term) → term × term → Prop),
    ∃ (env : List (term × term)) (tp : term × term), RACONV env tp →
      welltyped tp.1 ∧ welltyped tp.2 ∧
      (∀ (vp : term × term), vp ∈ env → (∃ (x : mlstring) (ty : type), vp.1 = Var x ty) ∧
        (∃ (x : mlstring) (ty : type), vp.2 = Var x ty))
       → C env tp := by
  intro C
  refine ⟨[], (Comb (Var (mls "a") BoolTy) (Var (mls "a") BoolTy),
              Comb (Var (mls "a") BoolTy) (Var (mls "a") BoolTy)), fun _ hp => ?_⟩
  exfalso
  obtain ⟨⟨ty, hty⟩, _⟩ := hp
  cases hty with
  | Comb h1 h2 =>
    cases h1

theorem mutated_holds : Mut.Smut := by
  obtain ⟨env, tp, h⟩ := witness (fun env tp =>
    dbterm (env.map (dest_var ∘ Prod.fst)) tp.1 = dbterm (env.map (dest_var ∘ Prod.snd)) tp.2)
  exact ⟨env, tp, h⟩

end Mut

#print axioms Mut.witness
