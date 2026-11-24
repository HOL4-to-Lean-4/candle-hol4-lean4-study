import CandleLean

open Candle HOL Classical

universe u

namespace Mut
noncomputable section

variable {U : Type u}

def is_std_interpretation0 [Nonempty U] (mem : U → U → Prop) (i : interpretation U) : Prop :=
  is_std_type_assignment0 mem (tyaof i) ∧
  interprets0 mem (tmaof i) (mls "a") [mls "A"]
    (fun l => abstract mem (HD l) (funspace mem (HD l) (boolset mem))
      (fun x => abstract mem (HD l) (boolset mem) (fun y => boolean mem (x = y))))

end
end Mut

-- U = Nat, mem trivially True.  The interpretation gives "=" its standard meaning F and every
-- other constant F + 1.  The base accepts it; the mutant (which tests the name "a") rejects it.
theorem witness : ∃ (mem : Nat → Nat → Prop) (i : interpretation Nat),
    is_std_interpretation0 mem i ∧ ¬ Mut.is_std_interpretation0 mem i := by
  let mem : Nat → Nat → Prop := fun _ _ => True
  let F : List Nat → Nat := fun l =>
    abstract mem (HD l) (funspace mem (HD l) (boolset mem))
      (fun x => abstract mem (HD l) (boolset mem) (fun y => boolean mem (x = y)))
  let δ : tyass Nat := fun n args =>
    if n = mls "fun" then (match args with | [d, r] => funspace mem d r | _ => 0) else boolset mem
  let γ : tmass Nat := fun n vs => if n = mls "=" then F vs else F vs + 1
  have hfb : mls "bool" ≠ mls "fun" := by decide
  have hea : mls "a" ≠ mls "=" := by decide
  have hstd : is_std_type_assignment0 mem δ := by
    refine ⟨fun dom rng => ?_, ?_⟩
    · simp [δ]
    · simp [δ, hfb]
  refine ⟨mem, (δ, γ), ⟨hstd, ?_⟩, ?_⟩
  · intro τ _
    simp [tmaof, γ, F]
  · rintro ⟨_, h⟩
    have := h (fun _ => 0) (fun _ => ⟨0, trivial⟩)
    simp [tmaof, γ, F, hea] at this

#print axioms witness
