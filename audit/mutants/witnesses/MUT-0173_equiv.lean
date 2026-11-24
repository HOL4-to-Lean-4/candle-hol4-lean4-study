import CandleLean

universe u v

open HOL Candle Classical

noncomputable section

namespace Mut

def Smut : Prop :=
    ∀ (n : Int) (tm : term) (env : List (term × term)) (tyin : List (type × type)),
        welltyped tm ∧ sizeof tm = n ∧
        (∀ (s s' : term), (s, s') ∈ env →
                ∃ (x : mlstring) (ty : type), s = Var x ty ∧
                       s' = Var x (TYPE_SUBST tyin ty))
        → (∃ (x : mlstring) (ty : type), INST_CORE env tyin tm = Clash (Var x (TYPE_SUBST tyin ty)) ∧
                  VFREE_IN (Var x ty) tm ∧
                  REV_ASSOCD (Var x (TYPE_SUBST tyin ty))
                    env (Var x ty) ≠ Var x ty)
        ∨ (∀ (x : mlstring) (ty : type), VFREE_IN (Var x ty) tm
                  → REV_ASSOCD (Var x (TYPE_SUBST tyin ty))
                      env (Var x ty) = Var x ty) ∧
          (∃ (tm' : term), INST_CORE env tyin tm = Result tm' ∧
                 has_type tm' (TYPE_SUBST tyin (typeof tm)) ∧
                 (∀ (u : mlstring) (uty : type), VFREE_IN (Var u uty) tm' ↔
                          ∃ (oty : type), VFREE_IN (Var u oty) tm ∧
                                uty = TYPE_SUBST tyin oty))

/-- the base statement, restated as a `def` (no proof, no `sorry`). -/
def Candle_Sbase : Prop :=
    ∀ (n : Nat) (tm : term) (env : List (term × term)) (tyin : List (type × type)),
        welltyped tm ∧ sizeof tm = n ∧
        (∀ (s s' : term), (s, s') ∈ env →
                ∃ (x : mlstring) (ty : type), s = Var x ty ∧
                       s' = Var x (TYPE_SUBST tyin ty))
        → (∃ (x : mlstring) (ty : type), INST_CORE env tyin tm = Clash (Var x (TYPE_SUBST tyin ty)) ∧
                  VFREE_IN (Var x ty) tm ∧
                  REV_ASSOCD (Var x (TYPE_SUBST tyin ty))
                    env (Var x ty) ≠ Var x ty)
        ∨ (∀ (x : mlstring) (ty : type), VFREE_IN (Var x ty) tm
                  → REV_ASSOCD (Var x (TYPE_SUBST tyin ty))
                      env (Var x ty) = Var x ty) ∧
          (∃ (tm' : term), INST_CORE env tyin tm = Result tm' ∧
                 has_type tm' (TYPE_SUBST tyin (typeof tm)) ∧
                 (∀ (u : mlstring) (uty : type), VFREE_IN (Var u uty) tm' ↔
                          ∃ (oty : type), VFREE_IN (Var u oty) tm ∧
                                uty = TYPE_SUBST tyin oty))

/-- The two statements are logically equivalent: `n` occurs only in `sizeof tm = n`. -/
theorem equiv : Mut.Smut ↔ Candle_Sbase := by
  constructor
  · intro h n tm env tyin hyp
    obtain ⟨h1, h2, h3⟩ := hyp
    subst h2
    exact h (sizeof tm) tm env tyin ⟨h1, rfl, h3⟩
  · intro h n tm env tyin hyp
    obtain ⟨h1, h2, h3⟩ := hyp
    subst h2
    exact h _ tm env tyin ⟨h1, rfl, h3⟩

theorem witness : Mut.Smut ↔ Candle_Sbase := equiv

end Mut

#print axioms Mut.witness
