import CandleLean
open HOL Candle Classical
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
noncomputable section

namespace Mut
/-- mutated statement of `INST_CORE_simple_inst` (fourth hypothesis dropped) -/
def INST_CORE_simple_inst_stmt : Prop :=
    ∀ (env : List (term × term)) (tyin : List (type × type)) (tm : term),
        ALL_DISTINCT (bv_names tm ++ env.map (Prod.fst ∘ dest_var ∘ Prod.snd)) ∧
        DISJOINT (LIST_TO_SET (bv_names tm)) (setOf (fun (x : mlstring) => ∃ (ty : type), VFREE_IN (Var x ty) tm)) ∧
        (∀ (s s' : term), (s, s') ∈ env → ∃ (x : mlstring) (ty : type), s = Var x ty ∧ s' = Var x (TYPE_SUBST tyin ty)) ∧
        welltyped tm
        → INST_CORE env tyin tm = Result (simple_inst tyin tm)
end Mut

/-- tm = x:a, tyin = [a ↦ b], env = [(x:b, x:b)]: the variable clashes with the environment. -/
theorem witness : ¬ Mut.INST_CORE_simple_inst_stmt := by
  intro h
  let a := Tyvar (mls "a")
  let b := Tyvar (mls "b")
  let x := mls "x"
  have hba : mls "b" ≠ mls "a" := by decide
  have key := h [(Var x b, Var x b)] [(b, a)] (Var x a) ⟨?_, ?_, ?_, ⟨_, has_type.Var⟩⟩
  · simp [INST_CORE, TYPE_SUBST, REV_ASSOCD, simple_inst, IS_CLASH, RESULT, a, b] at key
    exact hba key
  · simp [bv_names, ALL_DISTINCT, dest_var]
  · simp only [bv_names, LIST_TO_SET, DISJOINT, INTER, EMPTY]
    funext y
    apply propext
    exact ⟨fun h => h.1, fun h => (by exact h : False).elim⟩
  · intro s s' hs
    simp only [List.mem_singleton, Prod.mk.injEq] at hs
    obtain ⟨rfl, rfl⟩ := hs
    exact ⟨x, b, rfl, by simp [TYPE_SUBST, REV_ASSOCD, a, b]⟩

#print axioms witness
