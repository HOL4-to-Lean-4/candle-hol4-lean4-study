import CandleLean
open Candle HOL Classical

noncomputable section
namespace Mut
def INST_CORE (env : List (term × term)) (tyin : List (type × type)) : term → result term
  | Var x ty =>
    let tm := Var x ty
    let tm' := Var x (TYPE_SUBST tyin ty)
    if REV_ASSOCD tm' env tm ≠ tm then Result tm' else Clash tm'
  | Const x ty => Result (Const x (TYPE_SUBST tyin ty))
  | Comb s t =>
    let sres := INST_CORE env tyin s
    if IS_CLASH sres then sres else
    let tres := INST_CORE env tyin t
    if IS_CLASH tres then tres else
    let s' := RESULT sres
    let t' := RESULT tres
    Result (Comb s' t')
  | Abs v t =>
    let x := (dest_var v).1
    let ty := (dest_var v).2
    let ty' := TYPE_SUBST tyin ty
    let v' := Var x ty'
    let env' := (v, v') :: env
    let tres := INST_CORE env' tyin t
    if IS_RESULT tres then Result (Abs v' (RESULT tres)) else
    let w := CLASH tres
    if w ≠ v' then tres else
    let x' := VARIANT (RESULT (INST_CORE [] tyin t)) (explode x) ty'
    let t' := VSUBST [(Var x' ty, Var x ty)] t
    let ty' := TYPE_SUBST tyin ty
    let env' := (Var x' ty, Var x' ty') :: env
    let tres := INST_CORE env' tyin t'
    if IS_RESULT tres then Result (Abs (Var x' ty') (RESULT tres)) else tres
termination_by tm => sizeof tm
decreasing_by
  all_goals simp only [sizeof]
  all_goals try omega
  rw [Aux.sizeof_VSUBST_aux t _ (fun s' s hm => by
    rcases List.mem_singleton.mp hm with hm
    cases hm; exact ⟨_, _, rfl⟩)]
  omega
end Mut
end

/-- `INST_CORE [] [] (Var x ty)`: base `Result (Var x ty)`, mutant `Clash (Var x ty)` -/
theorem witness : ∃ (env : List (term × term)) (tyin : List (type × type)) (tm : term),
    Mut.INST_CORE env tyin tm ≠ INST_CORE env tyin tm := by
  refine ⟨[], [], Var (mls "x") BoolTy, ?_⟩
  intro h
  rw [Mut.INST_CORE, INST_CORE] at h
  simp [REV_ASSOCD, TYPE_SUBST] at h

#print axioms witness
