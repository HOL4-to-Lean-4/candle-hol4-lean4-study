import CandleLean

universe u v

open HOL Candle Classical

noncomputable section

namespace Mut

def theory_ok (thy : thy) : Prop :=
  (∀ ty, ty ∈ FRANGE (thy_tmsof thy) → type_ok (thy_tysof thy) ty) ∧
  (∀ p, p ∈ axsof thy → has_type p BoolTy) ∧
  is_std_sig (sigof thy)

theorem FLOOKUP_FUPDATE_aux {α : Type u} {β : Type v} [Nonempty β] (f : fmap α β) (p : α × β) (x : α) :
    FLOOKUP (FUPDATE f p) x = if x = p.1 then some p.2 else FLOOKUP f x := by
  by_cases h : x = p.1
  · simp [FLOOKUP, FDOM, FAPPLY, FUPDATE, h, Aux.mem_def]
  · simp [FLOOKUP, FDOM, FAPPLY, FUPDATE, h, Aux.mem_def]

theorem FLOOKUP_FEMPTY_aux {α : Type u} {β : Type v} [Nonempty β] (x : α) :
    FLOOKUP (FEMPTY : fmap α β) x = none := by
  simp [FLOOKUP, FDOM, FEMPTY, Aux.mem_def]

def eqty : type := Fun (Tyvar (mls "A")) (Fun (Tyvar (mls "A")) BoolTy)

def mysig : sig :=
  (FUPDATE (FUPDATE FEMPTY (mls "fun", 2)) (mls "bool", 0), FUPDATE FEMPTY (mls "=", eqty))

/-- one axiom: a constant `foo : bool` that is not in the signature -/
def mythy : thy := (mysig, fun p => p = Const (mls "foo") BoolTy)

theorem lk_fun : FLOOKUP (tysof mysig) (mls "fun") = some 2 := by
  have : mls "fun" ≠ mls "bool" := by decide
  simp [mysig, tysof, FLOOKUP_FUPDATE_aux, this]

theorem lk_bool : FLOOKUP (tysof mysig) (mls "bool") = some 0 := by
  simp [mysig, tysof, FLOOKUP_FUPDATE_aux]

theorem lk_eq : FLOOKUP (tmsof mysig) (mls "=") = some eqty := by
  simp [mysig, tmsof, FLOOKUP_FUPDATE_aux]

theorem lk_foo : FLOOKUP (tmsof mysig) (mls "foo") = none := by
  have : mls "foo" ≠ mls "=" := by decide
  simp [mysig, tmsof, FLOOKUP_FUPDATE_aux, this, FLOOKUP_FEMPTY_aux]

theorem eqty_ok : Candle.type_ok (tysof mysig) eqty := by
  have h1 : mls "fun" ≠ mls "bool" := by decide
  simp [eqty, Fun, BoolTy, Candle.type_ok, EVERY, lk_fun, lk_bool]

theorem witness : Mut.theory_ok mythy ∧ ¬ Candle.theory_ok mythy := by
  constructor
  · refine ⟨?_, ?_, ?_⟩
    · intro ty hty
      obtain ⟨x, hx, hxy⟩ := hty
      have hx' : x = mls "=" := by
        by_contra hne
        apply hx
        simp [thy_tmsof, sigof, mythy, mysig, tmsof, FUPDATE, FEMPTY, hne]
      subst hx'
      have : ty = eqty := by
        rw [← hxy]
        simp [thy_tmsof, sigof, mythy, mysig, tmsof, FAPPLY, FUPDATE, FEMPTY]
      subst this
      exact eqty_ok
    · intro p hp
      have : p = Const (mls "foo") BoolTy := hp
      subst this
      exact has_type.Const
    · exact ⟨lk_fun, lk_bool, lk_eq⟩
  · intro ⟨_, h2, _⟩
    obtain ⟨hok, _⟩ := h2 (Const (mls "foo") BoolTy) rfl
    obtain ⟨ty0, hl, _⟩ := hok
    simp [sigof, mythy] at hl
    rw [lk_foo] at hl
    cases hl

end Mut

#print axioms Mut.witness
