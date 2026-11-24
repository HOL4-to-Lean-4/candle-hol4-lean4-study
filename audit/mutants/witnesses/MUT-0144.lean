import CandleLean
open Candle HOL Classical

noncomputable section
namespace Mut
def term_ok (sig : sig) : term → Prop
  | Var _ ty => type_ok (tysof sig) ty
  | Const name ty =>
    ∀ ty0, FLOOKUP (tmsof sig) name = some ty0 ∧ type_ok (tysof sig) ty ∧ is_instance ty0 ty
  | Comb tm1 tm2 => term_ok sig tm1 ∧ term_ok sig tm2 ∧ welltyped (Comb tm1 tm2)
  | Abs v tm => ∃ x ty, v = Var x ty ∧ type_ok (tysof sig) ty ∧ term_ok sig tm
end Mut
end

theorem lookup_single (n : mlstring) (t : type) :
    FLOOKUP (FUPDATE (FEMPTY : fmap mlstring type) (n, t)) n = some t := by
  have hd : n ∈ FDOM (FUPDATE (FEMPTY : fmap mlstring type) (n, t)) := by
    show (FUPDATE (FEMPTY : fmap mlstring type) (n, t)).rep n ≠ none
    simp [FUPDATE, FEMPTY]
  rw [FLOOKUP, if_pos hd]
  simp [FAPPLY, FUPDATE, FEMPTY]

/-- sig with one constant `n : Tyvar a`; the term `Const n (Tyvar a)` is ok in the base, but the mutant's universal
    quantifier over `ty0` would force two different types to be looked up for `n`. -/
theorem witness : ∃ (s : sig) (tm : term), ¬ (Mut.term_ok s tm ↔ term_ok s tm) := by
  let a : mlstring := mls "a"
  let b : mlstring := mls "b"
  let n : mlstring := mls "n"
  refine ⟨(FEMPTY, FUPDATE FEMPTY (n, Tyvar a)), Const n (Tyvar a), ?_⟩
  intro h
  have hb : term_ok (FEMPTY, FUPDATE FEMPTY (n, Tyvar a)) (Const n (Tyvar a)) := by
    refine ⟨Tyvar a, ?_, by simp [type_ok, tysof], ⟨[], by simp [TYPE_SUBST, REV_ASSOCD]⟩⟩
    exact lookup_single n (Tyvar a)
  have hm := h.2 hb
  have h1 := (hm (Tyvar a)).1
  have h2 := (hm (Tyvar b)).1
  simp only [tmsof] at h1 h2
  rw [lookup_single] at h1 h2
  have : Tyvar a = Tyvar b := Option.some.inj (h1.symm.trans h2)
  have : a = b := type.Tyvar.inj this
  have hab : a ≠ b := by simp only [a, b, mls, ne_eq, mlstring.implode.injEq]; decide
  exact hab this

#print axioms witness
