import CandleLean

open Candle HOL Classical

namespace Mut
noncomputable section

def is_std_sig (sig : sig) : Prop :=
  FLOOKUP (tysof sig) (mls "fun") = some 1 ∧
  FLOOKUP (tysof sig) (mls "bool") = some 0 ∧
  FLOOKUP (tmsof sig) (mls "=") = some (Fun (Tyvar (mls "A")) (Fun (Tyvar (mls "A")) BoolTy))

end
end Mut

theorem rep_alist {α : Type} {β : Type} (l : List (α × β)) :
    (alist_to_fmap l).rep = fun a => ALOOKUP l a := by
  induction l with
  | nil => rfl
  | cons p t ih =>
    obtain ⟨k, v⟩ := p
    funext a
    show (if a = k then some v else (alist_to_fmap t).rep a) = ALOOKUP ((k, v) :: t) a
    rw [ih]
    simp [ALOOKUP, eq_comm]

theorem flookup_alist {α : Type} {β : Type} [Nonempty β] (l : List (α × β)) (x : α) :
    FLOOKUP (alist_to_fmap l) x = ALOOKUP l x := by
  unfold FLOOKUP FAPPLY
  rw [rep_alist]
  cases h : ALOOKUP l x <;> simp [FDOM, Aux.mem_def, rep_alist, h]
  

-- a signature with fun/1, bool/0 and the standard "=": mutant accepts it, base does not.
theorem witness : ∃ sg : sig, Mut.is_std_sig sg ∧ ¬ Candle.is_std_sig sg := by
  let eqty : type := Fun (Tyvar (mls "A")) (Fun (Tyvar (mls "A")) BoolTy)
  refine ⟨(alist_to_fmap [(mls "fun", (1 : Nat)), (mls "bool", 0)],
           alist_to_fmap [(mls "=", eqty)]), ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · show FLOOKUP (alist_to_fmap [(mls "fun", (1 : Nat)), (mls "bool", 0)]) (mls "fun") = some 1
      rw [flookup_alist]; simp [ALOOKUP]
    · show FLOOKUP (alist_to_fmap [(mls "fun", (1 : Nat)), (mls "bool", 0)]) (mls "bool") = some 0
      rw [flookup_alist]; simp [ALOOKUP]; decide
    · show FLOOKUP (alist_to_fmap [(mls "=", eqty)]) (mls "=") = some eqty
      rw [flookup_alist]; simp [ALOOKUP]
  · rintro ⟨h, _⟩
    have h' : FLOOKUP (alist_to_fmap [(mls "fun", (1 : Nat)), (mls "bool", 0)]) (mls "fun") = some 2 := h
    rw [flookup_alist] at h'
    simp [ALOOKUP] at h'

#print axioms witness
