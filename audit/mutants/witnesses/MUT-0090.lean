import CandleLean
open Candle HOL Classical

noncomputable section
namespace Mut
universe u
def is_interpretation0 {U : Type u} (mem : U → U → Prop) (sig : sig) (int : interpretation U) : Prop :=
  is_type_assignment0 mem (tysof sig) (tyaof int) ∧
  is_term_assignment0 mem (tmsof sig) (tmaof int) (tyaof int)
end Mut
end

/-- U = Nat, mem y z := y = 7 ∧ z = 5, no types, one constant `c : bool`, type assignment δ = 5, term assignment γ = 7.
    Base: `mem (γ c []) (δ bool [])` = `mem 7 5` holds. Mutant swaps δ and γ: it needs `mem 5 7`, false. -/
theorem witness : ∃ (mem : Nat → Nat → Prop) (s : sig) (i : interpretation Nat),
    is_interpretation0 mem s i ∧ ¬ Mut.is_interpretation0 mem s i := by
  let mem : Nat → Nat → Prop := fun y z => y = 7 ∧ z = 5
  let tms : tmsig := FUPDATE FEMPTY (mls "c", BoolTy)
  let s : sig := (FEMPTY, tms)
  let i : interpretation Nat := (fun _ _ => 5, fun _ _ => 7)
  have hty : is_type_assignment0 mem (tysof s) (tyaof i) := by
    intro x hx
    exact absurd rfl (hx : (FEMPTY : fmap mlstring Nat).rep x ≠ none)
  have hdom : ∀ x, x ∈ FDOM tms → x = mls "c" := by
    intro x hx
    have hx' : tms.rep x ≠ none := hx
    by_contra hne
    apply hx'
    simp [tms, FUPDATE, FEMPTY, hne]
  have hfa : FAPPLY (tmsof s) (mls "c") = BoolTy := by
    show FAPPLY tms (mls "c") = BoolTy
    simp [FAPPLY, tms, FUPDATE]
  refine ⟨mem, s, i, ⟨hty, ?_⟩, ?_⟩
  · intro x hx
    have hxc := hdom x hx
    subst hxc
    intro τ _
    rw [hfa]
    simp [typesem, BoolTy, mem, i, tmaof, tyaof]
  · intro h
    have h2 := h.2
    have hc : mls "c" ∈ FDOM (tmsof s) := by
      show tms.rep (mls "c") ≠ none
      simp [tms, FUPDATE]
    have := h2 (mls "c") hc (fun _ => 5) (fun _ => ⟨7, by simp [mem]⟩)
    rw [hfa] at this
    simp [typesem, BoolTy, mem, i, tmaof, tyaof] at this

#print axioms witness
