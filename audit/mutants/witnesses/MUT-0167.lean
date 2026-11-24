import CandleLean

universe u v

open HOL Candle Classical

noncomputable section

namespace Mut

-- U1 witness. HOL4 clause (the only saved one): list$HD, ⊢ ∀ h t. HD (h::t) = h  (HD [] is left open).
-- Mapped constants: HD and ARB. The mutant proves HD [] = ARB; the base HD_pkg is opaque, so the base
-- cannot prove it from HD_def alone.
private def HD_pkg {α : Type u} [Nonempty α] : {f : List α → α // ∀ h t, f (h :: t) = h} :=
  ⟨fun l => match l with | h :: _ => h | [] => ARB, fun _ _ => rfl⟩

def HD {α : Type u} [Nonempty α] : List α → α := HD_pkg.1

theorem witness {α : Type u} [Nonempty α] : Mut.HD ([] : List α) = (ARB : α) := rfl

end Mut

#print axioms Mut.witness
