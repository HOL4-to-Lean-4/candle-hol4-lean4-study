import CandleLean
open Candle HOL Classical
noncomputable section
namespace Mut
@[reducible] def ctxt_tysof (ctxt : List update) : tysig := alist_to_fmap (List.reverse (type_list ctxt))
end Mut

-- two declarations of the same type name with different arities: the base keeps the first, the mutant the last.
theorem witness : ∃ ctxt, Mut.ctxt_tysof ctxt ≠ Candle.ctxt_tysof ctxt := by
  refine ⟨[NewType (mls "n") 1, NewType (mls "n") 2], ?_⟩
  intro h
  have := congrArg (fun f : tysig => f.rep (mls "n")) h
  simp [Mut.ctxt_tysof, Candle.ctxt_tysof, type_list, types_of_upd, alist_to_fmap, FUPDATE, FEMPTY] at this

#print axioms witness
