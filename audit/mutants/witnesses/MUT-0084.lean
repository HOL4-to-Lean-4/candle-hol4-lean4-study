import CandleLean
open Candle HOL Classical

namespace Mut
universe u v
def ALOOKUP_MAP_dest_var_stmt : Prop :=
  ∀ {α : Type u} {β : Type v},
    ∀ (ls : List (term × α)) (f : α → β) (x : mlstring) (ty : type),
      EVERY (fun s => ∃ x ty, s = Var x ty) (ls.map Prod.fst) →
      ALOOKUP (List.reverse (ls.map (PAIR_MAP dest_var f))) (x, ty) =
      Option.map f (ALOOKUP ls (Var x ty))
end Mut

/-- ls = [(Var x bool, 1), (Var x bool, 2)], f = id: the base answer is `some 1` (first entry); the reversed list gives `some 2`. -/
theorem witness : ¬ Mut.ALOOKUP_MAP_dest_var_stmt.{0, 0} := by
  intro h
  have := h (α := Nat) (β := Nat) [(Var (mls "x") BoolTy, 1), (Var (mls "x") BoolTy, 2)] id (mls "x") BoolTy
    (by simp [EVERY])
  simp [ALOOKUP, PAIR_MAP, dest_var_def] at this

#print axioms witness
