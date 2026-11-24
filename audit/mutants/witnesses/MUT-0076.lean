import CandleLean
open HOL Candle Classical
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
noncomputable section

namespace Mut
/-- mutated statement of `VFREE_IN_FINITE` (arguments of `VFREE_IN` swapped) -/
def VFREE_IN_FINITE_stmt : Prop := ∀ (t : term), FINITE (setOf (fun x => VFREE_IN t x))
end Mut

def sz : term → Nat
  | Var _ _ => 0
  | Const _ _ => 0
  | Comb s t => sz s + sz t + 1
  | Abs _ t => sz t + 1

def xk (t : term) : Nat → term
  | 0 => t
  | k + 1 => Comb (xk t k) t

theorem sz_xk (a : mlstring) (ty : type) (k : Nat) : sz (xk (Var a ty) k) = k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [xk, sz, ih]

theorem free_xk (a : mlstring) (ty : type) (k : Nat) : VFREE_IN (Var a ty) (xk (Var a ty) k) := by
  induction k with
  | zero => rfl
  | succ k ih => exact Or.inl ih

/-- the set of terms in which a fixed variable occurs free is infinite (it contains `Comb (… (Comb v v) …) v`). -/
theorem witness : ¬ Mut.VFREE_IN_FINITE_stmt := by
  intro h
  have hf := h (Var (mls "a") (Tyvar (mls "a")))
  obtain ⟨n, hn⟩ := hf (fun s => ∃ n, ∀ x, x ∈ s → sz x ≤ n)
    ⟨⟨0, fun x hx => (by exact hx : False).elim⟩, by
      rintro s ⟨n, hn⟩ e
      refine ⟨max n (sz e), fun x hx => ?_⟩
      rcases (by exact hx : x = e ∨ x ∈ s) with rfl | hx
      · exact Nat.le_max_right _ _
      · exact Nat.le_trans (hn x hx) (Nat.le_max_left _ _)⟩
  have := hn (xk (Var (mls "a") (Tyvar (mls "a"))) (n + 1)) (free_xk _ _ _)
  rw [sz_xk] at this
  omega

#print axioms witness
