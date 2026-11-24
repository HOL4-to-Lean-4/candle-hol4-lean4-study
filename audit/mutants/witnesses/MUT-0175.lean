import CandleLean
open HOL Candle Classical
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
noncomputable section

namespace Mut
private def dest_var_pkg : {f : term → mlstring × type // ∀ x ty, f (Var x ty) = (x, ty)} :=
  ⟨fun t => match t with | Var x ty => (x, ty) | _ => default, fun _ _ => rfl⟩

/-- `Candle.dest_var` rebuilt on the mutated package (the only dependant used by the witness) -/
def dest_var : term → mlstring × type := dest_var_pkg.1
end Mut

/-- U1 witness. With `dest_var_pkg` a `def`, the mutant proves the equation
`dest_var (Const a ty) = dest_var (Abs u w)` between mapped constants; both sides compute to the same default pair.
The saved HOL4 clause that leaves it open is `dest_var_def : dest_var (Var x ty) = (x,ty)` (holSyntax), which says nothing about
non-variables, so the base (where `dest_var_pkg` is `opaque`) has no proof of it. -/
theorem witness (a : mlstring) (ty : type) (u w : term) :
    Mut.dest_var (Const a ty) = Mut.dest_var (Abs u w) := rfl

/-- the same fact in terms of the image of `ARB`-like default: the mutant fixes `dest_var` of a constant to `default` -/
theorem witness_default (a : mlstring) (ty : type) :
    Mut.dest_var (Const a ty) = default := rfl

#print axioms witness
