import CmlTS.Prelude.BinaryIeee
import CmlTS.Ast

/-
HOL4 theory `fpSem` (fpSemScript.sml).
The HOL4 type `fp_cmp` is `fp_cmp_t` here (`fp_cmp` is also a constant).
-/

namespace CmlTS

noncomputable section

open scoped Classical

/- HOL4:
Datatype:
  fp_cmp = FP_Less | FP_LessEqual | FP_Greater | FP_GreaterEqual | FP_Equal
End -/
inductive fp_cmp_t
  | FP_Less
  | FP_LessEqual
  | FP_Greater
  | FP_GreaterEqual
  | FP_Equal

/- HOL4:
Datatype:
  fp_uop = FP_Abs | FP_Neg | FP_Sqrt
End -/
inductive fp_uop
  | FP_Abs
  | FP_Neg
  | FP_Sqrt

/- HOL4:
Datatype:
  fp_bop = FP_Add | FP_Sub | FP_Mul | FP_Div
End -/
inductive fp_bop
  | FP_Add
  | FP_Sub
  | FP_Mul
  | FP_Div

/- HOL4:
Datatype:
  fp_top = FP_Fma
End -/
inductive fp_top
  | FP_Fma

/- HOL4:
Definition fp_cmp_def:
  fp_cmp cmp =
  case cmp of
  | Lt  => fp64_lessThan
  | Leq => fp64_lessEqual
  | Gt  => fp64_greaterThan
  | Geq => fp64_greaterEqual
End -/
def fp_cmp (cmp : opb) : word64 → word64 → Prop :=
  match cmp with
  | opb.Lt => fp64_lessThan
  | opb.Leq => fp64_lessEqual
  | opb.Gt => fp64_greaterThan
  | opb.Geq => fp64_greaterEqual

end

end CmlTS
