import CmlTS.Prelude.BinaryIeee
import CmlTS.Ast
/-
  Translation of HOL4 theory `fpSem` (fpSemScript.sml).
-/
set_option autoImplicit false

namespace CmlTS

/- HOL4:
Datatype:
  fp_cmp = FP_Less | FP_LessEqual | FP_Greater | FP_GreaterEqual | FP_Equal
End
   (Lean name `fp_cmp_t`: `fp_cmp` is also the constant defined below) -/
inductive fp_cmp_t
  | FP_Less | FP_LessEqual | FP_Greater | FP_GreaterEqual | FP_Equal
  deriving DecidableEq, Inhabited

/- HOL4:
Datatype:
  fp_uop = FP_Abs | FP_Neg | FP_Sqrt
End -/
inductive fp_uop
  | FP_Abs | FP_Neg | FP_Sqrt
  deriving DecidableEq, Inhabited

/- HOL4:
Datatype:
  fp_bop = FP_Add | FP_Sub | FP_Mul | FP_Div
End -/
inductive fp_bop
  | FP_Add | FP_Sub | FP_Mul | FP_Div
  deriving DecidableEq, Inhabited

/- HOL4:
Datatype:
  fp_top = FP_Fma
End -/
inductive fp_top
  | FP_Fma
  deriving DecidableEq, Inhabited

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
  | .Lt => fp64_lessThan
  | .Leq => fp64_lessEqual
  | .Gt => fp64_greaterThan
  | .Geq => fp64_greaterEqual

end CmlTS
