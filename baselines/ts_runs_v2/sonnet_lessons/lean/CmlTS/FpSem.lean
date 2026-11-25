import CmlTS.Ast
import CmlTS.Prelude.Float

/-!
# fpSem (HOL4 theory `fpSem`): floating point operations used in CakeML

The HOL4 datatype `fp_cmp` and the function `fp_cmp` have the same name; the datatype is
`fp_cmp_ty` in Lean.
-/

universe u v w

noncomputable section

open Classical

/- HOL4:
   Datatype:
     fp_cmp = FP_Less | FP_LessEqual | FP_Greater | FP_GreaterEqual | FP_Equal
   End -/
inductive fp_cmp_ty : Type where
  | FP_Less : fp_cmp_ty
  | FP_LessEqual : fp_cmp_ty
  | FP_Greater : fp_cmp_ty
  | FP_GreaterEqual : fp_cmp_ty
  | FP_Equal : fp_cmp_ty

/- HOL4:
   Datatype:
     fp_uop = FP_Abs | FP_Neg | FP_Sqrt
   End -/
inductive fp_uop : Type where
  | FP_Abs : fp_uop
  | FP_Neg : fp_uop
  | FP_Sqrt : fp_uop

/- HOL4:
   Datatype:
     fp_bop = FP_Add | FP_Sub | FP_Mul | FP_Div
   End -/
inductive fp_bop : Type where
  | FP_Add : fp_bop
  | FP_Sub : fp_bop
  | FP_Mul : fp_bop
  | FP_Div : fp_bop

/- HOL4:
   Datatype:
     fp_top = FP_Fma
   End -/
inductive fp_top : Type where
  | FP_Fma : fp_top

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

end
