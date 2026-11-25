import CmlTS.Prelude.Num

/-!
# HOL4 library prelude: IEEE-754 binary floating point (`binary_ieee`, `machine_ieee`)

Only what is needed for the 64-bit operations used by CakeML is translated (`fp64_*`), but the
underlying `binary_ieee` definitions are generic in the widths `t` (significand) and `w`
(exponent); `fp64` is `float 52 11`.

**Modelling choice for `real`.**  Lean core has no real numbers.  All reals occurring in these
definitions are values of finite floats (dyadic rationals, `Rat`) and sums, differences, products
and quotients of them, plus square roots of those (`sqrt`) for `float_sqrt`.  They are represented
by `RealX` (a rational, or the square root of a non-negative rational) and the only operations
needed on them (comparisons with rationals, and `|a - x| <= |b - x|` for rational `a`, `b`) are
defined exactly; for the second one we use the algebraic identity
`(a - x)^2 <= (b - x)^2  <=>  (a - b) * (a + b - 2x) <= 0`.
-/

universe u

noncomputable section

open Classical

/-- Exact real numbers needed by IEEE rounding: a rational, or `sqrt q` for a rational `q ≥ 0`. -/
inductive RealX : Type where
  | ofRat (q : Rat) : RealX
  | sqrt (q : Rat) : RealX

namespace RealX

/-- `x < p` -/
def lt_rat : RealX → Rat → Prop
  | .ofRat q, p => q < p
  | .sqrt q, p => 0 < p ∧ q < p * p
/-- `x ≤ p` -/
def le_rat : RealX → Rat → Prop
  | .ofRat q, p => q ≤ p
  | .sqrt q, p => 0 ≤ p ∧ q ≤ p * p
/-- `p < x` -/
def gt_rat : RealX → Rat → Prop
  | .ofRat q, p => p < q
  | .sqrt q, p => p < 0 ∨ p * p < q
/-- `p ≤ x` -/
def ge_rat : RealX → Rat → Prop
  | .ofRat q, p => p ≤ q
  | .sqrt q, p => p ≤ 0 ∨ p * p ≤ q
/-- `x = p` -/
def eq_rat : RealX → Rat → Prop
  | .ofRat q, p => q = p
  | .sqrt q, p => 0 ≤ p ∧ p * p = q

/-- absolute value -/
def abs : RealX → RealX
  | .ofRat q => .ofRat (if q < 0 then -q else q)
  | .sqrt q => .sqrt q

/-- `|a - x| <= |b - x|` for rational `a`, `b`. -/
def distLe (x : RealX) (a b : Rat) : Prop :=
  if a = b then True
  else if a < b then x.le_rat ((a + b) / 2)
  else x.ge_rat ((a + b) / 2)

end RealX

/-- absolute value of a rational -/
def ratAbs (q : Rat) : Rat := if q < 0 then -q else q

/-! ## Binary floating point representation -/

/- HOL4: binary_ieee theory,
   Datatype:
      float = <| Sign : word1; Exponent : 'w word; Significand : 't word |> -/
structure float (t w : Nat) where
  Sign : BitVec 1
  Exponent : BitVec w
  Significand : BitVec t
  deriving DecidableEq

instance (t w : Nat) : Inhabited (float t w) := ⟨⟨0, 0, 0⟩⟩

/- HOL4: binary_ieee theory, `Datatype: float_value = Float real | Infinity | NaN`
   (Lean name `float_value_ty`; `Float` carries a rational since finite floats are rational) -/
inductive float_value_ty : Type where
  | Float (r : Rat) : float_value_ty
  | Infinity : float_value_ty
  | NaN : float_value_ty

/-- `precision (:'t) = dimindex (:'t)` is `t`; `bias (:'w) = words$INT_MAX (:'w) = 2^(w-1) - 1` -/
def float_bias (w : Nat) : Nat := 2 ^ (w - 1) - 1

/- HOL4: words theory, `UINT_MAXw` : the all-ones word -/
def UINT_MAXw (w : Nat) : BitVec w := BitVec.ofNat w (2 ^ w - 1)

/- HOL4: binary_ieee theory,
   Definition float_to_real_def[nocompute]:
      float_to_real (x: ('t, 'w) float) =
         if x.Exponent = 0w
            then -1r pow (w2n x.Sign) *
                 (2r / 2r pow (bias (:'w))) *
                 (&(w2n x.Significand) / 2r pow (precision (:'t)))
         else -1r pow (w2n x.Sign) *
              (2r pow (w2n x.Exponent) / 2r pow (bias (:'w))) *
              (1r + &(w2n x.Significand) / 2r pow (precision (:'t)))
   End -/
def float_to_real {t w : Nat} (x : float t w) : Rat :=
  if x.Exponent = 0 then
    (-1 : Rat) ^ x.Sign.toNat * (2 / 2 ^ float_bias w) *
      ((x.Significand.toNat : Rat) / 2 ^ t)
  else
    (-1 : Rat) ^ x.Sign.toNat * (2 ^ x.Exponent.toNat / 2 ^ float_bias w) *
      (1 + (x.Significand.toNat : Rat) / 2 ^ t)

/- HOL4: binary_ieee theory,
   Definition float_value_def[nocompute]:
      float_value (x: ('t, 'w) float) =
         if x.Exponent = UINT_MAXw
            then if x.Significand = 0w then Infinity else NaN
         else Float (float_to_real x)
   End -/
def float_value {t w : Nat} (x : float t w) : float_value_ty :=
  if x.Exponent = UINT_MAXw w then
    (if x.Significand = 0 then .Infinity else .NaN)
  else .Float (float_to_real x)

/- HOL4: binary_ieee theory, `float_is_nan`, `float_is_signalling`, `float_is_infinite`,
   `float_is_normal`, `float_is_subnormal`, `float_is_zero`, `float_is_finite` -/
def float_is_nan {t w : Nat} (x : float t w) : Prop :=
  match float_value x with
  | .NaN => True
  | _ => False

def float_is_signalling {t w : Nat} (x : float t w) : Prop :=
  float_is_nan x ∧ ¬ (x.Significand.msb = true)

def float_is_infinite {t w : Nat} (x : float t w) : Prop :=
  match float_value x with
  | .Infinity => True
  | _ => False

def float_is_normal {t w : Nat} (x : float t w) : Prop :=
  x.Exponent ≠ 0 ∧ x.Exponent ≠ UINT_MAXw w

def float_is_subnormal {t w : Nat} (x : float t w) : Prop :=
  x.Exponent = 0 ∧ x.Significand ≠ 0

def float_is_zero {t w : Nat} (x : float t w) : Prop :=
  match float_value x with
  | .Float r => r = 0
  | _ => False

def float_is_finite {t w : Nat} (x : float t w) : Prop :=
  match float_value x with
  | .Float _ => True
  | _ => False

/- HOL4: binary_ieee theory, `float_negate x = x with Sign := ~x.Sign`,
   `float_abs x = x with Sign := 0w` -/
def float_negate {t w : Nat} (x : float t w) : float t w := { x with Sign := ~~~ x.Sign }
def float_abs {t w : Nat} (x : float t w) : float t w := { x with Sign := 0 }

/- HOL4: binary_ieee theory, constants
   `float_plus_infinity`, `float_plus_zero`, `float_top`, `float_plus_min`,
   `float_minus_infinity`, `float_minus_zero`, `float_bottom`, `float_minus_min`
   (all take the itself-argument `(:'t # 'w)`, here the explicit widths). -/
def float_plus_infinity (t w : Nat) : float t w := ⟨0, UINT_MAXw w, 0⟩
def float_plus_zero (t w : Nat) : float t w := ⟨0, 0, 0⟩
def float_top (t w : Nat) : float t w := ⟨0, UINT_MAXw w - 1, UINT_MAXw t⟩
def float_plus_min (t w : Nat) : float t w := ⟨0, 0, 1⟩
def float_minus_infinity (t w : Nat) : float t w := float_negate (float_plus_infinity t w)
def float_minus_zero (t w : Nat) : float t w := float_negate (float_plus_zero t w)
def float_bottom (t w : Nat) : float t w := float_negate (float_top t w)
def float_minus_min (t w : Nat) : float t w := float_negate (float_plus_min t w)

/-! ## Rounding reals to floating-point values -/

/- HOL4: binary_ieee theory,
   Datatype:
      flags = <| DivideByZero : bool; InvalidOp : bool; Overflow : bool; Precision : bool;
                 Underflow_BeforeRounding : bool; Underflow_AfterRounding : bool |>
   End -/
structure flags where
  DivideByZero : Prop
  InvalidOp : Prop
  Overflow : Prop
  Precision : Prop
  Underflow_BeforeRounding : Prop
  Underflow_AfterRounding : Prop

/- HOL4: binary_ieee theory, `clear_flags`, `invalidop_flags = clear_flags with InvalidOp := T`,
   `dividezero_flags = clear_flags with DivideByZero := T` -/
def clear_flags : flags := ⟨False, False, False, False, False, False⟩
def invalidop_flags : flags := { clear_flags with InvalidOp := True }
def dividezero_flags : flags := { clear_flags with DivideByZero := True }

/- HOL4: binary_ieee theory,
   Datatype:
      rounding = roundTiesToEven | roundTowardPositive | roundTowardNegative | roundTowardZero
   End -/
inductive rounding : Type where
  | roundTiesToEven : rounding
  | roundTowardPositive : rounding
  | roundTowardNegative : rounding
  | roundTowardZero : rounding
  deriving DecidableEq

/- HOL4: binary_ieee theory,
   Definition is_closest_def:
      is_closest s x a <=>
         a IN s /\
         !b. b IN s ==> abs (float_to_real a - x) <= abs (float_to_real b - x)
   End -/
def is_closest {t w : Nat} (s : Set (float t w)) (x : RealX) (a : float t w) : Prop :=
  s a ∧ ∀ b, s b → x.distLe (float_to_real a) (float_to_real b)

/- HOL4: binary_ieee theory,
   Definition closest_such_def[nocompute]:
      closest_such p s x =
         @a. is_closest s x a /\ (!b. is_closest s x b /\ p b ==> p a)
   End -/
def closest_such {t w : Nat} (p : float t w → Prop) (s : Set (float t w)) (x : RealX) :
    float t w :=
  Classical.epsilon fun a => is_closest s x a ∧ (∀ b, is_closest s x b ∧ p b → p a)

/- HOL4: binary_ieee theory, `closest = closest_such (K T)` -/
def closest {t w : Nat} (s : Set (float t w)) (x : RealX) : float t w :=
  closest_such (fun _ => True) s x

/- HOL4: binary_ieee theory,
   Definition largest_def[nocompute]:
      largest (:'t # 'w) =
         (2r pow (UINT_MAX (:'w) - 1) / 2r pow (INT_MAX (:'w))) *
         (2r - inv (2r pow dimindex(:'t)))
   End -/
def largest (t w : Nat) : Rat :=
  (2 ^ (2 ^ w - 1 - 1) / 2 ^ float_bias w) * (2 - 1 / 2 ^ t)

/- HOL4: binary_ieee theory,
   Definition threshold_def[nocompute]:
      threshold (:'t # 'w) =
         (2r pow (UINT_MAX (:'w) - 1) / 2r pow (INT_MAX (:'w))) *
         (2r - inv (2r pow SUC (dimindex(:'t))))
   End -/
def threshold (t w : Nat) : Rat :=
  (2 ^ (2 ^ w - 1 - 1) / 2 ^ float_bias w) * (2 - 1 / 2 ^ (t + 1))

/- HOL4: binary_ieee theory,
   Definition round_def[nocompute]:
      round mode (x: real) =
      case mode of
         roundTiesToEven =>
           let t = threshold (:'t # 'w) in
             if x <= -t
                then float_minus_infinity (:'t # 'w)
             else if x >= t
                then float_plus_infinity (:'t # 'w)
             else closest_such (\a. ~word_lsb a.Significand) float_is_finite x
       | roundTowardZero =>
           let t = largest (:'t # 'w) in
             if x < -t
                then float_bottom (:'t # 'w)
             else if x > t
                then float_top (:'t # 'w)
             else closest
                    {a | float_is_finite a /\ abs (float_to_real a) <= abs x} x
       | roundTowardPositive =>
           let t = largest (:'t # 'w) in
             if x < -t
                then float_bottom (:'t # 'w)
             else if x > t
                then float_plus_infinity (:'t # 'w)
             else closest {a | float_is_finite a /\ float_to_real a >= x} x
       | roundTowardNegative =>
           let t = largest (:'t # 'w) in
             if x < -t
                then float_minus_infinity (:'t # 'w)
             else if x > t
                then float_top (:'t # 'w)
             else closest {a | float_is_finite a /\ float_to_real a <= x} x
   End -/
def round (t w : Nat) (mode : rounding) (x : RealX) : float t w :=
  match mode with
  | .roundTiesToEven =>
    let th := threshold t w
    if x.le_rat (-th) then float_minus_infinity t w
    else if x.ge_rat th then float_plus_infinity t w
    else closest_such (fun a => ¬ (a.Significand.getLsbD 0 = true)) float_is_finite x
  | .roundTowardZero =>
    let th := largest t w
    if x.lt_rat (-th) then float_bottom t w
    else if x.gt_rat th then float_top t w
    else closest (fun a => float_is_finite a ∧ x.abs.ge_rat (ratAbs (float_to_real a))) x
  | .roundTowardPositive =>
    let th := largest t w
    if x.lt_rat (-th) then float_bottom t w
    else if x.gt_rat th then float_plus_infinity t w
    else closest (fun a => float_is_finite a ∧ x.le_rat (float_to_real a)) x
  | .roundTowardNegative =>
    let th := largest t w
    if x.lt_rat (-th) then float_minus_infinity t w
    else if x.gt_rat th then float_top t w
    else closest (fun a => float_is_finite a ∧ x.ge_rat (float_to_real a)) x

/-! ## NaNs -/

/- HOL4: binary_ieee theory,
   Datatype:
      fp_op =
        FP_Sqrt rounding (('t, 'w) float)
      | FP_Add rounding (('t, 'w) float) (('t, 'w) float)
      | FP_Sub rounding (('t, 'w) float) (('t, 'w) float)
      | FP_Mul rounding (('t, 'w) float) (('t, 'w) float)
      | FP_Div rounding (('t, 'w) float) (('t, 'w) float)
      | FP_MulAdd rounding (('t, 'w) float) (('t, 'w) float) (('t, 'w) float)
      | FP_MulSub rounding (('t, 'w) float) (('t, 'w) float) (('t, 'w) float)
   End -/
inductive fp_op (t w : Nat) : Type where
  | FP_Sqrt (m : rounding) (x : float t w) : fp_op t w
  | FP_Add (m : rounding) (x y : float t w) : fp_op t w
  | FP_Sub (m : rounding) (x y : float t w) : fp_op t w
  | FP_Mul (m : rounding) (x y : float t w) : fp_op t w
  | FP_Div (m : rounding) (x y : float t w) : fp_op t w
  | FP_MulAdd (m : rounding) (x y z : float t w) : fp_op t w
  | FP_MulSub (m : rounding) (x y z : float t w) : fp_op t w

/- HOL4: binary_ieee theory,
   Definition float_some_qnan_def[nocompute]:
      float_some_qnan (fp_op : ('t, 'w) fp_op) =
      (@f. let qnan = f fp_op in float_is_nan qnan /\ ~float_is_signalling qnan)
        fp_op : ('t, 'w) float
   End -/
def float_some_qnan {t w : Nat} (o : fp_op t w) : float t w :=
  (Classical.epsilon fun f : fp_op t w → float t w =>
    float_is_nan (f o) ∧ ¬ float_is_signalling (f o)) o

/-! ## Some arithmetic operations -/

/- HOL4: binary_ieee theory,
   Definition float_round_def[nocompute]:
      float_round mode toneg r =
         let x = round mode r in
            if float_is_zero x
               then if toneg
                       then float_minus_zero (:'t # 'w)
                    else float_plus_zero (:'t # 'w)
            else x
   End -/
def float_round (t w : Nat) (mode : rounding) (toneg : Prop) (r : RealX) : float t w :=
  let x := round t w mode r
  if float_is_zero x then (if toneg then float_minus_zero t w else float_plus_zero t w)
  else x

/- HOL4: binary_ieee theory,
   Definition float_round_with_flags_def[nocompute]:
     float_round_with_flags mode to_neg r =
     let x = float_round mode to_neg r : ('t, 'w) float and a = abs r in
     let inexact = (float_value x <> Float r) in
       ((clear_flags with
           <| Overflow := (float_is_infinite x \/ 2 pow (INT_MIN (:'w)) <= a)
            ; Underflow_BeforeRounding := (inexact /\ a < 2 / 2 pow (bias(:'w)))
            ; Underflow_AfterRounding :=
                (inexact /\
                 ((float_round mode to_neg r : ('t, 'w + 1) float).Exponent <=+
                  n2w (INT_MIN (:'w))))
            ; Precision := inexact
            |>), x)
   End -/
def float_round_with_flags (t w : Nat) (mode : rounding) (to_neg : Prop) (r : RealX) :
    flags × float t w :=
  let x := float_round t w mode to_neg r
  let a := r.abs
  let inexact : Prop :=
    match float_value x with
    | .Float r' => ¬ r.eq_rat r'
    | _ => True
  ({ clear_flags with
      Overflow := float_is_infinite x ∨ a.ge_rat (2 ^ (2 ^ (w - 1))),
      Underflow_BeforeRounding := inexact ∧ a.lt_rat (2 / 2 ^ float_bias w),
      Underflow_AfterRounding :=
        inexact ∧
          (float_round t (w + 1) mode to_neg r).Exponent.toNat ≤ 2 ^ (w - 1),
      Precision := inexact }, x)

/- HOL4: binary_ieee theory,
   Definition check_for_signalling_def[nocompute]:
     check_for_signalling l =
     clear_flags with InvalidOp := EXISTS float_is_signalling l
   End -/
def check_for_signalling {t w : Nat} (l : List (float t w)) : flags :=
  { clear_flags with InvalidOp := EXISTS float_is_signalling l }

/- HOL4: binary_ieee theory,
   Definition float_sqrt_def:
      float_sqrt mode (x: ('t, 'w) float) =
         if x.Sign = 0w then
            case float_value x of
               NaN => (check_for_signalling [x], float_some_qnan (FP_Sqrt mode x))
             | Infinity => (clear_flags, float_plus_infinity (:'t # 'w))
             | Float r => (float_round_with_flags mode F (sqrt r))
         else if x = float_minus_zero (:'t # 'w) then
           (clear_flags, float_minus_zero (:'t # 'w))
         else
           (invalidop_flags, float_some_qnan (FP_Sqrt mode x))
   End -/
def float_sqrt {t w : Nat} (mode : rounding) (x : float t w) : flags × float t w :=
  if x.Sign = 0 then
    match float_value x with
    | .NaN => (check_for_signalling [x], float_some_qnan (.FP_Sqrt mode x))
    | .Infinity => (clear_flags, float_plus_infinity t w)
    | .Float r => float_round_with_flags t w mode False (.sqrt r)
  else if x = float_minus_zero t w then (clear_flags, float_minus_zero t w)
  else (invalidop_flags, float_some_qnan (.FP_Sqrt mode x))

/- HOL4: binary_ieee theory,
   Definition float_add_def[nocompute]:
      float_add mode (x: ('t, 'w) float) (y: ('t, 'w) float) =
         case float_value x, float_value y of
            NaN, _ => (check_for_signalling [x; y],
                       float_some_qnan (FP_Add mode x y))
          | _, NaN => (check_for_signalling [y],
                       float_some_qnan (FP_Add mode x y))
          | Infinity, Infinity =>
               if x.Sign = y.Sign then
                  (clear_flags, x)
               else
                  (invalidop_flags, float_some_qnan (FP_Add mode x y))
          | Infinity, _ => (clear_flags, x)
          | _, Infinity => (clear_flags, y)
          | Float r1, Float r2 =>
               float_round_with_flags mode
                  (if (r1 = 0) /\ (r2 = 0) /\ (x.Sign = y.Sign) then
                     x.Sign = 1w
                   else mode = roundTowardNegative) (r1 + r2)
   End -/
def float_add {t w : Nat} (mode : rounding) (x y : float t w) : flags × float t w :=
  match float_value x, float_value y with
  | .NaN, _ => (check_for_signalling [x, y], float_some_qnan (.FP_Add mode x y))
  | _, .NaN => (check_for_signalling [y], float_some_qnan (.FP_Add mode x y))
  | .Infinity, .Infinity =>
    if x.Sign = y.Sign then (clear_flags, x)
    else (invalidop_flags, float_some_qnan (.FP_Add mode x y))
  | .Infinity, _ => (clear_flags, x)
  | _, .Infinity => (clear_flags, y)
  | .Float r1, .Float r2 =>
    float_round_with_flags t w mode
      (if (r1 = 0) ∧ (r2 = 0) ∧ (x.Sign = y.Sign) then x.Sign = 1
       else mode = .roundTowardNegative) (.ofRat (r1 + r2))

/- HOL4: binary_ieee theory,
   Definition float_sub_def[nocompute]:
      float_sub mode (x: ('t, 'w) float) (y: ('t, 'w) float) =
         case float_value x, float_value y of
            NaN, _ => (check_for_signalling [x; y],
                       float_some_qnan (FP_Sub mode x y))
          | _, NaN => (check_for_signalling [y],
                       float_some_qnan (FP_Sub mode x y))
          | Infinity, Infinity =>
               if x.Sign = y.Sign then
                  (invalidop_flags, float_some_qnan (FP_Sub mode x y))
               else
                  (clear_flags, x)
          | Infinity, _ => (clear_flags, x)
          | _, Infinity => (clear_flags, float_negate y)
          | Float r1, Float r2 =>
               float_round_with_flags mode
                  (if (r1 = 0) /\ (r2 = 0) /\ x.Sign <> y.Sign then
                     x.Sign = 1w
                   else mode = roundTowardNegative) (r1 - r2)
   End -/
def float_sub {t w : Nat} (mode : rounding) (x y : float t w) : flags × float t w :=
  match float_value x, float_value y with
  | .NaN, _ => (check_for_signalling [x, y], float_some_qnan (.FP_Sub mode x y))
  | _, .NaN => (check_for_signalling [y], float_some_qnan (.FP_Sub mode x y))
  | .Infinity, .Infinity =>
    if x.Sign = y.Sign then (invalidop_flags, float_some_qnan (.FP_Sub mode x y))
    else (clear_flags, x)
  | .Infinity, _ => (clear_flags, x)
  | _, .Infinity => (clear_flags, float_negate y)
  | .Float r1, .Float r2 =>
    float_round_with_flags t w mode
      (if (r1 = 0) ∧ (r2 = 0) ∧ x.Sign ≠ y.Sign then x.Sign = 1
       else mode = .roundTowardNegative) (.ofRat (r1 - r2))

/- HOL4: binary_ieee theory,
   Definition float_mul_def[nocompute]:
      float_mul mode (x: ('t, 'w) float) (y: ('t, 'w) float) =
         case float_value x, float_value y of
            NaN, _ => (check_for_signalling [x; y],
                       float_some_qnan (FP_Mul mode x y))
          | _, NaN => (check_for_signalling [y],
                       float_some_qnan (FP_Mul mode x y))
          | Infinity, Float r =>
               if r = 0 then
                  (invalidop_flags, float_some_qnan (FP_Mul mode x y))
               else
                  (clear_flags,
                   if x.Sign = y.Sign then
                      float_plus_infinity (:'t # 'w)
                   else float_minus_infinity (:'t # 'w))
          | Float r, Infinity =>
               if r = 0 then
                  (invalidop_flags, float_some_qnan (FP_Mul mode x y))
               else
                  (clear_flags,
                   if x.Sign = y.Sign then
                      float_plus_infinity (:'t # 'w)
                   else float_minus_infinity (:'t # 'w))
          | Infinity, Infinity =>
               (clear_flags,
                if x.Sign = y.Sign then
                   float_plus_infinity (:'t # 'w)
                else float_minus_infinity (:'t # 'w))
          | Float r1, Float r2 =>
               float_round_with_flags mode (x.Sign <> y.Sign) (r1 * r2)
   End -/
def float_mul {t w : Nat} (mode : rounding) (x y : float t w) : flags × float t w :=
  match float_value x, float_value y with
  | .NaN, _ => (check_for_signalling [x, y], float_some_qnan (.FP_Mul mode x y))
  | _, .NaN => (check_for_signalling [y], float_some_qnan (.FP_Mul mode x y))
  | .Infinity, .Float r =>
    if r = 0 then (invalidop_flags, float_some_qnan (.FP_Mul mode x y))
    else (clear_flags,
      if x.Sign = y.Sign then float_plus_infinity t w else float_minus_infinity t w)
  | .Float r, .Infinity =>
    if r = 0 then (invalidop_flags, float_some_qnan (.FP_Mul mode x y))
    else (clear_flags,
      if x.Sign = y.Sign then float_plus_infinity t w else float_minus_infinity t w)
  | .Infinity, .Infinity =>
    (clear_flags, if x.Sign = y.Sign then float_plus_infinity t w else float_minus_infinity t w)
  | .Float r1, .Float r2 =>
    float_round_with_flags t w mode (x.Sign ≠ y.Sign) (.ofRat (r1 * r2))

/- HOL4: binary_ieee theory,
   Definition float_div_def[nocompute]:
      float_div mode (x: ('t, 'w) float) (y: ('t, 'w) float) =
         case float_value x, float_value y of
            NaN, _ => (check_for_signalling [x; y],
                       float_some_qnan (FP_Div mode x y))
          | _, NaN => (check_for_signalling [y],
                       float_some_qnan (FP_Div mode x y))
          | Infinity, Infinity =>
               (invalidop_flags, float_some_qnan (FP_Div mode x y))
          | Infinity, _ =>
               (clear_flags,
                if x.Sign = y.Sign then
                   float_plus_infinity (:'t # 'w)
                else float_minus_infinity (:'t # 'w))
          | _, Infinity =>
               (clear_flags,
                if x.Sign = y.Sign then
                   float_plus_zero (:'t # 'w)
                else float_minus_zero (:'t # 'w))
          | Float r1, Float r2 =>
               if r2 = 0
                  then if r1 = 0 then
                          (invalidop_flags, float_some_qnan (FP_Div mode x y))
                       else
                          (dividezero_flags,
                           if x.Sign = y.Sign then
                              float_plus_infinity (:'t # 'w)
                           else float_minus_infinity (:'t # 'w))
               else float_round_with_flags mode (x.Sign <> y.Sign) (r1 / r2)
   End -/
def float_div {t w : Nat} (mode : rounding) (x y : float t w) : flags × float t w :=
  match float_value x, float_value y with
  | .NaN, _ => (check_for_signalling [x, y], float_some_qnan (.FP_Div mode x y))
  | _, .NaN => (check_for_signalling [y], float_some_qnan (.FP_Div mode x y))
  | .Infinity, .Infinity => (invalidop_flags, float_some_qnan (.FP_Div mode x y))
  | .Infinity, _ =>
    (clear_flags, if x.Sign = y.Sign then float_plus_infinity t w else float_minus_infinity t w)
  | _, .Infinity =>
    (clear_flags, if x.Sign = y.Sign then float_plus_zero t w else float_minus_zero t w)
  | .Float r1, .Float r2 =>
    if r2 = 0 then
      (if r1 = 0 then (invalidop_flags, float_some_qnan (.FP_Div mode x y))
       else (dividezero_flags,
         if x.Sign = y.Sign then float_plus_infinity t w else float_minus_infinity t w))
    else float_round_with_flags t w mode (x.Sign ≠ y.Sign) (.ofRat (r1 / r2))

/- HOL4: binary_ieee theory,
   Definition float_mul_add_def[nocompute]:
      float_mul_add mode
         (x: ('t, 'w) float) (y: ('t, 'w) float) (z: ('t, 'w) float) =
         let signP = x.Sign ?? y.Sign in
         let infP = (float_is_infinite x \/ float_is_infinite y)
         in
            if float_is_nan x \/ float_is_nan y \/ float_is_nan z then
               (check_for_signalling [x; y; z],
                float_some_qnan (FP_MulAdd mode x y z))
            else if float_is_infinite x /\ float_is_zero y \/
                    float_is_zero x /\ float_is_infinite y \/
                    float_is_infinite z /\ infP /\ signP <> z.Sign then
               (invalidop_flags, float_some_qnan (FP_MulAdd mode x y z))
            else if float_is_infinite z /\ (z.Sign = 0w) \/ infP /\ (signP = 0w)
               then (clear_flags, float_plus_infinity (:'t # 'w))
            else if float_is_infinite z /\ (z.Sign = 1w) \/ infP /\ (signP = 1w)
               then (clear_flags, float_minus_infinity (:'t # 'w))
            else
              let r1 = float_to_real x * float_to_real y ;
                  r2 = float_to_real z ;
                  r = r1 + r2 ;
              in
                float_round_with_flags
                  mode
                  ((r = 0) /\
                   (if (r1 = 0) /\ (r2 = 0) /\ (signP = z.Sign) then
                      signP = 1w
                    else mode = roundTowardNegative) \/
                   r < 0)
                  r
   End -/
def float_mul_add {t w : Nat} (mode : rounding) (x y z : float t w) : flags × float t w :=
  let signP := x.Sign ^^^ y.Sign
  let infP := float_is_infinite x ∨ float_is_infinite y
  if float_is_nan x ∨ float_is_nan y ∨ float_is_nan z then
    (check_for_signalling [x, y, z], float_some_qnan (.FP_MulAdd mode x y z))
  else if float_is_infinite x ∧ float_is_zero y ∨ float_is_zero x ∧ float_is_infinite y ∨
      float_is_infinite z ∧ infP ∧ signP ≠ z.Sign then
    (invalidop_flags, float_some_qnan (.FP_MulAdd mode x y z))
  else if float_is_infinite z ∧ (z.Sign = 0) ∨ infP ∧ (signP = 0) then
    (clear_flags, float_plus_infinity t w)
  else if float_is_infinite z ∧ (z.Sign = 1) ∨ infP ∧ (signP = 1) then
    (clear_flags, float_minus_infinity t w)
  else
    let r1 := float_to_real x * float_to_real y
    let r2 := float_to_real z
    let r := r1 + r2
    float_round_with_flags t w mode
      ((r = 0) ∧
        (if (r1 = 0) ∧ (r2 = 0) ∧ (signP = z.Sign) then signP = 1
         else mode = .roundTowardNegative) ∨
       r < 0)
      (.ofRat r)

/-! ## Some comparison operations -/

/- HOL4: binary_ieee theory, `Datatype:  float_compare = LT | EQ | GT | UN`
   (Lean name `float_compare_ty`) -/
inductive float_compare_ty : Type where
  | LT : float_compare_ty
  | EQ : float_compare_ty
  | GT : float_compare_ty
  | UN : float_compare_ty
  deriving DecidableEq

/- HOL4: binary_ieee theory,
   Definition float_compare_def[nocompute]:
      float_compare (x: ('t, 'w) float) (y: ('t, 'w) float) =
         case float_value x, float_value y of
            NaN, _ => UN
          | _, NaN => UN
          | Infinity, Infinity =>
               if x.Sign = y.Sign
                  then EQ
               else if x.Sign = 1w
                  then LT
               else GT
          | Infinity, _ => if x.Sign = 1w then LT else GT
          | _, Infinity => if y.Sign = 1w then GT else LT
          | Float r1, Float r2 =>
               if r1 < r2
                  then LT
               else if r1 = r2
                  then EQ
               else GT
   End -/
def float_compare {t w : Nat} (x y : float t w) : float_compare_ty :=
  match float_value x, float_value y with
  | .NaN, _ => .UN
  | _, .NaN => .UN
  | .Infinity, .Infinity => if x.Sign = y.Sign then .EQ else if x.Sign = 1 then .LT else .GT
  | .Infinity, _ => if x.Sign = 1 then .LT else .GT
  | _, .Infinity => if y.Sign = 1 then .GT else .LT
  | .Float r1, .Float r2 => if r1 < r2 then .LT else if r1 = r2 then .EQ else .GT

/- HOL4: binary_ieee theory, `float_less_than x y = (float_compare x y = LT)` -/
def float_less_than {t w : Nat} (x y : float t w) : Prop := float_compare x y = .LT

/- HOL4: binary_ieee theory,
   `float_less_equal x y = case float_compare x y of LT => T | EQ => T | _ => F` -/
def float_less_equal {t w : Nat} (x y : float t w) : Prop :=
  match float_compare x y with
  | .LT => True
  | .EQ => True
  | _ => False

/- HOL4: binary_ieee theory, `float_greater_than x y = (float_compare x y = GT)` -/
def float_greater_than {t w : Nat} (x y : float t w) : Prop := float_compare x y = .GT

/- HOL4: binary_ieee theory,
   `float_greater_equal x y = case float_compare x y of GT => T | EQ => T | _ => F` -/
def float_greater_equal {t w : Nat} (x y : float t w) : Prop :=
  match float_compare x y with
  | .GT => True
  | .EQ => True
  | _ => False

/- HOL4: binary_ieee theory, `float_equal x y = (float_compare x y = EQ)` -/
def float_equal {t w : Nat} (x y : float t w) : Prop := float_compare x y = .EQ

/-! ## machine_ieee: the 64-bit encoding `fp64` (52-bit significand, 11-bit exponent) -/

/- HOL4: machine_ieee theory (generated by `machine_ieeeLib.mk_fp_encoding ("fp64", 52, 11, ...)`):
   `fp64_to_float w = <| Sign := word_extract 63 63 w; Exponent := word_extract 62 52 w;
                         Significand := word_extract 51 0 w |>` -/
def fp64_to_float (w : word64) : float 52 11 :=
  ⟨w.extractLsb' 63 1, w.extractLsb' 52 11, w.extractLsb' 0 52⟩

/- HOL4: machine_ieee theory,
   `float_to_fp64 x = x.Sign @@ x.Exponent @@ x.Significand` -/
def float_to_fp64 (x : float 52 11) : word64 :=
  BitVec.cast (by decide) (x.Sign ++ (x.Exponent ++ x.Significand))

/- HOL4: machine_ieee theory, `fp64_abs = float_to_fp64 o float_abs o fp64_to_float`,
   `fp64_negate = float_to_fp64 o float_negate o fp64_to_float` -/
def fp64_abs (w : word64) : word64 := float_to_fp64 (float_abs (fp64_to_float w))
def fp64_negate (w : word64) : word64 := float_to_fp64 (float_negate (fp64_to_float w))

/- HOL4: machine_ieee theory, `fp64_sqrt mode = float_to_fp64 o SND o float_sqrt mode o fp64_to_float` -/
def fp64_sqrt (m : rounding) (w : word64) : word64 :=
  float_to_fp64 (float_sqrt m (fp64_to_float w)).2

/- HOL4: machine_ieee theory, `fp64_add mode a b = float_to_fp64 (SND (float_add mode (fp64_to_float a) (fp64_to_float b)))`
   and likewise `fp64_sub`, `fp64_mul`, `fp64_div` -/
def fp64_add (m : rounding) (a b : word64) : word64 :=
  float_to_fp64 (float_add m (fp64_to_float a) (fp64_to_float b)).2
def fp64_sub (m : rounding) (a b : word64) : word64 :=
  float_to_fp64 (float_sub m (fp64_to_float a) (fp64_to_float b)).2
def fp64_mul (m : rounding) (a b : word64) : word64 :=
  float_to_fp64 (float_mul m (fp64_to_float a) (fp64_to_float b)).2
def fp64_div (m : rounding) (a b : word64) : word64 :=
  float_to_fp64 (float_div m (fp64_to_float a) (fp64_to_float b)).2

/- HOL4: machine_ieee theory,
   `fp64_mul_add mode a b c = float_to_fp64 (SND (float_mul_add mode (fp64_to_float a) (fp64_to_float b) (fp64_to_float c)))` -/
def fp64_mul_add (m : rounding) (a b c : word64) : word64 :=
  float_to_fp64 (float_mul_add m (fp64_to_float a) (fp64_to_float b) (fp64_to_float c)).2

/- HOL4: machine_ieee theory, `fp64_equal a b = float_equal (fp64_to_float a) (fp64_to_float b)`,
   `fp64_lessThan`, `fp64_lessEqual`, `fp64_greaterThan`, `fp64_greaterEqual` likewise -/
def fp64_equal (a b : word64) : Prop := float_equal (fp64_to_float a) (fp64_to_float b)
def fp64_lessThan (a b : word64) : Prop := float_less_than (fp64_to_float a) (fp64_to_float b)
def fp64_lessEqual (a b : word64) : Prop := float_less_equal (fp64_to_float a) (fp64_to_float b)
def fp64_greaterThan (a b : word64) : Prop :=
  float_greater_than (fp64_to_float a) (fp64_to_float b)
def fp64_greaterEqual (a b : word64) : Prop :=
  float_greater_equal (fp64_to_float a) (fp64_to_float b)

end
