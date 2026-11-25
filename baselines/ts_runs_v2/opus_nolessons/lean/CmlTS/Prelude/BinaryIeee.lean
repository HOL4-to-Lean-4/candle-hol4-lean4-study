import CmlTS.Prelude.Real
import CmlTS.Prelude.List
/-
  HOL4 library constants: `binary_ieee`, `machine_ieee` (the part CakeML's `fp64_*` functions use).

  The HOL4 type `('t,'w) float` becomes `float t w`, where the natural numbers `t` and `w` stand for
  `dimindex(:'t)` and `dimindex(:'w)`.  Arguments `(:'t # 'w)` of HOL4 constants become the explicit
  arguments `t w`.  Everything lives in the namespace `CmlTS.ieee` (constructor names such as `FP_Add`
  also occur in `fpSem`), except `rounding` and the `fp64_*` functions.
-/
set_option autoImplicit false

namespace CmlTS

/- HOL4: binary_ieee
   Datatype: rounding = roundTiesToEven | roundTowardPositive | roundTowardNegative
                      | roundTowardZero End -/
inductive rounding
  | roundTiesToEven | roundTowardPositive | roundTowardNegative | roundTowardZero
  deriving DecidableEq, Inhabited

export rounding (roundTiesToEven roundTowardPositive roundTowardNegative roundTowardZero)

namespace ieee
open Classical

/- HOL4: Datatype: float = <| Sign : word1; Exponent : 'w word; Significand : 't word |> End -/
structure float (t w : Nat) where
  Sign : BitVec 1
  Exponent : BitVec w
  Significand : BitVec t
  deriving DecidableEq

instance (t w : Nat) : Inhabited (float t w) := ⟨⟨0, 0, 0⟩⟩

/- HOL4: Datatype: float_value = Float real | Infinity | NaN End -/
inductive float_value
  | Float (r : real) | Infinity | NaN

/- HOL4: words$INT_MIN:   INT_MIN (:'a) = 2 ** (dimindex(:'a) - 1) -/
def INT_MIN (w : Nat) : Nat := 2 ^ (w - 1)
/- HOL4: words$INT_MAX:   INT_MAX (:'a) = INT_MIN(:'a) - 1 -/
def INT_MAX (w : Nat) : Nat := INT_MIN w - 1
/- HOL4: words$UINT_MAX:  UINT_MAX (:'a) = dimword(:'a) - 1 -/
def UINT_MAX (w : Nat) : Nat := 2 ^ w - 1
/- HOL4: UINT_MAXw = n2w (UINT_MAX (:'a)) -/
def UINT_MAXw {w : Nat} : BitVec w := BitVec.ofNat w (UINT_MAX w)

/- HOL4: 2r pow n -/
noncomputable abbrev two_pow (n : Nat) : real := (2 : real) ^ n

/- HOL4: float_to_real_def (precision = dimindex, bias = INT_MAX)
   float_to_real (x: ('t, 'w) float) =
      if x.Exponent = 0w
         then -1r pow (w2n x.Sign) * (2r / 2r pow (bias (:'w))) *
              (&(w2n x.Significand) / 2r pow (precision (:'t)))
      else -1r pow (w2n x.Sign) *
           (2r pow (w2n x.Exponent) / 2r pow (bias (:'w))) *
           (1r + &(w2n x.Significand) / 2r pow (precision (:'t))) -/
noncomputable def float_to_real {t w : Nat} (x : float t w) : real :=
  if x.Exponent = 0 then
    (-1 : real) ^ x.Sign.toNat * (2 / two_pow (INT_MAX w)) *
      (real.ofNat x.Significand.toNat / two_pow t)
  else
    (-1 : real) ^ x.Sign.toNat * (two_pow x.Exponent.toNat / two_pow (INT_MAX w)) *
      (1 + real.ofNat x.Significand.toNat / two_pow t)

/- HOL4: float_value_def
   float_value (x: ('t, 'w) float) =
      if x.Exponent = UINT_MAXw
         then if x.Significand = 0w then Infinity else NaN
      else Float (float_to_real x)
   (named `get_float_value`, because `float_value` is also the type) -/
noncomputable def get_float_value {t w : Nat} (x : float t w) : float_value :=
  if x.Exponent = UINT_MAXw then
    if x.Significand = 0 then .Infinity else .NaN
  else .Float (float_to_real x)

/- HOL4: float_is_nan_def
   float_is_nan x = case float_value x of NaN => T | _ => F -/
def float_is_nan {t w : Nat} (x : float t w) : Prop :=
  match get_float_value x with
  | .NaN => True
  | _ => False

/- HOL4: float_is_signalling_def
   float_is_signalling x <=> float_is_nan x /\ ~word_msb x.Significand -/
def float_is_signalling {t w : Nat} (x : float t w) : Prop :=
  float_is_nan x ∧ ¬ (x.Significand.msb = true)

/- HOL4: float_is_infinite_def
   float_is_infinite x = case float_value x of Infinity => T | _ => F -/
def float_is_infinite {t w : Nat} (x : float t w) : Prop :=
  match get_float_value x with
  | .Infinity => True
  | _ => False

/- HOL4: float_is_zero_def
   float_is_zero x = case float_value x of Float r => r = 0 | _ => F -/
def float_is_zero {t w : Nat} (x : float t w) : Prop :=
  match get_float_value x with
  | .Float r => r = 0
  | _ => False

/- HOL4: float_is_finite_def
   float_is_finite x = case float_value x of Float _ => T | _ => F -/
def float_is_finite {t w : Nat} (x : float t w) : Prop :=
  match get_float_value x with
  | .Float _ => True
  | _ => False

/- HOL4: float_negate_def:  float_negate x = x with Sign := ~x.Sign -/
def float_negate {t w : Nat} (x : float t w) : float t w := { x with Sign := ~~~x.Sign }

/- HOL4: float_abs_def:  float_abs x = x with Sign := 0w -/
def float_abs {t w : Nat} (x : float t w) : float t w := { x with Sign := 0 }

/- HOL4: float_plus_infinity_def
   float_plus_infinity (:'t # 'w) = <| Sign := 0w; Exponent := UINT_MAXw; Significand := 0w |> -/
def float_plus_infinity (t w : Nat) : float t w := ⟨0, UINT_MAXw, 0⟩

/- HOL4: float_plus_zero_def
   float_plus_zero (:'t # 'w) = <| Sign := 0w; Exponent := 0w; Significand := 0w |> -/
def float_plus_zero (t w : Nat) : float t w := ⟨0, 0, 0⟩

/- HOL4: float_top_def
   float_top (:'t # 'w) =
     <| Sign := 0w; Exponent := UINT_MAXw - 1w; Significand := UINT_MAXw |> -/
def float_top (t w : Nat) : float t w := ⟨0, UINT_MAXw - 1, UINT_MAXw⟩

/- HOL4: float_minus_infinity_def
   float_minus_infinity (:'t # 'w) = float_negate (float_plus_infinity (:'t # 'w)) -/
def float_minus_infinity (t w : Nat) : float t w := float_negate (float_plus_infinity t w)

/- HOL4: float_minus_zero_def
   float_minus_zero (:'t # 'w) = float_negate (float_plus_zero (:'t # 'w)) -/
def float_minus_zero (t w : Nat) : float t w := float_negate (float_plus_zero t w)

/- HOL4: float_bottom_def:  float_bottom (:'t # 'w) = float_negate (float_top (:'t # 'w)) -/
def float_bottom (t w : Nat) : float t w := float_negate (float_top t w)

/- HOL4: Datatype:
   flags = <| DivideByZero : bool ; InvalidOp : bool ; Overflow : bool ; Precision : bool
            ; Underflow_BeforeRounding : bool ; Underflow_AfterRounding : bool |> End -/
structure flags where
  DivideByZero : Bool
  InvalidOp : Bool
  Overflow : Bool
  Precision : Bool
  Underflow_BeforeRounding : Bool
  Underflow_AfterRounding : Bool
  deriving DecidableEq, Inhabited

/- HOL4: clear_flags_def
   clear_flags = <| DivideByZero := F ; InvalidOp := F ; Overflow := F ; Precision := F
                  ; Underflow_BeforeRounding := F ; Underflow_AfterRounding := F |> -/
def clear_flags : flags :=
  { DivideByZero := false, InvalidOp := false, Overflow := false, Precision := false,
    Underflow_BeforeRounding := false, Underflow_AfterRounding := false }

/- HOL4: invalidop_flags_def:  invalidop_flags = clear_flags with InvalidOp := T -/
def invalidop_flags : flags := { clear_flags with InvalidOp := true }

/- HOL4: dividezero_flags_def:  dividezero_flags = clear_flags with DivideByZero := T -/
def dividezero_flags : flags := { clear_flags with DivideByZero := true }

/- HOL4: is_closest_def
   is_closest s x a <=>
      a IN s /\ !b. b IN s ==> abs (float_to_real a - x) <= abs (float_to_real b - x) -/
def is_closest {t w : Nat} (s : Set (float t w)) (x : real) (a : float t w) : Prop :=
  a ∈ s ∧ ∀ b, b ∈ s → real.abs (float_to_real a - x) ≤ real.abs (float_to_real b - x)

/- HOL4: closest_such_def
   closest_such p s x = @a. is_closest s x a /\ (!b. is_closest s x b /\ p b ==> p a) -/
noncomputable def closest_such {t w : Nat} (p : float t w → Prop) (s : Set (float t w))
    (x : real) : float t w :=
  SELECT fun a => is_closest s x a ∧ (∀ b, is_closest s x b ∧ p b → p a)

/- HOL4: closest_def:  closest = closest_such (K T) -/
noncomputable def closest {t w : Nat} : Set (float t w) → real → float t w :=
  closest_such (K True)

/- HOL4: largest_def
   largest (:'t # 'w) =
      (2r pow (UINT_MAX (:'w) - 1) / 2r pow (INT_MAX (:'w))) * (2r - inv (2r pow dimindex(:'t))) -/
noncomputable def largest (t w : Nat) : real :=
  (two_pow (UINT_MAX w - 1) / two_pow (INT_MAX w)) * (2 - (two_pow t)⁻¹)

/- HOL4: threshold_def
   threshold (:'t # 'w) =
      (2r pow (UINT_MAX (:'w) - 1) / 2r pow (INT_MAX (:'w))) *
      (2r - inv (2r pow SUC (dimindex(:'t)))) -/
noncomputable def threshold (t w : Nat) : real :=
  (two_pow (UINT_MAX w - 1) / two_pow (INT_MAX w)) * (2 - (two_pow (t + 1))⁻¹)

/- HOL4: round_def
   round mode (x: real) =
   case mode of
      roundTiesToEven =>
        let t = threshold (:'t # 'w) in
          if x <= -t then float_minus_infinity (:'t # 'w)
          else if x >= t then float_plus_infinity (:'t # 'w)
          else closest_such (\a. ~word_lsb a.Significand) float_is_finite x
    | roundTowardZero =>
        let t = largest (:'t # 'w) in
          if x < -t then float_bottom (:'t # 'w)
          else if x > t then float_top (:'t # 'w)
          else closest {a | float_is_finite a /\ abs (float_to_real a) <= abs x} x
    | roundTowardPositive =>
        let t = largest (:'t # 'w) in
          if x < -t then float_bottom (:'t # 'w)
          else if x > t then float_plus_infinity (:'t # 'w)
          else closest {a | float_is_finite a /\ float_to_real a >= x} x
    | roundTowardNegative =>
        let t = largest (:'t # 'w) in
          if x < -t then float_minus_infinity (:'t # 'w)
          else if x > t then float_top (:'t # 'w)
          else closest {a | float_is_finite a /\ float_to_real a <= x} x -/
noncomputable def round (t w : Nat) (mode : rounding) (x : real) : float t w :=
  match mode with
  | .roundTiesToEven =>
    let th := threshold t w
    if x ≤ -th then float_minus_infinity t w
    else if x ≥ th then float_plus_infinity t w
    else closest_such (fun a => ¬ (a.Significand.getLsbD 0 = true)) float_is_finite x
  | .roundTowardZero =>
    let th := largest t w
    if x < -th then float_bottom t w
    else if x > th then float_top t w
    else closest {a | float_is_finite a ∧ real.abs (float_to_real a) ≤ real.abs x} x
  | .roundTowardPositive =>
    let th := largest t w
    if x < -th then float_bottom t w
    else if x > th then float_plus_infinity t w
    else closest {a | float_is_finite a ∧ float_to_real a ≥ x} x
  | .roundTowardNegative =>
    let th := largest t w
    if x < -th then float_minus_infinity t w
    else if x > th then float_top t w
    else closest {a | float_is_finite a ∧ float_to_real a ≤ x} x

/- HOL4: Datatype:
   fp_op =
     FP_Sqrt rounding (('t, 'w) float)
   | FP_Add rounding (('t, 'w) float) (('t, 'w) float)
   | FP_Sub rounding (('t, 'w) float) (('t, 'w) float)
   | FP_Mul rounding (('t, 'w) float) (('t, 'w) float)
   | FP_Div rounding (('t, 'w) float) (('t, 'w) float)
   | FP_MulAdd rounding (('t, 'w) float) (('t, 'w) float) (('t, 'w) float)
   | FP_MulSub rounding (('t, 'w) float) (('t, 'w) float) (('t, 'w) float)
   End -/
inductive fp_op (t w : Nat)
  | FP_Sqrt (m : rounding) (x : float t w)
  | FP_Add (m : rounding) (x y : float t w)
  | FP_Sub (m : rounding) (x y : float t w)
  | FP_Mul (m : rounding) (x y : float t w)
  | FP_Div (m : rounding) (x y : float t w)
  | FP_MulAdd (m : rounding) (x y z : float t w)
  | FP_MulSub (m : rounding) (x y z : float t w)

/- HOL4: float_some_qnan_def
   float_some_qnan (fp_op : ('t, 'w) fp_op) =
   (@f. let qnan = f fp_op in float_is_nan qnan /\ ~float_is_signalling qnan)
     fp_op : ('t, 'w) float -/
noncomputable def float_some_qnan {t w : Nat} (fp_op : fp_op t w) : float t w :=
  (SELECT fun f : ieee.fp_op t w → float t w =>
    let qnan := f fp_op
    float_is_nan qnan ∧ ¬ float_is_signalling qnan) fp_op

/- HOL4: float_round_def
   float_round mode toneg r =
      let x = round mode r in
         if float_is_zero x
            then if toneg then float_minus_zero (:'t # 'w) else float_plus_zero (:'t # 'w)
         else x -/
noncomputable def float_round (t w : Nat) (mode : rounding) (toneg : Prop) (r : real) :
    float t w :=
  let x := round t w mode r
  if float_is_zero x then
    if toneg then float_minus_zero t w else float_plus_zero t w
  else x

/- HOL4: float_round_with_flags_def
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
         |>), x) -/
noncomputable def float_round_with_flags {t w : Nat} (mode : rounding) (to_neg : Prop) (r : real) :
    flags × float t w :=
  let x := float_round t w mode to_neg r
  let a := real.abs r
  let inexact := get_float_value x ≠ .Float r
  ({ clear_flags with
      Overflow := decide (float_is_infinite x ∨ two_pow (INT_MIN w) ≤ a)
      Underflow_BeforeRounding := decide (inexact ∧ a < 2 / two_pow (INT_MAX w))
      Underflow_AfterRounding :=
        decide (inexact ∧
          (float_round t (w + 1) mode to_neg r).Exponent ≤ BitVec.ofNat (w + 1) (INT_MIN w))
      Precision := decide inexact }, x)

/- HOL4: check_for_signalling_def
   check_for_signalling l = clear_flags with InvalidOp := EXISTS float_is_signalling l -/
noncomputable def check_for_signalling {t w : Nat} (l : List (float t w)) : flags :=
  { clear_flags with InvalidOp := decide (EXISTS float_is_signalling l) }

/- HOL4: float_sqrt_def
   float_sqrt mode (x: ('t, 'w) float) =
      if x.Sign = 0w then
         case float_value x of
            NaN => (check_for_signalling [x], float_some_qnan (FP_Sqrt mode x))
          | Infinity => (clear_flags, float_plus_infinity (:'t # 'w))
          | Float r => (float_round_with_flags mode F (sqrt r))
      else if x = float_minus_zero (:'t # 'w) then
        (clear_flags, float_minus_zero (:'t # 'w))
      else
        (invalidop_flags, float_some_qnan (FP_Sqrt mode x)) -/
noncomputable def float_sqrt {t w : Nat} (mode : rounding) (x : float t w) : flags × float t w :=
  if x.Sign = 0 then
    match get_float_value x with
    | .NaN => (check_for_signalling [x], float_some_qnan (.FP_Sqrt mode x))
    | .Infinity => (clear_flags, float_plus_infinity t w)
    | .Float r => float_round_with_flags mode False (real.sqrt r)
  else if x = float_minus_zero t w then
    (clear_flags, float_minus_zero t w)
  else
    (invalidop_flags, float_some_qnan (.FP_Sqrt mode x))

/- HOL4: float_add_def
   float_add mode (x: ('t, 'w) float) (y: ('t, 'w) float) =
      case float_value x, float_value y of
         NaN, _ => (check_for_signalling [x; y], float_some_qnan (FP_Add mode x y))
       | _, NaN => (check_for_signalling [y], float_some_qnan (FP_Add mode x y))
       | Infinity, Infinity =>
            if x.Sign = y.Sign then (clear_flags, x)
            else (invalidop_flags, float_some_qnan (FP_Add mode x y))
       | Infinity, _ => (clear_flags, x)
       | _, Infinity => (clear_flags, y)
       | Float r1, Float r2 =>
            float_round_with_flags mode
               (if (r1 = 0) /\ (r2 = 0) /\ (x.Sign = y.Sign) then x.Sign = 1w
                else mode = roundTowardNegative) (r1 + r2) -/
noncomputable def float_add {t w : Nat} (mode : rounding) (x y : float t w) : flags × float t w :=
  match get_float_value x, get_float_value y with
  | .NaN, _ => (check_for_signalling [x, y], float_some_qnan (.FP_Add mode x y))
  | _, .NaN => (check_for_signalling [y], float_some_qnan (.FP_Add mode x y))
  | .Infinity, .Infinity =>
    if x.Sign = y.Sign then (clear_flags, x)
    else (invalidop_flags, float_some_qnan (.FP_Add mode x y))
  | .Infinity, _ => (clear_flags, x)
  | _, .Infinity => (clear_flags, y)
  | .Float r1, .Float r2 =>
    float_round_with_flags mode
      (if r1 = 0 ∧ r2 = 0 ∧ x.Sign = y.Sign then x.Sign = 1
       else mode = roundTowardNegative) (r1 + r2)

/- HOL4: float_sub_def
   float_sub mode (x: ('t, 'w) float) (y: ('t, 'w) float) =
      case float_value x, float_value y of
         NaN, _ => (check_for_signalling [x; y], float_some_qnan (FP_Sub mode x y))
       | _, NaN => (check_for_signalling [y], float_some_qnan (FP_Sub mode x y))
       | Infinity, Infinity =>
            if x.Sign = y.Sign then (invalidop_flags, float_some_qnan (FP_Sub mode x y))
            else (clear_flags, x)
       | Infinity, _ => (clear_flags, x)
       | _, Infinity => (clear_flags, float_negate y)
       | Float r1, Float r2 =>
            float_round_with_flags mode
               (if (r1 = 0) /\ (r2 = 0) /\ x.Sign <> y.Sign then x.Sign = 1w
                else mode = roundTowardNegative) (r1 - r2) -/
noncomputable def float_sub {t w : Nat} (mode : rounding) (x y : float t w) : flags × float t w :=
  match get_float_value x, get_float_value y with
  | .NaN, _ => (check_for_signalling [x, y], float_some_qnan (.FP_Sub mode x y))
  | _, .NaN => (check_for_signalling [y], float_some_qnan (.FP_Sub mode x y))
  | .Infinity, .Infinity =>
    if x.Sign = y.Sign then (invalidop_flags, float_some_qnan (.FP_Sub mode x y))
    else (clear_flags, x)
  | .Infinity, _ => (clear_flags, x)
  | _, .Infinity => (clear_flags, float_negate y)
  | .Float r1, .Float r2 =>
    float_round_with_flags mode
      (if r1 = 0 ∧ r2 = 0 ∧ x.Sign ≠ y.Sign then x.Sign = 1
       else mode = roundTowardNegative) (r1 - r2)

/- HOL4: float_mul_def
   float_mul mode (x: ('t, 'w) float) (y: ('t, 'w) float) =
      case float_value x, float_value y of
         NaN, _ => (check_for_signalling [x; y], float_some_qnan (FP_Mul mode x y))
       | _, NaN => (check_for_signalling [y], float_some_qnan (FP_Mul mode x y))
       | Infinity, Float r =>
            if r = 0 then (invalidop_flags, float_some_qnan (FP_Mul mode x y))
            else (clear_flags,
                  if x.Sign = y.Sign then float_plus_infinity (:'t # 'w)
                  else float_minus_infinity (:'t # 'w))
       | Float r, Infinity =>
            if r = 0 then (invalidop_flags, float_some_qnan (FP_Mul mode x y))
            else (clear_flags,
                  if x.Sign = y.Sign then float_plus_infinity (:'t # 'w)
                  else float_minus_infinity (:'t # 'w))
       | Infinity, Infinity =>
            (clear_flags,
             if x.Sign = y.Sign then float_plus_infinity (:'t # 'w)
             else float_minus_infinity (:'t # 'w))
       | Float r1, Float r2 =>
            float_round_with_flags mode (x.Sign <> y.Sign) (r1 * r2) -/
noncomputable def float_mul {t w : Nat} (mode : rounding) (x y : float t w) : flags × float t w :=
  match get_float_value x, get_float_value y with
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
    (clear_flags,
     if x.Sign = y.Sign then float_plus_infinity t w else float_minus_infinity t w)
  | .Float r1, .Float r2 =>
    float_round_with_flags mode (x.Sign ≠ y.Sign) (r1 * r2)

/- HOL4: float_div_def
   float_div mode (x: ('t, 'w) float) (y: ('t, 'w) float) =
      case float_value x, float_value y of
         NaN, _ => (check_for_signalling [x; y], float_some_qnan (FP_Div mode x y))
       | _, NaN => (check_for_signalling [y], float_some_qnan (FP_Div mode x y))
       | Infinity, Infinity => (invalidop_flags, float_some_qnan (FP_Div mode x y))
       | Infinity, _ =>
            (clear_flags,
             if x.Sign = y.Sign then float_plus_infinity (:'t # 'w)
             else float_minus_infinity (:'t # 'w))
       | _, Infinity =>
            (clear_flags,
             if x.Sign = y.Sign then float_plus_zero (:'t # 'w)
             else float_minus_zero (:'t # 'w))
       | Float r1, Float r2 =>
            if r2 = 0
               then if r1 = 0 then
                       (invalidop_flags, float_some_qnan (FP_Div mode x y))
                    else
                       (dividezero_flags,
                        if x.Sign = y.Sign then float_plus_infinity (:'t # 'w)
                        else float_minus_infinity (:'t # 'w))
            else float_round_with_flags mode (x.Sign <> y.Sign) (r1 / r2) -/
noncomputable def float_div {t w : Nat} (mode : rounding) (x y : float t w) : flags × float t w :=
  match get_float_value x, get_float_value y with
  | .NaN, _ => (check_for_signalling [x, y], float_some_qnan (.FP_Div mode x y))
  | _, .NaN => (check_for_signalling [y], float_some_qnan (.FP_Div mode x y))
  | .Infinity, .Infinity => (invalidop_flags, float_some_qnan (.FP_Div mode x y))
  | .Infinity, _ =>
    (clear_flags,
     if x.Sign = y.Sign then float_plus_infinity t w else float_minus_infinity t w)
  | _, .Infinity =>
    (clear_flags,
     if x.Sign = y.Sign then float_plus_zero t w else float_minus_zero t w)
  | .Float r1, .Float r2 =>
    if r2 = 0 then
      if r1 = 0 then
        (invalidop_flags, float_some_qnan (.FP_Div mode x y))
      else
        (dividezero_flags,
         if x.Sign = y.Sign then float_plus_infinity t w else float_minus_infinity t w)
    else float_round_with_flags mode (x.Sign ≠ y.Sign) (r1 / r2)

/- HOL4: float_mul_add_def
   float_mul_add mode (x: ('t, 'w) float) (y: ('t, 'w) float) (z: ('t, 'w) float) =
      let signP = x.Sign ?? y.Sign in
      let infP = (float_is_infinite x \/ float_is_infinite y)
      in
         if float_is_nan x \/ float_is_nan y \/ float_is_nan z then
            (check_for_signalling [x; y; z], float_some_qnan (FP_MulAdd mode x y z))
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
                (if (r1 = 0) /\ (r2 = 0) /\ (signP = z.Sign) then signP = 1w
                 else mode = roundTowardNegative) \/
                r < 0)
               r -/
noncomputable def float_mul_add {t w : Nat} (mode : rounding) (x y z : float t w) :
    flags × float t w :=
  let signP := x.Sign ^^^ y.Sign
  let infP := float_is_infinite x ∨ float_is_infinite y
  if float_is_nan x ∨ float_is_nan y ∨ float_is_nan z then
    (check_for_signalling [x, y, z], float_some_qnan (.FP_MulAdd mode x y z))
  else if (float_is_infinite x ∧ float_is_zero y) ∨
          (float_is_zero x ∧ float_is_infinite y) ∨
          (float_is_infinite z ∧ infP ∧ signP ≠ z.Sign) then
    (invalidop_flags, float_some_qnan (.FP_MulAdd mode x y z))
  else if (float_is_infinite z ∧ z.Sign = 0) ∨ (infP ∧ signP = 0) then
    (clear_flags, float_plus_infinity t w)
  else if (float_is_infinite z ∧ z.Sign = 1) ∨ (infP ∧ signP = 1) then
    (clear_flags, float_minus_infinity t w)
  else
    let r1 := float_to_real x * float_to_real y
    let r2 := float_to_real z
    let r := r1 + r2
    float_round_with_flags mode
      ((r = 0 ∧
        (if r1 = 0 ∧ r2 = 0 ∧ signP = z.Sign then signP = 1
         else mode = roundTowardNegative)) ∨
       r < 0)
      r

/- HOL4: Datatype:  float_compare = LT | EQ | GT | UN End -/
inductive float_compare
  | LT | EQ | GT | UN
  deriving DecidableEq

/- HOL4: float_compare_def
   float_compare (x: ('t, 'w) float) (y: ('t, 'w) float) =
      case float_value x, float_value y of
         NaN, _ => UN
       | _, NaN => UN
       | Infinity, Infinity =>
            if x.Sign = y.Sign then EQ else if x.Sign = 1w then LT else GT
       | Infinity, _ => if x.Sign = 1w then LT else GT
       | _, Infinity => if y.Sign = 1w then GT else LT
       | Float r1, Float r2 => if r1 < r2 then LT else if r1 = r2 then EQ else GT
   (named `get_float_compare`, because `float_compare` is also the type) -/
noncomputable def get_float_compare {t w : Nat} (x y : float t w) : float_compare :=
  match get_float_value x, get_float_value y with
  | .NaN, _ => .UN
  | _, .NaN => .UN
  | .Infinity, .Infinity =>
    if x.Sign = y.Sign then .EQ else if x.Sign = 1 then .LT else .GT
  | .Infinity, _ => if x.Sign = 1 then .LT else .GT
  | _, .Infinity => if y.Sign = 1 then .GT else .LT
  | .Float r1, .Float r2 => if r1 < r2 then .LT else if r1 = r2 then .EQ else .GT

/- HOL4: float_less_than_def:  float_less_than x y = (float_compare x y = LT) -/
def float_less_than {t w : Nat} (x y : float t w) : Prop := get_float_compare x y = .LT

/- HOL4: float_less_equal_def
   float_less_equal x y = case float_compare x y of LT => T | EQ => T | _ => F -/
def float_less_equal {t w : Nat} (x y : float t w) : Prop :=
  match get_float_compare x y with
  | .LT => True
  | .EQ => True
  | _ => False

/- HOL4: float_greater_than_def:  float_greater_than x y = (float_compare x y = GT) -/
def float_greater_than {t w : Nat} (x y : float t w) : Prop := get_float_compare x y = .GT

/- HOL4: float_greater_equal_def
   float_greater_equal x y = case float_compare x y of GT => T | EQ => T | _ => F -/
def float_greater_equal {t w : Nat} (x y : float t w) : Prop :=
  match get_float_compare x y with
  | .GT => True
  | .EQ => True
  | _ => False

/- HOL4: float_equal_def:  float_equal x y = (float_compare x y = EQ) -/
def float_equal {t w : Nat} (x y : float t w) : Prop := get_float_compare x y = .EQ

end ieee

/-! `machine_ieee`: the definitions generated by `mk_fp_encoding ("fp64", 52, 11, SOME "double")`. -/

open ieee

/- HOL4: machine_ieee$fp64_to_float_def
   fp64_to_float w =
     <| Sign := (63 >< 63) w; Exponent := (62 >< 52) w; Significand := (51 >< 0) w |> -/
def fp64_to_float (w : BitVec 64) : float 52 11 :=
  { Sign := w.extractLsb' 63 1, Exponent := w.extractLsb' 52 11, Significand := w.extractLsb' 0 52 }

/- HOL4: machine_ieee$float_to_fp64_def
   float_to_fp64 x = x.Sign @@ x.Exponent @@ x.Significand -/
def float_to_fp64 (x : float 52 11) : BitVec 64 := x.Sign ++ (x.Exponent ++ x.Significand)

/- HOL4: fp64_sqrt_def:  fp64_sqrt mode = float_to_fp64 o SND o float_sqrt mode o fp64_to_float -/
noncomputable def fp64_sqrt (mode : rounding) (a : BitVec 64) : BitVec 64 :=
  float_to_fp64 (float_sqrt mode (fp64_to_float a)).2

/- HOL4: fp64_negate_def:  fp64_negate = float_to_fp64 o float_negate o fp64_to_float -/
def fp64_negate (a : BitVec 64) : BitVec 64 := float_to_fp64 (float_negate (fp64_to_float a))

/- HOL4: fp64_abs_def:  fp64_abs = float_to_fp64 o float_abs o fp64_to_float -/
def fp64_abs (a : BitVec 64) : BitVec 64 := float_to_fp64 (float_abs (fp64_to_float a))

/- HOL4: fp64_add_def
   fp64_add mode a b = float_to_fp64 (SND (float_add mode (fp64_to_float a) (fp64_to_float b))) -/
noncomputable def fp64_add (mode : rounding) (a b : BitVec 64) : BitVec 64 :=
  float_to_fp64 (float_add mode (fp64_to_float a) (fp64_to_float b)).2

/- HOL4: fp64_sub_def
   fp64_sub mode a b = float_to_fp64 (SND (float_sub mode (fp64_to_float a) (fp64_to_float b))) -/
noncomputable def fp64_sub (mode : rounding) (a b : BitVec 64) : BitVec 64 :=
  float_to_fp64 (float_sub mode (fp64_to_float a) (fp64_to_float b)).2

/- HOL4: fp64_mul_def
   fp64_mul mode a b = float_to_fp64 (SND (float_mul mode (fp64_to_float a) (fp64_to_float b))) -/
noncomputable def fp64_mul (mode : rounding) (a b : BitVec 64) : BitVec 64 :=
  float_to_fp64 (float_mul mode (fp64_to_float a) (fp64_to_float b)).2

/- HOL4: fp64_div_def
   fp64_div mode a b = float_to_fp64 (SND (float_div mode (fp64_to_float a) (fp64_to_float b))) -/
noncomputable def fp64_div (mode : rounding) (a b : BitVec 64) : BitVec 64 :=
  float_to_fp64 (float_div mode (fp64_to_float a) (fp64_to_float b)).2

/- HOL4: fp64_mul_add_def
   fp64_mul_add mode a b c =
     float_to_fp64
       (SND (float_mul_add mode (fp64_to_float a) (fp64_to_float b) (fp64_to_float c))) -/
noncomputable def fp64_mul_add (mode : rounding) (a b c : BitVec 64) : BitVec 64 :=
  float_to_fp64 (float_mul_add mode (fp64_to_float a) (fp64_to_float b) (fp64_to_float c)).2

/- HOL4: fp64_equal_def:  fp64_equal a b = float_equal (fp64_to_float a) (fp64_to_float b) -/
def fp64_equal (a b : BitVec 64) : Prop := float_equal (fp64_to_float a) (fp64_to_float b)

/- HOL4: fp64_lessThan_def
   fp64_lessThan a b = float_less_than (fp64_to_float a) (fp64_to_float b) -/
def fp64_lessThan (a b : BitVec 64) : Prop := float_less_than (fp64_to_float a) (fp64_to_float b)

/- HOL4: fp64_lessEqual_def
   fp64_lessEqual a b = float_less_equal (fp64_to_float a) (fp64_to_float b) -/
def fp64_lessEqual (a b : BitVec 64) : Prop := float_less_equal (fp64_to_float a) (fp64_to_float b)

/- HOL4: fp64_greaterThan_def
   fp64_greaterThan a b = float_greater_than (fp64_to_float a) (fp64_to_float b) -/
def fp64_greaterThan (a b : BitVec 64) : Prop :=
  float_greater_than (fp64_to_float a) (fp64_to_float b)

/- HOL4: fp64_greaterEqual_def
   fp64_greaterEqual a b = float_greater_equal (fp64_to_float a) (fp64_to_float b) -/
def fp64_greaterEqual (a b : BitVec 64) : Prop :=
  float_greater_equal (fp64_to_float a) (fp64_to_float b)

end CmlTS
