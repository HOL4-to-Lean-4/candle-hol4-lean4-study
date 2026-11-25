import CmlTS.Prelude.Real
import CmlTS.Prelude.Words
import CmlTS.Prelude.ListLib

/-
HOL4 library constants from `binary_ieee` and `machine_ieee` (the `fp64_*`
constants, which HOL4 generates with `machine_ieeeLib.mk_fp_encoding`
("fp64", 52, 11, SOME "double")).

`('t, 'w) float` is `float t w`; constants that take a type argument
`(:'t # 'w)` in HOL4 take the numbers `t w` here.
-/

namespace CmlTS

noncomputable section

open scoped Classical

variable {t w : Nat}

/- HOL4: binary_ieee$float
   Datatype: float = <| Sign : word1; Exponent : 'w word; Significand : 't word |> -/
structure float (t w : Nat) where
  Sign : BitVec 1
  Exponent : BitVec w
  Significand : BitVec t

instance : Nonempty (float t w) := ⟨⟨0, 0, 0⟩⟩

/- HOL4: binary_ieee$float_value (the type)
   Datatype: float_value = Float real | Infinity | NaN -/
inductive float_value_t
  | Float (r : real)
  | Infinity
  | NaN

/- HOL4: binary_ieee$float_to_real
   float_to_real (x: ('t, 'w) float) =
      if x.Exponent = 0w
         then -1r pow (w2n x.Sign) *
              (2r / 2r pow (bias (:'w))) *
              (&(w2n x.Significand) / 2r pow (precision (:'t)))
      else -1r pow (w2n x.Sign) *
           (2r pow (w2n x.Exponent) / 2r pow (bias (:'w))) *
           (1r + &(w2n x.Significand) / 2r pow (precision (:'t)))
   (precision = dimindex, bias = INT_MAX) -/
def float_to_real (x : float t w) : real :=
  if x.Exponent = n2w 0 then
    real.pow (-1) (w2n x.Sign) * (2 / real.pow 2 (INT_MAX w)) *
      (real.ofNum (w2n x.Significand) / real.pow 2 t)
  else
    real.pow (-1) (w2n x.Sign) * (real.pow 2 (w2n x.Exponent) / real.pow 2 (INT_MAX w)) *
      (1 + real.ofNum (w2n x.Significand) / real.pow 2 t)

/- HOL4: binary_ieee$float_value
   float_value (x: ('t, 'w) float) =
      if x.Exponent = UINT_MAXw
         then if x.Significand = 0w then Infinity else NaN
      else Float (float_to_real x) -/
def float_value (x : float t w) : float_value_t :=
  if x.Exponent = word_T then
    if x.Significand = n2w 0 then float_value_t.Infinity else float_value_t.NaN
  else float_value_t.Float (float_to_real x)

/- HOL4: binary_ieee$float_is_nan
   float_is_nan x = case float_value x of NaN => T | _ => F -/
def float_is_nan (x : float t w) : Prop :=
  match float_value x with
  | float_value_t.NaN => True
  | _ => False

/- HOL4: binary_ieee$float_is_signalling
   float_is_signalling x <=> float_is_nan x /\ ~word_msb x.Significand -/
def float_is_signalling (x : float t w) : Prop :=
  float_is_nan x ∧ ¬ word_msb x.Significand

/- HOL4: binary_ieee$float_is_infinite
   float_is_infinite x = case float_value x of Infinity => T | _ => F -/
def float_is_infinite (x : float t w) : Prop :=
  match float_value x with
  | float_value_t.Infinity => True
  | _ => False

/- HOL4: binary_ieee$float_is_zero
   float_is_zero x = case float_value x of Float r => r = 0 | _ => F -/
def float_is_zero (x : float t w) : Prop :=
  match float_value x with
  | float_value_t.Float r => r = 0
  | _ => False

/- HOL4: binary_ieee$float_is_finite
   float_is_finite x = case float_value x of Float _ => T | _ => F -/
def float_is_finite (x : float t w) : Prop :=
  match float_value x with
  | float_value_t.Float _ => True
  | _ => False

/- HOL4: binary_ieee$float_negate   float_negate x = x with Sign := ~x.Sign -/
def float_negate (x : float t w) : float t w := { x with Sign := word_1comp x.Sign }

/- HOL4: binary_ieee$float_abs   float_abs x = x with Sign := 0w -/
def float_abs (x : float t w) : float t w := { x with Sign := n2w 0 }

/- HOL4: binary_ieee$float_plus_infinity
   <| Sign := 0w; Exponent := UINT_MAXw; Significand := 0w |> -/
def float_plus_infinity (t w : Nat) : float t w :=
  { Sign := n2w 0, Exponent := word_T, Significand := n2w 0 }

/- HOL4: binary_ieee$float_plus_zero
   <| Sign := 0w; Exponent := 0w; Significand := 0w |> -/
def float_plus_zero (t w : Nat) : float t w :=
  { Sign := n2w 0, Exponent := n2w 0, Significand := n2w 0 }

/- HOL4: binary_ieee$float_top
   <| Sign := 0w; Exponent := UINT_MAXw - 1w; Significand := UINT_MAXw |> -/
def float_top (t w : Nat) : float t w :=
  { Sign := n2w 0, Exponent := word_sub word_T (n2w 1), Significand := word_T }

/- HOL4: binary_ieee$float_minus_infinity
   float_minus_infinity (:'t # 'w) = float_negate (float_plus_infinity (:'t # 'w)) -/
def float_minus_infinity (t w : Nat) : float t w := float_negate (float_plus_infinity t w)

/- HOL4: binary_ieee$float_minus_zero
   float_minus_zero (:'t # 'w) = float_negate (float_plus_zero (:'t # 'w)) -/
def float_minus_zero (t w : Nat) : float t w := float_negate (float_plus_zero t w)

/- HOL4: binary_ieee$float_bottom
   float_bottom (:'t # 'w) = float_negate (float_top (:'t # 'w)) -/
def float_bottom (t w : Nat) : float t w := float_negate (float_top t w)

/- HOL4: binary_ieee$flags
   Datatype: flags = <| DivideByZero : bool ; InvalidOp : bool ; Overflow : bool
                      ; Precision : bool ; Underflow_BeforeRounding : bool
                      ; Underflow_AfterRounding : bool |> -/
structure flags where
  DivideByZero : Bool
  InvalidOp : Bool
  Overflow : Bool
  Precision : Bool
  Underflow_BeforeRounding : Bool
  Underflow_AfterRounding : Bool

/- HOL4: binary_ieee$clear_flags   (all flags F) -/
def clear_flags : flags :=
  { DivideByZero := false
    InvalidOp := false
    Overflow := false
    Precision := false
    Underflow_BeforeRounding := false
    Underflow_AfterRounding := false }

/- HOL4: binary_ieee$invalidop_flags   clear_flags with InvalidOp := T -/
def invalidop_flags : flags := { clear_flags with InvalidOp := true }

/- HOL4: binary_ieee$dividezero_flags   clear_flags with DivideByZero := T -/
def dividezero_flags : flags := { clear_flags with DivideByZero := true }

/- HOL4: binary_ieee$rounding
   Datatype: rounding = roundTiesToEven | roundTowardPositive
                      | roundTowardNegative | roundTowardZero -/
inductive rounding
  | roundTiesToEven
  | roundTowardPositive
  | roundTowardNegative
  | roundTowardZero

/- HOL4: binary_ieee$is_closest
   is_closest s x a <=>
      a IN s /\
      !b. b IN s ==> abs (float_to_real a - x) <= abs (float_to_real b - x) -/
def is_closest (s : float t w → Prop) (x : real) (a : float t w) : Prop :=
  s a ∧ ∀ b, s b → real.abs (float_to_real a - x) ≤ real.abs (float_to_real b - x)

/- HOL4: binary_ieee$closest_such
   closest_such p s x = @a. is_closest s x a /\ (!b. is_closest s x b /\ p b ==> p a) -/
def closest_such (p : float t w → Prop) (s : float t w → Prop) (x : real) : float t w :=
  select fun a => is_closest s x a ∧ ∀ b, is_closest s x b ∧ p b → p a

/- HOL4: binary_ieee$closest   closest = closest_such (K T) -/
def closest : (float t w → Prop) → real → float t w := closest_such (K True)

/- HOL4: binary_ieee$largest
   largest (:'t # 'w) =
      (2r pow (UINT_MAX (:'w) - 1) / 2r pow (INT_MAX (:'w))) *
      (2r - inv (2r pow dimindex(:'t))) -/
def largest (t w : Nat) : real :=
  (real.pow 2 (UINT_MAX w - 1) / real.pow 2 (INT_MAX w)) * (2 - real.inv (real.pow 2 t))

/- HOL4: binary_ieee$threshold
   threshold (:'t # 'w) =
      (2r pow (UINT_MAX (:'w) - 1) / 2r pow (INT_MAX (:'w))) *
      (2r - inv (2r pow SUC (dimindex(:'t)))) -/
def threshold (t w : Nat) : real :=
  (real.pow 2 (UINT_MAX w - 1) / real.pow 2 (INT_MAX w)) * (2 - real.inv (real.pow 2 (t + 1)))

/- HOL4: binary_ieee$round
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
def round (mode : rounding) (x : real) : float t w :=
  match mode with
  | rounding.roundTiesToEven =>
    let th := threshold t w
    if x ≤ -th then float_minus_infinity t w
    else if x ≥ th then float_plus_infinity t w
    else closest_such (fun a => ¬ word_lsb a.Significand) float_is_finite x
  | rounding.roundTowardZero =>
    let th := largest t w
    if x < -th then float_bottom t w
    else if x > th then float_top t w
    else closest (fun a => float_is_finite a ∧ real.abs (float_to_real a) ≤ real.abs x) x
  | rounding.roundTowardPositive =>
    let th := largest t w
    if x < -th then float_bottom t w
    else if x > th then float_plus_infinity t w
    else closest (fun a => float_is_finite a ∧ float_to_real a ≥ x) x
  | rounding.roundTowardNegative =>
    let th := largest t w
    if x < -th then float_minus_infinity t w
    else if x > th then float_top t w
    else closest (fun a => float_is_finite a ∧ float_to_real a ≤ x) x

/- HOL4: binary_ieee$fp_op
   Datatype: fp_op =
     FP_Sqrt rounding (('t, 'w) float)
   | FP_Add rounding (('t, 'w) float) (('t, 'w) float)
   | FP_Sub rounding (('t, 'w) float) (('t, 'w) float)
   | FP_Mul rounding (('t, 'w) float) (('t, 'w) float)
   | FP_Div rounding (('t, 'w) float) (('t, 'w) float)
   | FP_MulAdd rounding (('t, 'w) float) (('t, 'w) float) (('t, 'w) float)
   | FP_MulSub rounding (('t, 'w) float) (('t, 'w) float) (('t, 'w) float) -/
inductive fp_op (t w : Nat)
  | FP_Sqrt (m : rounding) (x : float t w)
  | FP_Add (m : rounding) (x y : float t w)
  | FP_Sub (m : rounding) (x y : float t w)
  | FP_Mul (m : rounding) (x y : float t w)
  | FP_Div (m : rounding) (x y : float t w)
  | FP_MulAdd (m : rounding) (x y z : float t w)
  | FP_MulSub (m : rounding) (x y z : float t w)

/- HOL4: binary_ieee$float_some_qnan
   float_some_qnan (fp_op : ('t, 'w) fp_op) =
   (@f. let qnan = f fp_op in float_is_nan qnan /\ ~float_is_signalling qnan)
     fp_op : ('t, 'w) float -/
def float_some_qnan (op : fp_op t w) : float t w :=
  (select fun f : fp_op t w → float t w =>
    let qnan := f op
    float_is_nan qnan ∧ ¬ float_is_signalling qnan) op

/- HOL4: binary_ieee$float_round
   float_round mode toneg r =
      let x = round mode r in
         if float_is_zero x
            then if toneg then float_minus_zero (:'t # 'w)
                 else float_plus_zero (:'t # 'w)
         else x -/
def float_round (mode : rounding) (toneg : Prop) (r : real) : float t w :=
  let x : float t w := round mode r
  if float_is_zero x then
    if toneg then float_minus_zero t w else float_plus_zero t w
  else x

/- HOL4: binary_ieee$float_round_with_flags
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
def float_round_with_flags (mode : rounding) (to_neg : Prop) (r : real) : flags × float t w :=
  let x : float t w := float_round mode to_neg r
  let a := real.abs r
  let inexact : Prop := float_value x ≠ float_value_t.Float r
  ({ clear_flags with
      Overflow := decide (float_is_infinite x ∨ real.pow 2 (INT_MIN w) ≤ a)
      Underflow_BeforeRounding := decide (inexact ∧ a < 2 / real.pow 2 (INT_MAX w))
      Underflow_AfterRounding :=
        decide (inexact ∧
          word_ls (float_round mode to_neg r : float t (w + 1)).Exponent (n2w (INT_MIN w)))
      Precision := decide inexact }, x)

/- HOL4: binary_ieee$check_for_signalling
   check_for_signalling l = clear_flags with InvalidOp := EXISTS float_is_signalling l -/
def check_for_signalling (l : List (float t w)) : flags :=
  { clear_flags with InvalidOp := decide (EXISTS float_is_signalling l) }

/- HOL4: binary_ieee$float_sqrt
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
def float_sqrt (mode : rounding) (x : float t w) : flags × float t w :=
  if x.Sign = n2w 0 then
    match float_value x with
    | float_value_t.NaN => (check_for_signalling [x], float_some_qnan (fp_op.FP_Sqrt mode x))
    | float_value_t.Infinity => (clear_flags, float_plus_infinity t w)
    | float_value_t.Float r => float_round_with_flags mode False (real.sqrt r)
  else if x = float_minus_zero t w then (clear_flags, float_minus_zero t w)
  else (invalidop_flags, float_some_qnan (fp_op.FP_Sqrt mode x))

/- HOL4: binary_ieee$float_add
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
def float_add (mode : rounding) (x y : float t w) : flags × float t w :=
  match float_value x, float_value y with
  | float_value_t.NaN, _ => (check_for_signalling [x, y], float_some_qnan (fp_op.FP_Add mode x y))
  | _, float_value_t.NaN => (check_for_signalling [y], float_some_qnan (fp_op.FP_Add mode x y))
  | float_value_t.Infinity, float_value_t.Infinity =>
    if x.Sign = y.Sign then (clear_flags, x)
    else (invalidop_flags, float_some_qnan (fp_op.FP_Add mode x y))
  | float_value_t.Infinity, _ => (clear_flags, x)
  | _, float_value_t.Infinity => (clear_flags, y)
  | float_value_t.Float r1, float_value_t.Float r2 =>
    float_round_with_flags mode
      (if r1 = 0 ∧ r2 = 0 ∧ x.Sign = y.Sign then x.Sign = n2w 1
       else mode = rounding.roundTowardNegative) (r1 + r2)

/- HOL4: binary_ieee$float_sub
   float_sub mode (x: ('t, 'w) float) (y: ('t, 'w) float) =
      case float_value x, float_value y of
         NaN, _ => (check_for_signalling [x; y], float_some_qnan (FP_Sub mode x y))
       | _, NaN => (check_for_signalling [y], float_some_qnan (FP_Sub mode x y))
       | Infinity, Infinity =>
            if x.Sign = y.Sign then
               (invalidop_flags, float_some_qnan (FP_Sub mode x y))
            else (clear_flags, x)
       | Infinity, _ => (clear_flags, x)
       | _, Infinity => (clear_flags, float_negate y)
       | Float r1, Float r2 =>
            float_round_with_flags mode
               (if (r1 = 0) /\ (r2 = 0) /\ x.Sign <> y.Sign then x.Sign = 1w
                else mode = roundTowardNegative) (r1 - r2) -/
def float_sub (mode : rounding) (x y : float t w) : flags × float t w :=
  match float_value x, float_value y with
  | float_value_t.NaN, _ => (check_for_signalling [x, y], float_some_qnan (fp_op.FP_Sub mode x y))
  | _, float_value_t.NaN => (check_for_signalling [y], float_some_qnan (fp_op.FP_Sub mode x y))
  | float_value_t.Infinity, float_value_t.Infinity =>
    if x.Sign = y.Sign then (invalidop_flags, float_some_qnan (fp_op.FP_Sub mode x y))
    else (clear_flags, x)
  | float_value_t.Infinity, _ => (clear_flags, x)
  | _, float_value_t.Infinity => (clear_flags, float_negate y)
  | float_value_t.Float r1, float_value_t.Float r2 =>
    float_round_with_flags mode
      (if r1 = 0 ∧ r2 = 0 ∧ x.Sign ≠ y.Sign then x.Sign = n2w 1
       else mode = rounding.roundTowardNegative) (r1 - r2)

/- HOL4: binary_ieee$float_mul
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
def float_mul (mode : rounding) (x y : float t w) : flags × float t w :=
  match float_value x, float_value y with
  | float_value_t.NaN, _ => (check_for_signalling [x, y], float_some_qnan (fp_op.FP_Mul mode x y))
  | _, float_value_t.NaN => (check_for_signalling [y], float_some_qnan (fp_op.FP_Mul mode x y))
  | float_value_t.Infinity, float_value_t.Float r =>
    if r = 0 then (invalidop_flags, float_some_qnan (fp_op.FP_Mul mode x y))
    else (clear_flags,
      if x.Sign = y.Sign then float_plus_infinity t w else float_minus_infinity t w)
  | float_value_t.Float r, float_value_t.Infinity =>
    if r = 0 then (invalidop_flags, float_some_qnan (fp_op.FP_Mul mode x y))
    else (clear_flags,
      if x.Sign = y.Sign then float_plus_infinity t w else float_minus_infinity t w)
  | float_value_t.Infinity, float_value_t.Infinity =>
    (clear_flags,
      if x.Sign = y.Sign then float_plus_infinity t w else float_minus_infinity t w)
  | float_value_t.Float r1, float_value_t.Float r2 =>
    float_round_with_flags mode (x.Sign ≠ y.Sign) (r1 * r2)

/- HOL4: binary_ieee$float_div
   float_div mode (x: ('t, 'w) float) (y: ('t, 'w) float) =
      case float_value x, float_value y of
         NaN, _ => (check_for_signalling [x; y], float_some_qnan (FP_Div mode x y))
       | _, NaN => (check_for_signalling [y], float_some_qnan (FP_Div mode x y))
       | Infinity, Infinity =>
            (invalidop_flags, float_some_qnan (FP_Div mode x y))
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
def float_div (mode : rounding) (x y : float t w) : flags × float t w :=
  match float_value x, float_value y with
  | float_value_t.NaN, _ => (check_for_signalling [x, y], float_some_qnan (fp_op.FP_Div mode x y))
  | _, float_value_t.NaN => (check_for_signalling [y], float_some_qnan (fp_op.FP_Div mode x y))
  | float_value_t.Infinity, float_value_t.Infinity =>
    (invalidop_flags, float_some_qnan (fp_op.FP_Div mode x y))
  | float_value_t.Infinity, _ =>
    (clear_flags,
      if x.Sign = y.Sign then float_plus_infinity t w else float_minus_infinity t w)
  | _, float_value_t.Infinity =>
    (clear_flags, if x.Sign = y.Sign then float_plus_zero t w else float_minus_zero t w)
  | float_value_t.Float r1, float_value_t.Float r2 =>
    if r2 = 0 then
      if r1 = 0 then (invalidop_flags, float_some_qnan (fp_op.FP_Div mode x y))
      else (dividezero_flags,
        if x.Sign = y.Sign then float_plus_infinity t w else float_minus_infinity t w)
    else float_round_with_flags mode (x.Sign ≠ y.Sign) (r1 / r2)

/- HOL4: binary_ieee$float_mul_add
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
             float_round_with_flags mode
               ((r = 0) /\
                (if (r1 = 0) /\ (r2 = 0) /\ (signP = z.Sign) then signP = 1w
                 else mode = roundTowardNegative) \/
                r < 0)
               r -/
def float_mul_add (mode : rounding) (x y z : float t w) : flags × float t w :=
  let signP := word_xor x.Sign y.Sign
  let infP : Prop := float_is_infinite x ∨ float_is_infinite y
  if float_is_nan x ∨ float_is_nan y ∨ float_is_nan z then
    (check_for_signalling [x, y, z], float_some_qnan (fp_op.FP_MulAdd mode x y z))
  else if (float_is_infinite x ∧ float_is_zero y) ∨ (float_is_zero x ∧ float_is_infinite y) ∨
      (float_is_infinite z ∧ infP ∧ signP ≠ z.Sign) then
    (invalidop_flags, float_some_qnan (fp_op.FP_MulAdd mode x y z))
  else if (float_is_infinite z ∧ z.Sign = n2w 0) ∨ (infP ∧ signP = n2w 0) then
    (clear_flags, float_plus_infinity t w)
  else if (float_is_infinite z ∧ z.Sign = n2w 1) ∨ (infP ∧ signP = n2w 1) then
    (clear_flags, float_minus_infinity t w)
  else
    let r1 := float_to_real x * float_to_real y
    let r2 := float_to_real z
    let r := r1 + r2
    float_round_with_flags mode
      ((r = 0 ∧
        (if r1 = 0 ∧ r2 = 0 ∧ signP = z.Sign then signP = n2w 1
         else mode = rounding.roundTowardNegative)) ∨ r < 0) r

/- HOL4: binary_ieee$float_compare (the type)
   Datatype:  float_compare = LT | EQ | GT | UN -/
inductive float_compare_t
  | LT
  | EQ
  | GT
  | UN

/- HOL4: binary_ieee$float_compare
   float_compare (x: ('t, 'w) float) (y: ('t, 'w) float) =
      case float_value x, float_value y of
         NaN, _ => UN
       | _, NaN => UN
       | Infinity, Infinity =>
            if x.Sign = y.Sign then EQ
            else if x.Sign = 1w then LT
            else GT
       | Infinity, _ => if x.Sign = 1w then LT else GT
       | _, Infinity => if y.Sign = 1w then GT else LT
       | Float r1, Float r2 =>
            if r1 < r2 then LT else if r1 = r2 then EQ else GT -/
def float_compare (x y : float t w) : float_compare_t :=
  match float_value x, float_value y with
  | float_value_t.NaN, _ => float_compare_t.UN
  | _, float_value_t.NaN => float_compare_t.UN
  | float_value_t.Infinity, float_value_t.Infinity =>
    if x.Sign = y.Sign then float_compare_t.EQ
    else if x.Sign = n2w 1 then float_compare_t.LT
    else float_compare_t.GT
  | float_value_t.Infinity, _ =>
    if x.Sign = n2w 1 then float_compare_t.LT else float_compare_t.GT
  | _, float_value_t.Infinity =>
    if y.Sign = n2w 1 then float_compare_t.GT else float_compare_t.LT
  | float_value_t.Float r1, float_value_t.Float r2 =>
    if r1 < r2 then float_compare_t.LT
    else if r1 = r2 then float_compare_t.EQ
    else float_compare_t.GT

/- HOL4: binary_ieee$float_less_than   float_less_than x y = (float_compare x y = LT) -/
def float_less_than (x y : float t w) : Prop := float_compare x y = float_compare_t.LT

/- HOL4: binary_ieee$float_less_equal
   float_less_equal x y = case float_compare x y of LT => T | EQ => T | _ => F -/
def float_less_equal (x y : float t w) : Prop :=
  match float_compare x y with
  | float_compare_t.LT => True
  | float_compare_t.EQ => True
  | _ => False

/- HOL4: binary_ieee$float_greater_than   float_greater_than x y = (float_compare x y = GT) -/
def float_greater_than (x y : float t w) : Prop := float_compare x y = float_compare_t.GT

/- HOL4: binary_ieee$float_greater_equal
   float_greater_equal x y = case float_compare x y of GT => T | EQ => T | _ => F -/
def float_greater_equal (x y : float t w) : Prop :=
  match float_compare x y with
  | float_compare_t.GT => True
  | float_compare_t.EQ => True
  | _ => False

/- HOL4: binary_ieee$float_equal   float_equal x y = (float_compare x y = EQ) -/
def float_equal (x y : float t w) : Prop := float_compare x y = float_compare_t.EQ

/-! ### machine_ieee: the 64-bit encoding -/

/- HOL4: machine_ieee$fp64_to_float
   fp64_to_float w = <| Sign := (63 >< 63) w;
                        Exponent := (62 >< 52) w;
                        Significand := (51 >< 0) w |> -/
def fp64_to_float (w : word64) : float 52 11 :=
  { Sign := word_extract 63 63 w
    Exponent := word_extract 62 52 w
    Significand := word_extract 51 0 w }

/- HOL4: machine_ieee$float_to_fp64
   float_to_fp64 x = x.Sign @@ x.Exponent @@ x.Significand -/
def float_to_fp64 (x : float 52 11) : word64 :=
  word_concat x.Sign (word_concat x.Exponent x.Significand : BitVec 63)

/- HOL4: machine_ieee$fp64_sqrt   fp64_sqrt mode = float_to_fp64 o SND o float_sqrt mode o fp64_to_float -/
def fp64_sqrt (mode : rounding) (a : word64) : word64 :=
  float_to_fp64 (float_sqrt mode (fp64_to_float a)).2

/- HOL4: machine_ieee$fp64_negate   fp64_negate = float_to_fp64 o float_negate o fp64_to_float -/
def fp64_negate (a : word64) : word64 := float_to_fp64 (float_negate (fp64_to_float a))

/- HOL4: machine_ieee$fp64_abs   fp64_abs = float_to_fp64 o float_abs o fp64_to_float -/
def fp64_abs (a : word64) : word64 := float_to_fp64 (float_abs (fp64_to_float a))

/- HOL4: machine_ieee$fp64_add
   fp64_add mode a b = float_to_fp64 (SND (float_add mode (fp64_to_float a) (fp64_to_float b))) -/
def fp64_add (mode : rounding) (a b : word64) : word64 :=
  float_to_fp64 (float_add mode (fp64_to_float a) (fp64_to_float b)).2

/- HOL4: machine_ieee$fp64_sub
   fp64_sub mode a b = float_to_fp64 (SND (float_sub mode (fp64_to_float a) (fp64_to_float b))) -/
def fp64_sub (mode : rounding) (a b : word64) : word64 :=
  float_to_fp64 (float_sub mode (fp64_to_float a) (fp64_to_float b)).2

/- HOL4: machine_ieee$fp64_mul
   fp64_mul mode a b = float_to_fp64 (SND (float_mul mode (fp64_to_float a) (fp64_to_float b))) -/
def fp64_mul (mode : rounding) (a b : word64) : word64 :=
  float_to_fp64 (float_mul mode (fp64_to_float a) (fp64_to_float b)).2

/- HOL4: machine_ieee$fp64_div
   fp64_div mode a b = float_to_fp64 (SND (float_div mode (fp64_to_float a) (fp64_to_float b))) -/
def fp64_div (mode : rounding) (a b : word64) : word64 :=
  float_to_fp64 (float_div mode (fp64_to_float a) (fp64_to_float b)).2

/- HOL4: machine_ieee$fp64_mul_add
   fp64_mul_add mode a b c =
     float_to_fp64 (SND (float_mul_add mode (fp64_to_float a) (fp64_to_float b) (fp64_to_float c))) -/
def fp64_mul_add (mode : rounding) (a b c : word64) : word64 :=
  float_to_fp64 (float_mul_add mode (fp64_to_float a) (fp64_to_float b) (fp64_to_float c)).2

/- HOL4: machine_ieee$fp64_equal
   fp64_equal a b = float_equal (fp64_to_float a) (fp64_to_float b) -/
def fp64_equal (a b : word64) : Prop := float_equal (fp64_to_float a) (fp64_to_float b)

/- HOL4: machine_ieee$fp64_lessThan
   fp64_lessThan a b = float_less_than (fp64_to_float a) (fp64_to_float b) -/
def fp64_lessThan (a b : word64) : Prop := float_less_than (fp64_to_float a) (fp64_to_float b)

/- HOL4: machine_ieee$fp64_lessEqual
   fp64_lessEqual a b = float_less_equal (fp64_to_float a) (fp64_to_float b) -/
def fp64_lessEqual (a b : word64) : Prop := float_less_equal (fp64_to_float a) (fp64_to_float b)

/- HOL4: machine_ieee$fp64_greaterThan
   fp64_greaterThan a b = float_greater_than (fp64_to_float a) (fp64_to_float b) -/
def fp64_greaterThan (a b : word64) : Prop :=
  float_greater_than (fp64_to_float a) (fp64_to_float b)

/- HOL4: machine_ieee$fp64_greaterEqual
   fp64_greaterEqual a b = float_greater_equal (fp64_to_float a) (fp64_to_float b) -/
def fp64_greaterEqual (a b : word64) : Prop :=
  float_greater_equal (fp64_to_float a) (fp64_to_float b)

end

end CmlTS
