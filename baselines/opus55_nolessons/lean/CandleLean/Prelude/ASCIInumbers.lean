/-
  HOL4 library constants from the theories `numposrep` and `ASCIInumbers`.
-/
import CandleLean.Prelude.String

open Classical

/- HOL4: numposrep$l2n   (l2n b [] = 0) /\ (l2n b (h::t) = h MOD b + b * l2n b t) -/
def l2n (b : Nat) : List Nat → Nat
  | [] => 0
  | h :: t => h % b + b * l2n b t

/- HOL4: numposrep$n2l
   n2l b n = if n < b \/ b < 2 then [n MOD b] else n MOD b :: n2l b (n DIV b) -/
def n2l (b n : Nat) : List Nat :=
  if n < b ∨ b < 2 then [n % b] else n % b :: n2l b (n / b)
termination_by n
decreasing_by
  apply Nat.div_lt_self <;> omega

/- HOL4: ASCIInumbers$s2n   `s2n b f (s:string) = l2n b (MAP f (REVERSE s))` -/
def s2n (b : Nat) (f : char → Nat) (s : string) : Nat := l2n b ((s.reverse).map f)

/- HOL4: ASCIInumbers$n2s   `n2s b f n : string = REVERSE (MAP f (n2l b n))` -/
def n2s (b : Nat) (f : Nat → char) (n : Nat) : string := ((n2l b n).map f).reverse

/- HOL4: ASCIInumbers$HEX
   HEX n = if n < 10 then CHR (ORD #"0" + n) else
           if n < 16 then CHR (ORD #"A" + (n - 10)) else CHR 0 -/
noncomputable def HEX (n : Nat) : char :=
  if n < 10 then CHR (ORD ch!"0" + n) else
  if n < 16 then CHR (ORD ch!"A" + (n - 10)) else CHR 0

/- HOL4: ASCIInumbers$UNHEX
   UNHEX c = let n = ORD c in
     if ORD #"0" <= n /\ n <= ORD #"9" then n - ORD #"0" else
     if ORD #"a" <= n /\ n <= ORD #"f" then 10 + n - ORD #"a" else
     if ORD #"A" <= n /\ n <= ORD #"F" then 10 + n - ORD #"A" else 0 -/
noncomputable def UNHEX (c : char) : Nat :=
  let n := ORD c
  if ORD ch!"0" ≤ n ∧ n ≤ ORD ch!"9" then n - ORD ch!"0" else
  if ORD ch!"a" ≤ n ∧ n ≤ ORD ch!"f" then 10 + n - ORD ch!"a" else
  if ORD ch!"A" ≤ n ∧ n ≤ ORD ch!"F" then 10 + n - ORD ch!"A" else 0

/- HOL4: ASCIInumbers$num_from_hex_string   `num_from_hex_string = s2n 16 UNHEX` -/
noncomputable def num_from_hex_string : string → Nat := s2n 16 UNHEX

/- HOL4: ASCIInumbers$num_to_hex_string   `num_to_hex_string = n2s 16 HEX` -/
noncomputable def num_to_hex_string : Nat → string := n2s 16 HEX
