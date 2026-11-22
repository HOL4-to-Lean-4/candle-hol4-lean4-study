import CandleLean.Prelude.List

/-!
# HOL4 library: string (8-bit characters), numposrep, ASCIInumbers

HOL4 `char` is a type in bijection with `{n | n < 256}` (`ORD`/`CHR`); it is modelled by the
structure `HOL.char` holding such a number.  HOL4 `string` is `char list` (`HOL.string`).
This is *not* Lean's `Char`/`String`; the helpers `HOL.ch` and `HOL.str` turn Lean character
and string literals into HOL4 ones (for ASCII text, `ch c = CHR (Char.toNat c)`).
-/

universe u

namespace HOL

open Classical

noncomputable section

/- HOL4: string$char
     val CHAR_TYPE = new_type_definition("char", CHAR_EXISTS)   (* ∃n. n < 256 *)
     define_new_type_bijections {ABS="CHR", REP="ORD", ...} -/
structure char where
  /-- the representing number (HOL4 `ORD`) -/
  ord : Nat
  ord_lt : ord < 256
  deriving DecidableEq

instance : Nonempty char := ⟨⟨0, by decide⟩⟩
instance : Inhabited char := ⟨⟨0, by decide⟩⟩

/- HOL4: string$ORD    (representation function of char) -/
def ORD (c : char) : Nat := c.ord

/- HOL4: string$CHR    (abstraction function of char)
     CHR_ORD: CHR (ORD a) = a;  ORD_CHR: r < 256 <=> ORD (CHR r) = r
   `CHR n` for `n >= 256` is unspecified in HOL4; here it is `(ARB : Nat → char) n`. -/
def CHR (n : Nat) : char :=
  if h : n < 256 then ⟨n, h⟩ else (ARB : Nat → char) n

/-- Lean character literal to HOL4 `char` (for ASCII characters this is `CHR (Char.toNat c)`). -/
def ch (c : Char) : char := ⟨c.toNat % 256, Nat.mod_lt _ (by decide)⟩

/- HOL4: string$string    Type string = ``:char list`` -/
abbrev string := List char

/-- Lean string literal to HOL4 `string` (list of `ch` of its characters). -/
def str (s : String) : string := s.toList.map ch

/- HOL4: string$char_lt (overloaded as < on chars)    char_lt a b <=> ORD a < ORD b -/
def char_lt (a b : char) : Prop := ORD a < ORD b

/- HOL4: string$char_le    char_le a b <=> ORD a <= ORD b -/
def char_le (a b : char) : Prop := ORD a ≤ ORD b

/- HOL4: string$string_lt
     (string_lt s EMPTYSTRING <=> F) /\
     (string_lt EMPTYSTRING (STRING c s) <=> T) /\
     (string_lt (STRING c1 s1) (STRING c2 s2) <=>
        c1 < c2 \/ (c1 = c2) /\ string_lt s1 s2) -/
def string_lt : string → string → Prop
  | _, [] => False
  | [], _ :: _ => True
  | c1 :: s1, c2 :: s2 => char_lt c1 c2 ∨ (c1 = c2 ∧ string_lt s1 s2)

/- HOL4: string$string_le    string_le s1 s2 <=> (s1 = s2) \/ string_lt s1 s2 -/
def string_le (s1 s2 : string) : Prop := s1 = s2 ∨ string_lt s1 s2

theorem Aux.TL_length {α : Type u} (l : List α) : (TL l).length = l.length - 1 := by
  cases l <;> simp [TL]

/- HOL4: string$FIELDS
     (FIELDS P ([]:string) = [[]]) /\
     (FIELDS P (h::t) =
         let (l,r) = SPLITP P (h::t) in
           if NULL l then
             []::FIELDS P (TL r)
           else
             if NULL r then [l] else l::FIELDS P (TL r))
   (the `let (l,r) = ...` is written with projections) -/
def FIELDS (P : char → Prop) : string → List string
  | [] => [[]]
  | h :: t =>
    let lr := SPLITP P (h :: t)
    if NULL lr.1 then [] :: FIELDS P (TL lr.2)
    else if NULL lr.2 then [lr.1] else lr.1 :: FIELDS P (TL lr.2)
termination_by s => s.length
decreasing_by
  all_goals
    have h1 := Aux.SPLITP_snd_length P (h :: t)
    rw [Aux.TL_length]
    simp only [List.length_cons] at h1 ⊢
    omega

/-! ## numposrep -/

/- HOL4: numposrep$l2n    (l2n b [] = 0) /\ (l2n b (h::t) = h MOD b + b * l2n b t) -/
def l2n (b : Nat) : List Nat → Nat
  | [] => 0
  | h :: t => h % b + b * l2n b t

/- HOL4: numposrep$n2l    n2l b n = if n < b \/ b < 2 then [n MOD b] else n MOD b :: n2l b (n DIV b) -/
def n2l (b n : Nat) : List Nat :=
  if n < b ∨ b < 2 then [n % b] else n % b :: n2l b (n / b)
termination_by n
decreasing_by
  apply Nat.div_lt_self <;> omega

/-! ## ASCIInumbers -/

/- HOL4: ASCIInumbers$s2n    s2n b f (s:string) = l2n b (MAP f (REVERSE s)) -/
def s2n (b : Nat) (f : char → Nat) (s : string) : Nat := l2n b (s.reverse.map f)

/- HOL4: ASCIInumbers$n2s    n2s b f n : string = REVERSE (MAP f (n2l b n)) -/
def n2s (b : Nat) (f : Nat → char) (n : Nat) : string := ((n2l b n).map f).reverse

/- HOL4: ASCIInumbers$HEX
     HEX n = if n < 10 then CHR (ORD #"0" + n) else
             if n < 16 then CHR (ORD #"A" + (n - 10)) else CHR 0 -/
def HEX (n : Nat) : char :=
  if n < 10 then CHR (ORD (ch '0') + n) else
  if n < 16 then CHR (ORD (ch 'A') + (n - 10)) else CHR 0

/- HOL4: ASCIInumbers$UNHEX
     UNHEX c =
       let n = ORD c in
         if ORD #"0" <= n /\ n <= ORD #"9" then n - ORD #"0" else
         if ORD #"a" <= n /\ n <= ORD #"f" then 10 + n - ORD #"a" else
         if ORD #"A" <= n /\ n <= ORD #"F" then 10 + n - ORD #"A" else 0 -/
def UNHEX (c : char) : Nat :=
  let n := ORD c
  if ORD (ch '0') ≤ n ∧ n ≤ ORD (ch '9') then n - ORD (ch '0') else
  if ORD (ch 'a') ≤ n ∧ n ≤ ORD (ch 'f') then 10 + n - ORD (ch 'a') else
  if ORD (ch 'A') ≤ n ∧ n ≤ ORD (ch 'F') then 10 + n - ORD (ch 'A') else 0

/- HOL4: ASCIInumbers$num_from_hex_string    num_from_hex_string = s2n 16 UNHEX -/
def num_from_hex_string : string → Nat := s2n 16 UNHEX

/- HOL4: ASCIInumbers$num_to_hex_string    num_to_hex_string = n2s 16 HEX -/
def num_to_hex_string : Nat → string := n2s 16 HEX

end

end HOL
