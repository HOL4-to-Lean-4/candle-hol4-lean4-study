import CmlTS.Prelude.List

/-!
# HOL4 library prelude: characters, strings, integers, words, ordering

* `char` : HOL4 `char` is a type with exactly 256 elements (`ORD : char -> num`, `ORD c < 256`,
  `CHR n` for `n >= 256` is unspecified).  Modelled by a structure.
* `string = char list`.
* `int` = `Int`, with HOL4's `Num`, `ABS`, floor division `/` and `%`.
* words: `'a word` is `BitVec n` (`word8 = BitVec 8`, `word64 = BitVec 64`).
-/

universe u v w

noncomputable section

open Classical

/-! ## characters and strings -/

/- HOL4: string theory, type `char` (`new_type_definition("char", ...)` with
   `ORD : char -> num`, `ORD c < 256`, `CHR : num -> char`) -/
structure char where
  val : Nat
  lt256 : val < 256
  deriving DecidableEq

instance : Inhabited char := ⟨⟨0, by decide⟩⟩

/- HOL4: string theory, `ORD : char -> num` -/
def ORD (c : char) : Nat := c.val

/- HOL4: string theory, `CHR : num -> char`; `ORD (CHR n) = n` for `n < 256`, and `CHR n`
   is unspecified (`ARB`) for `n >= 256`. -/
def CHR (n : Nat) : char := if h : n < 256 then ⟨n, h⟩ else ARB

/- HOL4: string theory, `char_lt a b <=> ORD a < ORD b` (overloaded as `<`), likewise `<=`,
   `>`, `>=`. -/
instance : LT char := ⟨fun a b => ORD a < ORD b⟩
instance : LE char := ⟨fun a b => ORD a ≤ ORD b⟩
instance (a b : char) : Decidable (a < b) := inferInstanceAs (Decidable (ORD a < ORD b))
instance (a b : char) : Decidable (a ≤ b) := inferInstanceAs (Decidable (ORD a ≤ ORD b))

/- HOL4: string theory, `type string = char list` -/
abbrev string : Type := List char

/- HOL4: the list constructor `STRING c s = c :: s` on strings -/
def STRING (c : char) (s : string) : string := c :: s

/-- Embedding of Lean string literals into HOL4 `string`: `HOLstr "abc"` is HOL4's `"abc"`.
(Each Lean character is mapped through `CHR` of its code point, so code points `>= 256` map to
`ARB`; all literals used by the CakeML sources are ASCII.) -/
def HOLstr (s : String) : string := s.toList.map fun c => CHR c.toNat

/-! ## ordering -/

/- HOL4: ternaryComparisons theory, `Datatype: ordering = LESS | EQUAL | GREATER` -/
inductive ordering where
  | LESS
  | EQUAL
  | GREATER
  deriving DecidableEq

/-! ## numbers -/

/- HOL4: arithmetic theory, `DIV2 n = n DIV 2` -/
def DIV2 (n : Nat) : Nat := n / 2

/- HOL4: integer theory, `&n` (`int_of_num`) -/
def int_of_num (n : Nat) : Int := (n : Int)

/- HOL4: integer theory, `Num i = @n. if 0 <= i then i = &n else i = - &n` -/
def Num (i : Int) : Nat :=
  Classical.epsilon (fun n : Nat => if 0 ≤ i then i = (n : Int) else i = -(n : Int))

/- HOL4: integer theory, `ABS n = if n < 0 then ~n else n` -/
def ABS (n : Int) : Int := if n < 0 then -n else n

/- HOL4: integer theory, `int_div` (overloaded as `/`): floor division for `j <> 0`;
   `i / 0` is unspecified. -/
def int_div (i j : Int) : Int := if j = 0 then ARB else Int.fdiv i j

/- HOL4: integer theory, `int_mod` (overloaded as `%`): `i % j = i - i / j * j` for `j <> 0`;
   `i % 0` is unspecified. -/
def int_mod (i j : Int) : Int := if j = 0 then ARB else Int.fmod i j

/-! ## words -/

/- HOL4: words theory, `'a word` of width `dimindex(:'a)` -/
abbrev word (n : Nat) : Type := BitVec n
abbrev word8 : Type := BitVec 8
abbrev word64 : Type := BitVec 64

/- HOL4: words theory, `n2w n` (`n` modulo `2^width`) -/
def n2w {n : Nat} (k : Nat) : BitVec n := BitVec.ofNat n k
/- HOL4: words theory, `w2n w` -/
def w2n {n : Nat} (w : BitVec n) : Nat := w.toNat
/- HOL4: integer_word theory, `i2w i = if i < 0 then -(n2w (Num (-i))) else n2w (Num i)` -/
def i2w {n : Nat} (i : Int) : BitVec n :=
  if i < 0 then -(n2w (Num (-i))) else n2w (Num i)

/- HOL4: words theory, `word_add`, `word_sub`, `word_and`, `word_or`, `word_xor` -/
def word_add {n : Nat} (a b : BitVec n) : BitVec n := a + b
def word_sub {n : Nat} (a b : BitVec n) : BitVec n := a - b
def word_and {n : Nat} (a b : BitVec n) : BitVec n := a &&& b
def word_or {n : Nat} (a b : BitVec n) : BitVec n := a ||| b
def word_xor {n : Nat} (a b : BitVec n) : BitVec n := a ^^^ b

/- HOL4: words theory, `word_lsl w n = FCP i. i < WL /\ n <= i /\ w ' (i - n)` -/
def word_lsl {n : Nat} (w : BitVec n) (k : Nat) : BitVec n := w <<< k
/- HOL4: words theory, `word_lsr w n = FCP i. i + n < WL /\ w ' (i + n)` -/
def word_lsr {n : Nat} (w : BitVec n) (k : Nat) : BitVec n := w >>> k
/- HOL4: words theory, `word_asr w n = FCP i. if WL <= i + n then word_msb w else w ' (i + n)` -/
def word_asr {n : Nat} (w : BitVec n) (k : Nat) : BitVec n := w.sshiftRight k
/- HOL4: words theory, `word_ror w n = FCP i. w ' ((i + n) MOD WL)` -/
def word_ror {n : Nat} (w : BitVec n) (k : Nat) : BitVec n := w.rotateRight k

end
