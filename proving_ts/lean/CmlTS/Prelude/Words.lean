import CmlTS.Prelude.Core

/-
HOL4 library constants from `integer`, `words` and `integer_word`.
`'a word` is `BitVec n` (n for `dimindex (:'a)`); `int` is `Int`.
-/

namespace CmlTS

noncomputable section

open scoped Classical

/-! ### integer -/

/- HOL4: integer$int_of_num (written `&n`) -/
def int_of_num (n : Nat) : Int := (n : Int)

/- HOL4: integer$Num   Num i = @n. if 0 <= i then i = &n else i = - &n
   (the witness is unique: the absolute value) -/
def Num (i : Int) : Nat := i.natAbs

/- HOL4: integer$INT_ABS   ABS n = if n < 0 then ~n else n -/
def INT_ABS (n : Int) : Int := if n < 0 then -n else n

/- HOL4: integer$int_div (infix `/`): floor division, unspecified when the
   divisor is 0.  Specification: ~(j = 0) ==>
     (i / j = if 0 < j then
                if 0 <= i then &(Num i DIV Num j)
                else ~&(Num ~i DIV Num j) + (if Num ~i MOD Num j = 0 then 0 else ~1)
              else
                if 0 <= i then ~&(Num i DIV Num ~j) + (if Num i MOD Num ~j = 0 then 0 else ~1)
                else &(Num ~i DIV Num ~j)) -/
def int_div (i j : Int) : Int := if j = 0 then ARB else Int.fdiv i j

/- HOL4: integer$int_mod (infix `%`), unspecified when the divisor is 0.
   Specification: ~(j = 0) ==> (i % j = i - i / j * j) -/
def int_mod (i j : Int) : Int := if j = 0 then ARB else i - int_div i j * j

/-! ### words -/

variable {m n k : Nat}

/- HOL4: words, Type word8 = ``:8 word``, Type word64 = ``:64 word`` -/
abbrev word8 : Type := BitVec 8
abbrev word64 : Type := BitVec 64

/- HOL4: words$dimword   dimword (:'a) = 2 ** dimindex (:'a) -/
def dimword (n : Nat) : Nat := 2 ^ n

/- HOL4: words$INT_MIN   INT_MIN (:'a) = 2 ** (dimindex (:'a) - 1) -/
def INT_MIN (n : Nat) : Nat := 2 ^ (n - 1)

/- HOL4: words$UINT_MAX   UINT_MAX (:'a) = dimword(:'a) - 1 -/
def UINT_MAX (n : Nat) : Nat := dimword n - 1

/- HOL4: words$INT_MAX   INT_MAX (:'a) = INT_MIN(:'a) - 1 -/
def INT_MAX (n : Nat) : Nat := INT_MIN n - 1

/- HOL4: words$w2n   w2n w = SUM dimindex (\i. SBIT (w ' i) i) -/
def w2n (w : BitVec n) : Nat := w.toNat

/- HOL4: words$n2w   n2w n = FCP i. BIT i n   (i.e. modulo 2 ** dimindex) -/
def n2w (i : Nat) : BitVec n := BitVec.ofNat n i

/- HOL4: words$w2w   w2w w = n2w (w2n w) -/
def w2w (w : BitVec n) : BitVec m := n2w (w2n w)

/- HOL4: words$word_T (written UINT_MAXw)   word_T = n2w (UINT_MAX(:'a)) -/
def word_T : BitVec n := n2w (UINT_MAX n)

/- HOL4: words$word_1comp   word_1comp w = FCP i. ~(w ' i) -/
def word_1comp (w : BitVec n) : BitVec n := ~~~w

/- HOL4: words$word_and   word_and v w = FCP i. (v ' i) /\ (w ' i) -/
def word_and (v w : BitVec n) : BitVec n := v &&& w

/- HOL4: words$word_or   word_or v w = FCP i. (v ' i) \/ (w ' i) -/
def word_or (v w : BitVec n) : BitVec n := v ||| w

/- HOL4: words$word_xor   word_xor v w = FCP i. ~((v ' i) = (w ' i)) -/
def word_xor (v w : BitVec n) : BitVec n := v ^^^ w

/- HOL4: words$word_lsb   word_lsb w = w ' 0 -/
def word_lsb (w : BitVec n) : Prop := w.getLsbD 0 = true

/- HOL4: words$word_msb   word_msb w = w ' (dimindex - 1) -/
def word_msb (w : BitVec n) : Prop := w.getLsbD (n - 1) = true

/- HOL4: words$word_2comp   word_2comp w = n2w (dimword(:'a) - w2n w) -/
def word_2comp (w : BitVec n) : BitVec n := n2w (dimword n - w2n w)

/- HOL4: words$word_add   word_add v w = n2w (w2n v + w2n w) -/
def word_add (v w : BitVec n) : BitVec n := v + w

/- HOL4: words$word_sub   word_sub v w = word_add v (word_2comp w) -/
def word_sub (v w : BitVec n) : BitVec n := v - w

/- HOL4: words$word_ls (infix `<=+`), unsigned comparison
   word_ls a b = let (n,z,c,v) = nzcv a b in ~c \/ z
   (theorem WORD_LS: a <=+ b <=> w2n a <= w2n b) -/
def word_ls (a b : BitVec n) : Prop := w2n a ≤ w2n b

/- HOL4: words$word_lsl
   word_lsl w n = FCP i. i < dimindex /\ n <= i /\ w ' (i - n) -/
def word_lsl (w : BitVec n) (i : Nat) : BitVec n := w <<< i

/- HOL4: words$word_lsr   word_lsr w n = FCP i. i + n < dimindex /\ w ' (i + n) -/
def word_lsr (w : BitVec n) (i : Nat) : BitVec n := w >>> i

/- HOL4: words$word_asr
   word_asr w n = FCP i. if dimindex <= i + n then word_msb w else w ' (i + n) -/
def word_asr (w : BitVec n) (i : Nat) : BitVec n := w.sshiftRight i

/- HOL4: words$word_ror   word_ror w n = FCP i. w ' ((i + n) MOD dimindex) -/
def word_ror (w : BitVec n) (i : Nat) : BitVec n := w.rotateRight i

/- HOL4: words$word_bits
   word_bits h l = \w. FCP i. i + l <= MIN h (dimindex - 1) /\ w ' (i + l) -/
def word_bits (h l : Nat) (w : BitVec n) : BitVec n :=
  n2w ((w2n w / 2 ^ l) % 2 ^ (min h (n - 1) + 1 - l))

/- HOL4: words$word_extract   word_extract h l = w2w o word_bits h l -/
def word_extract (h l : Nat) (w : BitVec n) : BitVec m := w2w (word_bits h l w)

/- HOL4: words$word_join
   word_join v w = let cv = w2w v and cw = w2w w in (cv << dimindex (:'b)) || cw -/
def word_join (v : BitVec m) (w : BitVec n) : BitVec (m + n) :=
  word_or (word_lsl (w2w v) n) (w2w w)

/- HOL4: words$word_concat (infix `@@`)   word_concat v w = w2w (word_join v w) -/
def word_concat (v : BitVec m) (w : BitVec n) : BitVec k := w2w (word_join v w)

/- HOL4: integer_word$i2w
   i2w (i : int) : 'a word = if i < 0 then -(n2w (Num(-i))) else n2w (Num i) -/
def i2w (i : Int) : BitVec n :=
  if i < 0 then word_2comp (n2w (Num (-i))) else n2w (Num i)

end

end CmlTS
