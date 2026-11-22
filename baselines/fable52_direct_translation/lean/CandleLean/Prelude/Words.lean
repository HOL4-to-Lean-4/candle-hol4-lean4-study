/-
  HOL4 library constants: words, bitstring (only what the targets need).

  HOL `:N word` (N a numeral type, `dimindex(:N) = N`) is `word N` (= `BitVec N`):
  `word8` is `BitVec 8`, `word32` is `BitVec 32`.  HOL `bitstring` (= `bool list`,
  most significant bit first) is `List Prop`.
-/
import CandleLean.Prelude.List

namespace Candle

noncomputable section
open Classical

/- HOL4: words  `:'a word` (= `:bool['a]`), for `'a` a numeral type with `dimindex(:'a) = n` -/
abbrev word (n : Nat) : Type := BitVec n

/- HOL4: words  Type word8 = “:8 word” -/
abbrev word8 : Type := word 8

/- HOL4: words  Type word32 = “:32 word” -/
abbrev word32 : Type := word 32

/- HOL4: words$dimword_def  |- dimword (:'a) = 2 ** dimindex (:'a)
   (the type argument `(:N)` is the natural number `N`) -/
def dimword (n : Nat) : Nat := 2 ^ n

/- HOL4: words$n2w_def  |- n2w n = FCP i. BIT i n
   (the word with value `n MOD dimword`; HOL numerals `0w`, `1w` are `n2w 0`, `n2w 1`) -/
def n2w {n : Nat} (k : Nat) : word n := BitVec.ofNat n k

/- HOL4: words$w2n_def  |- w2n w = SUM (dimindex (:'a)) (\i. SBIT (w ' i) i)
   (the value of the word, below `dimword`) -/
def w2n {n : Nat} (w : word n) : Nat := BitVec.toNat w

/- HOL4: bitstring  Type bitstring = “:bool list” -/
abbrev bitstring : Type := List Prop

/- HOL4: bitstring$zero_extend_def  |- zero_extend n v = PAD_LEFT F n v -/
def zero_extend (n : Nat) (v : bitstring) : bitstring := PAD_LEFT False n v

/- HOL4: bitstring$fixwidth_def
   |- fixwidth n v = let l = LENGTH v in if l < n then zero_extend n v else DROP (l - n) v -/
def fixwidth (n : Nat) (v : bitstring) : bitstring :=
  let l := LENGTH v
  if l < n then zero_extend n v else DROP (l - n) v

/- HOL4: bitstring$shiftr_def  |- shiftr v m = TAKE (LENGTH v - m) v -/
def shiftr (v : bitstring) (m : Nat) : bitstring := TAKE (LENGTH v - m) v

/- HOL4: bitstring$field_def  |- field h l v = fixwidth (SUC h - l) (shiftr v l) -/
def field (h l : Nat) (v : bitstring) : bitstring := fixwidth (SUC h - l) (shiftr v l)

/- HOL4: bitstring$testbit_def  |- testbit b v <=> (field b b v = [T]) -/
def testbit (b : Nat) (v : bitstring) : Prop := field b b v = [True]

/-- The number below `2 ^ n` whose bit `i` (for `i < n`) is `f i`: the value of the
HOL word `FCP i. f i` at a word type of dimension `n`. -/
def FCP_value (f : Nat → Prop) : Nat → Nat
  | 0 => 0
  | n + 1 => FCP_value f n + (if f n then 2 ^ n else 0)

/- HOL4: bitstring$v2w_def  |- v2w v = FCP i. testbit i v -/
def v2w {n : Nat} (v : bitstring) : word n :=
  BitVec.ofNat n (FCP_value (fun i => testbit i v) n)

end

end Candle
