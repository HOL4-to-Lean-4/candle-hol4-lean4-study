import CandleLean.Prelude.List

/-!
# HOL4 library: words, bitstring (only what the targets need)

HOL4 `:'a word` (a finite Cartesian product `bool['a]` with `dimindex(:'a)` bits) is modelled by
Lean's `BitVec (dimindex(:'a))`: `word8 = BitVec 8`, `word32 = BitVec 32`.
`n2w n` is `BitVec.ofNat _ n` (HOL4 `FCP i. BIT i n`, i.e. `n MOD dimword`), and `w2n w` is
`BitVec.toNat w` (HOL4 `SUM (dimindex) (\i. SBIT (w ' i) i)`).  HOL4 numerals `0w`, `1w` are
`n2w 0`, `n2w 1` (equivalently the Lean literals `0`, `1` at type `BitVec n`).
-/

namespace HOL

open Classical

noncomputable section

/- HOL4: words$word (type)    :'a word  =  bool['a]  (here indexed by dimindex(:'a)) -/
abbrev word (n : Nat) := BitVec n

/- HOL4: words$word8 (type abbreviation)    word8 = :bool[8] -/
abbrev word8 := BitVec 8

/- HOL4: words$word32 (type abbreviation)    word32 = :bool[32] -/
abbrev word32 := BitVec 32

/- HOL4: fcp$dimindex    dimindex(:'a) = if FINITE UNIV then CARD UNIV else 1
   (for the numeric types used here, dimindex(:n) = n) -/
@[reducible] def dimindex (n : Nat) : Nat := n

/- HOL4: words$dimword    dimword (:'a) = 2 ** dimindex (:'a) -/
@[reducible] def dimword (n : Nat) : Nat := 2 ^ dimindex n

/- HOL4: words$n2w    (n2w:num->'a word) n = FCP i. BIT i n -/
def n2w {n : Nat} (k : Nat) : BitVec n := BitVec.ofNat n k

/- HOL4: words$w2n    w2n (w:'a word) = SUM (dimindex(:'a)) (\i. SBIT (w ' i) i) -/
def w2n {n : Nat} (w : BitVec n) : Nat := w.toNat

/-- `FCP i. f i` for an `n`-bit word: bit `i` (for `i < n`) is `f i`. -/
def FCP_bits : (n : Nat) → (Nat → Prop) → Nat
  | 0, _ => 0
  | k + 1, f => FCP_bits k f + (if f k then 2 ^ k else 0)

/- HOL4: fcp$FCP (restricted to words)    FCP i. f i   (the word whose bit i is f i) -/
def FCP {n : Nat} (f : Nat → Prop) : BitVec n := BitVec.ofNat n (FCP_bits n f)

/-! ### bitstring  (HOL4 `bitstring = :bool list`, MSB first; here `List Prop`) -/

/- HOL4: bitstring$bitstring    Type bitstring = “:bool list” -/
abbrev bitstring := List Prop

/- HOL4: bitstring$zero_extend    zero_extend n v = PAD_LEFT F n v -/
def zero_extend (n : Nat) (v : bitstring) : bitstring := PAD_LEFT False n v

/- HOL4: bitstring$fixwidth
     fixwidth n v = let l = LENGTH v in if l < n then zero_extend n v else DROP (l - n) v -/
def fixwidth (n : Nat) (v : bitstring) : bitstring :=
  let l := v.length
  if l < n then zero_extend n v else v.drop (l - n)

/- HOL4: bitstring$shiftr    shiftr (v: bitstring) m = TAKE (LENGTH v - m) v -/
def shiftr (v : bitstring) (m : Nat) : bitstring := v.take (v.length - m)

/- HOL4: bitstring$field    field h l v = fixwidth (SUC h - l) (shiftr v l) -/
def field (h l : Nat) (v : bitstring) : bitstring := fixwidth (h + 1 - l) (shiftr v l)

/- HOL4: bitstring$testbit    testbit b v = (field b b v = [T]) -/
def testbit (b : Nat) (v : bitstring) : Prop := field b b v = [True]

/- HOL4: bitstring$v2w    v2w v : 'a word = FCP i. testbit i v -/
def v2w {n : Nat} (v : bitstring) : BitVec n := FCP (fun i => testbit i v)

end

end HOL
