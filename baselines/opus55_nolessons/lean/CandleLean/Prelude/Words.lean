/-
  HOL4 library constants from the theories `fcp`, `words`, `bitstring`.

  HOL4 `:'a word` is `:bool['a]`, a finite Cartesian power with `dimindex(:'a)`
  bits.  Only the numeral index types `:8` and `:32` occur in this development,
  so a word type is indexed by its width `d : Nat` (`dimindex`).  A word is
  represented by its unsigned value `w2n w < 2 ** d`; this is in bijection with
  the HOL4 `FCP` representation (bit `i` of `w` is bit `i` of `w2n w`).
-/
import CandleLean.Prelude.List

open Classical

/- HOL4: words$word   `Type word = “:bool['a]”`   (`d` = `dimindex(:'a)`) -/
structure word (d : Nat) where
  /-- HOL4: words$w2n
      `w2n (w:'a word) = SUM (dimindex(:'a)) (\i. SBIT (w ' i) i)` -/
  w2n : Nat
  w2n_lt : w2n < 2 ^ d
  deriving DecidableEq

export word (w2n)

/- HOL4: `word8` = `:8 word`, `word32` = `:32 word` -/
abbrev word8 := word 8
abbrev word32 := word 32

/- HOL4: words$dimword   `dimword (:'a) = 2 ** dimindex(:'a)` -/
def dimword (d : Nat) : Nat := 2 ^ d

/- HOL4: words$n2w   `(n2w:num->'a word) n = FCP i. BIT i n`
   (bit i of the result is bit i of n for i < dimindex, i.e. the value is
   `n MOD dimword(:'a)`). HOL4 numerals `0w`, `1w`, `nw` are `n2w 0`, `n2w 1`, `n2w n`. -/
def n2w {d : Nat} (n : Nat) : word d := ⟨n % 2 ^ d, Nat.mod_lt _ (Nat.two_pow_pos d)⟩

instance (d : Nat) : Inhabited (word d) := ⟨n2w 0⟩

/- HOL4: fcp$FCP for words: `FCP i. f i` is the word whose bit `i` (for
   `i < dimindex`) is `f i`. -/
noncomputable def FCP {d : Nat} (f : Nat → Prop) : word d :=
  n2w ((List.range d).foldr (fun i acc => (if f i then 2 ^ i else 0) + acc) 0)

/- HOL4: list$PAD_LEFT   `PAD_LEFT c n s = (GENLIST (K c) (n - LENGTH s)) ++ s` -/
def PAD_LEFT {α : Type u} (c : α) (n : Nat) (s : List α) : List α :=
  GENLIST (K c) (n - s.length) ++ s

/- HOL4: bitstring$zero_extend   `zero_extend n v = PAD_LEFT F n v` -/
def zero_extend (n : Nat) (v : List Prop) : List Prop := PAD_LEFT False n v

/- HOL4: bitstring$fixwidth
   fixwidth n v = let l = LENGTH v in if l < n then zero_extend n v else DROP (l - n) v -/
def fixwidth (n : Nat) (v : List Prop) : List Prop :=
  let l := v.length
  if l < n then zero_extend n v else v.drop (l - n)

/- HOL4: bitstring$shiftr   `shiftr (v: bitstring) m = TAKE (LENGTH v - m) v` -/
def shiftr (v : List Prop) (m : Nat) : List Prop := v.take (v.length - m)

/- HOL4: bitstring$field   `field h l v = fixwidth (SUC h - l) (shiftr v l)` -/
def field (h l : Nat) (v : List Prop) : List Prop := fixwidth (h + 1 - l) (shiftr v l)

/- HOL4: bitstring$testbit   `testbit b v = (field b b v = [T])`
   (bit 0 is the last element of the list) -/
def testbit (b : Nat) (v : List Prop) : Prop := field b b v = [True]

/- HOL4: bitstring$v2w   `v2w v : 'a word = FCP i. testbit i v` -/
noncomputable def v2w {d : Nat} (v : List Prop) : word d := FCP (fun i => testbit i v)
