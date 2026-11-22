import CandleLean.Prelude.FMap
/-
  HOL4 library constants, part 4: chars, strings, words, hex strings, sptrees.
  (stringTheory, ASCIInumbersTheory, numposrepTheory, wordsTheory, bitstringTheory, sptreeTheory).
-/
namespace HOL

universe u v w

open Classical

noncomputable section

/-! ## Characters and strings -/

/- HOL4: stringTheory: `char` is the type of the natural numbers < 256, with bijections
   `ORD : char -> num` and `CHR : num -> char` (HOL4: new_type_definition("char", ∃n. n < 256)).
   Not Lean's `Char` (unicode scalar value). -/
structure char where
  val : Nat
  lt : val < 256
  deriving DecidableEq

instance : Inhabited char := ⟨⟨0, by decide⟩⟩

/- HOL4: ORD (the representation function of the char type) -/
def ORD (c : char) : Nat := c.val
/- HOL4: CHR (abstraction function). CHR n for n ≥ 256 is unspecified; here `CHR 0`. -/
def CHR (n : Nat) : char := if h : n < 256 then ⟨n, h⟩ else ⟨0, by decide⟩

theorem char.ext' {a b : char} (h : a.val = b.val) : a = b := by
  cases a; cases b; simp at h; subst h; rfl

/- HOL4: type_abbrev string = char list -/
abbrev string := List char

/-- Convert a Lean `Char` to a HOL4 `char` (code point mod 256; exact for Latin-1). -/
def hchar (c : Char) : char := CHR c.toNat
/-- HOL4 string literal `"abc"` as a `string` (list of HOL4 chars). -/
def hstr (s : String) : string := s.toList.map hchar

/- HOL4: stringTheory char_lt_def: char_lt a b ⇔ ORD a < ORD b  (Overload "<" on char) -/
def char_lt (a b : char) : Prop := ORD a < ORD b
/- HOL4: stringTheory string_lt_def (Overload "<" on string):
   string_lt s [] ⇔ F; string_lt [] (c::s) ⇔ T;
   string_lt (c1::s1) (c2::s2) ⇔ c1 < c2 ∨ (c1 = c2 ∧ string_lt s1 s2) -/
def string_lt : string → string → Prop
  | _, [] => False
  | [], _ :: _ => True
  | c1 :: s1, c2 :: s2 => char_lt c1 c2 ∨ (c1 = c2 ∧ string_lt s1 s2)

theorem SPLITP_length (P : α → Prop) (l : List α) :
    (SPLITP P l).1.length + (SPLITP P l).2.length = l.length := by
  induction l with
  | nil => simp [SPLITP]
  | cons x l ih =>
    unfold SPLITP
    split <;> simp_all <;> omega

/- HOL4: stringTheory FIELDS_def:
   FIELDS P "" = [""];
   FIELDS P (h::t) = let (l,r) = SPLITP P (h::t) in
     if NULL l then []::FIELDS P (TL r) else if NULL r then [l] else l::FIELDS P (TL r) -/
def FIELDS (P : char → Prop) : string → List string
  | [] => [[]]
  | h :: t =>
    if (SPLITP P (h :: t)).1 = [] then
      [] :: FIELDS P (TL (SPLITP P (h :: t)).2)
    else if (SPLITP P (h :: t)).2 = [] then [(SPLITP P (h :: t)).1]
    else (SPLITP P (h :: t)).1 :: FIELDS P (TL (SPLITP P (h :: t)).2)
termination_by s => s.length
decreasing_by
  all_goals
    have h1 := SPLITP_length P (h :: t)
    generalize (SPLITP P (h :: t)).1 = l at *
    generalize (SPLITP P (h :: t)).2 = r at *
    cases r <;> simp [TL, *] at * <;> (try cases l) <;> simp at * <;> omega

/-! ## Hex strings (ASCIInumbersTheory, numposrepTheory) -/

/- HOL4: numposrepTheory l2n_def: l2n b [] = 0; l2n b (h::t) = h MOD b + b * l2n b t -/
def l2n (b : Nat) : List Nat → Nat
  | [] => 0
  | h :: t => h % b + b * l2n b t

/- HOL4: numposrepTheory n2l_def: n2l b n = if n < b ∨ b < 2 then [n MOD b] else n MOD b :: n2l b (n DIV b) -/
def n2l (b n : Nat) : List Nat :=
  if h : n < b ∨ b < 2 then [n % b] else n % b :: n2l b (n / b)
termination_by n
decreasing_by
  have hb : 2 ≤ b := by omega
  have hn : b ≤ n := by omega
  exact Nat.div_lt_self (by omega) (by omega)

/- HOL4: ASCIInumbers s2n_def: s2n b f s = l2n b (MAP f (REVERSE s)) -/
def s2n (b : Nat) (f : char → Nat) (s : string) : Nat := l2n b (s.reverse.map f)
/- HOL4: ASCIInumbers n2s_def: n2s b f n = REVERSE (MAP f (n2l b n)) -/
def n2s (b : Nat) (f : Nat → char) (n : Nat) : string := (n2l b n |>.map f).reverse

/- HOL4: ASCIInumbers HEX:
   HEX n = if n < 10 then CHR (ORD #"0" + n) else if n < 16 then CHR (ORD #"A" + (n - 10)) else CHR 0 -/
def HEX (n : Nat) : char :=
  if n < 10 then CHR (ORD (hchar '0') + n)
  else if n < 16 then CHR (ORD (hchar 'A') + (n - 10)) else CHR 0

/- HOL4: ASCIInumbers UNHEX -/
def UNHEX (c : char) : Nat :=
  let n := ORD c
  if ORD (hchar '0') ≤ n ∧ n ≤ ORD (hchar '9') then n - ORD (hchar '0')
  else if ORD (hchar 'a') ≤ n ∧ n ≤ ORD (hchar 'f') then 10 + n - ORD (hchar 'a')
  else if ORD (hchar 'A') ≤ n ∧ n ≤ ORD (hchar 'F') then 10 + n - ORD (hchar 'A')
  else 0

/- HOL4: ASCIInumbers num_from_hex_string_def: num_from_hex_string = s2n 16 UNHEX -/
def num_from_hex_string : string → Nat := s2n 16 UNHEX
/- HOL4: ASCIInumbers num_to_hex_string_def: num_to_hex_string = n2s 16 HEX -/
def num_to_hex_string : Nat → string := n2s 16 HEX

/-! ## Words (wordsTheory, bitstringTheory) -/

/- HOL4: `'a word` (for a finite numeric type 'a of size n, e.g. `:8`) is `BitVec n`.
   word8 = BitVec 8, word32 = BitVec 32. -/
abbrev word (n : Nat) := BitVec n
abbrev word8 := BitVec 8
abbrev word32 := BitVec 32
/- HOL4: wordsTheory dimword (:'a) = 2 ** dimindex (:'a) -/
def dimword (n : Nat) : Nat := 2 ^ n
/- HOL4: wordsTheory n2w_def (n2w n = word with bit i = BIT i n) -/
def n2w {n : Nat} (k : Nat) : BitVec n := BitVec.ofNat n k
/- HOL4: wordsTheory w2n_def -/
def w2n {n : Nat} (w : BitVec n) : Nat := w.toNat
/- HOL4: bitstringTheory v2n_def: v2n l = l2n 2 (bitify [] l)  (MSB-first bool list; bool = Prop) -/
def v2n (l : List Prop) : Nat := l.foldl (fun acc b => 2 * acc + (if b then 1 else 0)) 0
/- HOL4: bitstringTheory v2w_def: v2w v : 'a word = FCP i. testbit i v
   (bit i is the i-th bit from the right of the MSB-first list; bits beyond the length are F). -/
def v2w {n : Nat} (l : List Prop) : BitVec n := BitVec.ofNat n (v2n l)

/-! ## Sparse trees (sptreeTheory) -/

/- HOL4: sptreeTheory Datatype: spt = LN | LS 'a | BN spt spt | BS spt 'a spt -/
inductive spt (α : Type u) where
  | LN : spt α
  | LS : α → spt α
  | BN : spt α → spt α → spt α
  | BS : spt α → α → spt α → spt α

namespace spt
variable {α : Type u}

/- HOL4: sptreeTheory lookup_def -/
def lookup : Nat → spt α → Option α
  | _, LN => none
  | k, LS a => if k = 0 then some a else none
  | k, BN t1 t2 =>
    if k = 0 then none else lookup ((k - 1) / 2) (if EVEN k then t1 else t2)
  | k, BS t1 a t2 =>
    if k = 0 then some a else lookup ((k - 1) / 2) (if EVEN k then t1 else t2)
termination_by k => k
decreasing_by all_goals omega

/- HOL4: sptreeTheory insert_def -/
def insert : Nat → α → spt α → spt α
  | k, a, LN =>
    if k = 0 then LS a
    else if EVEN k then BN (insert ((k - 1) / 2) a LN) LN
    else BN LN (insert ((k - 1) / 2) a LN)
  | k, a, LS a' =>
    if k = 0 then LS a
    else if EVEN k then BS (insert ((k - 1) / 2) a LN) a' LN
    else BS LN a' (insert ((k - 1) / 2) a LN)
  | k, a, BN t1 t2 =>
    if k = 0 then BS t1 a t2
    else if EVEN k then BN (insert ((k - 1) / 2) a t1) t2
    else BN t1 (insert ((k - 1) / 2) a t2)
  | k, a, BS t1 a' t2 =>
    if k = 0 then BS t1 a t2
    else if EVEN k then BS (insert ((k - 1) / 2) a t1) a' t2
    else BS t1 a' (insert ((k - 1) / 2) a t2)
termination_by k => k
decreasing_by all_goals omega

/- HOL4: sptreeTheory domain_def -/
def domain : spt α → Set Nat
  | LN => ∅
  | LS _ => {0}
  | BN t1 t2 => IMAGE (fun n => 2 * n + 2) (domain t1) ∪ IMAGE (fun n => 2 * n + 1) (domain t2)
  | BS t1 _ t2 => {0} ∪ IMAGE (fun n => 2 * n + 2) (domain t1) ∪ IMAGE (fun n => 2 * n + 1) (domain t2)
end spt

/- HOL4: sptreeTheory Type num_set = ``:unit spt`` -/
abbrev num_set := spt Unit

end

end HOL
