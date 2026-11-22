/-
  HOL4 library constants: string, numposrep, ASCIInumbers.

  HOL `char` (256 values) is `Candle.char`; HOL `string` (= `char list`) is
  `Candle.string` (= `List char`).  Lean's own `Char`/`String` are NOT used.
  Literals: HOL `#"a"` is `chr!"a"`, HOL `"abc"` is `str!"abc"`.
-/
import CandleLean.Prelude.List

namespace Candle

/- HOL4: string  `char`
   val CHAR_TYPE = new_type_definition("char", CHAR_EXISTS)     (|- ?n. (\n. n < 256) n)
   The type of the natural numbers below 256; `char.val` is the representation (`ORD`). -/
structure char where
  val : Nat
  isLt : val < 256
deriving DecidableEq

instance : Inhabited char := ⟨⟨0, by decide⟩⟩

instance : Repr char := ⟨fun c _ => "chr!" ++ repr (String.singleton (Char.ofNat c.val))⟩

/- HOL4: string  Type string = ``:char list`` -/
abbrev string : Type := List char

/-- `chr!"a"` is the HOL character literal `#"a"` (the character with code 97).
The argument is a Lean string literal with exactly one character, whose code must be
below 256 (use ASCII; escapes such as `chr!"\n"` and `chr!"'"` work). -/
macro:max "chr!" c:str : term => do
  match c.getString.toList with
  | [ch] =>
    let n := ch.toNat
    unless n < 256 do Lean.Macro.throwError "chr!: character code must be below 256"
    `(Candle.char.mk $(Lean.quote n) (by decide))
  | _ => Lean.Macro.throwError "chr!: expected a string literal with exactly one character"

/-- `str!"abc"` is the HOL string literal `"abc"`: the list of its characters
(`[chr!"a", chr!"b", chr!"c"]`).  Only characters with code below 256 are accepted;
use ASCII. -/
macro:max "str!" s:str : term => do
  let mut elems : Array (Lean.TSyntax `term) := #[]
  for c in s.getString.toList do
    let n := c.toNat
    unless n < 256 do Lean.Macro.throwError "str!: character code must be below 256"
    elems := elems.push (← `(Candle.char.mk $(Lean.quote n) (by decide)))
  `(([$elems,*] : Candle.string))

noncomputable section
open Classical

/- HOL4: string  `ORD`  (representation function of the type `char`)
   char_BIJ |- (!a. CHR (ORD a) = a) /\ (!r. (\n. n < 256) r <=> (ORD (CHR r) = r)) -/
def ORD (c : char) : Nat := c.val

/- HOL4: string  `CHR`  (abstraction function of the type `char`)
   char_BIJ |- (!a. CHR (ORD a) = a) /\ (!r. (\n. n < 256) r <=> (ORD (CHR r) = r))
   (`define_new_type_bijections`: `CHR n` is unspecified for `n >= 256`, so `CHR` is an
   arbitrary function that satisfies `!a. CHR (ORD a) = a`.) -/
def CHR : Nat → char := select (fun f => ∀ a, f (ORD a) = a)

/- HOL4: string$CHR_ORD  |- !a. CHR (ORD a) = a   (first conjunct of `char_BIJ`) -/
theorem CHR_ORD (a : char) : CHR (ORD a) = a :=
  select_spec (P := fun f : Nat → char => ∀ a, f (ORD a) = a)
    ⟨fun n => if h : n < 256 then ⟨n, h⟩ else default, fun a => by
      cases a with | mk v h => simp [ORD, h]⟩ a

/- For `n < 256`, `CHR n` is the character with code `n` (so `chr!"a" = CHR 97`). -/
theorem CHR_mk (n : Nat) (h : n < 256) : CHR n = ⟨n, h⟩ := CHR_ORD ⟨n, h⟩

/- HOL4: string$ORD_CHR  |- !r. r < 256 <=> (ORD (CHR r) = r)   (second conjunct of `char_BIJ`) -/
theorem ORD_CHR (r : Nat) : r < 256 ↔ ORD (CHR r) = r :=
  ⟨fun h => by rw [CHR_mk r h]; rfl, fun h => h ▸ (CHR r).isLt⟩

/- HOL4: string$char_lt_def  |- char_lt a b <=> ORD a < ORD b    (HOL overload `a < b`) -/
def char_lt (a b : char) : Prop := ORD a < ORD b

/- HOL4: string$string_lt_def
   |- (string_lt s EMPTYSTRING <=> F) /\
      (string_lt EMPTYSTRING (STRING c s) <=> T) /\
      (string_lt (STRING c1 s1) (STRING c2 s2) <=> c1 < c2 \/ (c1 = c2) /\ string_lt s1 s2)
   (HOL overload `s1 < s2`) -/
def string_lt : string → string → Prop
  | _, [] => False
  | [], _ :: _ => True
  | c1 :: s1, c2 :: s2 => char_lt c1 c2 ∨ c1 = c2 ∧ string_lt s1 s2

/-- Termination lemma for `FIELDS`. -/
theorem LENGTH_SND_SPLITP_le {α : Type} (P : α → Prop) (l : List α) :
    (SND (SPLITP P l)).length ≤ l.length := by
  induction l with
  | nil => simp [SPLITP, SND]
  | cons x l ih =>
    by_cases h : P x
    · simp [SPLITP, h, SND]
    · simp only [SPLITP, h, if_false, SND, List.length_cons] at *
      exact Nat.le_succ_of_le ih

/-- Termination lemma for `FIELDS`. -/
theorem LENGTH_TL_le {α : Type} (l : List α) : (TL l).length ≤ l.length - 1 := by
  cases l <;> simp [TL]

/- HOL4: string$FIELDS_def
   |- (FIELDS P [] = [[]]) /\
      (FIELDS P (h::t) =
         let (l,r) = SPLITP P (h::t) in
           if NULL l then []::FIELDS P (TL r)
           else if NULL r then [l] else l::FIELDS P (TL r)) -/
def FIELDS (P : char → Prop) : string → List string
  | [] => [[]]
  | h :: t =>
    let l := FST (SPLITP P (h :: t))
    let r := SND (SPLITP P (h :: t))
    if NULL l then [] :: FIELDS P (TL r)
    else if NULL r then [l] else l :: FIELDS P (TL r)
termination_by s => s.length
decreasing_by
  all_goals
    have h1 := LENGTH_SND_SPLITP_le P (h :: t)
    have h2 := LENGTH_TL_le (SND (SPLITP P (h :: t)))
    simp only [List.length_cons] at *
    omega

/- HOL4: numposrep$l2n_def  |- (l2n b [] = 0) /\ (l2n b (h::t) = h MOD b + b * l2n b t) -/
def l2n (b : Nat) : List Nat → Nat
  | [] => 0
  | h :: t => h % b + b * l2n b t

/- HOL4: numposrep$n2l_def
   |- n2l b n = if n < b \/ b < 2 then [n MOD b] else n MOD b::n2l b (n DIV b) -/
def n2l (b n : Nat) : List Nat :=
  if n < b ∨ b < 2 then [n % b] else n % b :: n2l b (n / b)
termination_by n
decreasing_by
  rename_i h
  have hb : 2 ≤ b := by omega
  have hn : 0 < n := by omega
  exact Nat.div_lt_self hn hb

/- HOL4: ASCIInumbers$s2n_def  |- s2n b f s = l2n b (MAP f (REVERSE s)) -/
def s2n (b : Nat) (f : char → Nat) (s : string) : Nat := l2n b (MAP f (REVERSE s))

/- HOL4: ASCIInumbers$n2s_def  |- n2s b f n = REVERSE (MAP f (n2l b n)) -/
def n2s (b : Nat) (f : Nat → char) (n : Nat) : string := REVERSE (MAP f (n2l b n))

/- HOL4: ASCIInumbers$HEX
   |- HEX n = if n < 10 then CHR (ORD #"0" + n) else
              if n < 16 then CHR (ORD #"A" + (n - 10)) else CHR 0 -/
def HEX (n : Nat) : char :=
  if n < 10 then CHR (ORD chr!"0" + n) else
  if n < 16 then CHR (ORD chr!"A" + (n - 10)) else CHR 0

/- HOL4: ASCIInumbers$UNHEX
   |- UNHEX c =
        let n = ORD c in
          if ORD #"0" <= n /\ n <= ORD #"9" then n - ORD #"0" else
          if ORD #"a" <= n /\ n <= ORD #"f" then 10 + n - ORD #"a" else
          if ORD #"A" <= n /\ n <= ORD #"F" then 10 + n - ORD #"A" else 0 -/
def UNHEX (c : char) : Nat :=
  let n := ORD c
  if ORD chr!"0" ≤ n ∧ n ≤ ORD chr!"9" then n - ORD chr!"0" else
  if ORD chr!"a" ≤ n ∧ n ≤ ORD chr!"f" then 10 + n - ORD chr!"a" else
  if ORD chr!"A" ≤ n ∧ n ≤ ORD chr!"F" then 10 + n - ORD chr!"A" else 0

/- HOL4: ASCIInumbers$num_from_hex_string_def  |- num_from_hex_string = s2n 16 UNHEX -/
def num_from_hex_string : string → Nat := s2n 16 UNHEX

/- HOL4: ASCIInumbers$num_to_hex_string_def  |- num_to_hex_string = n2s 16 HEX -/
def num_to_hex_string : Nat → string := n2s 16 HEX

end

end Candle
