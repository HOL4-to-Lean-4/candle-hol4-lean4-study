import CmlTS.Prelude.List
/-
  HOL4 library constants: `string`, `words`, `integer`, `integer_word`.
-/
set_option autoImplicit false

namespace CmlTS
open Classical

/- HOL4: string$char, the type with 256 elements in bijection (CHR, ORD) with {n | n < 256}. -/
abbrev char : Type := Fin 256

/- HOL4: string$ORD -/
abbrev ORD (c : char) : Nat := c.val

/- HOL4: string$CHR:  (!a. CHR (ORD a) = a) /\ (!r. r < 256 <=> (ORD (CHR r) = r))
   Unspecified for arguments >= 256. -/
noncomputable def CHR (n : Nat) : char := if h : n < 256 then ⟨n, h⟩ else ARB

/- HOL4: string$char_lt, char_le, char_gt, char_ge (overloads <, <=, >, >=) compare ORDs;
   this is the order of `Fin 256`. -/

/- HOL4: Type string = ``:char list`` -/
abbrev string : Type := List char

/- HOL4: string literals "..." (lists of ASCII characters). -/
def str_lit (s : String) : string := s.toList.map fun c => Fin.ofNat 256 c.toNat

/- HOL4: string$TOKENS:
   (TOKENS P ([]:string) = []) /\
   (TOKENS P (h::t) =
       let (l,r) = SPLITP P (h::t) in
         if NULL l then TOKENS P (TL r) else l::TOKENS P r) -/
theorem SPLITP_length {α : Type} (P : α → Prop) (l : List α) :
    (SPLITP P l).2.length ≤ l.length := by
  induction l with
  | nil => simp [SPLITP]
  | cons x l ih => simp only [SPLITP]; split <;> simp <;> omega

theorem SPLITP_length_lt {α : Type} (P : α → Prop) (h : α) (t : List α)
    (hn : ¬ NULL (SPLITP P (h :: t)).1) : (SPLITP P (h :: t)).2.length ≤ t.length := by
  simp only [SPLITP] at hn ⊢
  split
  · rename_i hp; simp [hp, NULL] at hn
  · exact SPLITP_length P t

noncomputable def TOKENS (P : char → Prop) : string → List string
  | [] => []
  | h :: t =>
    if NULL (SPLITP P (h :: t)).1 then
      TOKENS P (SPLITP P (h :: t)).2.tail
    else
      (SPLITP P (h :: t)).1 :: TOKENS P (SPLITP P (h :: t)).2
termination_by s => s.length
decreasing_by
  · have := SPLITP_length P (h :: t)
    simp at this ⊢
    omega
  · have := SPLITP_length_lt P h t (by assumption)
    simp
    omega

/- HOL4: integer$Num:  Num (i:int) = @n. if 0 <= i then i = &n else i = - &n -/
def Num (i : Int) : Nat := i.natAbs

/- HOL4: integer$ABS:  ABS n = if n < 0 then ~n else n -/
def ABS (i : Int) : Int := if i < 0 then -i else i

/- HOL4: integer$int_div (infix /), for j <> 0:
   i / j = if 0 < j then if 0 <= i then &(Num i DIV Num j)
                         else ~&(Num ~i DIV Num j) + (if Num ~i MOD Num j = 0 then 0 else ~1)
           else if 0 <= i then ~&(Num i DIV Num ~j) + (if Num i MOD Num ~j = 0 then 0 else ~1)
                else &(Num ~i DIV Num ~j)
   i.e. division rounding towards minus infinity; unspecified for j = 0. -/
noncomputable def int_div (i j : Int) : Int := if j = 0 then ARB else Int.fdiv i j

/- HOL4: integer$int_mod (infix %):  for j <> 0, i % j = i - i / j * j; unspecified for j = 0. -/
noncomputable def int_mod (i j : Int) : Int := if j = 0 then ARB else i - int_div i j * j

/- HOL4: words$word8 = 8 word, words$word64 = 64 word -/
abbrev word8 : Type := BitVec 8
abbrev word64 : Type := BitVec 64

/- HOL4: words$n2w, words$w2n, integer_word$i2w -/
abbrev n2w {n : Nat} (k : Nat) : BitVec n := BitVec.ofNat n k
abbrev w2n {n : Nat} (w : BitVec n) : Nat := w.toNat

/- HOL4: integer_word$i2w:  i2w i = if i < 0 then -(n2w (Num(-i))) else n2w (Num i) -/
def i2w {n : Nat} (i : Int) : BitVec n := if i < 0 then -(n2w (Num (-i))) else n2w (Num i)

/- HOL4: words$word_add, word_sub, word_and, word_or, word_xor -/
abbrev word_add {n : Nat} (v w : BitVec n) : BitVec n := v + w
abbrev word_sub {n : Nat} (v w : BitVec n) : BitVec n := v - w
abbrev word_and {n : Nat} (v w : BitVec n) : BitVec n := v &&& w
abbrev word_or {n : Nat} (v w : BitVec n) : BitVec n := v ||| w
abbrev word_xor {n : Nat} (v w : BitVec n) : BitVec n := v ^^^ w

/- HOL4: words$word_lsl:  word_lsl w n = FCP i. i < dimindex /\ n <= i /\ w ' (i - n) -/
abbrev word_lsl {n : Nat} (w : BitVec n) (k : Nat) : BitVec n := w <<< k

/- HOL4: words$word_lsr:  word_lsr w n = FCP i. i + n < dimindex /\ w ' (i + n) -/
abbrev word_lsr {n : Nat} (w : BitVec n) (k : Nat) : BitVec n := w >>> k

/- HOL4: words$word_asr:
   word_asr w n = FCP i. if dimindex <= i + n then word_msb w else w ' (i + n) -/
abbrev word_asr {n : Nat} (w : BitVec n) (k : Nat) : BitVec n := w.sshiftRight k

/- HOL4: words$word_ror:  word_ror w n = FCP i. w ' ((i + n) MOD dimindex) -/
abbrev word_ror {n : Nat} (w : BitVec n) (k : Nat) : BitVec n := w.rotateRight k

end CmlTS
