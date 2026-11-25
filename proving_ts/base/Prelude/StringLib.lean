import CmlTS.Prelude.ListLib

/-
HOL4 library constants from `string`.
-/

namespace CmlTS

noncomputable section

open scoped Classical

/- HOL4: string$char, the type of characters, in bijection (`CHR`/`ORD`) with
   the numbers below 256. -/
abbrev char : Type := Fin 256

/- HOL4: string$string, Type string = ``:char list`` -/
abbrev string : Type := List char

/- HOL4: string$ORD -/
def ORD (c : char) : Nat := c.val

/- HOL4: string$CHR   (ORD (CHR r) = r for r < 256; unspecified for r >= 256) -/
def CHR (n : Nat) : char := if h : n < 256 then ⟨n, h⟩ else ARB

/- HOL4: string$char_lt (overloaded as `<`)   char_lt a b <=> ORD a < ORD b -/
def char_lt (a b : char) : Prop := ORD a < ORD b

/- HOL4: string$TOKENS
   (TOKENS P ([]:string) = []) /\
   (TOKENS P (h::t) =
       let (l,r) = SPLITP P (h::t) in
         if NULL l then TOKENS P (TL r) else l::TOKENS P r) -/
def TOKENS (P : char → Prop) : string → List string
  | [] => []
  | h :: t =>
    if NULL (SPLITP P (h :: t)).1 then TOKENS P (TL (SPLITP P (h :: t)).2)
    else (SPLITP P (h :: t)).1 :: TOKENS P (SPLITP P (h :: t)).2
termination_by l => l.length
decreasing_by
  · have h1 := SPLITP_length_aux P (h :: t)
    rw [TL_length_aux]
    simp at h1 ⊢
    omega
  · rename_i hn
    have h1 := SPLITP_length_aux P t
    simp only [SPLITP] at hn ⊢
    split at hn
    · simp [NULL] at hn
    · rename_i hp
      simp only [hp, if_false, List.length_cons]
      omega

end

end CmlTS

/-- `str!"abc"` is the HOL4 string literal `"abc"` (a list of `CmlTS.char`).
Only characters with code below 256 are allowed. -/
macro:max "str!" s:str : term => do
  let cs := s.getString.toList
  let elems ← cs.mapM fun c => do
    if c.toNat ≥ 256 then Lean.Macro.throwError "character code must be below 256"
    let n := Lean.Syntax.mkNumLit (toString c.toNat)
    `(($n : CmlTS.char))
  let elems := elems.toArray
  `(([$elems,*] : CmlTS.string))
