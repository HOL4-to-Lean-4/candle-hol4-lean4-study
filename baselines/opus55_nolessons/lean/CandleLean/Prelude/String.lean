/-
  HOL4 library constants from the theory `string` (characters and strings).

  HOL4 `char` is a type with exactly 256 values (`ORD c < 256`), so it is NOT
  Lean's `Char`.  HOL4 `string` is `char list`.
-/
import CandleLean.Prelude.List

open Classical

/- HOL4: string$char
   `val CHAR_TYPE = new_type_definition("char", CHAR_EXISTS)` with
   `define_new_type_bijections {ABS="CHR", REP="ORD", ...}`:
   the type of natural numbers below 256; `ORD` is the representation. -/
structure char where
  /-- HOL4: string$ORD (the representation function of `char`). -/
  ORD : Nat
  ORD_lt : ORD < 256
  deriving DecidableEq

export char (ORD)

instance : Inhabited char := ⟨⟨0, by decide⟩⟩

/- HOL4: string$CHR (the abstraction function of `char`)
   char_BIJ: (!a. CHR (ORD a) = a) /\ (!r. r < 256 <=> (ORD (CHR r) = r))
   `CHR n` for `n >= 256` is unspecified: encoded as a choice over all functions
   satisfying the type-bijection theorem. -/
noncomputable def CHR : Nat → char :=
  Classical.epsilon (fun CHR : Nat → char =>
    (∀ a, CHR (ORD a) = a) ∧ (∀ r, r < 256 ↔ ORD (CHR r) = r))

/- HOL4: string$string   `Type string = ``:char list``` -/
abbrev string := List char

/- HOL4: string$char_lt   `char_lt a b <=> ORD a < ORD b`   (HOL4 `<` on chars) -/
def char_lt (a b : char) : Prop := ORD a < ORD b

/- HOL4: string$string_lt   (HOL4 `<` on strings)
   (string_lt s EMPTYSTRING <=> F) /\
   (string_lt EMPTYSTRING (STRING c s) <=> T) /\
   (string_lt (STRING c1 s1) (STRING c2 s2) <=> c1 < c2 \/ (c1 = c2) /\ string_lt s1 s2) -/
def string_lt : string → string → Prop
  | _, [] => False
  | [], _ :: _ => True
  | c1 :: s1, c2 :: s2 => char_lt c1 c2 ∨ (c1 = c2 ∧ string_lt s1 s2)

theorem SPLITP_snd_length_le {α : Type u} (P : α → Prop) :
    ∀ l : List α, (SPLITP P l).2.length ≤ l.length
  | [] => by simp [SPLITP]
  | x :: l => by
    unfold SPLITP
    by_cases h : P x
    · simp [h]
    · simp only [h, if_false]
      have := SPLITP_snd_length_le P l
      simp only [List.length_cons]; omega

/- HOL4: string$FIELDS
   (FIELDS P ([]:string) = [[]]) /\
   (FIELDS P (h::t) =
      let (l,r) = SPLITP P (h::t) in
        if NULL l then []::FIELDS P (TL r)
        else if NULL r then [l] else l::FIELDS P (TL r))
   Termination: WF_REL_TAC `measure (LENGTH o SND)` -/
noncomputable def FIELDS (P : char → Prop) : string → List string
  | [] => [[]]
  | h :: t =>
    let p := SPLITP P (h :: t)
    if NULL p.1 then [] :: FIELDS P (TL p.2)
    else if NULL p.2 then [p.1] else p.1 :: FIELDS P (TL p.2)
termination_by s => s.length
decreasing_by
  all_goals
    have hle := SPLITP_snd_length_le P (h :: t)
    cases hp : (SPLITP P (h :: t)).2 with
    | nil => simp [TL]
    | cons a r =>
      simp only [hp, TL, List.length_cons] at hle ⊢
      omega

/-! Literal helpers (not HOL4 constants): HOL4 character literal `#"c"` is
`CHR n` for the character code `n`; string literal `"abc"` is the list of its
characters.  `str!"abc"` expands to `[CHR 97, CHR 98, CHR 99]` and
`ch!"c"` expands to `CHR 99`. -/
open Lean in
macro:max "str!" s:str : term => do
  let cs := s.getString.toList
  let elems ← cs.toArray.mapM (fun c => `(CHR $(Lean.Syntax.mkNumLit (toString c.toNat))))
  `(([$elems,*] : string))

open Lean in
macro:max "ch!" s:str : term => do
  match s.getString.toList with
  | [c] => `(CHR $(Lean.Syntax.mkNumLit (toString c.toNat)))
  | _ => Macro.throwError "ch! expects a one-character string"
