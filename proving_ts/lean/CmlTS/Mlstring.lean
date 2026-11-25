import CmlTS.Misc
import CmlTS.Mllist
import CmlTS.Proofs.Tokens

/-
HOL4 theory `mlstring` (mlstringScript.sml).

The names `concat`, `str`, `compare` and `collate` are in the namespace
`CmlTS.mlstring` (`mlstring.concat`, `mlstring.str`, `mlstring.compare`,
`mlstring.collate`), the other ones directly in `CmlTS`.
-/

namespace CmlTS

noncomputable section

open scoped Classical

/- HOL4:
Datatype:
  mlstring = strlit string
End
val _ = add_strliteral_form{inj=``strlit``, ldelim = "«"}; -/
inductive mlstring
  | strlit (s : string)
  deriving Inhabited

export mlstring (strlit)

/- HOL4:
Definition implode_def:
  implode = strlit
End -/
def implode : string → mlstring := strlit

/- HOL4:
Definition strlen_def[simp]:
  strlen (strlit s) = LENGTH s
End -/
def strlen : mlstring → Nat
  | strlit s => s.length

/- HOL4:
Definition strsub_def[simp]:
  strsub (strlit s) n = EL n s
End -/
def strsub : mlstring → Nat → char
  | strlit s, n => EL n s

/- HOL4:
Definition concat_def:
  concat l = strlit (FLAT (MAP (λs. case s of strlit x => x) l))
End -/
def mlstring.concat (l : List mlstring) : mlstring :=
  strlit (l.map (fun s => match s with | strlit x => x)).flatten

/- HOL4:
Definition explode_aux_def[simp]:
  (explode_aux s n 0 = []) ∧
  (explode_aux s n (SUC len) =
    strsub s n :: (explode_aux s (n + 1) len))
End -/
def explode_aux : mlstring → Nat → Nat → List char
  | _, _, 0 => []
  | s, n, len + 1 => strsub s n :: explode_aux s (n + 1) len

/- HOL4:
Definition explode_def:
  explode s = explode_aux s 0 (strlen s)
End -/
def explode (s : mlstring) : List char := explode_aux s 0 (strlen s)

/- HOL4:
Definition strcat_def:
  strcat s1 s2 = concat [s1; s2]
End
(Overload "^" = ``λx y. strcat x y``) -/
def strcat (s1 s2 : mlstring) : mlstring := mlstring.concat [s1, s2]

/- HOL4:
Definition str_def:
  str (c: char) = implode [c]
End -/
def mlstring.str (c : char) : mlstring := implode [c]

/- HOL4:
Definition tokens_aux_def:
  (tokens_aux f s [] n 0 = []) /\
  (tokens_aux f s (h::t) n 0 = [implode (REVERSE (h::t))]) /\
  (tokens_aux f s [] n (SUC len) =
    if f (strsub s n)
      then tokens_aux f s [] (n + 1) len
    else tokens_aux f s [strsub s n] (n + 1) len) /\
  (tokens_aux f s (h::t) n (SUC len) =
    if f (strsub s n)
      then (implode (REVERSE (h::t)))::(tokens_aux f s [] (n + 1) len)
    else tokens_aux f s (strsub s n::(h::t)) (n + 1) len)
End -/
def tokens_aux (f : char → Prop) (s : mlstring) : List char → Nat → Nat → List mlstring
  | [], _, 0 => []
  | h :: t, _, 0 => [implode (h :: t).reverse]
  | [], n, len + 1 =>
    if f (strsub s n) then tokens_aux f s [] (n + 1) len
    else tokens_aux f s [strsub s n] (n + 1) len
  | h :: t, n, len + 1 =>
    if f (strsub s n) then implode (h :: t).reverse :: tokens_aux f s [] (n + 1) len
    else tokens_aux f s (strsub s n :: h :: t) (n + 1) len

/- HOL4:
Definition tokens_def:
 tokens f s = tokens_aux f s [] 0 (strlen s)
End -/
def tokens (f : char → Prop) (s : mlstring) : List mlstring := tokens_aux f s [] 0 (strlen s)

/- HOL4:
Definition isStringThere_aux_def:
  (isStringThere_aux s1 s2 s1i s2i 0 = T) /\
  (isStringThere_aux s1 s2 s1i s2i (SUC len) =
    if strsub s1 s1i = strsub s2 s2i
      then isStringThere_aux s1 s2 (s1i + 1) (s2i + 1) len
    else F)
End -/
def isStringThere_aux (s1 s2 : mlstring) : Nat → Nat → Nat → Prop
  | _, _, 0 => True
  | s1i, s2i, len + 1 =>
    if strsub s1 s1i = strsub s2 s2i then isStringThere_aux s1 s2 (s1i + 1) (s2i + 1) len
    else False

/- HOL4:
Definition isSubstring_aux_def:
  (isSubstring_aux s1 s2 lens1 n 0 = F) /\
  (isSubstring_aux s1 s2 lens1 n (SUC len) =
    if (isStringThere_aux s1 s2 0 n lens1)
      then T
    else isSubstring_aux s1 s2 lens1 (n + 1) len)
End -/
def isSubstring_aux (s1 s2 : mlstring) (lens1 : Nat) : Nat → Nat → Prop
  | _, 0 => False
  | n, len + 1 =>
    if isStringThere_aux s1 s2 0 n lens1 then True
    else isSubstring_aux s1 s2 lens1 (n + 1) len

/- HOL4:
Definition isSubstring_def:
  isSubstring s1 s2 =
  if strlen s1 <= strlen s2
    then isSubstring_aux s1 s2 (strlen s1) 0 ((strlen s2) - (strlen s1) + 1)
  else F
End -/
def isSubstring (s1 s2 : mlstring) : Prop :=
  if strlen s1 ≤ strlen s2 then
    isSubstring_aux s1 s2 (strlen s1) 0 (strlen s2 - strlen s1 + 1)
  else False

/- HOL4:
Definition compare_aux_def:
  compare_aux (s1: mlstring) s2 ord start len =
    if len = 0n then
      ord
    else if strsub s2 start < strsub s1 start
      then GREATER
    else if strsub s1 start < strsub s2 start
      then LESS
    else compare_aux s1 s2 ord (start + 1) (len - 1)
End -/
def compare_aux (s1 s2 : mlstring) (ord : ordering) (start len : Nat) : ordering :=
  if len = 0 then ord
  else if char_lt (strsub s2 start) (strsub s1 start) then ordering.GREATER
  else if char_lt (strsub s1 start) (strsub s2 start) then ordering.LESS
  else compare_aux s1 s2 ord (start + 1) (len - 1)
termination_by len

/- HOL4:
Definition compare_def:
  compare s1 s2 = if (strlen s1) < (strlen s2)
    then compare_aux s1 s2 LESS 0 (strlen s1)
  else if (strlen s2) < (strlen s1)
    then compare_aux s1 s2 GREATER 0 (strlen s2)
  else compare_aux s1 s2 EQUAL 0 (strlen s2)
End -/
def mlstring.compare (s1 s2 : mlstring) : ordering :=
  if strlen s1 < strlen s2 then compare_aux s1 s2 ordering.LESS 0 (strlen s1)
  else if strlen s2 < strlen s1 then compare_aux s1 s2 ordering.GREATER 0 (strlen s2)
  else compare_aux s1 s2 ordering.EQUAL 0 (strlen s2)

/- HOL4:
Definition mlstring_lt_def:
  mlstring_lt s1 s2 ⇔ (compare s1 s2 = LESS)
End -/
def mlstring_lt (s1 s2 : mlstring) : Prop := mlstring.compare s1 s2 = ordering.LESS

/- HOL4:
Definition mlstring_le_def:
  mlstring_le s1 s2 ⇔ (compare s1 s2 ≠ GREATER)
End -/
def mlstring_le (s1 s2 : mlstring) : Prop := mlstring.compare s1 s2 ≠ ordering.GREATER

/- HOL4:
Definition mlstring_gt_def:
  mlstring_gt s1 s2 ⇔ (compare s1 s2 = GREATER)
End -/
def mlstring_gt (s1 s2 : mlstring) : Prop := mlstring.compare s1 s2 = ordering.GREATER

/- HOL4:
Definition mlstring_ge_def:
  mlstring_ge s1 s2 ⇔ (compare s1 s2 <> LESS)
End -/
def mlstring_ge (s1 s2 : mlstring) : Prop := mlstring.compare s1 s2 ≠ ordering.LESS

/- HOL4:
Definition collate_aux_def:
  (collate_aux f (s1: mlstring) s2 ord n 0 = ord) /\
  (collate_aux f s1 s2 ord n (SUC len) =
    if f (strsub s1 n) (strsub s2 n) = EQUAL
      then collate_aux f s1 s2 ord (n + 1) len
    else f (strsub s1 n) (strsub s2 n))
End -/
def collate_aux (f : char → char → ordering) (s1 s2 : mlstring) (ord : ordering) :
    Nat → Nat → ordering
  | _, 0 => ord
  | n, len + 1 =>
    if f (strsub s1 n) (strsub s2 n) = ordering.EQUAL then collate_aux f s1 s2 ord (n + 1) len
    else f (strsub s1 n) (strsub s2 n)

/- HOL4:
Definition collate_def:
  collate f s1 s2 =
  if (strlen s1) < (strlen s2)
    then collate_aux f s1 s2 LESS 0 (strlen s1)
  else if (strlen s2) < (strlen s1)
    then collate_aux f s1 s2 GREATER 0 (strlen s2)
  else collate_aux f s1 s2 EQUAL 0 (strlen s2)
End -/
def mlstring.collate (f : char → char → ordering) (s1 s2 : mlstring) : ordering :=
  if strlen s1 < strlen s2 then collate_aux f s1 s2 ordering.LESS 0 (strlen s1)
  else if strlen s2 < strlen s1 then collate_aux f s1 s2 ordering.GREATER 0 (strlen s2)
  else collate_aux f s1 s2 ordering.EQUAL 0 (strlen s2)

/- HOL4:
Datatype:
  app_list_ann = BigList ('a list)
               | BigAppend app_list_ann app_list_ann
               | Small ('a app_list)
End -/
inductive app_list_ann (α : Type)
  | BigList (l : List α)
  | BigAppend (l1 l2 : app_list_ann α)
  | Small (l : app_list α)

/- HOL4:
Definition char_to_word8_def[simp]:
  char_to_word8 (c:char) = n2w (ORD c) :word8
End -/
def char_to_word8 (c : char) : word8 := n2w (ORD c)

/- HOL4:
Definition word8_to_char_def[simp]:
  word8_to_char (w:word8) = CHR (w2n w) : char
End -/
def word8_to_char (w : word8) : char := CHR (w2n w)

/- HOL4:
Definition empty_ffi_def:
  empty_ffi (s:mlstring) = ()
End -/
def empty_ffi (_ : mlstring) : Unit := ()

/-! ### Theorems -/

/- HOL4:
Theorem explode_aux_thm:
   ∀max n ls.
    (n + max = LENGTH ls) ⇒
    (explode_aux (strlit ls) n max = DROP n ls) -/
theorem explode_aux_thm :
    ∀ (max n : Nat) (ls : string),
      n + max = ls.length →
      explode_aux (strlit ls) n max = ls.drop n := by
  intro max
  induction max with
  | zero =>
    intro n ls h
    rw [explode_aux, List.drop_eq_nil_of_le (by omega)]
  | succ k ih =>
    intro n ls h
    have hn : n < ls.length := by omega
    rw [explode_aux, ih (n + 1) ls (by omega), strsub, Aux.EL_getElem hn,
      List.drop_eq_getElem_cons hn]

/- HOL4:
Theorem explode_thm[simp]:
   explode (strlit ls) = ls -/
theorem explode_thm {ls : string} : explode (strlit ls) = ls := by
  rw [explode, explode_aux_thm _ _ _ (by simp [strlen])]; rfl

/- HOL4:
Theorem explode_implode[simp]:
   ∀x. explode (implode x) = x -/
theorem explode_implode : ∀ x : string, explode (implode x) = x := fun _ => explode_thm

/- HOL4:
Theorem implode_explode[simp]:
   ∀x. implode (explode x) = x -/
theorem implode_explode : ∀ x : mlstring, implode (explode x) = x := by
  rintro ⟨s⟩; rw [explode_thm]; rfl

/- HOL4:
Theorem explode_11[simp]:
   ∀s1 s2. (explode s1 = explode s2) ⇔ (s1 = s2) -/
theorem explode_11 : ∀ s1 s2 : mlstring, explode s1 = explode s2 ↔ s1 = s2 := by
  rintro ⟨s1⟩ ⟨s2⟩; rw [explode_thm, explode_thm]; simp

theorem Aux.tokens_aux_tok (P : char → Prop) (s : string) (len : Nat) :
    ∀ (ss : List char) (n : Nat), n + len = s.length →
      (tokens_aux P (strlit s) ss n len).map explode = Aux.tok P ss (s.drop n) := by
  induction len with
  | zero =>
    intro ss n h
    rw [List.drop_eq_nil_of_le (by omega)]
    cases ss with
    | nil => simp [tokens_aux, Aux.tok, Aux.TOKENS_nil]
    | cons a t => simp [tokens_aux, Aux.tok, explode_implode]
  | succ len ih =>
    intro ss n h
    have hn : n < s.length := by omega
    have hd : s.drop n = EL n s :: s.drop (n + 1) := by
      rw [List.drop_eq_getElem_cons hn, Aux.EL_getElem hn]
    by_cases hp : P (EL n s)
    · cases ss with
      | nil =>
        simp only [tokens_aux, strsub, if_pos hp]
        rw [ih _ _ (by omega), hd]
        simp only [Aux.tok]
        rw [Aux.TOKENS_pos hp]
      | cons a t =>
        simp only [tokens_aux, strsub, if_pos hp, List.map_cons, explode_implode]
        rw [ih _ _ (by omega), hd]
        simp only [Aux.tok, if_pos hp]
        rw [Aux.TOKENS_pos hp]
    · rw [hd, Aux.tok_step hp, ← ih _ _ (by omega)]
      cases ss with
      | nil => simp only [tokens_aux, strsub, if_neg hp]
      | cons a t => simp only [tokens_aux, strsub, if_neg hp]

/- HOL4:
Theorem TOKENS_eq_tokens_aux:
   !P ls ss n len. (n + len = LENGTH (explode ls)) ==>
      (MAP explode (tokens_aux P ls ss n len) = case ss of
        | (h::t) => if (len <> 0) /\ ($~ (P (EL n (explode ls)))) then
          (REVERSE (h::t) ++ HD (TOKENS P (DROP n (explode ls))))::TL (TOKENS P (DROP n (explode ls)))
           else if (len <> 0) then
              REVERSE (h::t)::(TOKENS P (DROP n (explode ls)))
           else [REVERSE(h::t)]
        | [] => (TOKENS P (DROP n (explode ls)))) -/
theorem TOKENS_eq_tokens_aux :
    ∀ (P : char → Prop) (ls : mlstring) (ss : List char) (n len : Nat),
      n + len = (explode ls).length →
      (tokens_aux P ls ss n len).map explode =
        (match ss with
        | h :: t =>
          if len ≠ 0 ∧ ¬ P (EL n (explode ls)) then
            ((h :: t).reverse ++ HD (TOKENS P ((explode ls).drop n))) ::
              TL (TOKENS P ((explode ls).drop n))
          else if len ≠ 0 then
            (h :: t).reverse :: TOKENS P ((explode ls).drop n)
          else [(h :: t).reverse]
        | [] => TOKENS P ((explode ls).drop n)) := by
  rintro P ⟨s⟩ ss n len h
  rw [explode_thm] at h ⊢
  rw [Aux.tokens_aux_tok P s len ss n h]
  cases ss with
  | nil => rfl
  | cons a t =>
    cases len with
    | zero =>
      rw [List.drop_eq_nil_of_le (by omega)]
      simp [Aux.tok]
    | succ len =>
      have hn : n < s.length := by omega
      have hd : s.drop n = EL n s :: s.drop (n + 1) := by
        rw [List.drop_eq_getElem_cons hn, Aux.EL_getElem hn]
      rw [hd]
      by_cases hp : P (EL n s)
      · simp [Aux.tok, hp]
      · simp [Aux.tok, hp]

/- HOL4:
Theorem TOKENS_eq_tokens:
   !P ls.(MAP explode (tokens P ls) = TOKENS P (explode ls)) -/
theorem TOKENS_eq_tokens :
    ∀ (P : char → Prop) (ls : mlstring),
      (tokens P ls).map explode = TOKENS P (explode ls) := by
  rintro P ⟨s⟩
  rw [explode_thm, tokens, Aux.tokens_aux_tok P s _ [] 0 (by simp [strlen])]
  rfl

end

end CmlTS

/-- `ml!"abc"` is the HOL4 mlstring literal `«abc»`. -/
macro:max "ml!" s:str : term =>`((CmlTS.mlstring.strlit (str! $s) : CmlTS.mlstring))
