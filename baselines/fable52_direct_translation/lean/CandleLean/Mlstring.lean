/-
  HOL4 theory `mlstring` (basis/pure/mlstringScript.sml): the definitions the targets need.
-/
import CandleLean.Misc
import CandleLean.Mllist

namespace Candle

/- HOL4:
Datatype:
  mlstring = implode string
End
val _ = add_strliteral_form{inj=“implode”, ldelim = "«"};
   (HOL `«abc»` is `ml!"abc"`, i.e. `implode str!"abc"`) -/
inductive mlstring where
  | implode : string → mlstring
deriving DecidableEq

export mlstring (implode)

instance : Inhabited mlstring := ⟨implode []⟩

/- HOL4:
Overload strlit[inferior] = “implode” -/
@[match_pattern] abbrev strlit (s : string) : mlstring := implode s

/-- `ml!"abc"` is the HOL mlstring literal `«abc»` (= `implode "abc"`, `strlit "abc"`):
it expands to `implode str!"abc"`. -/
macro:max "ml!" s:str : term => `(Candle.mlstring.implode (str! $s))

noncomputable section
open Classical

/- HOL4:
Definition strlen_def[simp]:
  strlen (strlit s) = LENGTH s
End -/
def strlen : mlstring → Nat
  | strlit s => LENGTH s

/- HOL4:
Definition strsub_def[simp]:
  strsub (strlit s) n = EL n s
End -/
def strsub : mlstring → Nat → char
  | strlit s, n => EL n s

/- HOL4:
Definition substring_def:
  substring (strlit s) off len = strlit (if off + len ≤ LENGTH s then SEG len off s
                                         else if off <= LENGTH s then DROP off s
                                         else "")
End -/
def substring : mlstring → Nat → Nat → mlstring
  | strlit s, off, len =>
    strlit (if off + len ≤ LENGTH s then SEG len off s
            else if off ≤ LENGTH s then DROP off s
            else str!"")

/- HOL4:
Definition concat_def:
  concat l = strlit (FLAT (MAP (λs. case s of strlit x => x) l))
End -/
def concat (l : List mlstring) : mlstring :=
  strlit (FLAT (MAP (fun s => match s with | strlit x => x) l))

/- HOL4:
Definition explode_aux_def[simp]:
  (explode_aux s n 0 = []) ∧
  (explode_aux s n (SUC len) =
    strsub s n :: (explode_aux s (n + 1) len))
End -/
def explode_aux (s : mlstring) : Nat → Nat → string
  | _, 0 => []
  | n, len + 1 => strsub s n :: explode_aux s (n + 1) len

/- HOL4:
Definition explode_def:
  explode s = explode_aux s 0 (strlen s)
End -/
def explode (s : mlstring) : string := explode_aux s 0 (strlen s)

/- HOL4:
Definition strcat_def:
  strcat s1 s2 = concat [s1; s2]
End
val _ = Parse.add_infix("^",480,Parse.LEFT)
Overload "^" = ``λx y. strcat x y``
   (HOL `s1 ^ s2` on mlstrings is `strcat s1 s2`) -/
def strcat (s1 s2 : mlstring) : mlstring := concat [s1, s2]

/- HOL4:
Definition chr_to_str_def:
  chr_to_str (c: char) = implode [c]
End
Overload toString = “chr_to_str”
   (HOL `toString c` on a `char` is `chr_to_str c`) -/
def chr_to_str (c : char) : mlstring := implode [c]

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
End
   (`<` on `char` is `char_lt`) -/
def compare_aux (s1 s2 : mlstring) (ord : ordering) (start len : Nat) : ordering :=
  if len = 0 then
    ord
  else if char_lt (strsub s2 start) (strsub s1 start)
    then GREATER
  else if char_lt (strsub s1 start) (strsub s2 start)
    then LESS
  else compare_aux s1 s2 ord (start + 1) (len - 1)
termination_by len
decreasing_by omega

/- HOL4:
Definition compare_def:
  compare s1 s2 = if (strlen s1) < (strlen s2)
    then compare_aux s1 s2 LESS 0 (strlen s1)
  else if (strlen s2) < (strlen s1)
    then compare_aux s1 s2 GREATER 0 (strlen s2)
  else compare_aux s1 s2 EQUAL 0 (strlen s2)
End -/
def compare (s1 s2 : mlstring) : ordering :=
  if strlen s1 < strlen s2
    then compare_aux s1 s2 LESS 0 (strlen s1)
  else if strlen s2 < strlen s1
    then compare_aux s1 s2 GREATER 0 (strlen s2)
  else compare_aux s1 s2 EQUAL 0 (strlen s2)

/- HOL4:
Definition mlstring_lt_def:
  mlstring_lt s1 s2 ⇔ (compare s1 s2 = LESS)
End
Overload "<" = ``λx y. mlstring_lt x y``
   (HOL `s1 < s2` on mlstrings is `mlstring_lt s1 s2`) -/
def mlstring_lt (s1 s2 : mlstring) : Prop := compare s1 s2 = LESS

/- HOL4:
Datatype:
  app_list_ann = BigList ('a list)
               | BigAppend app_list_ann app_list_ann
               | Small ('a app_list)
End -/
inductive app_list_ann (α : Type) where
  | BigList : List α → app_list_ann α
  | BigAppend : app_list_ann α → app_list_ann α → app_list_ann α
  | Small : app_list α → app_list_ann α

export app_list_ann (BigList BigAppend Small)

instance {α : Type} : Inhabited (app_list_ann α) := ⟨BigList []⟩

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

end

end Candle

/-! ## Stage 2: theorem statements (HOL4 source order) -/

namespace Candle
noncomputable section
open Classical
set_option autoImplicit false

/- HOL4:
Theorem concat_nil[simp]:
   concat [] = «»
-/
theorem concat_nil :
    concat [] = ml!"" := by
  sorry

/- HOL4:
Theorem explode_aux_thm:
   ∀max n ls.
    (n + max = LENGTH ls) ⇒
    (explode_aux (strlit ls) n max = DROP n ls)
-/
theorem explode_aux_thm :
    ∀ (max n : Nat) (ls : string),
      (n + max = LENGTH ls) →
      (explode_aux (strlit ls) n max = DROP n ls) := by
  sorry

/- HOL4:
Theorem explode_thm[simp]:
   explode (strlit ls) = ls
-/
theorem explode_thm (ls : string) :
    explode (strlit ls) = ls := by
  sorry

/- HOL4:
Theorem explode_implode[simp]:
   ∀x. explode (implode x) = x
-/
theorem explode_implode :
    ∀ (x : string), explode (implode x) = x := by
  sorry

/- HOL4:
Theorem implode_explode[simp]:
   ∀x. implode (explode x) = x
-/
theorem implode_explode :
    ∀ (x : mlstring), implode (explode x) = x := by
  sorry

/- HOL4:
Theorem explode_11[simp]:
   ∀s1 s2. (explode s1 = explode s2) ⇔ (s1 = s2)
-/
theorem explode_11 :
    ∀ (s1 s2 : mlstring), (explode s1 = explode s2) ↔ (s1 = s2) := by
  sorry

/- HOL4:
Theorem explode_BIJ:
   BIJ explode UNIV UNIV
-/
theorem explode_BIJ :
    BIJ explode UNIV UNIV := by
  sorry

/- HOL4:
Theorem LENGTH_explode[simp]:
   LENGTH (explode s) = strlen s
-/
theorem LENGTH_explode (s : mlstring) :
    LENGTH (explode s) = strlen s := by
  sorry

/- HOL4:
Theorem strlen_implode[simp]:
   strlen (implode s) = LENGTH s
-/
theorem strlen_implode (s : string) :
    strlen (implode s) = LENGTH s := by
  sorry

/- HOL4:
Theorem substring_full[simp]:
   substring s 0 (strlen s) = s
-/
theorem substring_full (s : mlstring) :
    substring s 0 (strlen s) = s := by
  sorry

/- HOL4:
Theorem strcat_thm:
   strcat s1 s2 = implode (explode s1 ++ explode s2)
-/
theorem strcat_thm (s1 s2 : mlstring) :
    strcat s1 s2 = implode (explode s1 ++ explode s2) := by
  sorry

/- HOL4:
Theorem strcat_assoc[simp]:
   !s1 s2 s3.
    s1 ^ (s2 ^ s3) = s1 ^ s2 ^ s3
-/
theorem strcat_assoc :
    ∀ (s1 s2 s3 : mlstring),
      strcat s1 (strcat s2 s3) = strcat (strcat s1 s2) s3 := by
  sorry

/- HOL4:
Theorem strcat_nil[simp]:
   (strcat «» s = s) ∧
   (strcat s «» = s)
-/
theorem strcat_nil (s : mlstring) :
    (strcat ml!"" s = s) ∧
    (strcat s ml!"" = s) := by
  sorry

/- HOL4:
Theorem mlstring_common_prefix[simp]:
  ∀s t1 t2. s ^ t1 = s ^ t2 ⇔ t1 = t2
-/
theorem mlstring_common_prefix :
    ∀ (s t1 t2 : mlstring), strcat s t1 = strcat s t2 ↔ t1 = t2 := by
  sorry

/- HOL4:
Theorem mlstring_common_char_prefix[simp]:
  ∀c1 s1 s2 t2 t2. (strlit (c1 :: s1) ^ t1) = (strlit (c2 :: s2) ^ t2) ⇔
    c1 = c2 ∧ strlit s1 ^ t1 = strlit s2 ^ t2
-/
theorem mlstring_common_char_prefix (t1 : mlstring) (c2 : char) :
    ∀ (c1 : char) (s1 s2 : string) (t2 t2 : mlstring),
      (strcat (strlit (c1 :: s1)) t1) = (strcat (strlit (c2 :: s2)) t2) ↔
        c1 = c2 ∧ strcat (strlit s1) t1 = strcat (strlit s2) t2 := by
  sorry

/- HOL4:
Theorem mlstring_common_suffix[simp]:
  ∀s t1 t2. t1 ^ s = t2 ^ s ⇔ t1 = t2
-/
theorem mlstring_common_suffix :
    ∀ (s t1 t2 : mlstring), strcat t1 s = strcat t2 s ↔ t1 = t2 := by
  sorry

/- HOL4:
Theorem explode_strcat[simp]:
   explode (strcat s1 s2) = explode s1 ++ explode s2
-/
theorem explode_strcat (s1 s2 : mlstring) :
    explode (strcat s1 s2) = explode s1 ++ explode s2 := by
  sorry

/- HOL4:
Theorem strlen_strcat[simp]:
   strlen (strcat s1 s2) = strlen s1 + strlen s2
-/
theorem strlen_strcat (s1 s2 : mlstring) :
    strlen (strcat s1 s2) = strlen s1 + strlen s2 := by
  sorry

/- HOL4:
Theorem explode_toString[simp]:
   explode (toString c) = [c]
-/
theorem explode_toString (c : char) :
    explode (chr_to_str c) = [c] := by
  sorry

/- HOL4:
Theorem strlen_toString[simp]:
   strlen (toString c) = 1
-/
theorem strlen_toString (c : char) :
    strlen (chr_to_str c) = 1 := by
  sorry

/- HOL4:
Theorem substring_0[simp]:
  substring s i 0 = «»
-/
theorem substring_0 (s : mlstring) (i : Nat) :
    substring s i 0 = ml!"" := by
  sorry

/- HOL4:
Theorem mlstring_lt_inv_image:
   mlstring_lt = inv_image string_lt explode
-/
theorem mlstring_lt_inv_image :
    mlstring_lt = inv_image string_lt explode := by
  sorry

/- HOL4:
Theorem StrongLinearOrder_mlstring_lt:
   StrongLinearOrder mlstring_lt
-/
theorem StrongLinearOrder_mlstring_lt :
    StrongLinearOrder mlstring_lt := by
  sorry

/- HOL4:
Theorem ALL_DISTINCT_MAP_implode[simp]:
   ALL_DISTINCT ls ⇒ ALL_DISTINCT (MAP implode ls)
-/
theorem ALL_DISTINCT_MAP_implode (ls : List string) :
    ALL_DISTINCT ls → ALL_DISTINCT (MAP implode ls) := by
  sorry

/- HOL4:
Theorem ALL_DISTINCT_MAP_explode[simp]:
   ∀ls. ALL_DISTINCT (MAP explode ls) ⇔ ALL_DISTINCT ls
-/
theorem ALL_DISTINCT_MAP_explode :
    ∀ (ls : List mlstring), ALL_DISTINCT (MAP explode ls) ↔ ALL_DISTINCT ls := by
  sorry

/- HOL4:
Theorem concat_sing[simp]:
  concat [x] = x
-/
theorem concat_sing (x : mlstring) :
    concat [x] = x := by
  sorry

end
end Candle
