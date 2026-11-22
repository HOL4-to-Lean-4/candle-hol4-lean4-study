import CandleLean.Mllist
/-
  Translation of `basis/pure/mlstringScript.sml` (definitions).
  Namespace `Candle.Mlstring`.
  `mlstring` is a one-constructor wrapper around a HOL4 `string` (= `List HOL.char`).
-/
namespace Candle.Mlstring

open HOL Candle.Misc
universe u v

open Classical

noncomputable section

/- HOL4: Datatype:
  mlstring = implode string
End
   (add_strliteral_form{inj=“implode”, ldelim = "«"}: the literal «abc» is `implode "abc"`.
    Overload strlit[inferior] = “implode”.) -/
inductive mlstring where
  | implode : string → mlstring

export mlstring (implode)

/-- HOL4 `strlit` (an inferior overload of the constructor `implode`). -/
abbrev strlit : string → mlstring := mlstring.implode

/-- The HOL4 literal `«abc»`: `ml "abc" = implode "abc"` (chars are code points mod 256). -/
def ml (s : _root_.String) : mlstring := mlstring.implode (hstr s)

/- HOL4: Definition strlen_def[simp]:
  strlen (strlit s) = LENGTH s
End -/
def strlen : mlstring → Nat
  | .implode s => LENGTH s

/- HOL4: Definition strsub_def[simp]:
  strsub (strlit s) n = EL n s
End -/
def strsub : mlstring → Nat → char
  | .implode s, n => EL n s

/- HOL4: Definition substring_def:
  substring (strlit s) off len = strlit (if off + len ≤ LENGTH s then SEG len off s
                                         else if off <= LENGTH s then DROP off s
                                         else "")
End -/
def substring : mlstring → Nat → Nat → mlstring
  | .implode s, off, len =>
    .implode (if off + len ≤ LENGTH s then SEG len off s
              else if off ≤ LENGTH s then DROP off s else [])

/- HOL4: Definition concat_def:
  concat l = strlit (FLAT (MAP (λs. case s of strlit x => x) l))
End -/
def concat (l : List mlstring) : mlstring :=
  .implode (FLAT (MAP (fun s => match s with | .implode x => x) l))

/- HOL4: Definition explode_aux_def[simp]:
  (explode_aux s n 0 = []) ∧
  (explode_aux s n (SUC len) =
    strsub s n :: (explode_aux s (n + 1) len))
End -/
def explode_aux (s : mlstring) (n : Nat) : Nat → List char
  | 0 => []
  | len + 1 => strsub s n :: explode_aux s (n + 1) len

/- HOL4: Definition explode_def:
  explode s = explode_aux s 0 (strlen s)
End -/
def explode (s : mlstring) : string := explode_aux s 0 (strlen s)

/- HOL4: Definition extract_def:
  extract s i opt =
    if strlen s <= i
      then implode []
    else case opt of
        SOME x => substring s i (MIN (strlen s - i) x)
      | NONE => substring s i (strlen s - i)
End -/
def extract (s : mlstring) (i : Nat) (opt : Option Nat) : mlstring :=
  if strlen s ≤ i then .implode []
  else match opt with
    | some x => substring s i (MIN (strlen s - i) x)
    | none => substring s i (strlen s - i)

/- HOL4: Definition strcat_def:
  strcat s1 s2 = concat [s1; s2]
End
   (infixl `^` at 480; Overload "^" = λx y. strcat x y.  In Lean write `strcat s1 s2`.) -/
def strcat (s1 s2 : mlstring) : mlstring := concat [s1, s2]

/- HOL4: Definition chr_to_str_def:
  chr_to_str (c: char) = implode [c]
End
   (Overload toString = chr_to_str.) -/
def chr_to_str (c : char) : mlstring := .implode [c]

/- HOL4: Definition translate_aux_def:
  (translate_aux f s n 0 = []) /\
  (translate_aux f s n (SUC len) = f (strsub s n)::translate_aux f s (n + 1) len)
End -/
def translate_aux {α : Type u} (f : char → α) (s : mlstring) (n : Nat) : Nat → List α
  | 0 => []
  | len + 1 => f (strsub s n) :: translate_aux f s (n + 1) len

/- HOL4: Definition splitl_aux_def:
  splitl_aux P s i =
    if i < strlen s ∧ P (strsub s i) then
        splitl_aux P s (i+1)
    else (extract s 0 (SOME i), extract s i NONE)
Termination
  WF_REL_TAC`inv_image $< (λ(x,s,i). strlen s - i)`
End -/
def splitl_aux (P : char → Prop) (s : mlstring) (i : Nat) : mlstring × mlstring :=
  if h : i < strlen s ∧ P (strsub s i) then splitl_aux P s (i + 1)
  else (extract s 0 (some i), extract s i none)
termination_by strlen s - i
decreasing_by omega

/- HOL4: Definition tokens_aux_def:
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
  | h :: t, _, 0 => [.implode (REVERSE (h :: t))]
  | [], n, len + 1 =>
    if f (strsub s n) then tokens_aux f s [] (n + 1) len
    else tokens_aux f s [strsub s n] (n + 1) len
  | h :: t, n, len + 1 =>
    if f (strsub s n) then .implode (REVERSE (h :: t)) :: tokens_aux f s [] (n + 1) len
    else tokens_aux f s (strsub s n :: (h :: t)) (n + 1) len

/- HOL4: Definition tokens_def:
 tokens f s = tokens_aux f s [] 0 (strlen s)
End -/
def tokens (f : char → Prop) (s : mlstring) : List mlstring := tokens_aux f s [] 0 (strlen s)

/- HOL4: Definition tokens_alt_aux_def:
  (tokens_alt_aux f s i j n =
  if j < n then
    (if f (strsub s j)
    then
      (if i = j then tokens_alt_aux f s (i+1) (j+1) n
      else
        substring s i (j-i)::
        (tokens_alt_aux f s (j+1) (j+1) n))
    else
      tokens_alt_aux f s i (j+1) n)
  else
    if i = j then []
    else [substring s i (j-i)])
Termination
  WF_REL_TAC`measure (λf,s,i,j,n. n - j)`>>rw[]
End -/
def tokens_alt_aux (f : char → Prop) (s : mlstring) (i j n : Nat) : List mlstring :=
  if h : j < n then
    (if f (strsub s j) then
      (if i = j then tokens_alt_aux f s (i + 1) (j + 1) n
       else substring s i (j - i) :: tokens_alt_aux f s (j + 1) (j + 1) n)
     else tokens_alt_aux f s i (j + 1) n)
  else
    if i = j then [] else [substring s i (j - i)]
termination_by n - j
decreasing_by all_goals omega

/- HOL4: Definition fields_aux_def:
  (fields_aux f s ss n 0 = [implode (REVERSE ss)]) /\
  (fields_aux f s ss n (SUC len) =
    if f (strsub s n)
      then implode (REVERSE ss)::(fields_aux f s [] (n + 1) len)
    else fields_aux f s (strsub s n::ss) (n + 1) len)
End -/
def fields_aux (f : char → Prop) (s : mlstring) : List char → Nat → Nat → List mlstring
  | ss, _, 0 => [.implode (REVERSE ss)]
  | ss, n, len + 1 =>
    if f (strsub s n) then .implode (REVERSE ss) :: fields_aux f s [] (n + 1) len
    else fields_aux f s (strsub s n :: ss) (n + 1) len

/- HOL4: Definition fields_def:
  fields f s = fields_aux f s [] 0 (strlen s)
End -/
def fields (f : char → Prop) (s : mlstring) : List mlstring := fields_aux f s [] 0 (strlen s)

/- HOL4: Definition fields_alt_aux_def:
  (fields_alt_aux f s i j n =
  if j < n then
    (if f (strsub s j)
    then
        substring s i (j-i)::
        (fields_alt_aux f s (j+1) (j+1) n)
    else
      fields_alt_aux f s i (j+1) n)
  else
    [substring s i (j-i)])
Termination
  WF_REL_TAC`measure (λf,s,i,j,n. n - j)`>>rw[]
End -/
def fields_alt_aux (f : char → Prop) (s : mlstring) (i j n : Nat) : List mlstring :=
  if h : j < n then
    (if f (strsub s j) then
       substring s i (j - i) :: fields_alt_aux f s (j + 1) (j + 1) n
     else fields_alt_aux f s i (j + 1) n)
  else [substring s i (j - i)]
termination_by n - j
decreasing_by all_goals omega

/- HOL4: Definition isStringThere_aux_def:
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

/- HOL4: Definition compare_aux_def:
  compare_aux (s1: mlstring) s2 ord start len =
    if len = 0n then
      ord
    else if strsub s2 start < strsub s1 start
      then GREATER
    else if strsub s1 start < strsub s2 start
      then LESS
    else compare_aux s1 s2 ord (start + 1) (len - 1)
End   (`<` on chars is `char_lt`) -/
def compare_aux (s1 s2 : mlstring) (ord : Ordering) (start len : Nat) : Ordering :=
  if h : len = 0 then ord
  else if char_lt (strsub s2 start) (strsub s1 start) then GREATER
  else if char_lt (strsub s1 start) (strsub s2 start) then LESS
  else compare_aux s1 s2 ord (start + 1) (len - 1)
termination_by len
decreasing_by omega

/- HOL4: Definition compare_def:
  compare s1 s2 = if (strlen s1) < (strlen s2)
    then compare_aux s1 s2 LESS 0 (strlen s1)
  else if (strlen s2) < (strlen s1)
    then compare_aux s1 s2 GREATER 0 (strlen s2)
  else compare_aux s1 s2 EQUAL 0 (strlen s2)
End   (named `mlstring_compare` in Lean to avoid clashing with Lean's `compare`) -/
def mlstring_compare (s1 s2 : mlstring) : Ordering :=
  if strlen s1 < strlen s2 then compare_aux s1 s2 LESS 0 (strlen s1)
  else if strlen s2 < strlen s1 then compare_aux s1 s2 GREATER 0 (strlen s2)
  else compare_aux s1 s2 EQUAL 0 (strlen s2)

/- HOL4: Definition mlstring_lt_def:
  mlstring_lt s1 s2 ⇔ (compare s1 s2 = LESS)
End -/
def mlstring_lt (s1 s2 : mlstring) : Prop := mlstring_compare s1 s2 = LESS

/- HOL4: Definition collate_aux_def:
  (collate_aux f (s1: mlstring) s2 ord n 0 = ord) /\
  (collate_aux f s1 s2 ord n (SUC len) =
    if f (strsub s1 n) (strsub s2 n) = EQUAL
      then collate_aux f s1 s2 ord (n + 1) len
    else f (strsub s1 n) (strsub s2 n))
End -/
def collate_aux (f : char → char → Ordering) (s1 s2 : mlstring) (ord : Ordering) : Nat → Nat → Ordering
  | _, 0 => ord
  | n, len + 1 =>
    if f (strsub s1 n) (strsub s2 n) = EQUAL then collate_aux f s1 s2 ord (n + 1) len
    else f (strsub s1 n) (strsub s2 n)

/- HOL4: Definition collate_def:
  collate f s1 s2 =
  if (strlen s1) < (strlen s2)
    then collate_aux f s1 s2 LESS 0 (strlen s1)
  else if (strlen s2) < (strlen s1)
    then collate_aux f s1 s2 GREATER 0 (strlen s2)
  else collate_aux f s1 s2 EQUAL 0 (strlen s2)
End -/
def collate (f : char → char → Ordering) (s1 s2 : mlstring) : Ordering :=
  if strlen s1 < strlen s2 then collate_aux f s1 s2 LESS 0 (strlen s1)
  else if strlen s2 < strlen s1 then collate_aux f s1 s2 GREATER 0 (strlen s2)
  else collate_aux f s1 s2 EQUAL 0 (strlen s2)

/- HOL4: Datatype:
  app_list_ann = BigList ('a list)
               | BigAppend app_list_ann app_list_ann
               | Small ('a app_list)
End -/
inductive app_list_ann (α : Type u) where
  | BigList : List α → app_list_ann α
  | BigAppend : app_list_ann α → app_list_ann α → app_list_ann α
  | Small : app_list α → app_list_ann α

/- HOL4: Definition sum_sizes_def:
  sum_sizes [] k = k ∧
  sum_sizes (l::ls) k = sum_sizes ls (strlen l + k)
End -/
def sum_sizes : List mlstring → Nat → Nat
  | [], k => k
  | l :: ls, k => sum_sizes ls (strlen l + k)

/- HOL4: Overload size_limit[local] = “2048:num” -/
def size_limit : Nat := 2048

/- HOL4: Definition make_app_list_ann_def:
  make_app_list_ann input =
    case input of
    | Nil => (Small input, 0)
    | Append l1 l2 =>
        (let (x1,n1) = make_app_list_ann l1 in
         let (x2,n2) = make_app_list_ann l2 in
         let n = n1+n2 in
           if n < size_limit then
             (Small input,n)
           else
             (BigAppend x1 x2,n))
    | List ls =>
        (let n = sum_sizes ls 0 in
           if n < size_limit then
             (Small input,n)
           else (BigList ls,n))
End -/
def make_app_list_ann : app_list mlstring → app_list_ann mlstring × Nat
  | .Nil => (.Small .Nil, 0)
  | .Append l1 l2 =>
    let r1 := make_app_list_ann l1
    let r2 := make_app_list_ann l2
    let n := r1.2 + r2.2
    if n < size_limit then (.Small (.Append l1 l2), n)
    else (.BigAppend r1.1 r2.1, n)
  | .List ls =>
    let n := sum_sizes ls 0
    if n < size_limit then (.Small (.List ls), n) else (.BigList ls, n)

/- HOL4: Definition shrink_def:
  shrink (Small t) = List [concat (append t)] ∧
  shrink (BigList ls) = List ls ∧
  shrink (BigAppend l1 l2) = Append (shrink l1) (shrink l2)
End -/
def shrink : app_list_ann mlstring → app_list mlstring
  | .Small t => .List [concat (append t)]
  | .BigList ls => .List ls
  | .BigAppend l1 l2 => .Append (shrink l1) (shrink l2)

/- HOL4: Definition str_app_list_opt_def:
  str_app_list_opt l =
    let (t,n) = make_app_list_ann l in
      shrink t
End -/
def str_app_list_opt (l : app_list mlstring) : app_list mlstring :=
  let r := make_app_list_ann l
  shrink r.1

/- HOL4: Definition char_to_word8_def[simp]:
  char_to_word8 (c:char) = n2w (ORD c) :word8
End -/
def char_to_word8 (c : char) : word8 := n2w (ORD c)

/- HOL4: Definition word8_to_char_def[simp]:
  word8_to_char (w:word8) = CHR (w2n w) : char
End -/
def word8_to_char (w : word8) : char := CHR (w2n w)

/-! ## Target theorems -/

/- HOL4: Theorem concat_nil[simp]:
   concat [] = «» -/
theorem concat_nil : concat [] = ml "" := by sorry

/- HOL4: Theorem explode_aux_thm:
   ∀max n ls.
    (n + max = LENGTH ls) ⇒
    (explode_aux (strlit ls) n max = DROP n ls) -/
theorem explode_aux_thm :
    ∀ (max n : Nat) (ls : string),
      (n + max = LENGTH ls) → (explode_aux (strlit ls) n max = DROP n ls) := by sorry

/- HOL4: Theorem explode_thm[simp]:
   explode (strlit ls) = ls -/
theorem explode_thm (ls : string) : explode (strlit ls) = ls := by sorry

/- HOL4: Theorem explode_implode[simp]:
   ∀x. explode (implode x) = x -/
theorem explode_implode : ∀ (x : string), explode (implode x) = x := by sorry

/- HOL4: Theorem implode_explode[simp]:
   ∀x. implode (explode x) = x -/
theorem implode_explode : ∀ (x : mlstring), implode (explode x) = x := by sorry

/- HOL4: Theorem explode_11[simp]:
   ∀s1 s2. (explode s1 = explode s2) ⇔ (s1 = s2) -/
theorem explode_11 : ∀ (s1 s2 : mlstring), (explode s1 = explode s2) ↔ (s1 = s2) := by sorry

/- HOL4: Theorem explode_BIJ:
   BIJ explode UNIV UNIV -/
theorem explode_BIJ : BIJ explode UNIV UNIV := by sorry

/- HOL4: Theorem LENGTH_explode[simp]:
   LENGTH (explode s) = strlen s -/
theorem LENGTH_explode (s : mlstring) : LENGTH (explode s) = strlen s := by sorry

/- HOL4: Theorem strlen_implode[simp]:
   strlen (implode s) = LENGTH s -/
theorem strlen_implode (s : string) : strlen (implode s) = LENGTH s := by sorry

/- HOL4: Theorem substring_full[simp]:
   substring s 0 (strlen s) = s -/
theorem substring_full (s : mlstring) : substring s 0 (strlen s) = s := by sorry

/- HOL4: Theorem strcat_thm:
   strcat s1 s2 = implode (explode s1 ++ explode s2) -/
theorem strcat_thm (s1 s2 : mlstring) :
    strcat s1 s2 = implode (explode s1 ++ explode s2) := by sorry

/- HOL4: Theorem strcat_assoc[simp]:
   !s1 s2 s3.
    s1 ^ (s2 ^ s3) = s1 ^ s2 ^ s3
   (`^` is left associative: s1 ^ s2 ^ s3 = (s1 ^ s2) ^ s3) -/
theorem strcat_assoc :
    ∀ (s1 s2 s3 : mlstring), strcat s1 (strcat s2 s3) = strcat (strcat s1 s2) s3 := by sorry

/- HOL4: Theorem strcat_nil[simp]:
   (strcat «» s = s) ∧
   (strcat s «» = s) -/
theorem strcat_nil (s : mlstring) : (strcat (ml "") s = s) ∧ (strcat s (ml "") = s) := by sorry

/- HOL4: Theorem mlstring_common_prefix[simp]:
  ∀s t1 t2. s ^ t1 = s ^ t2 ⇔ t1 = t2 -/
theorem mlstring_common_prefix :
    ∀ (s t1 t2 : mlstring), strcat s t1 = strcat s t2 ↔ t1 = t2 := by sorry

/- HOL4: Theorem mlstring_common_char_prefix[simp]:
  ∀c1 s1 s2 t2 t2. (strlit (c1 :: s1) ^ t1) = (strlit (c2 :: s2) ^ t2) ⇔
    c1 = c2 ∧ strlit s1 ^ t1 = strlit s2 ^ t2
   (t1, c2 are free, hence universally quantified; the first `t2` binder is vacuous and
    is omitted) -/
theorem mlstring_common_char_prefix (t1 : mlstring) (c2 : char) :
    ∀ (c1 : char) (s1 s2 : string) (t2 : mlstring),
      (strcat (strlit (c1 :: s1)) t1) = (strcat (strlit (c2 :: s2)) t2) ↔
        c1 = c2 ∧ strcat (strlit s1) t1 = strcat (strlit s2) t2 := by sorry

/- HOL4: Theorem mlstring_common_suffix[simp]:
  ∀s t1 t2. t1 ^ s = t2 ^ s ⇔ t1 = t2 -/
theorem mlstring_common_suffix :
    ∀ (s t1 t2 : mlstring), strcat t1 s = strcat t2 s ↔ t1 = t2 := by sorry

/- HOL4: Theorem explode_strcat[simp]:
   explode (strcat s1 s2) = explode s1 ++ explode s2 -/
theorem explode_strcat (s1 s2 : mlstring) :
    explode (strcat s1 s2) = explode s1 ++ explode s2 := by sorry

/- HOL4: Theorem strlen_strcat[simp]:
   strlen (strcat s1 s2) = strlen s1 + strlen s2 -/
theorem strlen_strcat (s1 s2 : mlstring) :
    strlen (strcat s1 s2) = strlen s1 + strlen s2 := by sorry

/- HOL4: Theorem explode_toString[simp]:
   explode (toString c) = [c] -/
theorem explode_toString (c : char) : explode (chr_to_str c) = [c] := by sorry

/- HOL4: Theorem strlen_toString[simp]:
   strlen (toString c) = 1 -/
theorem strlen_toString (c : char) : strlen (chr_to_str c) = 1 := by sorry

/- HOL4: Theorem substring_0[simp]:
  substring s i 0 = «» -/
theorem substring_0 (s : mlstring) (i : Nat) : substring s i 0 = ml "" := by sorry

/- HOL4: Theorem mlstring_lt_inv_image:
   mlstring_lt = inv_image string_lt explode -/
theorem mlstring_lt_inv_image : mlstring_lt = inv_image string_lt explode := by sorry

/- HOL4: Theorem StrongLinearOrder_mlstring_lt:
   StrongLinearOrder mlstring_lt -/
theorem StrongLinearOrder_mlstring_lt : StrongLinearOrder mlstring_lt := by sorry

/- HOL4: Theorem ALL_DISTINCT_MAP_implode[simp]:
   ALL_DISTINCT ls ⇒ ALL_DISTINCT (MAP implode ls) -/
theorem ALL_DISTINCT_MAP_implode (ls : List string) :
    ALL_DISTINCT ls → ALL_DISTINCT (MAP implode ls) := by sorry

/- HOL4: Theorem ALL_DISTINCT_MAP_explode[simp]:
   ∀ls. ALL_DISTINCT (MAP explode ls) ⇔ ALL_DISTINCT ls -/
theorem ALL_DISTINCT_MAP_explode :
    ∀ (ls : List mlstring), ALL_DISTINCT (MAP explode ls) ↔ ALL_DISTINCT ls := by sorry

/- HOL4: Theorem concat_sing[simp]:
  concat [x] = x -/
theorem concat_sing (x : mlstring) : concat [x] = x := by sorry

end

end Candle.Mlstring
