import CmlTS.Mllist

/-!
# mlstring (HOL4 theory `mlstring`): strings as a separate type from `char list`

Functions of this theory that clash with other names are in the Lean namespace `mlstring`:
`mlstring.compare`, `mlstring.collate`.  HOL4's string literals `«foo»` are `mlstr "foo"`.
-/

universe u v w

noncomputable section

open Classical

/- HOL4:
   Datatype:
     mlstring = strlit string
   End -/
inductive mlstring : Type where
  | strlit (s : string) : mlstring
  deriving DecidableEq

instance : Inhabited mlstring := ⟨.strlit []⟩

/-- HOL4's `«foo»` (the `add_strliteral_form{inj=``strlit``, ldelim = "«"}` syntax) is
`mlstr "foo"` -/
def mlstr (s : String) : mlstring := .strlit (HOLstr s)

/- HOL4:
   Definition implode_def:
     implode = strlit
   End -/
def implode (s : string) : mlstring := mlstring.strlit s

/- HOL4:
   Definition strlen_def[simp]:
     strlen (strlit s) = LENGTH s
   End -/
def strlen : mlstring → Nat
  | .strlit s => LENGTH s

/- HOL4:
   Definition strsub_def[simp]:
     strsub (strlit s) n = EL n s
   End -/
def strsub : mlstring → Nat → char
  | .strlit s, n => EL n s

/- HOL4:
   Definition concat_def:
     concat l = strlit (FLAT (MAP (λs. case s of strlit x => x) l))
   End -/
def concat (l : List mlstring) : mlstring :=
  .strlit (FLAT (MAP (fun s => match s with | .strlit x => x) l))

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
   (in Lean `x ^ y` on mlstrings is written `strcat x y`) -/
def strcat (s1 s2 : mlstring) : mlstring := concat [s1, s2]

/- HOL4:
   Definition str_def:
     str (c: char) = implode [c]
   End -/
def str (c : char) : mlstring := implode [c]

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
def tokens_aux (f : char → Prop) (s : mlstring) : string → Nat → Nat → List mlstring
  | [], _, 0 => []
  | h :: t, _, 0 => [implode (REVERSE (h :: t))]
  | [], n, len + 1 =>
    if f (strsub s n) then tokens_aux f s [] (n + 1) len
    else tokens_aux f s [strsub s n] (n + 1) len
  | h :: t, n, len + 1 =>
    if f (strsub s n) then implode (REVERSE (h :: t)) :: tokens_aux f s [] (n + 1) len
    else tokens_aux f s (strsub s n :: (h :: t)) (n + 1) len

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
    isSubstring_aux s1 s2 (strlen s1) 0 ((strlen s2) - (strlen s1) + 1)
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
def mlstring.compare_aux (s1 s2 : mlstring) (ord : ordering) (start len : Nat) : ordering :=
  if len = 0 then ord
  else if strsub s2 start < strsub s1 start then .GREATER
  else if strsub s1 start < strsub s2 start then .LESS
  else mlstring.compare_aux s1 s2 ord (start + 1) (len - 1)
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
def mlstring.compare (s1 s2 : mlstring) : ordering :=
  if (strlen s1) < (strlen s2) then mlstring.compare_aux s1 s2 .LESS 0 (strlen s1)
  else if (strlen s2) < (strlen s1) then mlstring.compare_aux s1 s2 .GREATER 0 (strlen s2)
  else mlstring.compare_aux s1 s2 .EQUAL 0 (strlen s2)

/- HOL4:
   Definition mlstring_lt_def:
     mlstring_lt s1 s2 ⇔ (compare s1 s2 = LESS)
   End -/
def mlstring_lt (s1 s2 : mlstring) : Prop := mlstring.compare s1 s2 = .LESS

/- HOL4:
   Definition mlstring_le_def:
     mlstring_le s1 s2 ⇔ (compare s1 s2 ≠ GREATER)
   End -/
def mlstring_le (s1 s2 : mlstring) : Prop := mlstring.compare s1 s2 ≠ .GREATER

/- HOL4:
   Definition mlstring_gt_def:
     mlstring_gt s1 s2 ⇔ (compare s1 s2 = GREATER)
   End -/
def mlstring_gt (s1 s2 : mlstring) : Prop := mlstring.compare s1 s2 = .GREATER

/- HOL4:
   Definition mlstring_ge_def:
     mlstring_ge s1 s2 ⇔ (compare s1 s2 <> LESS)
   End
   Overload "<" = ``λx y. mlstring_lt x y``   Overload "<=" = ``λx y. mlstring_le x y``
   Overload ">" = ``λx y. mlstring_gt x y``   Overload ">=" = ``λx y. mlstring_ge x y``
   (in Lean `<` and `<=` on `mlstring` are the instances below; `>` and `>=` are NOT overloaded:
   use `mlstring_gt` and `mlstring_ge`) -/
def mlstring_ge (s1 s2 : mlstring) : Prop := mlstring.compare s1 s2 ≠ .LESS

instance : LT mlstring := ⟨mlstring_lt⟩
instance : LE mlstring := ⟨mlstring_le⟩

/- HOL4:
   Definition collate_aux_def:
     (collate_aux f (s1: mlstring) s2 ord n 0 = ord) /\
     (collate_aux f s1 s2 ord n (SUC len) =
       if f (strsub s1 n) (strsub s2 n) = EQUAL
         then collate_aux f s1 s2 ord (n + 1) len
       else f (strsub s1 n) (strsub s2 n))
   End -/
def mlstring.collate_aux (f : char → char → ordering) (s1 s2 : mlstring) (ord : ordering) :
    Nat → Nat → ordering
  | _, 0 => ord
  | n, len + 1 =>
    if f (strsub s1 n) (strsub s2 n) = .EQUAL then mlstring.collate_aux f s1 s2 ord (n + 1) len
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
  if (strlen s1) < (strlen s2) then mlstring.collate_aux f s1 s2 .LESS 0 (strlen s1)
  else if (strlen s2) < (strlen s1) then mlstring.collate_aux f s1 s2 .GREATER 0 (strlen s2)
  else mlstring.collate_aux f s1 s2 .EQUAL 0 (strlen s2)

/- HOL4:
   Datatype:
     app_list_ann = BigList ('a list)
                  | BigAppend app_list_ann app_list_ann
                  | Small ('a app_list)
   End -/
inductive app_list_ann (α : Type u) : Type u where
  | BigList (l : List α) : app_list_ann α
  | BigAppend (l1 l2 : app_list_ann α) : app_list_ann α
  | Small (l : app_list α) : app_list_ann α

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
def empty_ffi (_s : mlstring) : Unit := ()

/-! ## Theorems (stage 2) -/

/- HOL4: Theorem explode_aux_thm:
     ∀max n ls.
      (n + max = LENGTH ls) ⇒
      (explode_aux (strlit ls) n max = DROP n ls) -/
theorem explode_aux_thm :
    ∀ (max n : Nat) (ls : string),
      (n + max = LENGTH ls) →
      (explode_aux (mlstring.strlit ls) n max = DROP n ls) := by
  sorry

/- HOL4: Theorem explode_thm[simp]:
     explode (strlit ls) = ls -/
theorem explode_thm (ls : string) : explode (mlstring.strlit ls) = ls := by
  sorry

/- HOL4: Theorem explode_implode[simp]:
     ∀x. explode (implode x) = x -/
theorem explode_implode : ∀ x : string, explode (implode x) = x := by
  sorry

/- HOL4: Theorem implode_explode[simp]:
     ∀x. implode (explode x) = x -/
theorem implode_explode : ∀ x : mlstring, implode (explode x) = x := by
  sorry

/- HOL4: Theorem explode_11[simp]:
     ∀s1 s2. (explode s1 = explode s2) ⇔ (s1 = s2) -/
theorem explode_11 : ∀ s1 s2 : mlstring, (explode s1 = explode s2) ↔ (s1 = s2) := by
  sorry

/- HOL4: Theorem TOKENS_eq_tokens_aux:
     !P ls ss n len. (n + len = LENGTH (explode ls)) ==>
        (MAP explode (tokens_aux P ls ss n len) = case ss of
          | (h::t) => if (len <> 0) /\ ($~ (P (EL n (explode ls)))) then
            (REVERSE (h::t) ++ HD (TOKENS P (DROP n (explode ls))))::TL (TOKENS P (DROP n (explode ls)))
             else if (len <> 0) then
                REVERSE (h::t)::(TOKENS P (DROP n (explode ls)))
             else [REVERSE(h::t)]
          | [] => (TOKENS P (DROP n (explode ls)))) -/
theorem TOKENS_eq_tokens_aux :
    ∀ (P : char → Prop) (ls : mlstring) (ss : string) (n len : Nat),
      (n + len = LENGTH (explode ls)) →
      (MAP explode (tokens_aux P ls ss n len) =
        match ss with
        | h :: t =>
          if (len ≠ 0) ∧ (¬ (P (EL n (explode ls)))) then
            (REVERSE (h :: t) ++ HD (TOKENS P (DROP n (explode ls)))) ::
              TL (TOKENS P (DROP n (explode ls)))
          else if (len ≠ 0) then
            REVERSE (h :: t) :: (TOKENS P (DROP n (explode ls)))
          else [REVERSE (h :: t)]
        | [] => (TOKENS P (DROP n (explode ls)))) := by
  sorry

/- HOL4: Theorem TOKENS_eq_tokens:
     !P ls.(MAP explode (tokens P ls) = TOKENS P (explode ls)) -/
theorem TOKENS_eq_tokens :
    ∀ (P : char → Prop) (ls : mlstring), (MAP explode (tokens P ls) = TOKENS P (explode ls)) := by
  sorry

end
