import CandleLean.Mllist

/-!
# mlstring (CakeML `basis/pure/mlstringScript.sml`), reduced to what the targets need

HOL4 mlstring literals `«abc»` are `implode "abc"`; in Lean write `mls "abc"`
(`= mlstring.implode (str "abc")`).
-/

universe u

namespace Candle

open HOL Classical

noncomputable section

/- HOL4:
Datatype:
  mlstring = implode string
End
val _ = add_strliteral_form{inj=“implode”, ldelim = "«"};
Overload strlit[inferior] = “implode”
   (the constructor `mlstring.implode` is exported as `Candle.implode`; `strlit` is an
   abbreviation for it) -/
inductive mlstring where
  | implode : string → mlstring
  deriving DecidableEq, Inhabited

export mlstring (implode)

/- HOL4: Overload strlit[inferior] = “implode” -/
@[reducible, match_pattern] def strlit (s : string) : mlstring := mlstring.implode s

/-- HOL4 mlstring literal `«s»` (= `implode s`), from a Lean string literal. -/
def mls (s : String) : mlstring := mlstring.implode (str s)

/- HOL4:
Definition strlen_def[simp]:
  strlen (strlit s) = LENGTH s
End -/
def strlen : mlstring → Nat
  | .implode s => s.length

/- HOL4:
Definition strsub_def[simp]:
  strsub (strlit s) n = EL n s
End -/
def strsub : mlstring → Nat → char
  | .implode s, n => EL n s

/- HOL4:
Definition substring_def:
  substring (strlit s) off len = strlit (if off + len ≤ LENGTH s then SEG len off s
                                         else if off <= LENGTH s then DROP off s
                                         else "")
End -/
def substring : mlstring → Nat → Nat → mlstring
  | .implode s, off, len =>
    strlit (if off + len ≤ s.length then SEG len off s
            else if off ≤ s.length then s.drop off
            else [])

/- HOL4:
Definition concat_def:
  concat l = strlit (FLAT (MAP (λs. case s of strlit x => x) l))
End -/
def concat (l : List mlstring) : mlstring :=
  strlit (List.flatten (l.map (fun s => match s with | .implode x => x)))

/- HOL4:
Theorem concat_nil[simp]:
   concat [] = «» -/
theorem concat_nil : concat [] = mls "" := by
  sorry

/- HOL4:
Definition explode_aux_def[simp]:
  (explode_aux s n 0 = []) ∧
  (explode_aux s n (SUC len) =
    strsub s n :: (explode_aux s (n + 1) len))
End -/
def explode_aux : mlstring → Nat → Nat → string
  | _, _, 0 => []
  | s, n, len + 1 => strsub s n :: explode_aux s (n + 1) len

/- HOL4:
Theorem explode_aux_thm:
   ∀max n ls.
    (n + max = LENGTH ls) ⇒
    (explode_aux (strlit ls) n max = DROP n ls) -/
theorem explode_aux_thm :
    ∀ (max n : Nat) (ls : string),
      n + max = ls.length →
      explode_aux (implode ls) n max = List.drop n ls := by
  sorry

/- HOL4:
Definition explode_def:
  explode s = explode_aux s 0 (strlen s)
End -/
def explode (s : mlstring) : string := explode_aux s 0 (strlen s)

/-! Auxiliary lemmas (namespace `Candle.Aux`; used for the proof of `instance_def`). -/

theorem Aux.EL_cons_drop {α : Type u} [Nonempty α] :
    ∀ (n : Nat) (l : List α), n < l.length → EL n l :: l.drop (n + 1) = l.drop n
  | 0, a :: t, _ => by simp [EL, HD_def]
  | n + 1, a :: t, h => by
    simp only [EL, TL, List.drop_succ_cons]
    exact Aux.EL_cons_drop n t (by simp at h; omega)

theorem Aux.explode_aux_implode (l : string) :
    ∀ (m n : Nat), n + m = l.length → explode_aux (implode l) n m = l.drop n
  | 0, n, h => by simp [explode_aux]; omega
  | m + 1, n, h => by
    simp only [explode_aux, strsub]
    rw [Aux.explode_aux_implode l m (n + 1) (by omega)]
    exact Aux.EL_cons_drop n l (by omega)

theorem Aux.implode_explode_aux (s : mlstring) : implode (explode s) = s := by
  cases s with
  | implode l =>
    simp only [explode, strlen]
    rw [Aux.explode_aux_implode l l.length 0 (by omega)]
    rfl

/- HOL4:
Theorem explode_thm[simp]:
   explode (strlit ls) = ls -/
theorem explode_thm (ls : string) : explode (implode ls) = ls := by
  sorry

/- HOL4:
Theorem explode_implode[simp]:
   ∀x. explode (implode x) = x -/
theorem explode_implode : ∀ (x : string), explode (implode x) = x := by
  sorry

/- HOL4:
Theorem implode_explode[simp]:
   ∀x. implode (explode x) = x -/
theorem implode_explode : ∀ (x : mlstring), implode (explode x) = x := by
  sorry

/- HOL4:
Theorem explode_11[simp]:
   ∀s1 s2. (explode s1 = explode s2) ⇔ (s1 = s2) -/
theorem explode_11 : ∀ (s1 s2 : mlstring), explode s1 = explode s2 ↔ s1 = s2 := by
  sorry

/- HOL4:
Theorem explode_BIJ:
   BIJ explode UNIV UNIV -/
theorem explode_BIJ : BIJ explode UNIV UNIV := by
  sorry

/- HOL4:
Theorem LENGTH_explode[simp]:
   LENGTH (explode s) = strlen s -/
theorem LENGTH_explode (s : mlstring) : (explode s).length = strlen s := by
  sorry

/- HOL4:
Theorem strlen_implode[simp]:
   strlen (implode s) = LENGTH s -/
theorem strlen_implode (s : string) : strlen (implode s) = s.length := by
  sorry

/- HOL4:
Theorem substring_full[simp]:
   substring s 0 (strlen s) = s -/
theorem substring_full (s : mlstring) : substring s 0 (strlen s) = s := by
  sorry

/- HOL4:
Definition strcat_def:
  strcat s1 s2 = concat [s1; s2]
End
val _ = Parse.add_infix("^",480,Parse.LEFT)
Overload "^" = ``λx y. strcat x y``
   (`s1 ^ s2` is written `strcat s1 s2`) -/
def strcat (s1 s2 : mlstring) : mlstring := concat [s1, s2]

/- HOL4:
Theorem strcat_thm:
   strcat s1 s2 = implode (explode s1 ++ explode s2) -/
theorem strcat_thm (s1 s2 : mlstring) : strcat s1 s2 = implode (explode s1 ++ explode s2) := by
  sorry

/- HOL4:
Theorem strcat_assoc[simp]:
   !s1 s2 s3.
    s1 ^ (s2 ^ s3) = s1 ^ s2 ^ s3
   (`^` is left associative: the right-hand side is `(s1 ^ s2) ^ s3`) -/
theorem strcat_assoc :
    ∀ (s1 s2 s3 : mlstring), strcat s1 (strcat s2 s3) = strcat (strcat s1 s2) s3 := by
  sorry

/- HOL4:
Theorem strcat_nil[simp]:
   (strcat «» s = s) ∧
   (strcat s «» = s) -/
theorem strcat_nil (s : mlstring) : strcat (mls "") s = s ∧ strcat s (mls "") = s := by
  sorry

/- HOL4:
Theorem mlstring_common_prefix[simp]:
  ∀s t1 t2. s ^ t1 = s ^ t2 ⇔ t1 = t2 -/
theorem mlstring_common_prefix :
    ∀ (s t1 t2 : mlstring), strcat s t1 = strcat s t2 ↔ t1 = t2 := by
  sorry

/- HOL4:
Theorem mlstring_common_char_prefix[simp]:
  ∀c1 s1 s2 t2 t2. (strlit (c1 :: s1) ^ t1) = (strlit (c2 :: s2) ^ t2) ⇔
    c1 = c2 ∧ strlit s1 ^ t1 = strlit s2 ^ t2
   (as in the source, `t2` is bound twice (the outer binder is vacuous) and `t1`, `c2`
   are free, hence universally quantified outermost) -/
theorem mlstring_common_char_prefix (t1 : mlstring) (c2 : char) :
    ∀ (c1 : char) (s1 s2 : string) (t2 : mlstring) (t2 : mlstring),
      strcat (implode (c1 :: s1)) t1 = strcat (implode (c2 :: s2)) t2 ↔
        c1 = c2 ∧ strcat (implode s1) t1 = strcat (implode s2) t2 := by
  sorry

/- HOL4:
Theorem mlstring_common_suffix[simp]:
  ∀s t1 t2. t1 ^ s = t2 ^ s ⇔ t1 = t2 -/
theorem mlstring_common_suffix :
    ∀ (s t1 t2 : mlstring), strcat t1 s = strcat t2 s ↔ t1 = t2 := by
  sorry

/- HOL4:
Theorem explode_strcat[simp]:
   explode (strcat s1 s2) = explode s1 ++ explode s2 -/
theorem explode_strcat (s1 s2 : mlstring) :
    explode (strcat s1 s2) = explode s1 ++ explode s2 := by
  sorry

/- HOL4:
Theorem strlen_strcat[simp]:
   strlen (strcat s1 s2) = strlen s1 + strlen s2 -/
theorem strlen_strcat (s1 s2 : mlstring) : strlen (strcat s1 s2) = strlen s1 + strlen s2 := by
  sorry

/- HOL4:
Definition chr_to_str_def:
  chr_to_str (c: char) = implode [c]
End
Overload toString = “chr_to_str”
   (`toString c` is written `chr_to_str c`) -/
def chr_to_str (c : char) : mlstring := implode [c]

/- HOL4:
Theorem explode_toString[simp]:
   explode (toString c) = [c] -/
theorem explode_toString (c : char) : explode (chr_to_str c) = [c] := by
  sorry

/- HOL4:
Theorem strlen_toString[simp]:
   strlen (toString c) = 1 -/
theorem strlen_toString (c : char) : strlen (chr_to_str c) = 1 := by
  sorry

/- HOL4:
Theorem substring_0[simp]:
  substring s i 0 = «» -/
theorem substring_0 (s : mlstring) (i : Nat) : substring s i 0 = mls "" := by
  sorry

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
   (`<` on characters is `char_lt`) -/
def compare_aux (s1 s2 : mlstring) (ord : ordering) (start len : Nat) : ordering :=
  if len = 0 then ord
  else if char_lt (strsub s2 start) (strsub s1 start) then GREATER
  else if char_lt (strsub s1 start) (strsub s2 start) then LESS
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
End
   (Lean name `Candle.compare`; write it qualified if `Ord.compare` makes `compare` ambiguous) -/
def compare (s1 s2 : mlstring) : ordering :=
  if strlen s1 < strlen s2 then compare_aux s1 s2 LESS 0 (strlen s1)
  else if strlen s2 < strlen s1 then compare_aux s1 s2 GREATER 0 (strlen s2)
  else compare_aux s1 s2 EQUAL 0 (strlen s2)

/- HOL4:
Definition mlstring_lt_def:
  mlstring_lt s1 s2 ⇔ (compare s1 s2 = LESS)
End
Overload "<" = ``λx y. mlstring_lt x y`` -/
def mlstring_lt (s1 s2 : mlstring) : Prop := compare s1 s2 = LESS

/- HOL4:
val flip_ord_def = ternaryComparisonsTheory.invert_comparison_def
Overload flip_ord = ``invert_comparison`` -/
@[reducible] def flip_ord : ordering → ordering := invert_comparison

/- HOL4:
Theorem mlstring_lt_inv_image:
   mlstring_lt = inv_image string_lt explode -/
theorem mlstring_lt_inv_image : mlstring_lt = inv_image string_lt explode := by
  sorry

/- HOL4:
Theorem StrongLinearOrder_mlstring_lt:
   StrongLinearOrder mlstring_lt -/
theorem StrongLinearOrder_mlstring_lt : StrongLinearOrder mlstring_lt := by
  sorry

/- HOL4:
Theorem ALL_DISTINCT_MAP_implode[simp]:
   ALL_DISTINCT ls ⇒ ALL_DISTINCT (MAP implode ls) -/
theorem ALL_DISTINCT_MAP_implode (ls : List string) :
    ALL_DISTINCT ls → ALL_DISTINCT (List.map implode ls) := by
  sorry

/- HOL4:
Theorem ALL_DISTINCT_MAP_explode[simp]:
   ∀ls. ALL_DISTINCT (MAP explode ls) ⇔ ALL_DISTINCT ls -/
theorem ALL_DISTINCT_MAP_explode :
    ∀ (ls : List mlstring), ALL_DISTINCT (List.map explode ls) ↔ ALL_DISTINCT ls := by
  sorry

/- HOL4:
Datatype:
  app_list_ann = BigList ('a list)
               | BigAppend app_list_ann app_list_ann
               | Small ('a app_list)
End -/
inductive app_list_ann (α : Type u) where
  | BigList : List α → app_list_ann α
  | BigAppend : app_list_ann α → app_list_ann α → app_list_ann α
  | Small : app_list α → app_list_ann α
  deriving Inhabited

export app_list_ann (BigList BigAppend Small)

/- HOL4:
Theorem concat_sing[simp]:
  concat [x] = x -/
theorem concat_sing (x : mlstring) : concat [x] = x := by
  sorry

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
