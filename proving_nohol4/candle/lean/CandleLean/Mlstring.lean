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
  simp [concat, mls, str]

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
  intro max
  induction max with
  | zero => intro n ls h; simp [explode_aux]; omega
  | succ m ih =>
    intro n ls h
    simp only [explode_aux, strsub]
    rw [ih (n + 1) ls (by omega), Aux.EL_eq n ls (by omega)]
    exact (List.drop_eq_getElem_cons (by omega)).symm

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
  simp only [explode, strlen]
  rw [Aux.explode_aux_implode ls ls.length 0 (by omega)]
  rfl

/- HOL4:
Theorem explode_implode[simp]:
   ∀x. explode (implode x) = x -/
theorem explode_implode : ∀ (x : string), explode (implode x) = x := by
  exact explode_thm

/- HOL4:
Theorem implode_explode[simp]:
   ∀x. implode (explode x) = x -/
theorem implode_explode : ∀ (x : mlstring), implode (explode x) = x := by
  exact Aux.implode_explode_aux

/- HOL4:
Theorem explode_11[simp]:
   ∀s1 s2. (explode s1 = explode s2) ⇔ (s1 = s2) -/
theorem explode_11 : ∀ (s1 s2 : mlstring), explode s1 = explode s2 ↔ s1 = s2 := by
  intro s1 s2
  constructor
  · intro h
    rw [← implode_explode s1, h, implode_explode]
  · exact congrArg explode

/- HOL4:
Theorem explode_BIJ:
   BIJ explode UNIV UNIV -/
theorem explode_BIJ : BIJ explode UNIV UNIV := by
  exact ⟨⟨fun _ _ => trivial, fun x y _ h => (explode_11 x y).mp h⟩,
    ⟨fun _ _ => trivial, fun x _ => ⟨implode x, trivial, explode_thm x⟩⟩⟩

/- HOL4:
Theorem LENGTH_explode[simp]:
   LENGTH (explode s) = strlen s -/
theorem LENGTH_explode (s : mlstring) : (explode s).length = strlen s := by
  cases s with
  | implode s => rw [explode_thm]; rfl

/- HOL4:
Theorem strlen_implode[simp]:
   strlen (implode s) = LENGTH s -/
theorem strlen_implode (s : string) : strlen (implode s) = s.length := by
  rfl

/- HOL4:
Theorem substring_full[simp]:
   substring s 0 (strlen s) = s -/
theorem substring_full (s : mlstring) : substring s 0 (strlen s) = s := by
  have h : ∀ l : string, SEG l.length 0 l = l := by
    intro l
    induction l with
    | nil => exact SEG_def.1 0 []
    | cons a t ih => rw [List.length_cons, SEG_def.2.1, ih]
  cases s with
  | implode s => simp [substring, strlen, h]

theorem Aux.mls_empty : mls "" = implode [] := by
  simp [mls, str]

/- HOL4:
Definition strcat_def:
  strcat s1 s2 = concat [s1; s2]
End
val _ = Parse.add_infix("^",480,Parse.LEFT)
Overload "^" = ``λx y. strcat x y``
   (`s1 ^ s2` is written `strcat s1 s2`) -/
def strcat (s1 s2 : mlstring) : mlstring := concat [s1, s2]

theorem Aux.strcat_implode (a b : string) :
    strcat (implode a) (implode b) = implode (a ++ b) := by
  simp [strcat, concat]

/- HOL4:
Theorem strcat_thm:
   strcat s1 s2 = implode (explode s1 ++ explode s2) -/
theorem strcat_thm (s1 s2 : mlstring) : strcat s1 s2 = implode (explode s1 ++ explode s2) := by
  cases s1; cases s2
  rw [explode_thm, explode_thm, Aux.strcat_implode]

/- HOL4:
Theorem strcat_assoc[simp]:
   !s1 s2 s3.
    s1 ^ (s2 ^ s3) = s1 ^ s2 ^ s3
   (`^` is left associative: the right-hand side is `(s1 ^ s2) ^ s3`) -/
theorem strcat_assoc :
    ∀ (s1 s2 s3 : mlstring), strcat s1 (strcat s2 s3) = strcat (strcat s1 s2) s3 := by
  intro s1 s2 s3
  cases s1; cases s2; cases s3
  simp [Aux.strcat_implode]

/- HOL4:
Theorem strcat_nil[simp]:
   (strcat «» s = s) ∧
   (strcat s «» = s) -/
theorem strcat_nil (s : mlstring) : strcat (mls "") s = s ∧ strcat s (mls "") = s := by
  cases s
  simp [Aux.mls_empty, Aux.strcat_implode]

/- HOL4:
Theorem mlstring_common_prefix[simp]:
  ∀s t1 t2. s ^ t1 = s ^ t2 ⇔ t1 = t2 -/
theorem mlstring_common_prefix :
    ∀ (s t1 t2 : mlstring), strcat s t1 = strcat s t2 ↔ t1 = t2 := by
  intro s t1 t2
  cases s; cases t1; cases t2
  simp [Aux.strcat_implode]

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
  intro c1 s1 s2 _ t2
  cases t1; cases t2
  simp [Aux.strcat_implode]

/- HOL4:
Theorem mlstring_common_suffix[simp]:
  ∀s t1 t2. t1 ^ s = t2 ^ s ⇔ t1 = t2 -/
theorem mlstring_common_suffix :
    ∀ (s t1 t2 : mlstring), strcat t1 s = strcat t2 s ↔ t1 = t2 := by
  intro s t1 t2
  cases s; cases t1; cases t2
  simp [Aux.strcat_implode]

/- HOL4:
Theorem explode_strcat[simp]:
   explode (strcat s1 s2) = explode s1 ++ explode s2 -/
theorem explode_strcat (s1 s2 : mlstring) :
    explode (strcat s1 s2) = explode s1 ++ explode s2 := by
  rw [strcat_thm, explode_thm]

/- HOL4:
Theorem strlen_strcat[simp]:
   strlen (strcat s1 s2) = strlen s1 + strlen s2 -/
theorem strlen_strcat (s1 s2 : mlstring) : strlen (strcat s1 s2) = strlen s1 + strlen s2 := by
  rw [← LENGTH_explode, explode_strcat, List.length_append, LENGTH_explode, LENGTH_explode]

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
  exact explode_thm [c]

/- HOL4:
Theorem strlen_toString[simp]:
   strlen (toString c) = 1 -/
theorem strlen_toString (c : char) : strlen (chr_to_str c) = 1 := by
  rfl

/- HOL4:
Theorem substring_0[simp]:
  substring s i 0 = «» -/
theorem substring_0 (s : mlstring) (i : Nat) : substring s i 0 = mls "" := by
  cases s with
  | implode s =>
    rw [Aux.mls_empty]
    by_cases h : i ≤ s.length <;> simp [substring, h, SEG_def.1]

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

theorem Aux.char_ext {a b : char} (h : ORD a = ORD b) : a = b := by
  cases a; cases b; simp only [ORD] at h; subst h; rfl

theorem Aux.compare_aux_LESS (a b : string) (ord : ordering) : ∀ (len start : Nat),
    ((ord = LESS ∧ start + len = a.length ∧ start + len < b.length) ∨
     (ord = GREATER ∧ start + len = b.length ∧ start + len < a.length) ∨
     (ord = EQUAL ∧ start + len = a.length ∧ start + len = b.length)) →
    (compare_aux (implode a) (implode b) ord start len = LESS ↔
      string_lt (a.drop start) (b.drop start)) := by
  intro len
  induction len with
  | zero =>
    intro start h
    rw [compare_aux, if_pos rfl]
    rcases h with ⟨rfl, h1, h2⟩ | ⟨rfl, h1, h2⟩ | ⟨rfl, h1, h2⟩
    · rw [List.drop_eq_nil_of_le (by omega : a.length ≤ start),
        List.drop_eq_getElem_cons (by omega : start < b.length)]
      simp [string_lt]
    · rw [List.drop_eq_nil_of_le (by omega : b.length ≤ start)]
      simp [string_lt]
    · rw [List.drop_eq_nil_of_le (by omega : b.length ≤ start)]
      simp [string_lt]
  | succ len ih =>
    intro start h
    have ha : start < a.length := by omega
    have hb : start < b.length := by omega
    rw [compare_aux, if_neg (by omega)]
    rw [List.drop_eq_getElem_cons ha, List.drop_eq_getElem_cons hb]
    simp only [strsub, Aux.EL_eq start a ha, Aux.EL_eq start b hb, string_lt]
    by_cases h1 : char_lt b[start] a[start]
    · simp only [h1, if_true]
      have hn : ¬ char_lt a[start] b[start] := by
        simp only [char_lt] at h1 ⊢; omega
      have hne : ¬ a[start] = b[start] := by
        intro e; rw [e] at h1; simp [char_lt] at h1
      simp [hn, hne]
    · by_cases h2 : char_lt a[start] b[start]
      · simp [h1, h2]
      · have he : a[start] = b[start] := by
          apply Aux.char_ext
          simp only [char_lt] at h1 h2
          omega
        have hl : len + 1 - 1 = len := by omega
        have h' : (ord = LESS ∧ start + 1 + len = a.length ∧ start + 1 + len < b.length) ∨
            (ord = GREATER ∧ start + 1 + len = b.length ∧ start + 1 + len < a.length) ∨
            (ord = EQUAL ∧ start + 1 + len = a.length ∧ start + 1 + len = b.length) := by
          rcases h with ⟨e, h3, h4⟩ | ⟨e, h3, h4⟩ | ⟨e, h3, h4⟩
          · exact Or.inl ⟨e, by omega, by omega⟩
          · exact Or.inr (Or.inl ⟨e, by omega, by omega⟩)
          · exact Or.inr (Or.inr ⟨e, by omega, by omega⟩)
        rw [if_neg h1, if_neg h2, hl, ih (start + 1) h']
        simp [he]
        intro h; simp [char_lt] at h

/- HOL4:
Theorem mlstring_lt_inv_image:
   mlstring_lt = inv_image string_lt explode -/
theorem mlstring_lt_inv_image : mlstring_lt = inv_image string_lt explode := by
  funext s1 s2
  apply propext
  cases s1 with
  | implode a =>
  cases s2 with
  | implode b =>
  simp only [mlstring_lt, inv_image, explode_thm, Candle.compare, strlen]
  by_cases h1 : a.length < b.length
  · simp only [h1, if_true]
    exact Aux.compare_aux_LESS a b _ _ 0 (by simp; omega)
  · by_cases h2 : b.length < a.length
    · simp only [h1, h2, if_true, if_false]
      exact Aux.compare_aux_LESS a b _ _ 0 (by simp; omega)
    · simp only [h1, h2, if_false]
      exact Aux.compare_aux_LESS a b _ _ 0 (by simp; omega)

theorem Aux.string_lt_irrefl : ∀ s : string, ¬ string_lt s s
  | [] => by simp [string_lt]
  | a :: s => by
    have := Aux.string_lt_irrefl s
    simp [string_lt, char_lt, this]

theorem Aux.string_lt_trans : ∀ a b c : string, string_lt a b → string_lt b c → string_lt a c
  | _, _, [], _, h => by simp [string_lt] at h
  | _, [], _ :: _, h, _ => by simp [string_lt] at h
  | [], _ :: _, _ :: _, _, _ => by simp [string_lt]
  | x :: a, y :: b, z :: c, h1, h2 => by
    have ih := Aux.string_lt_trans a b c
    simp only [string_lt, char_lt] at h1 h2 ⊢
    rcases h1 with h1 | ⟨rfl, h1⟩
    · rcases h2 with h2 | ⟨rfl, h2⟩
      · left; omega
      · left; exact h1
    · rcases h2 with h2 | ⟨rfl, h2⟩
      · left; exact h2
      · right; exact ⟨rfl, ih h1 h2⟩

theorem Aux.string_lt_trichotomous : ∀ a b : string, string_lt a b ∨ string_lt b a ∨ a = b
  | [], [] => by simp
  | [], _ :: _ => by simp [string_lt]
  | _ :: _, [] => by simp [string_lt]
  | x :: a, y :: b => by
    have ih := Aux.string_lt_trichotomous a b
    simp only [string_lt, char_lt, List.cons.injEq]
    by_cases h1 : ORD x < ORD y
    · simp [h1]
    · by_cases h2 : ORD y < ORD x
      · simp [h2]
      · have : x = y := Aux.char_ext (by omega)
        subst this
        simpa using ih

theorem Aux.StrongLinearOrder_string_lt : StrongLinearOrder string_lt :=
  ⟨⟨Aux.string_lt_irrefl, fun a b c h => Aux.string_lt_trans a b c h.1 h.2⟩,
    Aux.string_lt_trichotomous⟩

/- HOL4:
Theorem StrongLinearOrder_mlstring_lt:
   StrongLinearOrder mlstring_lt -/
theorem StrongLinearOrder_mlstring_lt : StrongLinearOrder mlstring_lt := by
  rw [mlstring_lt_inv_image]
  refine ⟨⟨irreflexive_inv_image _ _ Aux.string_lt_irrefl, ?_⟩, ?_⟩
  · intro a b c ⟨h1, h2⟩
    exact Aux.string_lt_trans _ _ _ h1 h2
  · exact trichotomous_inv_image _ _ ⟨Aux.string_lt_trichotomous, explode_BIJ.1⟩

theorem Aux.ALL_DISTINCT_map {α β : Type} {f : α → β} (hf : ∀ x y, f x = f y → x = y)
    (l : List α) : ALL_DISTINCT (l.map f) ↔ ALL_DISTINCT l := by
  induction l with
  | nil => simp [ALL_DISTINCT]
  | cons a t ih =>
    simp only [List.map_cons, ALL_DISTINCT, ih, List.mem_map]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨fun h => h1 ⟨a, h, rfl⟩, h2⟩
    · rintro ⟨h1, h2⟩
      refine ⟨?_, h2⟩
      rintro ⟨x, hx, e⟩
      exact h1 (hf _ _ e ▸ hx)

/- HOL4:
Theorem ALL_DISTINCT_MAP_implode[simp]:
   ALL_DISTINCT ls ⇒ ALL_DISTINCT (MAP implode ls) -/
theorem ALL_DISTINCT_MAP_implode (ls : List string) :
    ALL_DISTINCT ls → ALL_DISTINCT (List.map implode ls) := by
  exact (Aux.ALL_DISTINCT_map (fun _ _ h => mlstring.implode.inj h) ls).mpr

/- HOL4:
Theorem ALL_DISTINCT_MAP_explode[simp]:
   ∀ls. ALL_DISTINCT (MAP explode ls) ⇔ ALL_DISTINCT ls -/
theorem ALL_DISTINCT_MAP_explode :
    ∀ (ls : List mlstring), ALL_DISTINCT (List.map explode ls) ↔ ALL_DISTINCT ls := by
  exact Aux.ALL_DISTINCT_map (fun x y h => (explode_11 x y).mp h)

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
  cases x
  simp [concat]

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
