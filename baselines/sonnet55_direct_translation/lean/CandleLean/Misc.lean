import CandleLean.Prelude.Sort
/-
  Translation of `misc/miscScript.sml` (only the definitions needed by the target theorems).
  Namespace `Candle.Misc`.
-/
namespace Candle.Misc

open HOL
universe u v

open Classical

noncomputable section

/- HOL4: Definition the_def:
  the _ (SOME x) = x ∧
  the x NONE =  x
End -/
def the {α : Type u} : α → Option α → α
  | _, some x => x
  | x, none => x

/- HOL4: Datatype:
  app_list = List ('a list) | Append app_list app_list | Nil
End -/
inductive app_list (α : Type u) where
  | List : _root_.List α → app_list α
  | Append : app_list α → app_list α → app_list α
  | Nil : app_list α

/- HOL4: Definition append_aux_def:
  (append_aux Nil aux = aux) /\
  (append_aux (List xs) aux = xs ++ aux) /\
  (append_aux (Append l1 l2) aux = append_aux l1 (append_aux l2 aux))
End -/
def append_aux {α : Type u} : app_list α → _root_.List α → _root_.List α
  | .Nil, aux => aux
  | .List xs, aux => xs ++ aux
  | .Append l1 l2, aux => append_aux l1 (append_aux l2 aux)

/- HOL4: Definition append_def:
  append l = append_aux l []
End -/
def append {α : Type u} (l : app_list α) : _root_.List α := append_aux l []

/- HOL4: Definition SmartAppend_def[simp]:
  (SmartAppend Nil l2 = l2) ∧
  (SmartAppend l1 Nil = l1) ∧
  (SmartAppend l1 l2 = Append l1 l2)
End -/
def SmartAppend {α : Type u} : app_list α → app_list α → app_list α
  | .Nil, l2 => l2
  | l1, .Nil => l1
  | l1, l2 => .Append l1 l2

/- HOL4: Definition max3_def[simp]:
  max3 (x:num) y z = if x > y then (if z > x then z else x)
                     else (if z > y then z else y)
End -/
def max3 (x y z : Nat) : Nat :=
  if x > y then (if z > x then z else x) else (if z > y then z else y)

/- HOL4: Definition UPDATE_LIST_def:
  UPDATE_LIST = FOLDL (combin$C (UNCURRY UPDATE))
End
   (infix `=++`, Overload "=++" = UPDATE_LIST) -/
def UPDATE_LIST {α : Type u} {β : Type v} (f : α → β) (l : _root_.List (α × β)) : α → β :=
  FOLDL (C (UNCURRY (UPDATE (α := α) (β := β)))) f l
scoped infixl:500 " =++ " => UPDATE_LIST

/- HOL4: Definition find_index_def:
  (find_index _ [] _ = NONE) ∧
  (find_index y (x::xs) n = if x = y then SOME n else find_index y xs (n+1))
End -/
def find_index {α : Type u} : α → _root_.List α → Nat → Option Nat
  | _, [], _ => none
  | y, x :: xs, n => if x = y then some n else find_index y xs (n + 1)

/- HOL4: Definition splitlines_def:
  splitlines ls =
  let lines = FIELDS ((=) #"\n") ls in
  (* discard trailing newline *)
  if NULL (LAST lines) then FRONT lines else lines
End -/
def splitlines (ls : string) : _root_.List string :=
  let lines := FIELDS (fun c => hchar '\n' = c) ls
  if NULL (LAST lines) then FRONT lines else lines

/- HOL4: Definition is_subseq_def:
  (is_subseq ls [] ⇔ T) ∧
  (is_subseq [] (x::xs) ⇔ F) ∧
  (is_subseq (y::ys) (x::xs) ⇔
   (x = y ∧ is_subseq ys xs) ∨
   (is_subseq ys (x::xs)))
End -/
def is_subseq {α : Type u} : _root_.List α → _root_.List α → Prop
  | _, [] => True
  | [], _ :: _ => False
  | y :: ys, x :: xs => (x = y ∧ is_subseq ys xs) ∨ is_subseq ys (x :: xs)

/- HOL4: Definition make_even_def:
  make_even n = if EVEN n then n else n+1
End -/
def make_even (n : Nat) : Nat := if EVEN n then n else n + 1

/- HOL4: Definition fmap_update_def[simp]:
  fmap_update f k v = f |+ (k,v)
End -/
def fmap_update {α : Type u} {β : Type v} (f : FMap α β) (k : α) (v : β) : FMap α β := f |+ (k, v)

/-! ## Target theorems -/

/- HOL4: Theorem append_aux_thm:
   !l xs. append_aux l xs = append_aux l [] ++ xs -/
theorem append_aux_thm {α : Type u} : ∀ (l : app_list α) (xs : _root_.List α),
    append_aux l xs = append_aux l [] ++ xs := by sorry

/- HOL4: Theorem append_thm[simp]:
   append (Append l1 l2) = append l1 ++ append l2 /\
    append (List xs) = xs /\
    append Nil = [] -/
theorem append_thm {α : Type u} (l1 l2 : app_list α) (xs : _root_.List α) :
    append (app_list.Append l1 l2) = append l1 ++ append l2 ∧
    append (app_list.List xs) = xs ∧
    append (app_list.Nil : app_list α) = [] := by sorry

/- HOL4: Theorem SmartAppend_thm:
   ∀l1 l2.
    SmartAppend l1 l2 =
      if l1 = Nil then l2 else
      if l2 = Nil then l1 else Append l1 l2 -/
theorem SmartAppend_thm {α : Type u} : ∀ (l1 l2 : app_list α),
    SmartAppend l1 l2 =
      if l1 = app_list.Nil then l2 else
      if l2 = app_list.Nil then l1 else app_list.Append l1 l2 := by sorry

/- HOL4: Theorem append_SmartAppend[simp]:
   append (SmartAppend l1 l2) = append l1 ++ append l2 -/
theorem append_SmartAppend {α : Type u} (l1 l2 : app_list α) :
    append (SmartAppend l1 l2) = append l1 ++ append l2 := by sorry

/- HOL4: Theorem MAP_FST_I_PAIR_MAP[simp]:
   !xs. MAP FST (MAP (I ## f) xs) = MAP FST xs -/
theorem MAP_FST_I_PAIR_MAP {α : Type u} {β : Type v} {γ : Type _} (f : β → γ) :
    ∀ (xs : _root_.List (α × β)), MAP FST (MAP (I ## f) xs) = MAP FST xs := by sorry

/- HOL4: Theorem MAX_LIST_APPEND[simp]:
   MAX_LIST (xs++ys) = MAX (MAX_LIST xs) (MAX_LIST ys) -/
theorem MAX_LIST_APPEND (xs ys : _root_.List Nat) :
    MAX_LIST (xs ++ ys) = MAX (MAX_LIST xs) (MAX_LIST ys) := by sorry

/- HOL4: Theorem MAX_LIST_SNOC[simp]:
   MAX_LIST (SNOC x xs) = MAX (MAX_LIST xs) x -/
theorem MAX_LIST_SNOC (x : Nat) (xs : _root_.List Nat) :
    MAX_LIST (SNOC x xs) = MAX (MAX_LIST xs) x := by sorry

/- HOL4: Theorem domain_nat_set_from_list[simp]:
   ∀ls ns. domain (FOLDL (λs n. insert n () s) ns ls) = domain ns ∪ set ls -/
theorem domain_nat_set_from_list :
    ∀ (ls : _root_.List Nat) (ns : num_set),
      spt.domain (FOLDL (fun (s : num_set) (n : Nat) => spt.insert n () s) ns ls)
        = spt.domain ns ∪ LIST_TO_SET ls := by sorry

/- HOL4: Theorem UPDATE_LIST_THM:
   ∀f. (f =++ [] = f) ∧ ∀h t. (f =++ (h::t) = (FST h =+ SND h) f =++ t) -/
theorem UPDATE_LIST_THM {α : Type u} {β : Type v} :
    ∀ (f : α → β), ((f =++ []) = f) ∧
      ∀ (h : α × β) (t : _root_.List (α × β)),
        ((f =++ (h :: t)) = (((FST h =+ SND h) f) =++ t)) := by sorry

/- HOL4: Theorem APPLY_UPDATE_LIST_ALOOKUP:
   ∀ls f x. (f =++ ls) x = case ALOOKUP (REVERSE ls) x of NONE => f x | SOME y => y -/
theorem APPLY_UPDATE_LIST_ALOOKUP {α : Type u} {β : Type v} :
    ∀ (ls : _root_.List (α × β)) (f : α → β) (x : α),
      (f =++ ls) x = (match ALOOKUP (REVERSE ls) x with
                      | none => f x
                      | some y => y) := by sorry

/- HOL4: Theorem find_index_ALL_DISTINCT_EL[simp]:
 ∀ls n m. ALL_DISTINCT ls ∧ n < LENGTH ls ⇒ (find_index (EL n ls) ls m = SOME (m + n)) -/
theorem find_index_ALL_DISTINCT_EL {α : Type u} [Inhabited α] :
    ∀ (ls : _root_.List α) (n m : Nat),
      ALL_DISTINCT ls ∧ n < LENGTH ls → (find_index (EL n ls) ls m = some (m + n)) := by sorry

/- HOL4: Theorem find_index_shift_0:
   ∀ls x k. find_index x ls k = OPTION_MAP (λx. x + k) (find_index x ls 0) -/
theorem find_index_shift_0 {α : Type u} :
    ∀ (ls : _root_.List α) (x : α) (k : Nat),
      find_index x ls k = OPTION_MAP (fun x => x + k) (find_index x ls 0) := by sorry

/- HOL4: Theorem EVERY2_RC_same[simp]:
   EVERY2 (RC R) l l -/
theorem EVERY2_RC_same {α : Type u} (R : α → α → Prop) (l : _root_.List α) :
    EVERY2 (RC R) l l := by sorry

/- HOL4: Theorem I_PERMUTES[simp]:
   I PERMUTES s -/
theorem I_PERMUTES {α : Type u} (s : HOL.Set α) : PERMUTES I s := by sorry

/- HOL4: Theorem MAP_EQ_ID:
 !f ls. (MAP f ls = ls) = (!x. MEM x ls ==> (f x = x)) -/
theorem MAP_EQ_ID {α : Type u} :
    ∀ (f : α → α) (ls : _root_.List α), (MAP f ls = ls) = (∀ x, MEM x ls → (f x = x)) := by sorry

/- HOL4: Theorem FUN_FMAP_FAPPLY_FEMPTY_FAPPLY[simp]:
 FINITE s ==> (FUN_FMAP ($FAPPLY FEMPTY) s ' x = FEMPTY ' x) -/
theorem FUN_FMAP_FAPPLY_FEMPTY_FAPPLY {α : Type u} {β : Type v} [Inhabited β]
    (s : HOL.Set α) (x : α) :
    FINITE s → (FAPPLY (FUN_FMAP (FAPPLY (FEMPTY : FMap α β)) s) x = FAPPLY (FEMPTY : FMap α β) x) := by sorry

/- HOL4: Theorem LESS_1[simp]:
 x < 1 ⇔ (x = 0:num) -/
theorem LESS_1 (x : Nat) : x < 1 ↔ (x = 0) := by sorry

/- HOL4: Theorem num_from_hex_string_num_to_hex_string[simp]:
   num_from_hex_string (num_to_hex_string n) = n -/
theorem num_from_hex_string_num_to_hex_string (n : Nat) :
    num_from_hex_string (num_to_hex_string n) = n := by sorry

/- HOL4: Theorem MAPi_ID[simp]:
   MAPi (\x y. y) = I -/
theorem MAPi_ID {α : Type u} :
    MAPi (fun (_ : Nat) (y : α) => y) = (I : _root_.List α → _root_.List α) := by sorry

/- HOL4: Theorem OPT_MMAP_SOME[simp]:
   OPT_MMAP SOME ls = SOME ls -/
theorem OPT_MMAP_SOME {α : Type u} (ls : _root_.List α) :
    OPT_MMAP some ls = some ls := by sorry

/- HOL4: Theorem w2n_lt_256 =
  w2n_lt |> INST_TYPE [``:'a``|->``:8``]
         |> SIMP_RULE std_ss [EVAL ``dimword (:8)``]
   (i.e. !w:word8. w2n w < 256) -/
theorem w2n_lt_256 : ∀ (w : word8), w2n w < 256 := by sorry

/- HOL4: Theorem CHR_w2n_n2w_ORD:
   (CHR o w2n o (n2w:num->word8) o ORD) = I -/
theorem CHR_w2n_n2w_ORD :
    (CHR ∘ w2n ∘ (n2w : Nat → word8) ∘ ORD) = (I : char → char) := by sorry

/- HOL4: Theorem n2w_ORD_CHR_w2n:
   ((n2w:num->word8) o ORD o CHR o w2n) = I -/
theorem n2w_ORD_CHR_w2n :
    ((n2w : Nat → word8) ∘ ORD ∘ CHR ∘ w2n) = (I : word8 → word8) := by sorry

/- HOL4: Theorem CHR_w2n_n2w_ORD_simp[simp]:
   !c. CHR(w2n((n2w:num->word8)(ORD c))) = c -/
theorem CHR_w2n_n2w_ORD_simp : ∀ (c : char), CHR (w2n ((n2w : Nat → word8) (ORD c))) = c := by sorry

/- HOL4: Theorem n2w_ORD_CHR_w2n_simp[simp]:
   !w. n2w(ORD(CHR(w2n w))) = (w:word8) -/
theorem n2w_ORD_CHR_w2n_simp :
    ∀ (w : word8), (n2w : Nat → word8) (ORD (CHR (w2n w))) = w := by sorry

/- HOL4: Theorem LENGTH_FIELDS:
   ∀ls. LENGTH (FIELDS P ls) = LENGTH (FILTER P ls) + 1 -/
theorem LENGTH_FIELDS (P : char → Prop) :
    ∀ (ls : string), LENGTH (FIELDS P ls) = LENGTH (FILTER P ls) + 1 := by sorry

/- HOL4: Theorem FIELDS_NEQ_NIL[simp]:
   FIELDS P ls ≠ [] -/
theorem FIELDS_NEQ_NIL (P : char → Prop) (ls : string) : FIELDS P ls ≠ [] := by sorry

/- HOL4: Theorem FIELDS_next:
   ∀ls l1 l2.
   FIELDS P ls = l1::l2 ⇒
   LENGTH l1 < LENGTH ls ⇒
   FIELDS P (DROP (SUC (LENGTH l1)) ls) = l2 ∧
   (∃c. l1 ++ [c] ≼ ls ∧ P c) -/
theorem FIELDS_next (P : char → Prop) :
    ∀ (ls : string) (l1 : string) (l2 : _root_.List string),
      FIELDS P ls = l1 :: l2 →
      LENGTH l1 < LENGTH ls →
      FIELDS P (DROP ((LENGTH l1).succ) ls) = l2 ∧
      (∃ c, isPREFIX (l1 ++ [c]) ls ∧ P c) := by sorry

/- HOL4: Theorem splitlines_nil[simp] = EVAL“splitlines ""”
   (the EVAL result is `splitlines "" = []`) -/
theorem splitlines_nil : splitlines (hstr "") = [] := by sorry

/- HOL4: Theorem splitlines_eq_nil[simp]:
   splitlines ls = [] ⇔ (ls = []) -/
theorem splitlines_eq_nil (ls : string) : splitlines ls = [] ↔ (ls = []) := by sorry

/- HOL4: Theorem irreflexive_inv_image:
   !R f. irreflexive R ==> irreflexive (inv_image R f) -/
theorem irreflexive_inv_image {α : Type u} {β : Type v} :
    ∀ (R : β → β → Prop) (f : α → β), irreflexive R → irreflexive (inv_image R f) := by sorry

/- HOL4: Theorem trichotomous_inv_image:
   !R f. trichotomous R /\ (INJ f UNIV UNIV) ==> trichotomous (inv_image R f) -/
theorem trichotomous_inv_image {α : Type u} {β : Type v} :
    ∀ (R : β → β → Prop) (f : α → β),
      trichotomous R ∧ (INJ f UNIV UNIV) → trichotomous (inv_image R f) := by sorry

/- HOL4: Theorem plus_0_I[simp]:
   $+ 0n = I -/
theorem plus_0_I : (HAdd.hAdd (0 : Nat) : Nat → Nat) = I := by sorry

/- HOL4: Theorem OPTION_MAP_I[simp]:
   OPTION_MAP I x = x -/
theorem OPTION_MAP_I {α : Type u} (x : Option α) : OPTION_MAP I x = x := by sorry

/- HOL4: Theorem is_subseq_refl[simp]:
   ∀ls. is_subseq ls ls -/
theorem is_subseq_refl {α : Type u} : ∀ (ls : _root_.List α), is_subseq ls ls := by sorry

/- HOL4: Theorem is_subseq_nil[simp]:
   is_subseq [] ls ⇔ ls = [] -/
theorem is_subseq_nil {α : Type u} (ls : _root_.List α) : is_subseq [] ls ↔ ls = [] := by sorry

/- HOL4: Theorem EVEN_make_even[simp]:
   EVEN (make_even x) -/
theorem EVEN_make_even (x : Nat) : EVEN (make_even x) := by sorry

/- HOL4: Theorem v2w_32_F[simp]:
   (v2w [F] : word32) = 0w -/
theorem v2w_32_F : (v2w [False] : word32) = (n2w 0 : word32) := by sorry

/- HOL4: Theorem v2w_32_T[simp]:
   (v2w [T] : word32) = 1w -/
theorem v2w_32_T : (v2w [True] : word32) = (n2w 1 : word32) := by sorry

end

end Candle.Misc
