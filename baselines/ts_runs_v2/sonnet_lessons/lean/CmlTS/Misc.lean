import CmlTS.Prelude.Basic
import CmlTS.Prelude.List
import CmlTS.Prelude.Num
import CmlTS.Prelude.FMap
import CmlTS.Prelude.Coalg
import CmlTS.Prelude.Sort

/-!
# misc (HOL4 theory `misc`): miscellaneous definitions
-/

universe u v w

noncomputable section

open Classical

/- HOL4:
   (* Total version of THE *)
   Definition the_def:
     the _ (SOME x) = x ∧
     the x NONE =  x
   End -/
def the {α : Type u} : α → Option α → α
  | _, some x => x
  | x, none => x

/- HOL4:
   Datatype:
     app_list = List ('a list) | Append app_list app_list | Nil
   End -/
inductive app_list (α : Type u) : Type u where
  | List (l : List α) : app_list α
  | Append (l1 l2 : app_list α) : app_list α
  | Nil : app_list α

/- HOL4:
   Definition append_aux_def:
     (append_aux Nil aux = aux) /\
     (append_aux (List xs) aux = xs ++ aux) /\
     (append_aux (Append l1 l2) aux = append_aux l1 (append_aux l2 aux))
   End -/
def append_aux {α : Type u} : app_list α → List α → List α
  | .Nil, aux => aux
  | .List xs, aux => xs ++ aux
  | .Append l1 l2, aux => append_aux l1 (append_aux l2 aux)

/- HOL4:
   Definition append_def:
     append l = append_aux l []
   End -/
def append {α : Type u} (l : app_list α) : List α := append_aux l []

/- HOL4:
   Definition MAP3_def[simp]:
     (MAP3 f [] [] [] = []) /\
     (MAP3 f (h1::t1) (h2::t2) (h3::t3) = f h1 h2 h3::MAP3 f t1 t2 t3)
   End
   (the other cases are unspecified: `ARB`) -/
def MAP3 {α : Type u} {β : Type v} {γ : Type w} {δ : Type _}
    (f : α → β → γ → δ) : List α → List β → List γ → List δ
  | [], [], [] => []
  | h1 :: t1, h2 :: t2, h3 :: t3 => f h1 h2 h3 :: MAP3 f t1 t2 t3
  | _, _, _ => ARB

/- HOL4:
   Definition tlookup_def:
     tlookup m k = case lookup k m of NONE => k | SOME k => k
   End -/
def tlookup (m : spt Nat) (k : Nat) : Nat :=
  match sptree.lookup k m with
  | none => k
  | some k => k

/- HOL4:
   Definition max3_def[simp]:
     max3 (x:num) y z = if x > y then (if z > x then z else x)
                        else (if z > y then z else y)
   End -/
def max3 (x y z : Nat) : Nat :=
  if x > y then (if z > x then z else x)
  else (if z > y then z else y)

/- HOL4:
   Definition UPDATE_LIST_def:
     UPDATE_LIST = FOLDL (combin$C (UNCURRY UPDATE))
   End
   val _ = Parse.add_infix("=++",500,Parse.LEFT)
   Overload "=++" = ``UPDATE_LIST`` -/
def UPDATE_LIST {α : Type u} {β : Type v} : (α → β) → List (α × β) → (α → β) :=
  FOLDL (flip (UNCURRY UPDATE))

/-- HOL4 `f =++ l` is `UPDATE_LIST f l` -/
infixl:500 " =++ " => UPDATE_LIST

/- HOL4:
   Definition find_index_def:
     (find_index _ [] _ = NONE) ∧
     (find_index y (x::xs) n = if x = y then SOME n else find_index y xs (n+1))
   End -/
def find_index {α : Type u} : α → List α → Nat → Option Nat
  | _, [], _ => none
  | y, x :: xs, n => if x = y then some n else find_index y xs (n + 1)

/- HOL4:
   Definition between_def:
     between x y z ⇔ x:num ≤ z ∧ z < y
   End -/
def between (x y z : Nat) : Prop := x ≤ z ∧ z < y

/- HOL4:
   (* lookup_vars vs env = OPT_MMAP (\i. oEL i env) vs *)
   Definition lookup_vars_def:
     (lookup_vars [] env = SOME []) /\
     (lookup_vars (v::vs) env =
        if v < LENGTH env then
          case lookup_vars vs env of
          | SOME xs => SOME (EL v env :: xs)
          | NONE => NONE
        else NONE)
   End -/
def lookup_vars {α : Type u} [Nonempty α] : List Nat → List α → Option (List α)
  | [], _ => some []
  | v :: vs, env =>
    if v < LENGTH env then
      match lookup_vars vs env with
      | some xs => some (EL v env :: xs)
      | none => none
    else none

/- HOL4:
   Definition enumerate_def:
     (enumerate n [] = []) ∧
     (enumerate n (x::xs) = (n,x)::enumerate (n+1n) xs)
   End -/
def enumerate {α : Type u} : Nat → List α → List (Nat × α)
  | _, [] => []
  | n, x :: xs => (n, x) :: enumerate (n + 1) xs

/- HOL4:
   Definition range_def:
     range s = {v | ∃n. lookup n s = SOME v}
   End -/
def range {α : Type u} (s : spt α) : Set α := fun v => ∃ n, sptree.lookup n s = some v

/-! ## Theorems (stage 2) -/

/- HOL4: Theorem CARD_IMAGE_ID_BIJ:
     ∀s. FINITE s ⇒ (∀x. x ∈ s ⇒ f x ∈ s) ∧ CARD (IMAGE f s) = CARD s ⇒ BIJ f s s -/
theorem CARD_IMAGE_ID_BIJ {α : Type u} (f : α → α) :
    ∀ s : Set α, FINITE s → ((∀ x, x ∈ s → f x ∈ s) ∧ CARD (IMAGE f s) = CARD s) →
      BIJ f s s := by
  sorry

/- HOL4: Theorem tlookup_bij_suff:
     set (toList names) = domain names ⇒
     BIJ (tlookup names) UNIV UNIV -/
theorem tlookup_bij_suff (names : spt Nat) :
    LIST_TO_SET (sptree.toList names) = sptree.domain names →
    BIJ (tlookup names) UNIV UNIV := by
  sorry

/- HOL4: Theorem tlookup_bij_iff:
     BIJ (tlookup names) UNIV UNIV ⇔
     set (toList names) = domain names -/
theorem tlookup_bij_iff (names : spt Nat) :
    BIJ (tlookup names) UNIV UNIV ↔
    LIST_TO_SET (sptree.toList names) = sptree.domain names := by
  sorry

/- HOL4: Theorem find_index_LESS_LENGTH:
     ∀ls n m i. (find_index n ls m = SOME i) ⇒ (m <= i) ∧ (i < m + LENGTH ls) -/
theorem find_index_LESS_LENGTH {α : Type u} :
    ∀ (ls : List α) (n : α) (m i : Nat),
      find_index n ls m = some i → (m ≤ i) ∧ (i < m + LENGTH ls) := by
  sorry

/- HOL4: Theorem ALOOKUP_find_index_SOME:
     (ALOOKUP env k = SOME v) ⇒
     ∃i. (find_index k (MAP FST env) 0 = SOME i) ∧
         i < LENGTH env ∧ (v = SND (EL i env)) -/
theorem ALOOKUP_find_index_SOME {α : Type u} {β : Type v} [Nonempty α] [Nonempty β]
    (env : List (α × β)) (k : α) (v : β) :
    ALOOKUP env k = some v →
    ∃ i, (find_index k (MAP FST env) 0 = some i) ∧
         i < LENGTH env ∧ (v = SND (EL i env)) := by
  sorry

/- HOL4: Theorem IS_PREFIX_THM:
     !l2 l1. IS_PREFIX l1 l2 <=> (LENGTH l2 <= LENGTH l1) /\ !n. n < LENGTH l2 ==> (EL n l2 = EL n l1) -/
theorem IS_PREFIX_THM {α : Type u} [Nonempty α] :
    ∀ (l2 l1 : List α), IS_PREFIX l1 l2 ↔
      (LENGTH l2 ≤ LENGTH l1) ∧ ∀ n, n < LENGTH l2 → (EL n l2 = EL n l1) := by
  sorry

/- HOL4: Theorem FST_pair:
     (λ(n,v). n) = FST -/
theorem FST_pair {α : Type u} {β : Type v} :
    (fun p : α × β => match p with | (n, _) => n) = (FST : α × β → α) := by
  sorry

/- HOL4: Theorem LESS_1[simp]:
     x < 1 ⇔ (x = 0:num) -/
theorem LESS_1 : ∀ x : Nat, x < 1 ↔ (x = 0) := by
  sorry

/- HOL4: Theorem map_some_eq:
     !l1 l2. (MAP SOME l1 = MAP SOME l2) ⇔ (l1 = l2) -/
theorem map_some_eq {α : Type u} :
    ∀ l1 l2 : List α, (MAP some l1 = MAP some l2) ↔ (l1 = l2) := by
  sorry

/- HOL4: Theorem map_some_eq_append:
     !l1 l2 l3. (MAP SOME l1 ++ MAP SOME l2 = MAP SOME l3) ⇔ (l1 ++ l2 = l3) -/
theorem map_some_eq_append {α : Type u} :
    ∀ l1 l2 l3 : List α, (MAP some l1 ++ MAP some l2 = MAP some l3) ↔ (l1 ++ l2 = l3) := by
  sorry

/- HOL4: Theorem MAP_EQ_MAP_IMP:
     !xs ys f.
        (!x y. MEM x xs /\ MEM y ys /\ (f x = f y) ==> (x = y)) ==>
        (MAP f xs = MAP f ys) ==> (xs = ys) -/
theorem MAP_EQ_MAP_IMP {α : Type u} {β : Type v} :
    ∀ (xs ys : List α) (f : α → β),
      (∀ x y, MEM x xs ∧ MEM y ys ∧ (f x = f y) → (x = y)) →
      (MAP f xs = MAP f ys) → (xs = ys) := by
  sorry

/- HOL4: Theorem FDOM_FLOOKUP:
     x ∈ FDOM f ⇔ ∃v. FLOOKUP f x = SOME v -/
theorem FDOM_FLOOKUP {α : Type u} {β : Type v} (x : α) (f : FMap α β) :
    x ∈ FDOM f ↔ ∃ v, FLOOKUP f x = some v := by
  sorry

/- HOL4: Theorem DROP_EMPTY:
     !ls n. (DROP n ls = []) ==> (n >= LENGTH ls) -/
theorem DROP_EMPTY {α : Type u} :
    ∀ (ls : List α) (n : Nat), (DROP n ls = []) → (n ≥ LENGTH ls) := by
  sorry

/- HOL4: Theorem plus_0_I[simp]:
     $+ 0n = I -/
theorem plus_0_I : (fun n : Nat => 0 + n) = (id : Nat → Nat) := by
  sorry

end
