import CmlTS.Prelude.Set
import CmlTS.Prelude.List
import CmlTS.Prelude.Fmap
import CmlTS.Prelude.Llist
import CmlTS.Prelude.String
import CmlTS.Prelude.Sptree
import CmlTS.LprefixLub
/-
  Translation of HOL4 theory `misc` (miscScript.sml).
-/
set_option autoImplicit false

namespace CmlTS
open Classical

universe u v w x

/- HOL4:
Definition the_def:
  the _ (SOME x) = x ∧
  the x NONE =  x
End -/
def the {α : Type u} : α → Option α → α
  | _, some x => x
  | x, none => x

/- HOL4:
   ∀s. FINITE s ⇒ (∀x. x ∈ s ⇒ f x ∈ s) ∧ CARD (IMAGE f s) = CARD s ⇒ BIJ f s s -/
theorem CARD_IMAGE_ID_BIJ {α : Type} {f : α → α} :
    ∀ s : Set α, FINITE s → (∀ x, x ∈ s → f x ∈ s) ∧ CARD (IMAGE f s) = CARD s → BIJ f s s := by
  sorry

/- HOL4:
Datatype:
  app_list = List ('a list) | Append app_list app_list | Nil
End -/
inductive app_list (α : Type u) : Type u
  | List (xs : List α)
  | Append (l1 l2 : app_list α)
  | Nil
  deriving Inhabited

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
   (ARB on the argument shapes that are not listed) -/
noncomputable def MAP3 {α : Type u} {β : Type v} {γ : Type w} {δ : Type x}
    (f : α → β → γ → δ) : List α → List β → List γ → List δ
  | [], [], [] => []
  | h1 :: t1, h2 :: t2, h3 :: t3 => f h1 h2 h3 :: MAP3 f t1 t2 t3
  | _, _, _ => ARB

/- HOL4:
Definition tlookup_def:
  tlookup m k = case lookup k m of NONE => k | SOME k => k
End -/
def tlookup (m : spt Nat) (k : Nat) : Nat :=
  match lookup k m with
  | none => k
  | some k => k

/- HOL4:
   set (toList names) = domain names ⇒
   BIJ (tlookup names) UNIV UNIV -/
theorem tlookup_bij_suff {names : spt Nat} :
    LIST_TO_SET (toList names) = domain names →
    BIJ (tlookup names) UNIV UNIV := by
  sorry

/- HOL4:
   BIJ (tlookup names) UNIV UNIV ⇔
   set (toList names) = domain names -/
theorem tlookup_bij_iff {names : spt Nat} :
    BIJ (tlookup names) UNIV UNIV ↔
    LIST_TO_SET (toList names) = domain names := by
  sorry

/- HOL4:
Definition max3_def[simp]:
  max3 (x:num) y z = if x > y then (if z > x then z else x)
                     else (if z > y then z else y)
End -/
def max3 (x y z : Nat) : Nat :=
  if x > y then (if z > x then z else x)
  else (if z > y then z else y)

/- HOL4:
Type num_set = ``:unit spt``
Type num_map = ``:'a spt`` -/
abbrev num_set : Type := spt Unit
abbrev num_map (α : Type u) : Type u := spt α

/- HOL4:
Definition UPDATE_LIST_def:
  UPDATE_LIST = FOLDL (combin$C (UNCURRY UPDATE))
End
val _ = Parse.add_infix("=++",500,Parse.LEFT)
Overload "=++" = ``UPDATE_LIST`` -/
noncomputable def UPDATE_LIST {α : Type u} {β : Type v} : (α → β) → List (α × β) → α → β :=
  List.foldl (C (UNCURRY UPDATE))

/- HOL4:
Definition find_index_def:
  (find_index _ [] _ = NONE) ∧
  (find_index y (x::xs) n = if x = y then SOME n else find_index y xs (n+1))
End -/
noncomputable def find_index {α : Type u} (y : α) : List α → Nat → Option Nat
  | [], _ => none
  | x :: xs, n => if x = y then some n else find_index y xs (n + 1)

/- HOL4:
 ∀ls n m i. (find_index n ls m = SOME i) ⇒ (m <= i) ∧ (i < m + LENGTH ls) -/
theorem find_index_LESS_LENGTH {α : Type} :
    ∀ (ls : List α) (n : α) (m i : Nat),
      find_index n ls m = some i → m ≤ i ∧ i < m + ls.length := by
  sorry

/- HOL4:
   (ALOOKUP env k = SOME v) ⇒
    ∃i. (find_index k (MAP FST env) 0 = SOME i) ∧
        i < LENGTH env ∧ (v = SND (EL i env)) -/
theorem ALOOKUP_find_index_SOME {α β : Type} [Nonempty α] [Nonempty β]
    {env : List (α × β)} {k : α} {v : β} :
    ALOOKUP env k = some v →
      ∃ i, find_index k (env.map Prod.fst) 0 = some i ∧
        i < env.length ∧ v = (EL i env).2 := by
  sorry

/- HOL4:
  !l2 l1. IS_PREFIX l1 l2 <=> (LENGTH l2 <= LENGTH l1) /\ !n. n < LENGTH l2 ==> (EL n l2 = EL n l1) -/
theorem IS_PREFIX_THM {α : Type} [Nonempty α] :
    ∀ l2 l1 : List α,
      l2 <+: l1 ↔ l2.length ≤ l1.length ∧ ∀ n, n < l2.length → EL n l2 = EL n l1 := by
  sorry

/- HOL4:
Definition between_def:
  between x y z ⇔ x:num ≤ z ∧ z < y
End -/
def between (x y z : Nat) : Prop := x ≤ z ∧ z < y

/- HOL4:
 (λ(n,v). n) = FST -/
theorem FST_pair {α β : Type} : (fun ((n, _v) : α × β) => n) = Prod.fst := by
  sorry

/- HOL4:
 x < 1 ⇔ (x = 0:num) -/
theorem LESS_1 {x : Nat} : x < 1 ↔ x = 0 := by
  sorry

/- HOL4:
 !l1 l2. (MAP SOME l1 = MAP SOME l2) ⇔ (l1 = l2) -/
theorem map_some_eq {α : Type} :
    ∀ l1 l2 : List α, l1.map some = l2.map some ↔ l1 = l2 := by
  sorry

/- HOL4:
 !l1 l2 l3. (MAP SOME l1 ++ MAP SOME l2 = MAP SOME l3) ⇔ (l1 ++ l2 = l3) -/
theorem map_some_eq_append {α : Type} :
    ∀ l1 l2 l3 : List α, l1.map some ++ l2.map some = l3.map some ↔ l1 ++ l2 = l3 := by
  sorry

/- HOL4:
   !xs ys f.
      (!x y. MEM x xs /\ MEM y ys /\ (f x = f y) ==> (x = y)) ==>
      (MAP f xs = MAP f ys) ==> (xs = ys) -/
theorem MAP_EQ_MAP_IMP {α β : Type} :
    ∀ (xs ys : List α) (f : α → β),
      (∀ x y, x ∈ xs ∧ y ∈ ys ∧ f x = f y → x = y) →
      xs.map f = ys.map f → xs = ys := by
  sorry

/- HOL4:
Definition lookup_vars_def:
  (lookup_vars [] env = SOME []) /\
  (lookup_vars (v::vs) env =
     if v < LENGTH env then
       case lookup_vars vs env of
       | SOME xs => SOME (EL v env :: xs)
       | NONE => NONE
     else NONE)
End -/
noncomputable def lookup_vars {α : Type u} [Nonempty α] : List Nat → List α → Option (List α)
  | [], _ => some []
  | v :: vs, env =>
    if v < env.length then
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
   x ∈ FDOM f ⇔ ∃v. FLOOKUP f x = SOME v -/
theorem FDOM_FLOOKUP {α β : Type} {f : fmap α β} {x : α} :
    x ∈ FDOM f ↔ ∃ v, FLOOKUP f x = some v := by
  sorry

/- HOL4:
   !ls n. (DROP n ls = []) ==> (n >= LENGTH ls) -/
theorem DROP_EMPTY {α : Type} :
    ∀ (ls : List α) (n : Nat), ls.drop n = [] → n ≥ ls.length := by
  sorry

/- HOL4:
   $+ 0n = I -/
theorem plus_0_I : (fun x : Nat => 0 + x) = I := by
  sorry

/- HOL4:
Definition range_def:
  range s = {v | ∃n. lookup n s = SOME v}
End -/
def range {α : Type u} (s : spt α) : Set α := {v | ∃ n, lookup n s = some v}

end CmlTS
