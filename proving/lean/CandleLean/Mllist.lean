import CandleLean.Misc

/-!
# mllist (CakeML `basis/pure/mllistScript.sml`), reduced to what the targets need

The mergesort functions the targets mention (`merge_tail`, `sort2_tail`, `sort3_tail`,
`mergesortN_tail`, `mergesort_tail`) are HOL4 library constants (theory `mergesort`),
translated in `CandleLean/Prelude/List.lean` (namespace `HOL`).
-/

universe u

namespace Candle

open HOL Classical

noncomputable section

/-! Auxiliary lemmas (namespace `Candle.Aux`). -/

theorem Aux.PERM_of_perm {α : Type u} {l1 l2 : List α} (h : l1.Perm l2) : PERM l1 l2 := by
  intro x
  induction h with
  | nil => rfl
  | cons a _ ih => simp only [FILTER, ih]
  | swap a b l =>
    simp only [FILTER]
    by_cases h1 : x = a
    · by_cases h2 : x = b
      · subst h1; subst h2; rfl
      · subst h1; simp [h2]
    · simp [h1]
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

theorem Aux.REV_eq {α : Type u} (l acc : List α) : REV l acc = l.reverse ++ acc := by
  induction l generalizing acc with
  | nil => rfl
  | cons a t ih => simp [REV, ih]

theorem Aux.merge_tail_perm {α : Type u} (negate : Prop) (R : α → α → Prop)
    (xs ys acc : List α) : (xs ++ ys ++ acc).Perm (merge_tail negate R xs ys acc) := by
  fun_induction merge_tail negate R xs ys acc with
  | case1 => simp
  | case2 => rw [Aux.REV_eq, List.append_nil]; exact (List.reverse_perm _).symm.append_right _
  | case3 => rw [Aux.REV_eq, List.nil_append]; exact (List.reverse_perm _).symm.append_right _
  | case4 acc x l1 y l2 h ih => exact List.Perm.trans List.perm_middle.symm ih
  | case5 =>
    rename_i ih
    refine List.Perm.trans ?_ ih
    exact (List.perm_middle.append_right _).trans List.perm_middle.symm

theorem Aux.sort2_tail_perm {α : Type u} (neg : Prop) (R : α → α → Prop) (x y : α) :
    [x, y].Perm (sort2_tail neg R x y) := by
  unfold sort2_tail
  split
  · exact List.Perm.refl _
  · exact List.Perm.swap y x []

theorem Aux.sort3_tail_perm {α : Type u} (neg : Prop) (R : α → α → Prop) (x y z : α) :
    [x, y, z].Perm (sort3_tail neg R x y z) := by
  unfold sort3_tail
  split
  · split
    · exact List.Perm.refl _
    · split
      · exact (List.Perm.swap z y []).cons x
      · exact List.perm_middle (l₁ := [x, y]) (a := z) (l₂ := [])
  · split
    · split
      · exact List.Perm.swap y x [z]
      · exact (List.perm_middle (l₁ := [y, z]) (a := x) (l₂ := [])).symm
    · exact (List.reverse_perm [x, y, z]).symm

theorem Aux.mergesortN_tail_perm {α : Type u} (negate : Prop) (R : α → α → Prop) (n : Nat)
    (l : List α) : (l.take n).Perm (mergesortN_tail negate R n l) := by
  fun_induction mergesortN_tail negate R n l with
  | case1 => simp
  | case2 => simp
  | case3 => simp
  | case4 => simpa using Aux.sort2_tail_perm _ _ _ _
  | case5 => simp
  | case6 => simp
  | case7 => simpa using Aux.sort3_tail_perm _ _ _ _ _
  | case8 => simpa using Aux.sort2_tail_perm _ _ _ _
  | case9 => simp
  | case10 => simp
  | case11 negate n l len1 neg ih1 ih2 =>
    refine List.Perm.trans ?_ (Aux.merge_tail_perm _ _ _ _ _)
    rw [List.append_nil]
    refine List.Perm.trans ?_ (ih1.append ih2)
    have e : n + 4 = DIV2 (n + 4) + (n + 4 - len1) := by
      simp only [len1, DIV2]; omega
    have e2 : List.take (n + 4) l = List.take (DIV2 (n + 4)) l ++
        List.take (n + 4 - len1) (List.drop len1 l) := by
      conv => lhs; rw [e]
      rw [List.take_add]
    rw [e2]

/- HOL4:
Theorem merge_tail_MEM:
  !negate R xs ys acc. MEM x (merge_tail negate R xs ys acc) = ((MEM x xs) \/ (MEM x ys) \/ (MEM x acc)) -/
theorem merge_tail_MEM {α : Type u} (x : α) :
    ∀ (negate : Prop) (R : α → α → Prop) (xs ys acc : List α),
      (x ∈ merge_tail negate R xs ys acc) = (x ∈ xs ∨ x ∈ ys ∨ x ∈ acc) := by
  intro negate R xs ys acc
  apply propext
  rw [← (Aux.merge_tail_perm negate R xs ys acc).mem_iff]
  simp

/- HOL4:
Theorem mergesortN_tail_MEM:
  !negate R length lst. (MEM x (mergesortN_tail negate R length lst) <=> MEM x (TAKE length lst)) -/
theorem mergesortN_tail_MEM {α : Type u} (x : α) :
    ∀ (negate : Prop) (R : α → α → Prop) (length : Nat) (lst : List α),
      (x ∈ mergesortN_tail negate R length lst ↔ x ∈ List.take length lst) := by
  intro negate R length lst
  exact (Aux.mergesortN_tail_perm negate R length lst).mem_iff.symm

/- HOL4:
Theorem mergesort_tail_MEM:
  ∀R l. MEM x (mergesort$mergesort_tail R l) ⇔ MEM x l -/
theorem mergesort_tail_MEM {α : Type u} (x : α) :
    ∀ (R : α → α → Prop) (l : List α), x ∈ mergesort_tail R l ↔ x ∈ l := by
  intro R l
  have h := mergesortN_tail_MEM x False R l.length l
  rw [List.take_length] at h
  exact h

theorem Aux.mergesort_tail_perm {α : Type u} (R : α → α → Prop) (l : List α) :
    l.Perm (mergesort_tail R l) := by
  have h := Aux.mergesortN_tail_perm False R l.length l
  rw [List.take_length] at h
  exact h

/- HOL4:
Theorem merge_tail_PERM:
  !negate R xs ys acc. PERM (xs++ys++acc) (merge_tail negate R xs ys acc) -/
theorem merge_tail_PERM {α : Type u} :
    ∀ (negate : Prop) (R : α → α → Prop) (xs ys acc : List α),
      PERM (xs ++ ys ++ acc) (merge_tail negate R xs ys acc) := by
  intro negate R xs ys acc
  exact Aux.PERM_of_perm (Aux.merge_tail_perm negate R xs ys acc)

/- HOL4:
Theorem sort2_tail_PERM:
  !neg R x y. PERM [x;y] (sort2_tail neg R x y) -/
theorem sort2_tail_PERM {α : Type u} :
    ∀ (neg : Prop) (R : α → α → Prop) (x y : α), PERM [x, y] (sort2_tail neg R x y) := by
  intro neg R x y
  exact Aux.PERM_of_perm (Aux.sort2_tail_perm neg R x y)

/- HOL4:
Theorem sort3_tail_PERM:
  !neg R x y z. PERM [x;y;z] (sort3_tail neg R x y z) -/
theorem sort3_tail_PERM {α : Type u} :
    ∀ (neg : Prop) (R : α → α → Prop) (x y z : α),
      PERM [x, y, z] (sort3_tail neg R x y z) := by
  intro neg R x y z
  exact Aux.PERM_of_perm (Aux.sort3_tail_perm neg R x y z)

/- HOL4:
Theorem mergesortN_tail_PERM:
  !neg R len l. PERM (TAKE len l) (mergesortN_tail neg R len l) -/
theorem mergesortN_tail_PERM {α : Type u} :
    ∀ (neg : Prop) (R : α → α → Prop) (len : Nat) (l : List α),
      PERM (List.take len l) (mergesortN_tail neg R len l) := by
  intro neg R len l
  exact Aux.PERM_of_perm (Aux.mergesortN_tail_perm neg R len l)

/- HOL4:
Definition sort_def:
  sort = mergesort$mergesort_tail
End -/
def sort {α : Type u} : (α → α → Prop) → List α → List α := mergesort_tail

/- HOL4:
Theorem sort_MEM[simp]:
  !R L. MEM x (sort R L) ⇔ MEM x L -/
theorem sort_MEM {α : Type u} (x : α) :
    ∀ (R : α → α → Prop) (L : List α), x ∈ sort R L ↔ x ∈ L := by
  exact mergesort_tail_MEM x

/- HOL4:
Theorem sort_PERM:
  !R L. sorting$PERM L (sort R L) -/
theorem sort_PERM {α : Type u} :
    ∀ (R : α → α → Prop) (L : List α), PERM L (sort R L) := by
  intro R L
  exact Aux.PERM_of_perm (Aux.mergesort_tail_perm R L)

/- HOL4:
Theorem sort_LENGTH[simp]:
  !R l. LENGTH (sort R l) = LENGTH l -/
theorem sort_LENGTH {α : Type u} :
    ∀ (R : α → α → Prop) (l : List α), (sort R l).length = l.length := by
  intro R l
  exact (Aux.mergesort_tail_perm R l).length_eq.symm

/- HOL4:
Theorem sort_set[simp]:
  set (sort R ls) = set ls -/
theorem sort_set {α : Type u} (R : α → α → Prop) (ls : List α) :
    LIST_TO_SET (sort R ls) = LIST_TO_SET ls := by
  apply Aux.set_ext
  intro x
  rw [Aux.mem_LIST_TO_SET, Aux.mem_LIST_TO_SET, sort_MEM]

end

end Candle
