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

theorem Aux.REV_eq {α : Type u} (l acc : List α) : REV l acc = l.reverse ++ acc := by
  induction l generalizing acc with
  | nil => rfl
  | cons a t ih => simp [REV, ih]

theorem Aux.merge_tail_perm {α : Type u} (negate : Prop) (R : α → α → Prop) :
    ∀ (xs ys acc : List α), (merge_tail negate R xs ys acc).Perm (xs ++ ys ++ acc)
  | [], [], acc => by simp [merge_tail]
  | x :: xs, [], acc => by
    rw [merge_tail, Aux.REV_eq]
    · simp only [List.append_nil]
      exact (List.reverse_perm _).append_right acc
    · simp
  | [], y :: ys, acc => by
    rw [merge_tail, Aux.REV_eq]
    · exact (List.reverse_perm _).append_right acc
    · simp
  | x :: xs, y :: ys, acc => by
    rw [merge_tail]
    split
    · exact (Aux.merge_tail_perm negate R xs (y :: ys) (x :: acc)).trans List.perm_middle
    · refine (Aux.merge_tail_perm negate R (x :: xs) ys (y :: acc)).trans ?_
      exact List.perm_middle.trans
        ((List.perm_middle (l₁ := x :: xs) (l₂ := ys) (a := y)).append_right acc).symm
termination_by xs ys => xs.length + ys.length

theorem Aux.sort2_tail_perm {α : Type u} (neg : Prop) (R : α → α → Prop) (x y : α) :
    (sort2_tail neg R x y).Perm [x, y] := by
  unfold sort2_tail
  split
  · exact List.Perm.refl _
  · exact List.Perm.swap _ _ _

theorem Aux.sort3_tail_perm {α : Type u} (neg : Prop) (R : α → α → Prop) (x y z : α) :
    (sort3_tail neg R x y z).Perm [x, y, z] := by
  unfold sort3_tail
  rw [List.perm_iff_count]
  intro a
  repeat' split
  all_goals (simp only [List.count_cons, List.count_nil]; try omega)

theorem Aux.mergesortN_tail_perm {α : Type u} (R : α → α → Prop) (n : Nat) :
    ∀ (negate : Prop) (l : List α), (mergesortN_tail negate R n l).Perm (l.take n) := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro negate l
    match n, l, ih with
    | 0, l, _ => simp [mergesortN_tail]
    | 1, [], _ => simp [mergesortN_tail]
    | 1, x :: l, _ => simp [mergesortN_tail]
    | 2, [], _ => simp [mergesortN_tail]
    | 2, [x], _ => simp [mergesortN_tail]
    | 2, x :: y :: l, _ => simpa [mergesortN_tail] using Aux.sort2_tail_perm negate R x y
    | 3, [], _ => simp [mergesortN_tail]
    | 3, [x], _ => simp [mergesortN_tail]
    | 3, [x, y], _ => simpa [mergesortN_tail] using Aux.sort2_tail_perm negate R x y
    | 3, x :: y :: z :: l, _ => simpa [mergesortN_tail] using Aux.sort3_tail_perm negate R x y z
    | n + 4, l, ih =>
      rw [mergesortN_tail]
      have h1 : DIV2 (n + 4) < n + 4 := by unfold DIV2; omega
      have h2 : n + 4 - DIV2 (n + 4) < n + 4 := by unfold DIV2; omega
      refine (Aux.merge_tail_perm _ R _ _ []).trans ?_
      rw [List.append_nil]
      refine ((ih _ h1 _ l).append (ih _ h2 _ _)).trans ?_
      rw [← List.take_add]
      have : DIV2 (n + 4) + (n + 4 - DIV2 (n + 4)) = n + 4 := by omega
      rw [this]

/- HOL4:
Theorem merge_tail_MEM:
  !negate R xs ys acc. MEM x (merge_tail negate R xs ys acc) = ((MEM x xs) \/ (MEM x ys) \/ (MEM x acc)) -/
theorem merge_tail_MEM {α : Type u} (x : α) :
    ∀ (negate : Prop) (R : α → α → Prop) (xs ys acc : List α),
      (x ∈ merge_tail negate R xs ys acc) = (x ∈ xs ∨ x ∈ ys ∨ x ∈ acc) := by
  intro negate R xs ys acc
  rw [(Aux.merge_tail_perm negate R xs ys acc).mem_iff]
  simp

/- HOL4:
Theorem mergesortN_tail_MEM:
  !negate R length lst. (MEM x (mergesortN_tail negate R length lst) <=> MEM x (TAKE length lst)) -/
theorem mergesortN_tail_MEM {α : Type u} (x : α) :
    ∀ (negate : Prop) (R : α → α → Prop) (length : Nat) (lst : List α),
      (x ∈ mergesortN_tail negate R length lst ↔ x ∈ List.take length lst) := by
  intro negate R length lst
  exact (Aux.mergesortN_tail_perm R length negate lst).mem_iff

/- HOL4:
Theorem mergesort_tail_MEM:
  ∀R l. MEM x (mergesort$mergesort_tail R l) ⇔ MEM x l -/
theorem mergesort_tail_MEM {α : Type u} (x : α) :
    ∀ (R : α → α → Prop) (l : List α), x ∈ mergesort_tail R l ↔ x ∈ l := by
  intro R l
  unfold mergesort_tail
  rw [mergesortN_tail_MEM, List.take_length]

/- HOL4:
Theorem merge_tail_PERM:
  !negate R xs ys acc. PERM (xs++ys++acc) (merge_tail negate R xs ys acc) -/
theorem merge_tail_PERM {α : Type u} :
    ∀ (negate : Prop) (R : α → α → Prop) (xs ys acc : List α),
      PERM (xs ++ ys ++ acc) (merge_tail negate R xs ys acc) := by
  intro negate R xs ys acc
  exact Aux.PERM_iff.mpr (Aux.merge_tail_perm negate R xs ys acc).symm

/- HOL4:
Theorem sort2_tail_PERM:
  !neg R x y. PERM [x;y] (sort2_tail neg R x y) -/
theorem sort2_tail_PERM {α : Type u} :
    ∀ (neg : Prop) (R : α → α → Prop) (x y : α), PERM [x, y] (sort2_tail neg R x y) := by
  intro neg R x y
  exact Aux.PERM_iff.mpr (Aux.sort2_tail_perm neg R x y).symm

/- HOL4:
Theorem sort3_tail_PERM:
  !neg R x y z. PERM [x;y;z] (sort3_tail neg R x y z) -/
theorem sort3_tail_PERM {α : Type u} :
    ∀ (neg : Prop) (R : α → α → Prop) (x y z : α),
      PERM [x, y, z] (sort3_tail neg R x y z) := by
  intro neg R x y z
  exact Aux.PERM_iff.mpr (Aux.sort3_tail_perm neg R x y z).symm

/- HOL4:
Theorem mergesortN_tail_PERM:
  !neg R len l. PERM (TAKE len l) (mergesortN_tail neg R len l) -/
theorem mergesortN_tail_PERM {α : Type u} :
    ∀ (neg : Prop) (R : α → α → Prop) (len : Nat) (l : List α),
      PERM (List.take len l) (mergesortN_tail neg R len l) := by
  intro neg R len l
  exact Aux.PERM_iff.mpr (Aux.mergesortN_tail_perm R len neg l).symm

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
  have h := mergesortN_tail_PERM False R L.length L
  rw [List.take_length] at h
  exact h

/- HOL4:
Theorem sort_LENGTH[simp]:
  !R l. LENGTH (sort R l) = LENGTH l -/
theorem sort_LENGTH {α : Type u} :
    ∀ (R : α → α → Prop) (l : List α), (sort R l).length = l.length := by
  intro R l
  exact (Aux.PERM_iff.mp (sort_PERM R l)).length_eq.symm

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
