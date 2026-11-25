import Batteries.Data.List.Perm
import Batteries.Data.List.Lemmas
import CmlTS.Prelude.FiniteMap
import CmlTS.Prelude.Sptree
import CmlTS.Prelude.StringLib

/-! Auxiliary lemmas about the library constants. -/

namespace CmlTS

open scoped Classical

variable {α β γ : Type}

/-! ### sets -/

theorem Aux.set_ext {s t : Set α} (h : ∀ x, x ∈ s ↔ x ∈ t) : s = t := by
  funext x; exact propext (h x)

theorem Aux.mem_setOf {P : α → Prop} {x : α} : x ∈ setOf P ↔ P x := Iff.rfl
theorem Aux.mem_union {s t : Set α} {x : α} : x ∈ s ∪ t ↔ x ∈ s ∨ x ∈ t := Iff.rfl
theorem Aux.mem_inter {s t : Set α} {x : α} : x ∈ s ∩ t ↔ x ∈ s ∧ x ∈ t := Iff.rfl
theorem Aux.mem_diff {s t : Set α} {x : α} : x ∈ s \ t ↔ x ∈ s ∧ ¬ x ∈ t := Iff.rfl
theorem Aux.mem_empty {x : α} : x ∈ (∅ : Set α) ↔ False := Iff.rfl
theorem Aux.mem_insert {s : Set α} {x a : α} : x ∈ (insert a s : Set α) ↔ x = a ∨ x ∈ s := Iff.rfl
theorem Aux.mem_singleton {x a : α} : x ∈ ({a} : Set α) ↔ x = a :=
  ⟨fun h => h.elim id False.elim, Or.inl⟩
theorem Aux.mem_LIST_TO_SET {l : List α} {x : α} : x ∈ LIST_TO_SET l ↔ x ∈ l := Iff.rfl
theorem Aux.mem_IMAGE {f : α → β} {s : Set α} {y : β} : y ∈ IMAGE f s ↔ ∃ x, y = f x ∧ x ∈ s :=
  Iff.rfl
theorem Aux.mem_UNIV {x : α} : x ∈ (UNIV : Set α) := trivial
theorem Aux.subset_def {s t : Set α} : s ⊆ t ↔ ∀ x, x ∈ s → x ∈ t := Iff.rfl

theorem Aux.disjoint_iff {s t : Set α} : DISJOINT s t ↔ ∀ x, x ∈ s → ¬ x ∈ t := by
  constructor
  · intro h x hx ht
    have : x ∈ s ∩ t := ⟨hx, ht⟩
    rw [h] at this
    exact this
  · intro h
    exact Aux.set_ext fun x => ⟨fun hx => h x hx.1 hx.2, fun hx => hx.elim⟩

theorem Aux.finite_list {s : Set α} (h : FINITE s) : ∃ l : List α, l.Nodup ∧ ∀ x, x ∈ l ↔ x ∈ s := by
  apply h (fun s => ∃ l : List α, l.Nodup ∧ ∀ x, x ∈ l ↔ x ∈ s)
  refine ⟨⟨[], List.nodup_nil, fun x => Iff.intro (fun h => by cases h) (fun h => False.elim h)⟩, ?_⟩
  rintro s ⟨l, hl, hm⟩ e
  by_cases he : e ∈ l
  · refine ⟨l, hl, fun x => ?_⟩
    rw [Aux.mem_insert, hm]
    exact ⟨Or.inr, fun h => h.elim (fun h => by rw [h]; exact (hm e).1 he) id⟩
  · refine ⟨e :: l, List.nodup_cons.2 ⟨he, hl⟩, fun x => ?_⟩
    rw [Aux.mem_insert, List.mem_cons, hm]

theorem Aux.nodup_length_eq {l1 l2 : List α} (h1 : l1.Nodup) (h2 : l2.Nodup)
    (h : ∀ x, x ∈ l1 ↔ x ∈ l2) : l1.length = l2.length :=
  Nat.le_antisymm (List.subperm_of_subset h1 fun x hx => (h x).1 hx).length_le
    (List.subperm_of_subset h2 fun x hx => (h x).2 hx).length_le

theorem Aux.CARD_eq {s : Set α} {l : List α} (hl : l.Nodup) (hm : ∀ x, x ∈ l ↔ x ∈ s) :
    CARD s = l.length := by
  have h : ∃ n, ∃ l : List α, l.Nodup ∧ l.length = n ∧ ∀ x, x ∈ l ↔ x ∈ s := ⟨_, l, hl, rfl, hm⟩
  obtain ⟨l', h1, h2, h3⟩ := Classical.epsilon_spec h
  unfold CARD select
  rw [← h2]
  exact Aux.nodup_length_eq h1 hl fun x => by rw [h3, hm]

theorem Aux.exists_dedup (l : List α) :
    ∃ l' : List α, l'.Nodup ∧ (∀ x, x ∈ l' ↔ x ∈ l) ∧ l'.length ≤ l.length ∧
      (l'.length = l.length → l.Nodup) := by
  induction l with
  | nil => exact ⟨[], List.nodup_nil, fun _ => Iff.rfl, Nat.le_refl _, fun _ => List.nodup_nil⟩
  | cons a l ih =>
    obtain ⟨l', h1, h2, h3, h4⟩ := ih
    by_cases ha : a ∈ l
    · refine ⟨l', h1, fun x => ?_, ?_, ?_⟩
      · rw [h2, List.mem_cons]
        exact ⟨Or.inr, fun h => h.elim (fun h => h ▸ ha) id⟩
      · simp; omega
      · simp; omega
    · refine ⟨a :: l', ?_, fun x => ?_, ?_, ?_⟩
      · rw [List.nodup_cons, h2]; exact ⟨ha, h1⟩
      · rw [List.mem_cons, List.mem_cons, h2]
      · simp; omega
      · intro h
        rw [List.nodup_cons]
        exact ⟨ha, h4 (by simpa using h)⟩

theorem Aux.inj_of_nodup_map {f : α → β} {l : List α} (h : (l.map f).Nodup) :
    ∀ x y, x ∈ l → y ∈ l → f x = f y → x = y := by
  induction l with
  | nil => intro x y hx; cases hx
  | cons a l ih =>
    rw [List.map_cons, List.nodup_cons] at h
    intro x y hx hy hf
    rw [List.mem_cons] at hx hy
    rcases hx with rfl | hx <;> rcases hy with rfl | hy
    · rfl
    · exact absurd (List.mem_map.2 ⟨y, hy, hf.symm⟩) h.1
    · exact absurd (List.mem_map.2 ⟨x, hx, hf⟩) h.1
    · exact ih h.2 x y hx hy hf

/-! ### lists -/

theorem Aux.EVERY_iff {P : α → Prop} {l : List α} : EVERY P l ↔ ∀ x, x ∈ l → P x :=
  EVERY_iff_forall

theorem Aux.EXISTS_iff {P : α → Prop} {l : List α} : EXISTS P l ↔ ∃ x, x ∈ l ∧ P x := by
  induction l with
  | nil => simp [EXISTS]
  | cons h t ih => simp [EXISTS, ih]

theorem Aux.EL_getElem? [Nonempty α] {l : List α} {n : Nat} (h : n < l.length) :
    l[n]? = some (EL n l) := by
  induction n generalizing l with
  | zero => cases l <;> simp_all [EL, HD]
  | succ n ih =>
    cases l with
    | nil => simp at h
    | cons a l =>
      have : EL (n + 1) (a :: l) = EL n l := rfl
      rw [this, List.getElem?_cons_succ]
      exact ih (by simpa using h)

theorem Aux.EL_getElem [Nonempty α] {l : List α} {n : Nat} (h : n < l.length) : EL n l = l[n] := by
  have := Aux.EL_getElem? h
  rw [List.getElem?_eq_getElem h] at this
  exact (Option.some.inj this).symm

theorem Aux.EL_of_getElem? [Nonempty α] {l : List α} {n : Nat} {x : α} (h : l[n]? = some x) :
    EL n l = x := by
  have hl : n < l.length := by
    rcases Nat.lt_or_ge n l.length with h' | h'
    · exact h'
    · rw [List.getElem?_eq_none h'] at h; cases h
  rw [Aux.EL_getElem? hl] at h
  exact Option.some.inj h

theorem Aux.EL_mem [Nonempty α] {l : List α} {n : Nat} (h : n < l.length) : EL n l ∈ l := by
  rw [Aux.EL_getElem h]; exact List.getElem_mem h

theorem Aux.EL_map [Nonempty α] [Nonempty β] {f : α → β} {l : List α} {n : Nat}
    (h : n < l.length) : EL n (l.map f) = f (EL n l) := by
  rw [Aux.EL_getElem h, Aux.EL_getElem (by simpa using h)]; simp

theorem Aux.LUPDATE_eq_set (e : α) (n : Nat) (l : List α) : LUPDATE e n l = l.set n e := by
  induction l generalizing n with
  | nil => simp [LUPDATE]
  | cons a l ih =>
    cases n with
    | zero => simp [LUPDATE]
    | succ n => simp [LUPDATE, ih]

theorem Aux.ALL_DISTINCT_iff {l : List α} : ALL_DISTINCT l ↔ l.Nodup := by
  induction l with
  | nil => simp [ALL_DISTINCT]
  | cons a l ih => simp [ALL_DISTINCT, ih]

/-! ### association lists -/

theorem Aux.ALOOKUP_append (l1 l2 : List (α × β)) (k : α) :
    ALOOKUP (l1 ++ l2) k = (match ALOOKUP l1 k with | some x => some x | none => ALOOKUP l2 k) := by
  induction l1 with
  | nil => rfl
  | cons p l1 ih =>
    obtain ⟨a, b⟩ := p
    simp only [List.cons_append, ALOOKUP]
    split
    · rfl
    · exact ih

theorem Aux.ALOOKUP_mem {l : List (α × β)} {k : α} {x : β} (h : ALOOKUP l k = some x) :
    (k, x) ∈ l := by
  induction l with
  | nil => simp [ALOOKUP] at h
  | cons p t ih =>
    obtain ⟨a, b⟩ := p
    simp only [ALOOKUP] at h
    split at h
    · simp_all
    · exact List.mem_cons_of_mem _ (ih h)

theorem Aux.ALOOKUP_eq_none {l : List (α × β)} {k : α} :
    ALOOKUP l k = none ↔ ¬ k ∈ l.map Prod.fst := by
  induction l with
  | nil => simp [ALOOKUP]
  | cons p t ih =>
    obtain ⟨a, b⟩ := p
    simp only [ALOOKUP]
    split
    · simp_all
    · rename_i h
      rw [ih]
      simp only [List.map_cons, List.mem_cons, not_or]
      exact ⟨fun h' => ⟨fun e => h e.symm, h'⟩, fun h' => h'.2⟩

theorem Aux.ALOOKUP_map (f : β → γ) (l : List (α × β)) (k : α) :
    ALOOKUP (l.map fun p => (p.1, f p.2)) k = (ALOOKUP l k).map f := by
  induction l with
  | nil => rfl
  | cons p t ih =>
    obtain ⟨a, b⟩ := p
    simp only [List.map_cons, ALOOKUP]
    split
    · rfl
    · exact ih

theorem Aux.ALOOKUP_of_mem {l : List (α × β)} {k : α} {x : β} (hd : (l.map Prod.fst).Nodup)
    (h : (k, x) ∈ l) : ALOOKUP l k = some x := by
  induction l with
  | nil => cases h
  | cons p t ih =>
    obtain ⟨a, b⟩ := p
    rw [List.map_cons, List.nodup_cons] at hd
    simp only [ALOOKUP]
    rcases List.mem_cons.1 h with h | h
    · cases h; simp
    · split
      · rename_i e
        exact absurd (List.mem_map.2 ⟨(k, x), h, e.symm⟩) hd.1
      · exact ih hd.2 h

/-! ### finite maps -/

theorem Aux.fmap_ext {f g : fmap α β} (h : ∀ x, FLOOKUP f x = FLOOKUP g x) : f = g := by
  cases f; cases g
  simp only [fmap.mk.injEq]
  exact funext h

theorem Aux.mem_FDOM {f : fmap α β} {x : α} : x ∈ FDOM f ↔ ∃ v, FLOOKUP f x = some v :=
  Option.ne_none_iff_exists'

theorem Aux.not_mem_FDOM {f : fmap α β} {x : α} : ¬ x ∈ FDOM f ↔ FLOOKUP f x = none := by
  show ¬ (f.rep x ≠ none) ↔ _
  rw [Classical.not_not]; rfl

theorem Aux.FLOOKUP_FEMPTY {x : α} : FLOOKUP (FEMPTY : fmap α β) x = none := rfl

theorem Aux.FLOOKUP_FUPDATE {f : fmap α β} {k x : α} {v : β} :
    FLOOKUP (FUPDATE f (k, v)) x = if x = k then some v else FLOOKUP f x := rfl

theorem Aux.FLOOKUP_FUNION {f g : fmap α β} {x : α} :
    FLOOKUP (FUNION f g) x = (match FLOOKUP f x with | some v => some v | none => FLOOKUP g x) := by
  show (if x ∈ FDOM f then f.rep x else g.rep x) = _
  by_cases h : x ∈ FDOM f
  · rw [if_pos h]
    obtain ⟨v, hv⟩ := Aux.mem_FDOM.1 h
    rw [hv]; exact hv
  · rw [if_neg h, Aux.not_mem_FDOM.1 h]; rfl

theorem Aux.FLOOKUP_o_f {f : β → γ} {g : fmap α β} {x : α} :
    FLOOKUP (o_f f g) x = (FLOOKUP g x).map f := rfl

theorem Aux.FAPPLY_of_FLOOKUP [Nonempty β] {f : fmap α β} {x : α} {v : β}
    (h : FLOOKUP f x = some v) : FAPPLY f x = v := by
  unfold FAPPLY
  have : f.rep x = some v := h
  rw [this]

theorem Aux.SUBMAP_iff {f g : fmap α β} :
    SUBMAP f g ↔ ∀ x v, FLOOKUP f x = some v → FLOOKUP g x = some v := by
  constructor
  · intro h x v hx
    rw [← (h x (Aux.mem_FDOM.2 ⟨v, hx⟩)).2, hx]
  · intro h x hx
    obtain ⟨v, hv⟩ := Aux.mem_FDOM.1 hx
    exact ⟨Aux.mem_FDOM.2 ⟨v, h x v hv⟩, by rw [hv, h x v hv]⟩

theorem Aux.FLOOKUP_FUPDATE_LIST {f : fmap α β} {l : List (α × β)} {x : α} :
    FLOOKUP (FUPDATE_LIST f l) x =
      (match ALOOKUP l.reverse x with | some v => some v | none => FLOOKUP f x) := by
  induction l generalizing f with
  | nil => rfl
  | cons p l ih =>
    obtain ⟨a, b⟩ := p
    have : FUPDATE_LIST f ((a, b) :: l) = FUPDATE_LIST (FUPDATE f (a, b)) l := rfl
    rw [this, ih, List.reverse_cons, Aux.ALOOKUP_append]
    cases ALOOKUP l.reverse x with
    | some v => rfl
    | none =>
      simp only [Aux.FLOOKUP_FUPDATE, ALOOKUP]
      by_cases h : x = a
      · rw [if_pos h, if_pos h.symm]
      · rw [if_neg h, if_neg fun e => h e.symm]

theorem Aux.FLOOKUP_alist_to_fmap {l : List (α × β)} {x : α} :
    FLOOKUP (alist_to_fmap l) x = ALOOKUP l x := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    obtain ⟨a, b⟩ := p
    have : alist_to_fmap ((a, b) :: l) = FUPDATE (alist_to_fmap l) (a, b) := rfl
    rw [this, Aux.FLOOKUP_FUPDATE, ih]
    simp only [ALOOKUP]
    by_cases h : x = a
    · rw [if_pos h, if_pos h.symm]
    · rw [if_neg h, if_neg fun e => h e.symm]

/-! ### sptree -/

theorem Aux.mem_domain {t : spt α} {k : Nat} : k ∈ domain t ↔ ∃ v, lookup k t = some v := by
  induction t generalizing k with
  | LN => simp [domain, lookup, Aux.mem_empty]
  | LS a =>
    simp only [domain, lookup, Aux.mem_singleton]
    by_cases h : k = 0 <;> simp [h]
  | BN t1 t2 ih1 ih2 =>
    simp only [domain, lookup, Aux.mem_union, Aux.mem_IMAGE, ih1, ih2]
    by_cases h : k = 0
    · subst h; simp
    · rw [if_neg h]
      by_cases hk : k % 2 = 0
      · rw [if_pos hk]
        constructor
        · rintro (⟨n, rfl, v, hv⟩ | ⟨n, rfl, v, hv⟩)
          · exact ⟨v, by rw [← hv]; congr 1; omega⟩
          · omega
        · rintro ⟨v, hv⟩
          exact Or.inl ⟨(k - 1) / 2, by omega, v, hv⟩
      · rw [if_neg hk]
        constructor
        · rintro (⟨n, rfl, v, hv⟩ | ⟨n, rfl, v, hv⟩)
          · omega
          · exact ⟨v, by rw [← hv]; congr 1; omega⟩
        · rintro ⟨v, hv⟩
          exact Or.inr ⟨(k - 1) / 2, by omega, v, hv⟩
  | BS t1 a t2 ih1 ih2 =>
    simp only [domain, lookup, Aux.mem_union, Aux.mem_IMAGE, ih1, ih2, Aux.mem_singleton]
    by_cases h : k = 0
    · subst h; simp
    · rw [if_neg h]
      by_cases hk : k % 2 = 0
      · rw [if_pos hk]
        constructor
        · rintro ((h' | ⟨n, rfl, v, hv⟩) | ⟨n, rfl, v, hv⟩)
          · exact absurd h' h
          · exact ⟨v, by rw [← hv]; congr 1; omega⟩
          · omega
        · rintro ⟨v, hv⟩
          exact Or.inl (Or.inr ⟨(k - 1) / 2, by omega, v, hv⟩)
      · rw [if_neg hk]
        constructor
        · rintro ((h' | ⟨n, rfl, v, hv⟩) | ⟨n, rfl, v, hv⟩)
          · exact absurd h' h
          · omega
          · exact ⟨v, by rw [← hv]; congr 1; omega⟩
        · rintro ⟨v, hv⟩
          exact Or.inr ⟨(k - 1) / 2, by omega, v, hv⟩

theorem Aux.domain_list (t : spt α) : ∃ l : List Nat, ∀ x, x ∈ l ↔ x ∈ domain t := by
  induction t with
  | LN => exact ⟨[], fun x => by simp [domain, Aux.mem_empty]⟩
  | LS a => exact ⟨[0], fun x => by simp [domain, Aux.mem_singleton]⟩
  | BN t1 t2 ih1 ih2 =>
    obtain ⟨l1, h1⟩ := ih1
    obtain ⟨l2, h2⟩ := ih2
    refine ⟨l1.map (fun n => 2 * n + 2) ++ l2.map (fun n => 2 * n + 1), fun x => ?_⟩
    simp only [domain, Aux.mem_union, Aux.mem_IMAGE, List.mem_append, List.mem_map, h1, h2]
    constructor
    · rintro (⟨n, h, e⟩ | ⟨n, h, e⟩)
      · exact Or.inl ⟨n, e.symm, h⟩
      · exact Or.inr ⟨n, e.symm, h⟩
    · rintro (⟨n, h, e⟩ | ⟨n, h, e⟩)
      · exact Or.inl ⟨n, e, h.symm⟩
      · exact Or.inr ⟨n, e, h.symm⟩
  | BS t1 a t2 ih1 ih2 =>
    obtain ⟨l1, h1⟩ := ih1
    obtain ⟨l2, h2⟩ := ih2
    refine ⟨0 :: (l1.map (fun n => 2 * n + 2) ++ l2.map (fun n => 2 * n + 1)), fun x => ?_⟩
    simp only [domain, Aux.mem_union, Aux.mem_IMAGE, List.mem_append, List.mem_map, h1, h2,
      Aux.mem_singleton, List.mem_cons]
    constructor
    · rintro (h | ⟨n, h, e⟩ | ⟨n, h, e⟩)
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr ⟨n, e.symm, h⟩)
      · exact Or.inr ⟨n, e.symm, h⟩
    · rintro ((h | ⟨n, h, e⟩) | ⟨n, h, e⟩)
      · exact Or.inl h
      · exact Or.inr (Or.inl ⟨n, e, h.symm⟩)
      · exact Or.inr (Or.inr ⟨n, e, h.symm⟩)

theorem Aux.mem_toListA {t : spt α} {acc : List α} {x : α} :
    x ∈ toListA acc t ↔ x ∈ acc ∨ ∃ k, lookup k t = some x := by
  induction t generalizing acc with
  | LN => simp [toListA, lookup]
  | LS a =>
    simp only [toListA, lookup, List.mem_cons]
    constructor
    · rintro (h | h)
      · exact Or.inr ⟨0, by simp [h]⟩
      · exact Or.inl h
    · rintro (h | ⟨k, h⟩)
      · exact Or.inr h
      · split at h
        · exact Or.inl (Option.some.inj h).symm
        · cases h
  | BN t1 t2 ih1 ih2 =>
    simp only [toListA, ih1, ih2]
    constructor
    · rintro ((h | ⟨k, h⟩) | ⟨k, h⟩)
      · exact Or.inl h
      · refine Or.inr ⟨2 * k + 1, ?_⟩
        rw [lookup, if_neg (by omega), if_neg (by omega)]
        rw [← h]; congr 1; omega
      · refine Or.inr ⟨2 * k + 2, ?_⟩
        rw [lookup, if_neg (by omega), if_pos (by omega)]
        rw [← h]; congr 1; omega
    · rintro (h | ⟨k, h⟩)
      · exact Or.inl (Or.inl h)
      · rw [lookup] at h
        split at h
        · cases h
        · split at h
          · exact Or.inr ⟨_, h⟩
          · exact Or.inl (Or.inr ⟨_, h⟩)
  | BS t1 a t2 ih1 ih2 =>
    simp only [toListA, ih1, List.mem_cons, ih2]
    constructor
    · rintro ((h | h | ⟨k, h⟩) | ⟨k, h⟩)
      · exact Or.inr ⟨0, by simp [lookup, h]⟩
      · exact Or.inl h
      · refine Or.inr ⟨2 * k + 1, ?_⟩
        rw [lookup, if_neg (by omega), if_neg (by omega)]
        rw [← h]; congr 1; omega
      · refine Or.inr ⟨2 * k + 2, ?_⟩
        rw [lookup, if_neg (by omega), if_pos (by omega)]
        rw [← h]; congr 1; omega
    · rintro (h | ⟨k, h⟩)
      · exact Or.inl (Or.inr (Or.inl h))
      · rw [lookup] at h
        split at h
        · exact Or.inl (Or.inl (Option.some.inj h).symm)
        · split at h
          · exact Or.inr ⟨_, h⟩
          · exact Or.inl (Or.inr (Or.inr ⟨_, h⟩))

theorem Aux.mem_spt_toList {t : spt α} {x : α} :
    x ∈ spt_toList t ↔ ∃ k, lookup k t = some x := by
  simp [spt_toList, Aux.mem_toListA]

end CmlTS
