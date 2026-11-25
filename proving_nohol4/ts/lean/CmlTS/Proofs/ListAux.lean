import CmlTS.Prelude.ListLib
import CmlTS.Prelude.FiniteMap
import Batteries.Data.List.Perm

/-! Auxiliary lemmas on the prelude constants. -/

namespace CmlTS

open scoped Classical

variable {α β γ δ : Type}

/-! ### sets -/

theorem Aux.set_ext {s t : Set α} (h : ∀ x, x ∈ s ↔ x ∈ t) : s = t := by
  funext x
  exact propext (h x)

theorem Aux.mem_LIST_TO_SET {x : α} {l : List α} : x ∈ LIST_TO_SET l ↔ x ∈ l := Iff.rfl

theorem Aux.mem_IMAGE {f : α → β} {s : Set α} {y : β} :
    y ∈ IMAGE f s ↔ ∃ x, y = f x ∧ x ∈ s := Iff.rfl

theorem Aux.mem_setOf {P : α → Prop} {x : α} : x ∈ setOf P ↔ P x := Iff.rfl

theorem Aux.mem_union {s t : Set α} {x : α} : x ∈ s ∪ t ↔ (x ∈ s ∨ x ∈ t) := Iff.rfl

theorem Aux.mem_inter {s t : Set α} {x : α} : x ∈ s ∩ t ↔ (x ∈ s ∧ x ∈ t) := Iff.rfl

theorem Aux.mem_diff {s t : Set α} {x : α} : x ∈ s \ t ↔ (x ∈ s ∧ ¬ x ∈ t) := Iff.rfl

theorem Aux.mem_singleton {x y : α} : x ∈ ({y} : Set α) ↔ x = y := by
  show (x = y ∨ False) ↔ x = y
  simp

theorem Aux.mem_insert {x y : α} {s : Set α} : x ∈ insert y s ↔ (x = y ∨ x ∈ s) := Iff.rfl

theorem Aux.not_mem_empty {x : α} : ¬ x ∈ (∅ : Set α) := fun h => h

theorem Aux.mem_UNIV {x : α} : x ∈ (UNIV : Set α) := trivial

theorem Aux.DISJOINT_iff {s t : Set α} : DISJOINT s t ↔ ∀ x, x ∈ s → x ∈ t → False := by
  constructor
  · intro h x hs ht
    have : x ∈ s ∩ t := ⟨hs, ht⟩
    unfold DISJOINT at h
    rw [h] at this
    exact this
  · intro h
    apply Aux.set_ext
    intro x
    exact ⟨fun hx => (h x hx.1 hx.2).elim, fun hx => hx.elim⟩

/-! ### finiteness -/

theorem Aux.nodup_enum (l : List α) : ∃ l' : List α, l'.Nodup ∧ ∀ x, x ∈ l' ↔ x ∈ l := by
  induction l with
  | nil => exact ⟨[], List.nodup_nil, fun x => Iff.rfl⟩
  | cons a t ih =>
    obtain ⟨l', h1, h2⟩ := ih
    by_cases h : a ∈ l'
    · refine ⟨l', h1, fun x => ?_⟩
      rw [h2 x, List.mem_cons]
      constructor
      · exact Or.inr
      · rintro (rfl | hx)
        · exact (h2 _).mp h
        · exact hx
    · refine ⟨a :: l', List.nodup_cons.mpr ⟨h, h1⟩, fun x => ?_⟩
      rw [List.mem_cons, List.mem_cons, h2 x]

theorem Aux.FINITE_enum {s : Set α} (h : FINITE s) :
    ∃ l : List α, l.Nodup ∧ ∀ x, x ∈ l ↔ x ∈ s := by
  have : ∃ l : List α, ∀ x, x ∈ l ↔ x ∈ s := by
    apply h (fun s => ∃ l : List α, ∀ x, x ∈ l ↔ x ∈ s)
    constructor
    · exact ⟨[], fun x => by simp [Aux.not_mem_empty]⟩
    · rintro s ⟨l, hl⟩ e
      refine ⟨e :: l, fun x => ?_⟩
      rw [List.mem_cons, hl x, Aux.mem_insert]
  obtain ⟨l, hl⟩ := this
  obtain ⟨l', h1, h2⟩ := Aux.nodup_enum l
  exact ⟨l', h1, fun x => (h2 x).trans (hl x)⟩

theorem Aux.CARD_eq {s : Set α} {l : List α} (h1 : l.Nodup) (h2 : ∀ x, x ∈ l ↔ x ∈ s) :
    CARD s = l.length := by
  have hex : ∃ n, ∃ l : List α, l.Nodup ∧ l.length = n ∧ ∀ x, x ∈ l ↔ x ∈ s :=
    ⟨l.length, l, h1, rfl, h2⟩
  have := Classical.epsilon_spec hex
  obtain ⟨l', h3, h4, h5⟩ := this
  unfold CARD select
  rw [← h4]
  exact ((List.perm_ext_iff_of_nodup h3 h1).mpr fun x => (h5 x).trans (h2 x).symm).length_eq

theorem Aux.nodup_map_inj {f : α → β} {l : List α} (h : (l.map f).Nodup) :
    ∀ x y, x ∈ l → y ∈ l → f x = f y → x = y := by
  induction l with
  | nil => intro x y hx; simp at hx
  | cons a t ih =>
    rw [List.map_cons, List.nodup_cons] at h
    intro x y hx hy hxy
    rw [List.mem_cons] at hx hy
    rcases hx with rfl | hx
    · rcases hy with rfl | hy
      · rfl
      · exact absurd (hxy ▸ List.mem_map_of_mem hy) h.1
    · rcases hy with rfl | hy
      · exact absurd (hxy ▸ List.mem_map_of_mem hx) h.1
      · exact ih h.2 x y hx hy hxy

theorem Aux.inj_nodup_map {f : α → β} {l : List α} (hl : l.Nodup)
    (h : ∀ x y, x ∈ l → y ∈ l → f x = f y → x = y) : (l.map f).Nodup := by
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.nodup_cons] at hl
    rw [List.map_cons, List.nodup_cons]
    refine ⟨?_, ih hl.2 fun x y hx hy =>
      h x y (List.mem_cons_of_mem _ hx) (List.mem_cons_of_mem _ hy)⟩
    intro hm
    obtain ⟨y, hy, hfy⟩ := List.mem_map.mp hm
    have := h y a (List.mem_cons_of_mem _ hy) List.mem_cons_self hfy
    exact hl.1 (this ▸ hy)

/-- Pigeonhole: a list of the same length as a duplicate-free sublist (as sets) has no
duplicates. -/
theorem Aux.nodup_of_subset {l l' : List α} (h1 : l'.Nodup) (h2 : ∀ x, x ∈ l' → x ∈ l)
    (h3 : l.length ≤ l'.length) : l.Nodup ∧ ∀ x, x ∈ l → x ∈ l' := by
  have hp := (List.subperm_of_subset h1 h2).perm_of_length_le h3
  exact ⟨hp.nodup h1, fun x hx => hp.mem_iff.mpr hx⟩

/-! ### lists -/

theorem Aux.EL_eq [Nonempty α] (l : List α) (n : Nat) (h : n < l.length) : EL n l = l[n] := by
  induction l generalizing n with
  | nil => simp at h
  | cons a t ih =>
    cases n with
    | zero => rfl
    | succ n =>
      simp only [EL, TL, List.getElem_cons_succ]
      exact ih n (by simpa using h)

theorem Aux.EL_getElem? [Nonempty α] (l : List α) (n : Nat) (h : n < l.length) :
    l[n]? = some (EL n l) := by
  rw [Aux.EL_eq l n h, List.getElem?_eq_getElem h]

theorem Aux.EL_mem [Nonempty α] (l : List α) (n : Nat) (h : n < l.length) : EL n l ∈ l := by
  rw [Aux.EL_eq l n h]
  exact List.getElem_mem h

theorem Aux.EL_map [Nonempty α] [Nonempty β] (f : α → β) (l : List α) (n : Nat)
    (h : n < l.length) : EL n (l.map f) = f (EL n l) := by
  rw [Aux.EL_eq _ n (by simpa using h), Aux.EL_eq l n h, List.getElem_map]

theorem Aux.isPREFIX_iff {l1 l2 : List α} : isPREFIX l1 l2 ↔ ∃ l, l2 = l1 ++ l := by
  induction l1 generalizing l2 with
  | nil => simp [isPREFIX]
  | cons a t ih =>
    cases l2 with
    | nil => simp [isPREFIX]
    | cons b t2 =>
      simp only [isPREFIX, ih, List.cons_append, List.cons.injEq]
      constructor
      · rintro ⟨rfl, l, rfl⟩
        exact ⟨l, rfl, rfl⟩
      · rintro ⟨l, rfl, rfl⟩
        exact ⟨rfl, l, rfl⟩

theorem Aux.ALL_DISTINCT_iff {l : List α} : ALL_DISTINCT l ↔ l.Nodup := by
  induction l with
  | nil => simp [ALL_DISTINCT]
  | cons a t ih => simp [ALL_DISTINCT, ih]

theorem Aux.EVERY_mono {P Q : α → Prop} {l : List α} (h : ∀ x, x ∈ l → P x → Q x)
    (hp : EVERY P l) : EVERY Q l := by
  rw [EVERY_iff_forall] at hp ⊢
  exact fun x hx => h x hx (hp x hx)

theorem Aux.EVERY_append {P : α → Prop} {l1 l2 : List α} :
    EVERY P (l1 ++ l2) ↔ EVERY P l1 ∧ EVERY P l2 := by
  simp only [EVERY_iff_forall, List.mem_append]
  exact ⟨fun h => ⟨fun x hx => h x (.inl hx), fun x hx => h x (.inr hx)⟩,
    fun h x hx => hx.elim (h.1 x) (h.2 x)⟩

theorem Aux.EVERY_reverse {P : α → Prop} {l : List α} : EVERY P l.reverse ↔ EVERY P l := by
  simp only [EVERY_iff_forall, List.mem_reverse]

theorem Aux.EVERY_cons {P : α → Prop} {a : α} {l : List α} :
    EVERY P (a :: l) ↔ P a ∧ EVERY P l := Iff.rfl

theorem Aux.EVERY_nil {P : α → Prop} : EVERY P ([] : List α) := trivial

theorem Aux.EVERY_EL [Nonempty α] {P : α → Prop} {l : List α} (h : EVERY P l) (n : Nat)
    (hn : n < l.length) : P (EL n l) :=
  EVERY_iff_forall.mp h _ (Aux.EL_mem l n hn)

theorem Aux.LIST_REL_length {R : α → β → Prop} {l1 : List α} {l2 : List β}
    (h : LIST_REL R l1 l2) : l1.length = l2.length := (LIST_REL_iff_aux.mp h).1

theorem Aux.LIST_REL_mono {R S : α → β → Prop} {l1 : List α} {l2 : List β}
    (h : ∀ a b, a ∈ l1 → b ∈ l2 → R a b → S a b) (hr : LIST_REL R l1 l2) : LIST_REL S l1 l2 := by
  induction l1 generalizing l2 with
  | nil => cases l2 <;> simp_all [LIST_REL]
  | cons a t ih =>
    cases l2 with
    | nil => simp [LIST_REL] at hr
    | cons b t2 =>
      simp only [LIST_REL] at hr ⊢
      exact ⟨h a b List.mem_cons_self List.mem_cons_self hr.1,
        ih (fun x y hx hy => h x y (List.mem_cons_of_mem _ hx) (List.mem_cons_of_mem _ hy)) hr.2⟩

theorem Aux.LIST_REL_append {R : α → β → Prop} {l1 l1' : List α} {l2 l2' : List β}
    (h1 : LIST_REL R l1 l2) (h2 : LIST_REL R l1' l2') : LIST_REL R (l1 ++ l1') (l2 ++ l2') := by
  induction l1 generalizing l2 with
  | nil => cases l2 <;> simp_all [LIST_REL]
  | cons a t ih =>
    cases l2 with
    | nil => simp [LIST_REL] at h1
    | cons b t2 =>
      simp only [LIST_REL, List.cons_append] at h1 ⊢
      exact ⟨h1.1, ih h1.2⟩

theorem Aux.LIST_REL_reverse {R : α → β → Prop} {l1 : List α} {l2 : List β}
    (h : LIST_REL R l1 l2) : LIST_REL R l1.reverse l2.reverse := by
  induction l1 generalizing l2 with
  | nil => cases l2 <;> simp_all [LIST_REL]
  | cons a t ih =>
    cases l2 with
    | nil => simp [LIST_REL] at h
    | cons b t2 =>
      simp only [LIST_REL] at h
      rw [List.reverse_cons, List.reverse_cons]
      exact Aux.LIST_REL_append (ih h.2) ⟨h.1, trivial⟩

theorem Aux.LIST_REL_reverse_iff {R : α → β → Prop} {l1 : List α} {l2 : List β} :
    LIST_REL R l1.reverse l2 ↔ LIST_REL R l1 l2.reverse := by
  constructor
  · intro h
    have := Aux.LIST_REL_reverse h
    rwa [List.reverse_reverse] at this
  · intro h
    have := Aux.LIST_REL_reverse h
    rwa [List.reverse_reverse] at this

theorem Aux.LIST_REL_map {R : γ → δ → Prop} {f : α → γ} {g : β → δ} {l1 : List α} {l2 : List β} :
    LIST_REL R (l1.map f) (l2.map g) ↔ LIST_REL (fun a b => R (f a) (g b)) l1 l2 := by
  induction l1 generalizing l2 with
  | nil => cases l2 <;> simp [LIST_REL]
  | cons a t ih =>
    cases l2 with
    | nil => simp [LIST_REL]
    | cons b t2 => simp [LIST_REL, ih]

theorem Aux.LIST_REL_nil_left {R : α → β → Prop} {l : List β} : LIST_REL R [] l ↔ l = [] := by
  cases l <;> simp [LIST_REL]

theorem Aux.LIST_REL_nil_right {R : α → β → Prop} {l : List α} : LIST_REL R l [] ↔ l = [] := by
  cases l <;> simp [LIST_REL]

theorem Aux.LIST_REL_cons_left {R : α → β → Prop} {a : α} {l : List α} {l2 : List β} :
    LIST_REL R (a :: l) l2 ↔ ∃ b t, l2 = b :: t ∧ R a b ∧ LIST_REL R l t := by
  cases l2 with
  | nil => simp [LIST_REL]
  | cons b t =>
    simp only [LIST_REL, List.cons.injEq]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨b, t, ⟨rfl, rfl⟩, h1, h2⟩
    · rintro ⟨b', t', ⟨rfl, rfl⟩, h1, h2⟩; exact ⟨h1, h2⟩

theorem Aux.LIST_REL_cons_right {R : α → β → Prop} {b : β} {l : List α} {l2 : List β} :
    LIST_REL R l (b :: l2) ↔ ∃ a t, l = a :: t ∧ R a b ∧ LIST_REL R t l2 := by
  cases l with
  | nil => simp [LIST_REL]
  | cons a t =>
    simp only [LIST_REL, List.cons.injEq]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨a, t, ⟨rfl, rfl⟩, h1, h2⟩
    · rintro ⟨b', t', ⟨rfl, rfl⟩, h1, h2⟩; exact ⟨h1, h2⟩

/-! ### association lists -/

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

theorem Aux.ALOOKUP_append {l1 l2 : List (α × β)} {k : α} :
    ALOOKUP (l1 ++ l2) k = (match ALOOKUP l1 k with | some x => some x | none => ALOOKUP l2 k) := by
  induction l1 with
  | nil => simp [ALOOKUP]
  | cons p t ih =>
    obtain ⟨a, b⟩ := p
    simp only [List.cons_append, ALOOKUP]
    split
    · rfl
    · exact ih

theorem Aux.ALOOKUP_none_iff {l : List (α × β)} {k : α} :
    ALOOKUP l k = none ↔ ¬ k ∈ l.map Prod.fst := by
  induction l with
  | nil => simp [ALOOKUP]
  | cons p t ih =>
    obtain ⟨a, b⟩ := p
    simp only [ALOOKUP, List.map_cons, List.mem_cons, not_or]
    by_cases h : a = k
    · simp [h]
    · rw [if_neg h, ih]
      exact ⟨fun h2 => ⟨fun e => h e.symm, h2⟩, fun h2 => h2.2⟩

theorem Aux.ALOOKUP_map_snd {f : β → γ} {l : List (α × β)} {k : α} :
    ALOOKUP (l.map (fun p => (p.1, f p.2))) k = (ALOOKUP l k).map f := by
  induction l with
  | nil => simp [ALOOKUP]
  | cons p t ih =>
    obtain ⟨a, b⟩ := p
    simp only [List.map_cons, ALOOKUP, ih]
    split <;> simp

theorem Aux.mem_ALOOKUP_some {l : List (α × β)} {k : α} (h : k ∈ l.map Prod.fst) :
    ∃ x, ALOOKUP l k = some x := by
  cases hl : ALOOKUP l k with
  | none => exact absurd h (Aux.ALOOKUP_none_iff.mp hl)
  | some x => exact ⟨x, rfl⟩

theorem Aux.mem_ALOOKUP {l : List (α × β)} {k : α} {x : β} (hd : (l.map Prod.fst).Nodup)
    (h : (k, x) ∈ l) : ALOOKUP l k = some x := by
  induction l with
  | nil => simp at h
  | cons p t ih =>
    obtain ⟨a, b⟩ := p
    rw [List.map_cons, List.nodup_cons] at hd
    simp only [ALOOKUP]
    rw [List.mem_cons] at h
    rcases h with h | h
    · cases h; simp
    · rw [if_neg, ih hd.2 h]
      rintro rfl
      exact hd.1 (List.mem_map.mpr ⟨_, h, rfl⟩)

/-! ### finite maps -/

theorem Aux.fmap_ext {f g : fmap α β} (h : ∀ x, FLOOKUP f x = FLOOKUP g x) : f = g := by
  cases f; cases g
  simp only [FLOOKUP] at h
  have := funext h
  subst this
  rfl

theorem Aux.FLOOKUP_FEMPTY {x : α} : FLOOKUP (FEMPTY : fmap α β) x = none := rfl

theorem Aux.FLOOKUP_FUPDATE {f : fmap α β} {k x : α} {v : β} :
    FLOOKUP (FUPDATE f (k, v)) x = if x = k then some v else FLOOKUP f x := rfl

theorem Aux.mem_FDOM {f : fmap α β} {x : α} : x ∈ FDOM f ↔ FLOOKUP f x ≠ none := Iff.rfl

theorem Aux.mem_FRANGE {f : fmap α β} {y : β} : y ∈ FRANGE f ↔ ∃ x, FLOOKUP f x = some y := Iff.rfl

theorem Aux.FLOOKUP_FUNION {f g : fmap α β} {x : α} :
    FLOOKUP (FUNION f g) x =
      (match FLOOKUP f x with | some y => some y | none => FLOOKUP g x) := by
  show (if x ∈ FDOM f then f.rep x else g.rep x) = _
  by_cases h : x ∈ FDOM f
  · rw [if_pos h]
    rw [Aux.mem_FDOM] at h
    show FLOOKUP f x = _
    cases h2 : FLOOKUP f x with
    | none => exact absurd h2 h
    | some y => rfl
  · rw [if_neg h]
    rw [Aux.mem_FDOM] at h
    have h2 : FLOOKUP f x = none := Classical.not_not.mp h
    rw [h2]
    rfl

theorem Aux.FLOOKUP_o_f {g : β → γ} {f : fmap α β} {x : α} :
    FLOOKUP (o_f g f) x = (FLOOKUP f x).map g := rfl

theorem Aux.FLOOKUP_FUPDATE_LIST {f : fmap α β} {l : List (α × β)} {x : α} :
    FLOOKUP (FUPDATE_LIST f l) x =
      (match ALOOKUP l.reverse x with | some y => some y | none => FLOOKUP f x) := by
  induction l generalizing f with
  | nil => rfl
  | cons p t ih =>
    obtain ⟨k, v⟩ := p
    show FLOOKUP (FUPDATE_LIST (FUPDATE f (k, v)) t) x = _
    rw [ih, List.reverse_cons, Aux.ALOOKUP_append, Aux.FLOOKUP_FUPDATE]
    cases ALOOKUP t.reverse x with
    | some y => rfl
    | none =>
      simp only [ALOOKUP]
      by_cases h : x = k
      · simp [h]
      · have h' : ¬ k = x := fun e => h e.symm
        simp [h, h']

theorem Aux.FLOOKUP_alist_to_fmap {l : List (α × β)} {x : α} :
    FLOOKUP (alist_to_fmap l) x = ALOOKUP l x := by
  induction l with
  | nil => rfl
  | cons p t ih =>
    obtain ⟨k, v⟩ := p
    show FLOOKUP (FUPDATE (alist_to_fmap t) (k, v)) x = _
    rw [Aux.FLOOKUP_FUPDATE, ih]
    simp only [ALOOKUP]
    by_cases h : x = k
    · simp [h]
    · have h' : ¬ k = x := fun e => h e.symm
      simp [h, h']

/-- The two ways of building a substitution agree. -/
theorem Aux.FUPDATE_LIST_reverse {l : List (α × β)} :
    FUPDATE_LIST FEMPTY l.reverse = alist_to_fmap l := by
  apply Aux.fmap_ext
  intro x
  rw [Aux.FLOOKUP_FUPDATE_LIST, List.reverse_reverse, Aux.FLOOKUP_alist_to_fmap]
  cases ALOOKUP l x <;> rfl

theorem Aux.SUBMAP_iff {f g : fmap α β} :
    SUBMAP f g ↔ ∀ x y, FLOOKUP f x = some y → FLOOKUP g x = some y := by
  constructor
  · intro h x y hx
    have := h x (by rw [Aux.mem_FDOM, hx]; simp)
    rw [← this.2, hx]
  · intro h x hx
    rw [Aux.mem_FDOM] at hx
    cases h2 : FLOOKUP f x with
    | none => exact absurd h2 hx
    | some y =>
      have := h x y h2
      exact ⟨by rw [Aux.mem_FDOM, this]; simp, this.symm⟩

end CmlTS
