import CandleLean.Prelude

/-! Auxiliary lemmas about the HOL4 library constants (all in `Candle.Aux`). -/

universe u v w

namespace Candle

open HOL Classical

/-! ## sets -/

theorem Aux.set_ext {α : Type u} {s t : Set α} (h : ∀ x, x ∈ s ↔ x ∈ t) : s = t :=
  funext fun x => propext (h x)

theorem Aux.mem_setOf {α : Type u} {P : α → Prop} {x : α} : x ∈ setOf P ↔ P x := Iff.rfl

theorem Aux.mem_UNION {α : Type u} {s t : Set α} {x : α} :
    x ∈ UNION s t ↔ x ∈ s ∨ x ∈ t := Iff.rfl

theorem Aux.mem_INTER {α : Type u} {s t : Set α} {x : α} :
    x ∈ INTER s t ↔ x ∈ s ∧ x ∈ t := Iff.rfl

theorem Aux.mem_INSERT {α : Type u} {s : Set α} {x y : α} :
    x ∈ INSERT y s ↔ x = y ∨ x ∈ s := Iff.rfl

theorem Aux.mem_EMPTY {α : Type u} {x : α} : x ∈ (EMPTY : Set α) ↔ False := Iff.rfl

theorem Aux.mem_UNIV {α : Type u} {x : α} : x ∈ (UNIV : Set α) ↔ True := Iff.rfl

theorem Aux.mem_GSPEC {α : Type u} {β : Type v} {f : β → α × Prop} {x : α} :
    x ∈ GSPEC f ↔ ∃ y, x = (f y).1 ∧ (f y).2 := by
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨y, congrArg Prod.fst hy, ?_⟩
    have := congrArg Prod.snd hy
    exact this ▸ trivial
  · rintro ⟨y, h1, h2⟩
    refine ⟨y, Prod.ext h1 ?_⟩
    exact (eq_true h2).symm

theorem Aux.mem_IMAGE {α : Type u} {β : Type v} {f : α → β} {s : Set α} {x : β} :
    x ∈ IMAGE f s ↔ ∃ y, x = f y ∧ y ∈ s := Aux.mem_GSPEC

theorem Aux.mem_LIST_TO_SET {α : Type u} {l : List α} {x : α} :
    x ∈ LIST_TO_SET l ↔ x ∈ l := by
  induction l with
  | nil => simp [LIST_TO_SET, HOL.Aux.mem_def]
  | cons a t ih =>
    simp only [List.mem_cons, ← ih]
    exact Iff.rfl

theorem Aux.DISJOINT_iff {α : Type u} {s t : Set α} :
    DISJOINT s t ↔ ∀ x, x ∈ s → ¬ x ∈ t := by
  constructor
  · intro h x hs ht
    have : x ∈ INTER s t := ⟨hs, ht⟩
    rw [show INTER s t = EMPTY from h] at this
    exact this
  · intro h
    apply Aux.set_ext
    intro x
    exact ⟨fun hx => h x hx.1 hx.2, False.elim⟩

theorem Aux.FINITE_iff {α : Type u} {s : Set α} :
    FINITE s ↔ ∃ l : List α, ∀ x, x ∈ s → x ∈ l :=
  ⟨HOL.Aux.FINITE_list_bound s, fun ⟨l, hl⟩ => HOL.Aux.FINITE_of_list_bound l s hl⟩

theorem Aux.FINITE_subset {α : Type u} {s t : Set α} (ht : FINITE t) (h : ∀ x, x ∈ s → x ∈ t) :
    FINITE s := by
  obtain ⟨l, hl⟩ := Aux.FINITE_iff.mp ht
  exact Aux.FINITE_iff.mpr ⟨l, fun x hx => hl x (h x hx)⟩

theorem Aux.FINITE_UNION {α : Type u} {s t : Set α} (hs : FINITE s) (ht : FINITE t) :
    FINITE (UNION s t) := by
  obtain ⟨l, hl⟩ := Aux.FINITE_iff.mp hs
  obtain ⟨l', hl'⟩ := Aux.FINITE_iff.mp ht
  refine Aux.FINITE_iff.mpr ⟨l ++ l', fun x hx => ?_⟩
  rcases hx with h | h
  · exact List.mem_append_left _ (hl x h)
  · exact List.mem_append_right _ (hl' x h)

/-! ## lists -/

theorem Aux.EVERY_iff {α : Type u} {P : α → Prop} {l : List α} :
    EVERY P l ↔ ∀ x, x ∈ l → P x := by
  induction l with
  | nil => simp [EVERY]
  | cons a t ih => simp [EVERY, ih]

theorem Aux.EXISTS_iff {α : Type u} {P : α → Prop} {l : List α} :
    EXISTS P l ↔ ∃ x, x ∈ l ∧ P x := by
  induction l with
  | nil => simp [EXISTS]
  | cons a t ih => simp [EXISTS, ih]

theorem Aux.FILTER_eq {α : Type u} (P : α → Prop) (l : List α) :
    FILTER P l = l.filter (fun x => decide (P x)) := by
  induction l with
  | nil => rfl
  | cons a t ih => by_cases h : P a <;> simp [FILTER, h, ih]

theorem Aux.mem_FILTER {α : Type u} {P : α → Prop} {l : List α} {x : α} :
    x ∈ FILTER P l ↔ x ∈ l ∧ P x := by
  simp [Aux.FILTER_eq]

theorem Aux.ALL_DISTINCT_iff {α : Type u} {l : List α} : ALL_DISTINCT l ↔ l.Nodup := by
  induction l with
  | nil => simp [ALL_DISTINCT]
  | cons a t ih => simp [ALL_DISTINCT, ih]

theorem Aux.FILTER_eq_replicate {α : Type u} (x : α) (l : List α) :
    FILTER (fun y => x = y) l = List.replicate (l.count x) x := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    by_cases h : x = a
    · subst h; simp [FILTER, ih, List.replicate_succ]
    · have h' : ¬ a = x := fun e => h e.symm
      simp [FILTER, ih, h, h']

theorem Aux.PERM_iff {α : Type u} {l1 l2 : List α} : PERM l1 l2 ↔ l1.Perm l2 := by
  rw [List.perm_iff_count]
  unfold PERM
  constructor
  · intro h a
    have := congrArg List.length (h a)
    simpa [Aux.FILTER_eq_replicate] using this
  · intro h a
    simp [Aux.FILTER_eq_replicate, h a]

theorem Aux.SNOC_eq {α : Type u} (x : α) (l : List α) : SNOC x l = l ++ [x] := by
  induction l with
  | nil => rfl
  | cons a t ih => simp [SNOC, ih]

theorem Aux.GENLIST_K {α : Type u} (c : α) (n : Nat) : GENLIST (K c) n = List.replicate n c := by
  induction n with
  | zero => rfl
  | succ n ih => simp [GENLIST, ih, Aux.SNOC_eq, ← List.replicate_succ']

theorem Aux.EL_eq {α : Type u} [Nonempty α] : ∀ (n : Nat) (l : List α) (h : n < l.length),
    EL n l = l[n]
  | 0, a :: t, _ => by simp [EL, HD_def]
  | n + 1, a :: t, h => by
    simp only [EL, TL, List.getElem_cons_succ]
    exact Aux.EL_eq n t (by simpa using h)

theorem Aux.isPREFIX_iff {α : Type u} {l1 l2 : List α} : isPREFIX l1 l2 ↔ l1 <+: l2 := by
  induction l1 generalizing l2 with
  | nil => simp [isPREFIX]
  | cons a t ih =>
    cases l2 with
    | nil => simp [isPREFIX]
    | cons b s => simp [isPREFIX, ih, List.cons_prefix_cons]

theorem Aux.ALOOKUP_append {α : Type u} {β : Type v} (l1 l2 : List (α × β)) (x : α) :
    ALOOKUP (l1 ++ l2) x = match ALOOKUP l1 x with | some y => some y | none => ALOOKUP l2 x := by
  induction l1 with
  | nil => rfl
  | cons a t ih =>
    obtain ⟨a, b⟩ := a
    by_cases h : a = x <;> simp [ALOOKUP, h, ih]

/-! ## finite maps -/

theorem Aux.FLOOKUP_eq_some {α : Type u} {β : Type v} [Nonempty β] {f : fmap α β} {x : α} {y : β} :
    FLOOKUP f x = some y ↔ x ∈ FDOM f ∧ FAPPLY f x = y := by
  unfold FLOOKUP
  by_cases h : x ∈ FDOM f <;> simp [h]

/-! ## numbers -/

theorem Aux.EVEN_iff (n : Nat) : EVEN n ↔ n % 2 = 0 := by
  induction n with
  | zero => simp [EVEN]
  | succ n ih => simp only [EVEN, ih]; omega

theorem Aux.MAX_eq (m n : Nat) : MAX m n = max m n := by
  unfold MAX; split <;> omega

/-! ## sptree -/

theorem Aux.mem_domain_insert {α : Type u} (a : α) : ∀ (k : Nat) (t : spt α) (x : Nat),
    x ∈ sptree.domain (sptree.insert k a t) ↔ x = k ∨ x ∈ sptree.domain t := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro t x
    by_cases hk : k = 0
    · subst hk
      cases t <;> rw [sptree.insert] <;>
        simp [sptree.domain, Aux.mem_UNION, Aux.mem_INSERT, Aux.mem_EMPTY, or_assoc]
    · by_cases he : EVEN k
      · obtain ⟨m, rfl⟩ : ∃ m, k = 2 * m + 2 := ⟨(k - 1) / 2, by
          rw [Aux.EVEN_iff] at he; omega⟩
        have e : (2 * m + 2 - 1) / 2 = m := by omega
        have ih' := ih m (by omega)
        cases t <;> rw [sptree.insert] <;>
          simp only [hk, he, if_true, if_false, sptree.domain, Aux.mem_UNION, Aux.mem_INSERT,
            Aux.mem_EMPTY, Aux.mem_IMAGE, e, ih'] <;> grind
      · obtain ⟨m, rfl⟩ : ∃ m, k = 2 * m + 1 := ⟨(k - 1) / 2, by
          rw [Aux.EVEN_iff] at he; omega⟩
        have e : (2 * m + 1 - 1) / 2 = m := by omega
        have ih' := ih m (by omega)
        cases t <;> rw [sptree.insert] <;>
          simp only [hk, he, if_false, sptree.domain, Aux.mem_UNION, Aux.mem_INSERT,
            Aux.mem_EMPTY, Aux.mem_IMAGE, e, ih'] <;> grind

/-! ## strings and numbers -/

theorem Aux.FIELDS_cons (P : char → Prop) (h : char) (t : string) :
    FIELDS P (h :: t) =
      if P h then [] :: FIELDS P t
      else match FIELDS P t with
        | [] => [[h]]
        | f :: fs => (h :: f) :: fs := by
  by_cases hp : P h
  · rw [FIELDS]; simp [SPLITP, hp, NULL, TL]
  · rw [FIELDS]
    cases t with
    | nil => simp [SPLITP, hp, NULL, FIELDS]
    | cons a t =>
      rw [FIELDS]
      by_cases ha : P a
      · simp [SPLITP, hp, ha, NULL, TL]
      · simp only [SPLITP, hp, ha, if_false, NULL]
        cases hs : (SPLITP P t).2 <;> simp

theorem Aux.n2l_lt (b n : Nat) (hb : 2 ≤ b) : ∀ d, d ∈ n2l b n → d < b := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro d hd
    rw [n2l] at hd
    split at hd
    · simp at hd; subst hd; exact Nat.mod_lt _ (by omega)
    · rename_i hc
      simp at hd
      rcases hd with h | h
      · subst h; exact Nat.mod_lt _ (by omega)
      · exact ih (n / b) (Nat.div_lt_self (by omega) (by omega)) d h

theorem Aux.l2n_n2l (b n : Nat) (hb : 2 ≤ b) : l2n b (n2l b n) = n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    rw [n2l]
    split
    · simp only [l2n, Nat.mod_mod]
      have : n < b := by omega
      simp [Nat.mod_eq_of_lt this]
    · simp only [l2n, Nat.mod_mod]
      rw [ih (n / b) (Nat.div_lt_self (by omega) (by omega))]
      exact Nat.mod_add_div n b

theorem Aux.UNHEX_HEX (d : Nat) (h : d < 16) : UNHEX (HEX d) = d := by
  unfold HEX
  have h0 : ORD (ch '0') = 48 := by decide
  have hA : ORD (ch 'A') = 65 := by decide
  have ha : ORD (ch 'a') = 97 := by decide
  have h9 : ORD (ch '9') = 57 := by decide
  have hf : ORD (ch 'f') = 102 := by decide
  have hF : ORD (ch 'F') = 70 := by decide
  by_cases h10 : d < 10
  · simp only [h10, if_true, h0]
    rw [CHR_of_lt (by omega : 48 + d < 256)]
    simp only [UNHEX, h0, h9]
    simp only [ORD]
    rw [if_pos (by omega)]; omega
  · simp only [h10, h, if_true, if_false, hA]
    rw [CHR_of_lt (by omega : 65 + (d - 10) < 256)]
    simp only [UNHEX, h0, h9, ha, hf, hA, hF]
    simp only [ORD]
    rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)]; omega

end Candle
