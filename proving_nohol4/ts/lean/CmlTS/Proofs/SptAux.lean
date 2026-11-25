import CmlTS.Prelude.Sptree
import CmlTS.Proofs.ListAux

namespace CmlTS

open scoped Classical

variable {α β : Type}

theorem Aux.lookup_even (n : Nat) (t1 t2 : spt α) (a : α) :
    lookup (2 * n + 2) (spt.BN t1 t2) = lookup n t1 ∧
    lookup (2 * n + 2) (spt.BS t1 a t2) = lookup n t1 := by
  have h1 : (2 * n + 2) % 2 = 0 := by omega
  have h2 : (2 * n + 2 - 1) / 2 = n := by omega
  have h3 : 2 * n + 2 ≠ 0 := by omega
  constructor
  · rw [lookup, if_neg h3, if_pos h1, h2]
  · rw [lookup, if_neg h3, if_pos h1, h2]

theorem Aux.lookup_odd (n : Nat) (t1 t2 : spt α) (a : α) :
    lookup (2 * n + 1) (spt.BN t1 t2) = lookup n t2 ∧
    lookup (2 * n + 1) (spt.BS t1 a t2) = lookup n t2 := by
  have h1 : ¬ (2 * n + 1) % 2 = 0 := by omega
  have h2 : (2 * n + 1 - 1) / 2 = n := by omega
  have h3 : 2 * n + 1 ≠ 0 := by omega
  constructor
  · rw [lookup, if_neg h3, if_neg h1, h2]
  · rw [lookup, if_neg h3, if_neg h1, h2]

theorem Aux.nat_cases (n : Nat) : n = 0 ∨ (∃ k, n = 2 * k + 2) ∨ (∃ k, n = 2 * k + 1) := by
  by_cases h : n = 0
  · exact Or.inl h
  · by_cases h2 : n % 2 = 0
    · exact Or.inr (Or.inl ⟨n / 2 - 1, by omega⟩)
    · exact Or.inr (Or.inr ⟨n / 2, by omega⟩)

theorem Aux.mem_domain (m : spt α) : ∀ n, n ∈ domain m ↔ ∃ v, lookup n m = some v := by
  induction m with
  | LN => intro n; simp [domain, lookup, Aux.not_mem_empty]
  | LS a =>
    intro n
    simp only [domain, lookup, Aux.mem_singleton]
    by_cases h : n = 0 <;> simp [h]
  | BN t1 t2 ih1 ih2 =>
    intro n
    simp only [domain, Aux.mem_union, Aux.mem_IMAGE]
    rcases Aux.nat_cases n with rfl | ⟨k, rfl⟩ | ⟨k, rfl⟩
    · simp [lookup]
    · constructor
      · rintro (⟨x, hx, hd⟩ | ⟨x, hx, hd⟩)
        · have : x = k := by omega
          subst this
          obtain ⟨v, hv⟩ := (ih1 x).mp hd
          by_cases ha : Nonempty α
          · exact ⟨v, by rw [(Aux.lookup_even x t1 t2 v).1, hv]⟩
          · exact (ha ⟨v⟩).elim
        · omega
      · rintro ⟨v, hv⟩
        rw [(Aux.lookup_even k t1 t2 v).1] at hv
        exact Or.inl ⟨k, rfl, (ih1 k).mpr ⟨v, hv⟩⟩
    · constructor
      · rintro (⟨x, hx, hd⟩ | ⟨x, hx, hd⟩)
        · omega
        · have : x = k := by omega
          subst this
          obtain ⟨v, hv⟩ := (ih2 x).mp hd
          exact ⟨v, by rw [(Aux.lookup_odd x t1 t2 v).1, hv]⟩
      · rintro ⟨v, hv⟩
        rw [(Aux.lookup_odd k t1 t2 v).1] at hv
        exact Or.inr ⟨k, rfl, (ih2 k).mpr ⟨v, hv⟩⟩
  | BS t1 a t2 ih1 ih2 =>
    intro n
    simp only [domain, Aux.mem_union, Aux.mem_IMAGE, Aux.mem_singleton]
    rcases Aux.nat_cases n with rfl | ⟨k, rfl⟩ | ⟨k, rfl⟩
    · simp [lookup]
    · constructor
      · rintro ((h | ⟨x, hx, hd⟩) | ⟨x, hx, hd⟩)
        · omega
        · have : x = k := by omega
          subst this
          obtain ⟨v, hv⟩ := (ih1 x).mp hd
          exact ⟨v, by rw [(Aux.lookup_even x t1 t2 a).2, hv]⟩
        · omega
      · rintro ⟨v, hv⟩
        rw [(Aux.lookup_even k t1 t2 a).2] at hv
        exact Or.inl (Or.inr ⟨k, rfl, (ih1 k).mpr ⟨v, hv⟩⟩)
    · constructor
      · rintro ((h | ⟨x, hx, hd⟩) | ⟨x, hx, hd⟩)
        · omega
        · omega
        · have : x = k := by omega
          subst this
          obtain ⟨v, hv⟩ := (ih2 x).mp hd
          exact ⟨v, by rw [(Aux.lookup_odd x t1 t2 a).2, hv]⟩
      · rintro ⟨v, hv⟩
        rw [(Aux.lookup_odd k t1 t2 a).2] at hv
        exact Or.inr ⟨k, rfl, (ih2 k).mpr ⟨v, hv⟩⟩

theorem Aux.mem_toListA (m : spt α) :
    ∀ acc v, v ∈ toListA acc m ↔ v ∈ acc ∨ ∃ n, lookup n m = some v := by
  induction m with
  | LN => intro acc v; simp [toListA, lookup]
  | LS a =>
    intro acc v
    simp only [toListA, lookup, List.mem_cons]
    constructor
    · rintro (rfl | h)
      · exact Or.inr ⟨0, by simp⟩
      · exact Or.inl h
    · rintro (h | ⟨n, hn⟩)
      · exact Or.inr h
      · by_cases h : n = 0
        · simp [h] at hn; exact Or.inl hn.symm
        · simp [h] at hn
  | BN t1 t2 ih1 ih2 =>
    intro acc v
    simp only [toListA, ih1, ih2]
    constructor
    · rintro ((h | ⟨n, hn⟩) | ⟨n, hn⟩)
      · exact Or.inl h
      · exact Or.inr ⟨2 * n + 1, by rw [(Aux.lookup_odd n t1 t2 v).1, hn]⟩
      · exact Or.inr ⟨2 * n + 2, by rw [(Aux.lookup_even n t1 t2 v).1, hn]⟩
    · rintro (h | ⟨n, hn⟩)
      · exact Or.inl (Or.inl h)
      · rcases Aux.nat_cases n with rfl | ⟨k, rfl⟩ | ⟨k, rfl⟩
        · simp [lookup] at hn
        · rw [(Aux.lookup_even k t1 t2 v).1] at hn; exact Or.inr ⟨k, hn⟩
        · rw [(Aux.lookup_odd k t1 t2 v).1] at hn; exact Or.inl (Or.inr ⟨k, hn⟩)
  | BS t1 a t2 ih1 ih2 =>
    intro acc v
    simp only [toListA, ih1, ih2, List.mem_cons]
    constructor
    · rintro ((rfl | h | ⟨n, hn⟩) | ⟨n, hn⟩)
      · exact Or.inr ⟨0, by simp [lookup]⟩
      · exact Or.inl h
      · exact Or.inr ⟨2 * n + 1, by rw [(Aux.lookup_odd n t1 t2 a).2, hn]⟩
      · exact Or.inr ⟨2 * n + 2, by rw [(Aux.lookup_even n t1 t2 a).2, hn]⟩
    · rintro (h | ⟨n, hn⟩)
      · exact Or.inl (Or.inr (Or.inl h))
      · rcases Aux.nat_cases n with rfl | ⟨k, rfl⟩ | ⟨k, rfl⟩
        · simp [lookup] at hn; exact Or.inl (Or.inl hn.symm)
        · rw [(Aux.lookup_even k t1 t2 a).2] at hn; exact Or.inr ⟨k, hn⟩
        · rw [(Aux.lookup_odd k t1 t2 a).2] at hn; exact Or.inl (Or.inr (Or.inr ⟨k, hn⟩))

theorem Aux.mem_spt_toList (m : spt α) (v : α) :
    v ∈ spt_toList m ↔ ∃ n, lookup n m = some v := by
  unfold spt_toList
  rw [Aux.mem_toListA]
  simp

theorem Aux.domain_enum (m : spt α) : ∃ l : List Nat, l.Nodup ∧ ∀ x, x ∈ l ↔ x ∈ domain m := by
  have : ∃ l : List Nat, ∀ x, x ∈ l ↔ x ∈ domain m := by
    induction m with
    | LN => exact ⟨[], fun x => by simp [domain, Aux.not_mem_empty]⟩
    | LS a => exact ⟨[0], fun x => by simp [domain, Aux.mem_singleton]⟩
    | BN t1 t2 ih1 ih2 =>
      obtain ⟨l1, h1⟩ := ih1
      obtain ⟨l2, h2⟩ := ih2
      refine ⟨l1.map (fun n => 2 * n + 2) ++ l2.map (fun n => 2 * n + 1), fun x => ?_⟩
      simp only [List.mem_append, List.mem_map, domain, Aux.mem_union, Aux.mem_IMAGE, h1, h2]
      constructor
      · rintro (⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩)
        · exact Or.inl ⟨a, rfl, ha⟩
        · exact Or.inr ⟨a, rfl, ha⟩
      · rintro (⟨a, rfl, ha⟩ | ⟨a, rfl, ha⟩)
        · exact Or.inl ⟨a, ha, rfl⟩
        · exact Or.inr ⟨a, ha, rfl⟩
    | BS t1 a t2 ih1 ih2 =>
      obtain ⟨l1, h1⟩ := ih1
      obtain ⟨l2, h2⟩ := ih2
      refine ⟨0 :: (l1.map (fun n => 2 * n + 2) ++ l2.map (fun n => 2 * n + 1)), fun x => ?_⟩
      simp only [List.mem_cons, List.mem_append, List.mem_map, domain, Aux.mem_union,
        Aux.mem_IMAGE, Aux.mem_singleton, h1, h2]
      constructor
      · rintro (h | ⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩)
        · exact Or.inl (Or.inl h)
        · exact Or.inl (Or.inr ⟨a, rfl, ha⟩)
        · exact Or.inr ⟨a, rfl, ha⟩
      · rintro ((h | ⟨a, rfl, ha⟩) | ⟨a, rfl, ha⟩)
        · exact Or.inl h
        · exact Or.inr (Or.inl ⟨a, ha, rfl⟩)
        · exact Or.inr (Or.inr ⟨a, ha, rfl⟩)
  obtain ⟨l, hl⟩ := this
  obtain ⟨l', h1, h2⟩ := Aux.nodup_enum l
  exact ⟨l', h1, fun x => (h2 x).trans (hl x)⟩

end CmlTS
