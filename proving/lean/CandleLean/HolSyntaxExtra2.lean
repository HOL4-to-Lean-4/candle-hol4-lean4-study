/-
  HOL4 theory `holSyntaxExtra` (candle/standard/syntax/holSyntaxExtraScript.sml):
  target theorems, second part (split from `HolSyntaxExtra.lean` for parallel translation).
-/
import CandleLean.HolSyntaxExtra

namespace Candle

open HOL Classical

noncomputable section

universe u

/-! Auxiliary lemmas (namespace `Candle.Aux`). -/

theorem Aux.REV_ASSOCD_FILTER' {α β : Type u} (P : β → Prop) (l : List (α × β)) (a : β) (b : α) :
    REV_ASSOCD a (FILTER (fun p => P p.2) l) b = if P a then REV_ASSOCD a l b else b :=
  REV_ASSOCD_FILTER P l a b ()

theorem Aux.REV_ASSOCD_not_mem {α β : Type u} (l : List (α × β)) (a : β) (d : α)
    (h : ¬ a ∈ l.map Prod.snd) : REV_ASSOCD a l d = d := by
  rcases REV_ASSOCD_MEM l a d with h' | h'
  · exact absurd (List.mem_map.mpr ⟨_, h', rfl⟩) h
  · exact h'

theorem Aux.VSUBST_Abs (ilist : List (term × term)) (x : mlstring) (ty : type) (b : term) :
    VSUBST ilist (Abs (Var x ty) b) =
      if EXISTS (fun p => VFREE_IN (Var x ty) p.1 ∧ VFREE_IN p.2 b)
          (FILTER (fun p => ¬ (p.2 = Var x ty)) ilist)
      then Abs (Var (VARIANT (VSUBST (FILTER (fun p => ¬ (p.2 = Var x ty)) ilist) b) (explode x) ty) ty)
        (VSUBST ((Var (VARIANT (VSUBST (FILTER (fun p => ¬ (p.2 = Var x ty)) ilist) b) (explode x) ty) ty,
          Var x ty) :: FILTER (fun p => ¬ (p.2 = Var x ty)) ilist) b)
      else Abs (Var x ty) (VSUBST (FILTER (fun p => ¬ (p.2 = Var x ty)) ilist) b) := by
  simp only [VSUBST, dest_var_def]

theorem Aux.VFREE_IN_Var {v : term} {x : mlstring} {ty : type} :
    VFREE_IN v (Var x ty) ↔ Var x ty = v := Iff.rfl

theorem Aux.VFREE_IN_Const {v : term} {x : mlstring} {ty : type} :
    VFREE_IN v (Const x ty) ↔ Const x ty = v := Iff.rfl

theorem Aux.VFREE_IN_Comb {v s t : term} :
    VFREE_IN v (Comb s t) ↔ VFREE_IN v s ∨ VFREE_IN v t := Iff.rfl

theorem Aux.VFREE_IN_Abs {v w t : term} :
    VFREE_IN v (Abs w t) ↔ w ≠ v ∧ VFREE_IN v t := Iff.rfl

/- HOL4:
Theorem VFREE_IN_VSUBST:
   ∀tm u uty ilist.
      welltyped tm ⇒
      (VFREE_IN (Var u uty) (VSUBST ilist tm) ⇔
       ∃y ty. VFREE_IN (Var y ty) tm ∧
              VFREE_IN (Var u uty) (REV_ASSOCD (Var y ty) ilist (Var y ty))) -/
theorem VFREE_IN_VSUBST :
    ∀ (tm : term) (u : mlstring) (uty : type) (ilist : List (term × term)),
        welltyped tm →
        (VFREE_IN (Var u uty) (VSUBST ilist tm) ↔
         ∃ (y : mlstring) (ty : type), VFREE_IN (Var y ty) tm ∧
                VFREE_IN (Var u uty) (REV_ASSOCD (Var y ty) ilist (Var y ty))) := by
  intro tm u uty
  induction tm with
  | Var x ty =>
    intro ilist _
    simp only [VSUBST]
    constructor
    · intro h; exact ⟨x, ty, rfl, h⟩
    · rintro ⟨y, ty', h1, h2⟩
      rw [Aux.VFREE_IN_Var] at h1
      rw [h1]; exact h2
  | Const x ty =>
    intro ilist _
    simp only [VSUBST]
    constructor
    · intro h; cases h
    · rintro ⟨y, ty', h1, h2⟩; cases h1
  | Comb a b iha ihb =>
    intro ilist hw
    obtain ⟨wa, wb, _⟩ := Aux.welltyped_Comb.mp hw
    simp only [VSUBST, Aux.VFREE_IN_Comb, iha ilist wa, ihb ilist wb]
    constructor
    · rintro (⟨y, ty, h1, h2⟩ | ⟨y, ty, h1, h2⟩)
      · exact ⟨y, ty, Or.inl h1, h2⟩
      · exact ⟨y, ty, Or.inr h1, h2⟩
    · rintro ⟨y, ty, h1 | h1, h2⟩
      · exact Or.inl ⟨y, ty, h1, h2⟩
      · exact Or.inr ⟨y, ty, h1, h2⟩
  | Abs v b _ ihb =>
    intro ilist hw
    obtain ⟨x, xty, rfl, wb⟩ := Aux.welltyped_Abs.mp hw
    rw [Aux.VSUBST_Abs]
    have hF : ∀ y ty, Var y ty ≠ Var x xty →
        REV_ASSOCD (Var y ty) (FILTER (fun p => ¬ (p.2 = Var x xty)) ilist) (Var y ty) =
          REV_ASSOCD (Var y ty) ilist (Var y ty) := by
      intro y ty hne
      rw [Aux.REV_ASSOCD_FILTER' (fun s => ¬ s = Var x xty), if_pos hne]
    have hF2 : REV_ASSOCD (Var x xty) (FILTER (fun p => ¬ (p.2 = Var x xty)) ilist) (Var x xty) =
          Var x xty := by
      rw [Aux.REV_ASSOCD_FILTER' (fun s => ¬ s = Var x xty), if_neg (fun h => h rfl)]
    split
    · have hv := VARIANT_THM (VSUBST (FILTER (fun p => ¬ (p.2 = Var x xty)) ilist) b) (explode x) xty
      generalize VARIANT (VSUBST (FILTER (fun p => ¬ (p.2 = Var x xty)) ilist) b) (explode x) xty = z at hv ⊢
      rw [Aux.VFREE_IN_Abs, ihb _ wb]
      constructor
      · rintro ⟨hne, y, ty, h1, h2⟩
        simp only [REV_ASSOCD] at h2
        by_cases he : Var x xty = Var y ty
        · rw [if_pos he] at h2
          exact absurd h2 hne
        · rw [if_neg he, hF y ty (fun h => he h.symm)] at h2
          exact ⟨y, ty, ⟨he, h1⟩, h2⟩
      · rintro ⟨y, ty, ⟨he, h1⟩, h2⟩
        refine ⟨fun hz => hv ?_, y, ty, h1, ?_⟩
        · rw [hz, ihb _ wb]
          exact ⟨y, ty, h1, by rw [hF y ty (fun h => he h.symm)]; exact h2⟩
        · simp only [REV_ASSOCD]
          rw [if_neg he, hF y ty (fun h => he h.symm)]; exact h2
    · next hne =>
      rw [Aux.VFREE_IN_Abs, ihb _ wb]
      constructor
      · rintro ⟨hne', y, ty, h1, h2⟩
        by_cases he : Var x xty = Var y ty
        · rw [← he, hF2] at h2
          exact absurd h2 hne'
        · rw [hF y ty (fun h => he h.symm)] at h2
          exact ⟨y, ty, ⟨he, h1⟩, h2⟩
      · rintro ⟨y, ty, ⟨he, h1⟩, h2⟩
        refine ⟨fun hz => ?_, y, ty, h1, by rw [hF y ty (fun h => he h.symm)]; exact h2⟩
        rw [← hz] at h2
        rcases REV_ASSOCD_MEM ilist (Var y ty) (Var y ty) with hm | hm
        · apply hne
          rw [Aux.EXISTS_iff]
          refine ⟨_, (Aux.mem_FILTER _ _ _).mpr ⟨hm, fun h => he h.symm⟩, h2, h1⟩
        · rw [hm] at h2
          exact he h2.symm

/- HOL4:
Theorem VSUBST_NIL[simp]:
   ∀tm. VSUBST [] tm = tm -/
theorem VSUBST_NIL :
    ∀ (tm : term), VSUBST [] tm = tm := by
  intro tm
  induction tm with
  | Var x ty => rfl
  | Const x ty => rfl
  | Comb a b iha ihb => simp only [VSUBST, iha, ihb]
  | Abs v b _ ihb => simp [VSUBST, FILTER, EXISTS, ihb]

theorem Aux.INST_CORE_Var (env : List (term × term)) (tyin : List (type × type)) (x : mlstring)
    (ty : type) : INST_CORE env tyin (Var x ty) =
      if REV_ASSOCD (Var x (TYPE_SUBST tyin ty)) env (Var x ty) = Var x ty
      then Result (Var x (TYPE_SUBST tyin ty)) else Clash (Var x (TYPE_SUBST tyin ty)) := by
  rw [INST_CORE]

theorem Aux.INST_CORE_Const (env : List (term × term)) (tyin : List (type × type)) (x : mlstring)
    (ty : type) : INST_CORE env tyin (Const x ty) = Result (Const x (TYPE_SUBST tyin ty)) := by
  rw [INST_CORE]

theorem Aux.INST_CORE_Comb (env : List (term × term)) (tyin : List (type × type)) (s t : term) :
    INST_CORE env tyin (Comb s t) =
      match INST_CORE env tyin s, INST_CORE env tyin t with
      | Result s', Result t' => Result (Comb s' t')
      | Clash c, _ => Clash c
      | Result _, Clash c => Clash c := by
  rw [INST_CORE]
  cases INST_CORE env tyin s with
  | Clash c => simp [IS_CLASH]
  | Result s' =>
    cases INST_CORE env tyin t with
    | Clash c => simp [IS_CLASH]
    | Result t' => simp [IS_CLASH, RESULT_def]

theorem Aux.INST_CORE_Abs (env : List (term × term)) (tyin : List (type × type)) (x : mlstring)
    (ty : type) (b : term) :
    INST_CORE env tyin (Abs (Var x ty) b) =
      match INST_CORE ((Var x ty, Var x (TYPE_SUBST tyin ty)) :: env) tyin b with
      | Result b' => Result (Abs (Var x (TYPE_SUBST tyin ty)) b')
      | Clash w =>
        if w ≠ Var x (TYPE_SUBST tyin ty) then Clash w else
        match INST_CORE
          ((Var (VARIANT (RESULT (INST_CORE [] tyin b)) (explode x) (TYPE_SUBST tyin ty)) ty,
            Var (VARIANT (RESULT (INST_CORE [] tyin b)) (explode x) (TYPE_SUBST tyin ty))
              (TYPE_SUBST tyin ty)) :: env) tyin
          (VSUBST [(Var (VARIANT (RESULT (INST_CORE [] tyin b)) (explode x) (TYPE_SUBST tyin ty)) ty,
            Var x ty)] b) with
        | Result b' => Result (Abs (Var (VARIANT (RESULT (INST_CORE [] tyin b)) (explode x)
            (TYPE_SUBST tyin ty)) (TYPE_SUBST tyin ty)) b')
        | Clash w => Clash w := by
  rw [INST_CORE]
  simp only [dest_var_def]
  cases INST_CORE ((Var x ty, Var x (TYPE_SUBST tyin ty)) :: env) tyin b with
  | Result b' => simp [IS_RESULT, RESULT_def]
  | Clash w =>
    simp only [IS_RESULT, if_false, CLASH_def]
    by_cases hw : w ≠ Var x (TYPE_SUBST tyin ty)
    · rw [if_pos hw, if_pos hw]
    · rw [if_neg hw, if_neg hw]
      cases INST_CORE
          ((Var (VARIANT (RESULT (INST_CORE [] tyin b)) (explode x) (TYPE_SUBST tyin ty)) ty,
            Var (VARIANT (RESULT (INST_CORE [] tyin b)) (explode x) (TYPE_SUBST tyin ty))
              (TYPE_SUBST tyin ty)) :: env) tyin
          (VSUBST [(Var (VARIANT (RESULT (INST_CORE [] tyin b)) (explode x) (TYPE_SUBST tyin ty)) ty,
            Var x ty)] b) with
      | Result b' => simp [RESULT_def]
      | Clash w => simp

theorem Aux.INST_CORE_Comb_Result {env : List (term × term)} {tyin : List (type × type)} {s t r : term}
    (h : INST_CORE env tyin (Comb s t) = Result r) :
    ∃ s' t', INST_CORE env tyin s = Result s' ∧ INST_CORE env tyin t = Result t' ∧ r = Comb s' t' := by
  rw [Aux.INST_CORE_Comb] at h
  cases hs : INST_CORE env tyin s with
  | Clash c => rw [hs] at h; simp at h
  | Result s' =>
    cases ht : INST_CORE env tyin t with
    | Clash c => rw [hs, ht] at h; simp at h
    | Result t' =>
      rw [hs, ht] at h
      exact ⟨s', t', rfl, rfl, (result.Result.inj h).symm⟩

theorem Aux.INST_CORE_Abs_Result {env : List (term × term)} {tyin : List (type × type)} {x : mlstring}
    {ty : type} {b r : term} (h : INST_CORE env tyin (Abs (Var x ty) b) = Result r) :
    (∃ b', INST_CORE ((Var x ty, Var x (TYPE_SUBST tyin ty)) :: env) tyin b = Result b' ∧
      r = Abs (Var x (TYPE_SUBST tyin ty)) b') ∨
    (∃ x' b', x' = VARIANT (RESULT (INST_CORE [] tyin b)) (explode x) (TYPE_SUBST tyin ty) ∧
      INST_CORE ((Var x' ty, Var x' (TYPE_SUBST tyin ty)) :: env) tyin
        (VSUBST [(Var x' ty, Var x ty)] b) = Result b' ∧
      r = Abs (Var x' (TYPE_SUBST tyin ty)) b') := by
  rw [Aux.INST_CORE_Abs] at h
  split at h
  · next b' hb => exact Or.inl ⟨b', hb, (result.Result.inj h).symm⟩
  · split at h
    · cases h
    · split at h
      · next b' hb => exact Or.inr ⟨_, b', rfl, hb, (result.Result.inj h).symm⟩
      · cases h

theorem Aux.VFREE_IN_VSUBST_single {b : term} {x x' u : mlstring} {ty uty : type} (hw : welltyped b) :
    VFREE_IN (Var u uty) (VSUBST [(Var x' ty, Var x ty)] b) ↔
      (VFREE_IN (Var u uty) b ∧ Var x ty ≠ Var u uty) ∨
      (VFREE_IN (Var x ty) b ∧ Var x' ty = Var u uty) := by
  rw [VFREE_IN_VSUBST b u uty _ hw]
  constructor
  · rintro ⟨y, t, h1, h2⟩
    simp only [REV_ASSOCD] at h2
    by_cases he : Var x ty = Var y t
    · rw [if_pos he] at h2
      exact Or.inr ⟨he ▸ h1, h2⟩
    · rw [if_neg he] at h2
      rw [Aux.VFREE_IN_Var] at h2
      rw [h2] at h1 he
      exact Or.inl ⟨h1, he⟩
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · refine ⟨u, uty, h1, ?_⟩
      simp only [REV_ASSOCD]
      rw [if_neg h2]; rfl
    · refine ⟨x, ty, h1, ?_⟩
      simp only [REV_ASSOCD, if_true]
      exact h2

theorem Aux.single_subst_ok(x x' : mlstring) (ty : type) :
    ∀ s s', (s', s) ∈ [(Var x' ty, Var x ty)] → ∃ y t, s = Var y t ∧ has_type s' t := by
  intro s s' hm
  cases List.mem_singleton.mp hm
  exact ⟨x, ty, rfl, has_type.Var⟩

theorem Aux.single_subst_ok' (x x' : mlstring) (ty : type) :
    ∀ s' s, (s', s) ∈ [(Var x' ty, Var x ty)] → ∃ y t, s' = Var y t := by
  intro s' s hm
  cases List.mem_singleton.mp hm
  exact ⟨x', ty, rfl⟩

theorem Aux.typeof_VSUBST {tm : term} {ilist : List (term × term)} (hw : welltyped tm)
    (hi : ∀ s s', (s', s) ∈ ilist → ∃ y t, s = Var y t ∧ has_type s' t) :
    typeof (VSUBST ilist tm) = typeof tm :=
  WELLTYPED_LEMMA _ _ (VSUBST_HAS_TYPE tm _ ilist ⟨(WELLTYPED tm).mp hw, hi⟩)

/- HOL4:
Theorem INST_CORE_HAS_TYPE:
   ∀n tm env tyin.
      welltyped tm ∧ (sizeof tm = n) ∧
      (∀s s'. MEM (s,s') env ⇒
              ∃x ty. (s = Var x ty) ∧
                     (s' = Var x (TYPE_SUBST tyin ty)))
      ⇒ (∃x ty. (INST_CORE env tyin tm = Clash(Var x (TYPE_SUBST tyin ty))) ∧
                VFREE_IN (Var x ty) tm ∧
                REV_ASSOCD (Var x (TYPE_SUBST tyin ty))
                  env (Var x ty) ≠ Var x ty)
      ∨ (∀x ty. VFREE_IN (Var x ty) tm
                ⇒ REV_ASSOCD (Var x (TYPE_SUBST tyin ty))
                    env (Var x ty) = Var x ty) ∧
        (∃tm'. INST_CORE env tyin tm = Result tm' ∧
               tm' has_type (TYPE_SUBST tyin (typeof tm)) ∧
               (∀u uty. VFREE_IN (Var u uty) tm' ⇔
                        ∃oty. VFREE_IN (Var u oty) tm ∧
                              uty = TYPE_SUBST tyin oty)) -/
theorem INST_CORE_HAS_TYPE :
    ∀ (n : Nat) (tm : term) (env : List (term × term)) (tyin : List (type × type)),
        welltyped tm ∧ sizeof tm = n ∧
        (∀ (s s' : term), (s, s') ∈ env →
                ∃ (x : mlstring) (ty : type), s = Var x ty ∧
                       s' = Var x (TYPE_SUBST tyin ty))
        → (∃ (x : mlstring) (ty : type), INST_CORE env tyin tm = Clash (Var x (TYPE_SUBST tyin ty)) ∧
                  VFREE_IN (Var x ty) tm ∧
                  REV_ASSOCD (Var x (TYPE_SUBST tyin ty))
                    env (Var x ty) ≠ Var x ty)
        ∨ (∀ (x : mlstring) (ty : type), VFREE_IN (Var x ty) tm
                  → REV_ASSOCD (Var x (TYPE_SUBST tyin ty))
                      env (Var x ty) = Var x ty) ∧
          (∃ (tm' : term), INST_CORE env tyin tm = Result tm' ∧
                 has_type tm' (TYPE_SUBST tyin (typeof tm)) ∧
                 (∀ (u : mlstring) (uty : type), VFREE_IN (Var u uty) tm' ↔
                          ∃ (oty : type), VFREE_IN (Var u oty) tm ∧
                                uty = TYPE_SUBST tyin oty)) := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n IH =>
    rintro tm env tyin ⟨hw, hn, he⟩
    cases tm with
    | Var x ty =>
      rw [Aux.INST_CORE_Var]
      by_cases h : REV_ASSOCD (Var x (TYPE_SUBST tyin ty)) env (Var x ty) = Var x ty
      · rw [if_pos h]
        refine Or.inr ⟨?_, _, rfl, has_type.Var, ?_⟩
        · intro y uy hv
          obtain ⟨rfl, rfl⟩ := term.Var.inj (Aux.VFREE_IN_Var.mp hv)
          exact h
        · intro u uty
          constructor
          · intro hv
            obtain ⟨rfl, rfl⟩ := term.Var.inj (Aux.VFREE_IN_Var.mp hv)
            exact ⟨ty, rfl, rfl⟩
          · rintro ⟨oty, hv, rfl⟩
            obtain ⟨rfl, rfl⟩ := term.Var.inj (Aux.VFREE_IN_Var.mp hv)
            rfl
      · rw [if_neg h]
        exact Or.inl ⟨x, ty, rfl, rfl, h⟩
    | Const x ty =>
      rw [Aux.INST_CORE_Const]
      refine Or.inr ⟨?_, _, rfl, has_type.Const, ?_⟩
      · intro y uy hv; cases hv
      · intro u uty
        constructor
        · intro hv; cases hv
        · rintro ⟨oty, hv, _⟩; cases hv
    | Comb s t =>
      obtain ⟨ws, wt, rty, hst⟩ := Aux.welltyped_Comb.mp hw
      simp only [sizeof] at hn
      rw [Aux.INST_CORE_Comb]
      rcases IH (sizeof s) (by omega) s env tyin ⟨ws, rfl, he⟩ with
        ⟨x, ty, h1, h2, h3⟩ | ⟨h1, s', h2, h3, h4⟩
      · refine Or.inl ⟨x, ty, ?_, Or.inl h2, h3⟩
        rw [h1]
      · rcases IH (sizeof t) (by omega) t env tyin ⟨wt, rfl, he⟩ with
          ⟨x, ty, k1, k2, k3⟩ | ⟨k1, t', k2, k3, k4⟩
        · refine Or.inl ⟨x, ty, ?_, Or.inr k2, k3⟩
          rw [h2, k1]
        · refine Or.inr ⟨?_, Comb s' t', ?_, ?_, ?_⟩
          · rintro y uy (hv | hv)
            · exact h1 y uy hv
            · exact k1 y uy hv
          · rw [h2, k2]
          · rw [hst, Aux.TYPE_SUBST_Fun] at h3
            have : typeof (Comb s t) = rty := by rw [typeof, hst]; rfl
            rw [this]
            exact has_type.Comb h3 k3
          · intro u uty
            rw [Aux.VFREE_IN_Comb, h4, k4]
            constructor
            · rintro (⟨o, g1, g2⟩ | ⟨o, g1, g2⟩)
              · exact ⟨o, Or.inl g1, g2⟩
              · exact ⟨o, Or.inr g1, g2⟩
            · rintro ⟨o, g1 | g1, g2⟩
              · exact Or.inl ⟨o, g1, g2⟩
              · exact Or.inr ⟨o, g1, g2⟩
    | Abs v b =>
      obtain ⟨x, ty, rfl, wb⟩ := Aux.welltyped_Abs.mp hw
      simp only [sizeof] at hn
      have he1 : ∀ (s s' : term), (s, s') ∈ (Var x ty, Var x (TYPE_SUBST tyin ty)) :: env →
          ∃ (x : mlstring) (ty : type), s = Var x ty ∧ s' = Var x (TYPE_SUBST tyin ty) := by
        intro s s' hm
        rcases List.mem_cons.mp hm with hm | hm
        · cases hm; exact ⟨x, ty, rfl, rfl⟩
        · exact he s s' hm
      have hT : TYPE_SUBST tyin (typeof (Abs (Var x ty) b)) =
          Fun (TYPE_SUBST tyin ty) (TYPE_SUBST tyin (typeof b)) := by
        simp only [typeof]; exact Aux.TYPE_SUBST_Fun _ _ _
      rw [hT, Aux.INST_CORE_Abs]
      rcases IH (sizeof b) (by omega) b _ tyin ⟨wb, rfl, he1⟩ with
        ⟨y, uy, h1, h2, h3⟩ | ⟨h1, b', h2, h3, h4⟩
      · simp only [h1]
        simp only [REV_ASSOCD] at h3
        by_cases hc : Var x (TYPE_SUBST tyin ty) = Var y (TYPE_SUBST tyin uy)
        · -- rename
          rw [if_neg (fun h => h hc.symm)]
          have hN : ¬ ∃ oty, VFREE_IN (Var (VARIANT (RESULT (INST_CORE [] tyin b)) (explode x)
              (TYPE_SUBST tyin ty)) oty) b ∧ TYPE_SUBST tyin ty = TYPE_SUBST tyin oty := by
            rcases IH (sizeof b) (by omega) b [] tyin ⟨wb, rfl, by simp⟩ with
              ⟨y, uy, _, _, k3⟩ | ⟨_, r, k2, _, k4⟩
            · exact absurd rfl k3
            · have hv := VARIANT_THM (RESULT (INST_CORE [] tyin b)) (explode x) (TYPE_SUBST tyin ty)
              generalize VARIANT (RESULT (INST_CORE [] tyin b)) (explode x) (TYPE_SUBST tyin ty) = z at hv ⊢
              rw [k2, RESULT_def, k4] at hv
              exact hv
          generalize VARIANT (RESULT (INST_CORE [] tyin b)) (explode x) (TYPE_SUBST tyin ty) = x' at hN ⊢
          have he2 : ∀ (s s' : term), (s, s') ∈ (Var x' ty, Var x' (TYPE_SUBST tyin ty)) :: env →
              ∃ (x : mlstring) (ty : type), s = Var x ty ∧ s' = Var x (TYPE_SUBST tyin ty) := by
            intro s s' hm
            rcases List.mem_cons.mp hm with hm | hm
            · cases hm; exact ⟨x', ty, rfl, rfl⟩
            · exact he s s' hm
          have hsz : sizeof (VSUBST [(Var x' ty, Var x ty)] b) = sizeof b :=
            SIZEOF_VSUBST b _ (Aux.single_subst_ok' x x' ty)
          have hwb2 : welltyped (VSUBST [(Var x' ty, Var x ty)] b) :=
            VSUBST_WELLTYPED b ty _ ⟨wb, Aux.single_subst_ok x x' ty⟩
          rcases IH (sizeof b) (by omega) (VSUBST [(Var x' ty, Var x ty)] b) _ tyin
            ⟨hwb2, hsz, he2⟩ with ⟨y2, uy2, k1, k2, k3⟩ | ⟨k1, b2, k2, k3, k4⟩
          · simp only [k1]
            refine Or.inl ⟨y2, uy2, rfl, ?_⟩
            simp only [REV_ASSOCD] at k3
            rcases (Aux.VFREE_IN_VSUBST_single wb).mp k2 with ⟨g1, g2⟩ | ⟨g1, g2⟩
            · by_cases hd : Var x' (TYPE_SUBST tyin ty) = Var y2 (TYPE_SUBST tyin uy2)
              · obtain ⟨rfl, hd2⟩ := term.Var.inj hd
                exact absurd ⟨uy2, g1, hd2⟩ hN
              · rw [if_neg hd] at k3
                exact ⟨⟨g2, g1⟩, k3⟩
            · obtain ⟨rfl, rfl⟩ := term.Var.inj g2
              rw [if_pos rfl] at k3
              exact absurd rfl k3
          · simp only [k2]
            refine Or.inr ⟨?_, _, rfl, ?_, ?_⟩
            · rintro u uu ⟨g1, g2⟩
              have g3 := k1 u uu ((Aux.VFREE_IN_VSUBST_single wb).mpr (Or.inl ⟨g2, g1⟩))
              simp only [REV_ASSOCD] at g3
              by_cases hd : Var x' (TYPE_SUBST tyin ty) = Var u (TYPE_SUBST tyin uu)
              · obtain ⟨rfl, hd2⟩ := term.Var.inj hd
                exact absurd ⟨uu, g2, hd2⟩ hN
              · rw [if_neg hd] at g3; exact g3
            · rw [Aux.typeof_VSUBST wb (Aux.single_subst_ok x x' ty)] at k3
              exact has_type.Abs k3
            · intro u uty
              rw [Aux.VFREE_IN_Abs, k4]
              constructor
              · rintro ⟨g1, oty, g2, rfl⟩
                rcases (Aux.VFREE_IN_VSUBST_single wb).mp g2 with ⟨l1, l2⟩ | ⟨l1, l2⟩
                · exact ⟨oty, ⟨l2, l1⟩, rfl⟩
                · obtain ⟨rfl, rfl⟩ := term.Var.inj l2
                  exact absurd rfl g1
              · rintro ⟨oty, ⟨g1, g2⟩, rfl⟩
                refine ⟨fun hd => ?_, oty, (Aux.VFREE_IN_VSUBST_single wb).mpr (Or.inl ⟨g2, g1⟩), rfl⟩
                obtain ⟨rfl, hd2⟩ := term.Var.inj hd
                exact absurd ⟨oty, g2, hd2⟩ hN
        · rw [if_pos (fun h => hc h.symm)]
          rw [if_neg hc] at h3
          refine Or.inl ⟨y, uy, rfl, ⟨fun h => ?_, h2⟩, h3⟩
          obtain ⟨rfl, rfl⟩ := term.Var.inj h
          exact hc rfl
      · simp only [h2]
        have hd : ∀ y uy, VFREE_IN (Var y uy) b → Var x ty ≠ Var y uy →
            Var x (TYPE_SUBST tyin ty) ≠ Var y (TYPE_SUBST tyin uy) := by
          intro y uy g1 g2 g3
          have := h1 y uy g1
          simp only [REV_ASSOCD] at this
          rw [if_pos g3] at this
          exact g2 this
        refine Or.inr ⟨?_, _, rfl, has_type.Abs h3, ?_⟩
        · rintro y uy ⟨g1, g2⟩
          have := h1 y uy g2
          simp only [REV_ASSOCD] at this
          rw [if_neg (hd y uy g2 g1)] at this
          exact this
        · intro u uty
          rw [Aux.VFREE_IN_Abs, h4]
          constructor
          · rintro ⟨g1, oty, g2, rfl⟩
            refine ⟨oty, ⟨fun h => ?_, g2⟩, rfl⟩
            obtain ⟨rfl, rfl⟩ := term.Var.inj h
            exact g1 rfl
          · rintro ⟨oty, ⟨g1, g2⟩, rfl⟩
            exact ⟨hd u oty g2 g1, oty, g2, rfl⟩

theorem Aux.INST_CORE_nil {tyin : List (type × type)} {tm : term} (hw : welltyped tm) :
    ∃ (tm' : term), INST_CORE [] tyin tm = Result tm' ∧
      has_type tm' (TYPE_SUBST tyin (typeof tm)) ∧
      (∀ (u : mlstring) (uty : type), VFREE_IN (Var u uty) tm' ↔
        ∃ (oty : type), VFREE_IN (Var u oty) tm ∧ uty = TYPE_SUBST tyin oty) := by
  rcases INST_CORE_HAS_TYPE (sizeof tm) tm [] tyin ⟨hw, rfl, by simp⟩ with
    ⟨y, uy, _, _, k3⟩ | ⟨_, h⟩
  · exact absurd rfl k3
  · exact h

/- HOL4:
Theorem INST_CORE_NIL_IS_RESULT:
   ∀tyin tm. welltyped tm ⇒ IS_RESULT (INST_CORE [] tyin tm) -/
theorem INST_CORE_NIL_IS_RESULT :
    ∀ (tyin : List (type × type)) (tm : term), welltyped tm → IS_RESULT (INST_CORE [] tyin tm) := by
  intro tyin tm hw
  obtain ⟨tm', h, _⟩ := Aux.INST_CORE_nil (tyin := tyin) hw
  rw [h]; trivial

theorem Aux.INST_spec {tyin : List (type × type)} {tm : term} (hw : welltyped tm) :
    INST_CORE [] tyin tm = Result (INST tyin tm) ∧
      has_type (INST tyin tm) (TYPE_SUBST tyin (typeof tm)) ∧
      (∀ (u : mlstring) (uty : type), VFREE_IN (Var u uty) (INST tyin tm) ↔
        ∃ (oty : type), VFREE_IN (Var u oty) tm ∧ uty = TYPE_SUBST tyin oty) := by
  obtain ⟨tm', h1, h2, h3⟩ := Aux.INST_CORE_nil (tyin := tyin) hw
  have : INST tyin tm = tm' := by rw [INST, h1, RESULT_def]
  rw [this]
  exact ⟨h1, h2, h3⟩

/- HOL4:
Theorem INST_HAS_TYPE:
   ∀tm ty tyin ty'. tm has_type ty ∧ ty' = TYPE_SUBST tyin ty ⇒ INST tyin tm has_type ty' -/
theorem INST_HAS_TYPE :
    ∀ (tm : term) (ty : type) (tyin : List (type × type)) (ty' : type),
        has_type tm ty ∧ ty' = TYPE_SUBST tyin ty → has_type (INST tyin tm) ty' := by
  rintro tm ty tyin ty' ⟨h, rfl⟩
  have := (Aux.INST_spec (tyin := tyin) ⟨ty, h⟩).2.1
  rw [WELLTYPED_LEMMA _ _ h] at this
  exact this

/- HOL4:
Theorem INST_WELLTYPED:
   ∀tm tyin.  welltyped tm ⇒ welltyped (INST tyin tm) -/
theorem INST_WELLTYPED :
    ∀ (tm : term) (tyin : List (type × type)), welltyped tm → welltyped (INST tyin tm) := by
  intro tm tyin hw
  exact ⟨_, (Aux.INST_spec hw).2.1⟩

/- HOL4:
Theorem tyvars_ALL_DISTINCT[simp]:
   ∀ty. ALL_DISTINCT (tyvars ty) -/
theorem tyvars_ALL_DISTINCT :
    ∀ (ty : type), ALL_DISTINCT (tyvars ty) := by
  intro ty
  cases ty with
  | Tyvar v => simp [tyvars, ALL_DISTINCT]
  | Tyapp n tys =>
    rw [tyvars]
    induction tys with
    | nil => trivial
    | cons a t ih => exact ALL_DISTINCT_LIST_UNION _ _ ih

/- HOL4:
Theorem tvars_ALL_DISTINCT[simp]:
   ∀tm. ALL_DISTINCT (tvars tm) -/
theorem tvars_ALL_DISTINCT :
    ∀ (tm : term), ALL_DISTINCT (tvars tm) := by
  intro tm
  induction tm with
  | Var x ty => exact tyvars_ALL_DISTINCT ty
  | Const x ty => exact tyvars_ALL_DISTINCT ty
  | Comb a b _ ihb => exact ALL_DISTINCT_LIST_UNION _ _ ihb
  | Abs a b _ ihb => exact ALL_DISTINCT_LIST_UNION _ _ ihb

/- HOL4:
Theorem EQUATION_HAS_TYPE_BOOL:
   ∀s t. (s === t) has_type Bool
          ⇔ welltyped s ∧ welltyped t ∧ (typeof s = typeof t) -/
theorem EQUATION_HAS_TYPE_BOOL :
    ∀ (s t : term), has_type (equation s t) BoolTy
            ↔ welltyped s ∧ welltyped t ∧ typeof s = typeof t := by
  intro s t
  constructor
  · intro h
    cases h with
    | Comb h1 h2 =>
      cases h1 with
      | Comb h3 h4 =>
        have e := WELLTYPED_LEMMA _ _ h3
        simp only [typeof, type.Tyapp.injEq, List.cons.injEq, true_and, and_true] at e
        refine ⟨⟨_, h4⟩, ⟨_, h2⟩, ?_⟩
        rw [WELLTYPED_LEMMA _ _ h2]
        exact e.2
  · rintro ⟨hs, ht, e⟩
    refine has_type.Comb (has_type.Comb has_type.Const ((WELLTYPED s).mp hs)) ?_
    rw [e]
    exact (WELLTYPED t).mp ht

/- HOL4:
Theorem type_ok_TYPE_SUBST:
   ∀s tyin ty.
      type_ok s ty ∧
      EVERY (type_ok s) (MAP FST tyin)
    ⇒ type_ok s (TYPE_SUBST tyin ty) -/
theorem type_ok_TYPE_SUBST :
    ∀ (s : tysig) (tyin : List (type × type)) (ty : type),
        type_ok s ty ∧
        EVERY (type_ok s) (tyin.map Prod.fst)
      → type_ok s (TYPE_SUBST tyin ty) := by
  rintro s tyin ty ⟨h1, h2⟩
  rw [Aux.EVERY_iff] at h2
  induction ty using Aux.type_ind with
  | h1 v =>
    rw [TYPE_SUBST]
    rcases REV_ASSOCD_MEM tyin (Tyvar v) (Tyvar v) with h | h
    · exact h2 _ (List.mem_map.mpr ⟨_, h, rfl⟩)
    · rw [h]; exact h1
  | h2 n tys ih =>
    rw [type_ok, Aux.EVERY_iff] at h1
    rw [TYPE_SUBST, type_ok, Aux.EVERY_iff]
    refine ⟨by rw [List.length_map]; exact h1.1, ?_⟩
    intro x hx
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
    exact ih a ha (h1.2 a ha)

/- HOL4:
Theorem type_ok_TYPE_SUBST_imp:
   ∀s tyin ty. type_ok s (TYPE_SUBST tyin ty) ⇒
                ∀x. MEM x (tyvars ty) ⇒ type_ok s (TYPE_SUBST tyin (Tyvar x)) -/
theorem type_ok_TYPE_SUBST_imp :
    ∀ (s : tysig) (tyin : List (type × type)) (ty : type), type_ok s (TYPE_SUBST tyin ty) →
                  ∀ (x : mlstring), x ∈ tyvars ty → type_ok s (TYPE_SUBST tyin (Tyvar x)) := by
  intro s tyin ty
  induction ty using Aux.type_ind with
  | h1 v =>
    intro h x hx
    simp only [tyvars, List.mem_singleton] at hx
    subst hx; exact h
  | h2 n tys ih =>
    intro h x hx
    rw [TYPE_SUBST, type_ok, Aux.EVERY_iff] at h
    obtain ⟨a, ha, hxa⟩ := (Aux.mem_tyvars_Tyapp x n tys).mp hx
    exact ih a ha (h.2 _ (List.mem_map.mpr ⟨a, ha, rfl⟩)) x hxa

/- HOL4:
Theorem term_ok_welltyped:
   ∀sig t. term_ok sig t ⇒ welltyped t -/
theorem term_ok_welltyped :
    ∀ (sig : sig) (t : term), term_ok sig t → welltyped t := by
  intro sig t
  induction t with
  | Var x ty => intro _; exact Aux.welltyped_Var
  | Const x ty => intro _; exact Aux.welltyped_Const
  | Comb a b _ _ => intro h; exact h.2.2
  | Abs v b _ ihb =>
    rintro ⟨x, ty, rfl, _, h⟩
    exact Aux.welltyped_Abs.mpr ⟨x, ty, rfl, ihb h⟩

theorem Aux.type_ok_Fun_imp {s : tysig} {a b : type} (h : type_ok s (Fun a b)) :
    type_ok s a ∧ type_ok s b := by
  rw [type_ok] at h
  exact ⟨h.2.1, h.2.2.1⟩

theorem Aux.type_ok_Fun {sig : sig} (hs : is_std_sig sig) {a b : type} (h1 : type_ok sig.1 a)
    (h2 : type_ok sig.1 b) : type_ok sig.1 (Fun a b) := by
  rw [type_ok]
  exact ⟨hs.1, h1, h2, trivial⟩

theorem Aux.type_ok_Bool {sig : sig} (hs : is_std_sig sig) : type_ok sig.1 BoolTy := by
  rw [type_ok]
  exact ⟨hs.2.1, trivial⟩

/- HOL4:
Theorem term_ok_type_ok:
   ∀sig t. is_std_sig sig ∧ term_ok sig t
          ⇒ type_ok (FST sig) (typeof t) -/
theorem term_ok_type_ok :
    ∀ (sig : sig) (t : term), is_std_sig sig ∧ term_ok sig t
            → type_ok sig.1 (typeof t) := by
  rintro sig t ⟨hs, ht⟩
  induction t with
  | Var x ty => exact ht
  | Const x ty => obtain ⟨_, _, h, _⟩ := ht; exact h
  | Comb a b iha _ =>
    obtain ⟨h1, _, h3⟩ := ht
    obtain ⟨_, _, rty, e⟩ := Aux.welltyped_Comb.mp h3
    have h4 := iha h1
    rw [e] at h4
    rw [typeof, e]
    exact (Aux.type_ok_Fun_imp h4).2
  | Abs v b _ ihb =>
    obtain ⟨x, ty, rfl, h1, h2⟩ := ht
    exact Aux.type_ok_Fun hs h1 (ihb h2)

/- HOL4:
Theorem term_ok_equation:
   is_std_sig sig ⇒
      (term_ok sig (s === t) ⇔
        term_ok sig s ∧ term_ok sig t ∧
        typeof t = typeof s) -/
theorem term_ok_equation :
    ∀ (sig : sig) (s t : term), is_std_sig sig →
        (term_ok sig (equation s t) ↔
          term_ok sig s ∧ term_ok sig t ∧
          typeof t = typeof s) := by
  intro sig s t hs
  constructor
  · rintro ⟨⟨_, h1, _⟩, h2, h3⟩
    have h4 : has_type (equation s t) BoolTy := by
      have e := (WELLTYPED _).mp h3
      exact e
    exact ⟨h1, h2, ((EQUATION_HAS_TYPE_BOOL s t).mp h4).2.2.symm⟩
  · rintro ⟨h1, h2, e⟩
    have w1 := term_ok_welltyped _ _ h1
    have w2 := term_ok_welltyped _ _ h2
    have hb : has_type (equation s t) BoolTy := (EQUATION_HAS_TYPE_BOOL s t).mpr ⟨w1, w2, e.symm⟩
    have hty := term_ok_type_ok sig s ⟨hs, h1⟩
    refine ⟨⟨⟨_, hs.2.2, ?_, [(typeof s, Tyvar (mls "A"))], ?_⟩, h1, ?_⟩, h2, ⟨_, hb⟩⟩
    · exact Aux.type_ok_Fun hs hty (Aux.type_ok_Fun hs hty (Aux.type_ok_Bool hs))
    · rw [Aux.TYPE_SUBST_Fun, Aux.TYPE_SUBST_Fun, TYPE_SUBST_Bool, TYPE_SUBST]
      simp [REV_ASSOCD]
    · exact ⟨_, has_type.Comb has_type.Const ((WELLTYPED s).mp w1)⟩

/- HOL4:
Theorem term_ok_VSUBST:
   ∀sig tm ilist.
    term_ok sig tm ∧
    (∀s s'. MEM (s',s) ilist ⇒ ∃x ty. s = Var x ty ∧ s' has_type ty ∧ term_ok sig s')
    ⇒
    term_ok sig (VSUBST ilist tm) -/
theorem term_ok_VSUBST :
    ∀ (sig : sig) (tm : term) (ilist : List (term × term)),
      term_ok sig tm ∧
      (∀ (s s' : term), (s', s) ∈ ilist → ∃ (x : mlstring) (ty : type), s = Var x ty ∧ has_type s' ty ∧ term_ok sig s')
      →
      term_ok sig (VSUBST ilist tm) := by
  intro sig tm
  induction tm with
  | Var x ty =>
    rintro ilist ⟨h, hi⟩
    simp only [VSUBST]
    rcases REV_ASSOCD_MEM ilist (Var x ty) (Var x ty) with hm | hm
    · obtain ⟨_, _, _, _, h'⟩ := hi _ _ hm
      exact h'
    · rw [hm]; exact h
  | Const x ty =>
    rintro ilist ⟨h, hi⟩
    exact h
  | Comb a b iha ihb =>
    rintro ilist ⟨h, hi⟩
    refine ⟨iha ilist ⟨h.1, hi⟩, ihb ilist ⟨h.2.1, hi⟩, ?_⟩
    exact VSUBST_WELLTYPED (Comb a b) (Tyvar default) ilist ⟨h.2.2, fun s s' hm => by
      obtain ⟨x, ty, h1, h2, _⟩ := hi s s' hm
      exact ⟨x, ty, h1, h2⟩⟩
  | Abs v b _ ihb =>
    rintro ilist ⟨⟨x, ty, rfl, h1, h2⟩, hi⟩
    rw [Aux.VSUBST_Abs]
    have hf : ∀ s s', (s', s) ∈ FILTER (fun p => ¬ (p.2 = Var x ty)) ilist →
        ∃ x ty, s = Var x ty ∧ has_type s' ty ∧ term_ok sig s' :=
      fun s s' hm => hi s s' (Aux.mem_FILTER_imp _ _ _ hm)
    split
    · refine ⟨_, ty, rfl, h1, ihb _ ⟨h2, fun s s' hm => ?_⟩⟩
      rcases List.mem_cons.mp hm with hm | hm
      · cases hm; exact ⟨x, ty, rfl, has_type.Var, h1⟩
      · exact hf s s' hm
    · exact ⟨x, ty, rfl, h1, ihb _ ⟨h2, hf⟩⟩

theorem Aux.term_ok_INST_CORE (sig : sig) (tyin : List (type × type))
    (ht : EVERY (type_ok sig.1) (tyin.map Prod.fst)) (n : Nat) :
    ∀ (env : List (term × term)) (tm r : term), sizeof tm = n → term_ok sig tm →
      (∀ (s s' : term), (s, s') ∈ env →
        ∃ (x : mlstring) (ty : type), s = Var x ty ∧ s' = Var x (TYPE_SUBST tyin ty)) →
      INST_CORE env tyin tm = Result r → term_ok sig r := by
  induction n using Nat.strongRecOn with
  | ind n IH =>
    intro env tm r hn hok he hr
    cases tm with
    | Var x ty =>
      rw [Aux.INST_CORE_Var] at hr
      split at hr
      · cases hr; exact type_ok_TYPE_SUBST _ _ _ ⟨hok, ht⟩
      · cases hr
    | Const x ty =>
      rw [Aux.INST_CORE_Const] at hr
      cases hr
      obtain ⟨ty0, h1, h2, i, rfl⟩ := hok
      exact ⟨ty0, h1, type_ok_TYPE_SUBST _ _ _ ⟨h2, ht⟩, _, TYPE_SUBST_compose _ _ _⟩
    | Comb s t =>
      simp only [sizeof] at hn
      have hw := hok.2.2
      rcases INST_CORE_HAS_TYPE _ (Comb s t) env tyin ⟨hw, rfl, he⟩ with
        ⟨_, _, h, _⟩ | ⟨_, r', h, h', _⟩
      · rw [hr] at h; cases h
      · rw [hr] at h
        cases h
        obtain ⟨s', t', hs, ht', rfl⟩ := Aux.INST_CORE_Comb_Result hr
        exact ⟨IH (sizeof s) (by omega) env s s' rfl hok.1 he hs,
          IH (sizeof t) (by omega) env t t' rfl hok.2.1 he ht', _, h'⟩
    | Abs v b =>
      simp only [sizeof] at hn
      obtain ⟨x, ty, rfl, h1, h2⟩ := hok
      rcases Aux.INST_CORE_Abs_Result hr with ⟨b', hb, rfl⟩ | ⟨x', b', _, hb, rfl⟩
      · refine ⟨x, _, rfl, type_ok_TYPE_SUBST _ _ _ ⟨h1, ht⟩,
          IH (sizeof b) (by omega) _ b b' rfl h2 ?_ hb⟩
        intro s s' hm
        rcases List.mem_cons.mp hm with hm | hm
        · cases hm; exact ⟨x, ty, rfl, rfl⟩
        · exact he s s' hm
      · refine ⟨x', _, rfl, type_ok_TYPE_SUBST _ _ _ ⟨h1, ht⟩,
          IH (sizeof b) (by omega) _ _ b' (SIZEOF_VSUBST b _ (Aux.single_subst_ok' x x' ty)) ?_ ?_ hb⟩
        · refine term_ok_VSUBST sig b _ ⟨h2, fun s s' hm => ?_⟩
          cases List.mem_singleton.mp hm
          exact ⟨x, ty, rfl, has_type.Var, h1⟩
        · intro s s' hm
          rcases List.mem_cons.mp hm with hm | hm
          · cases hm; exact ⟨x', ty, rfl, rfl⟩
          · exact he s s' hm

/- HOL4:
Theorem term_ok_INST_CORE:
   ∀sig env tyin tm.
      term_ok sig tm ∧
      EVERY (type_ok (FST sig)) (MAP FST tyin) ∧
      (∀s s'. MEM (s,s') env ⇒ ∃x ty. s = Var x ty ∧ s' = Var x (TYPE_SUBST tyin ty)) ∧
      IS_RESULT (INST_CORE env tyin tm)
      ⇒
      term_ok sig (RESULT (INST_CORE env tyin tm)) -/
theorem term_ok_INST_CORE :
    ∀ (sig : sig) (env : List (term × term)) (tyin : List (type × type)) (tm : term),
        term_ok sig tm ∧
        EVERY (type_ok sig.1) (tyin.map Prod.fst) ∧
        (∀ (s s' : term), (s, s') ∈ env → ∃ (x : mlstring) (ty : type), s = Var x ty ∧ s' = Var x (TYPE_SUBST tyin ty)) ∧
        IS_RESULT (INST_CORE env tyin tm)
        →
        term_ok sig (RESULT (INST_CORE env tyin tm)) := by
  rintro sig env tyin tm ⟨h1, h2, h3, h4⟩
  cases h : INST_CORE env tyin tm with
  | Clash c => rw [h] at h4; exact h4.elim
  | Result r =>
    rw [RESULT_def]
    exact Aux.term_ok_INST_CORE sig tyin h2 _ env tm r rfl h1 h3 h

/- HOL4:
Theorem term_ok_INST:
   ∀sig tyin tm.
    term_ok sig tm ∧
    EVERY (type_ok (FST sig)) (MAP FST tyin) ⇒
    term_ok sig (INST tyin tm) -/
theorem term_ok_INST :
    ∀ (sig : sig) (tyin : List (type × type)) (tm : term),
      term_ok sig tm ∧
      EVERY (type_ok sig.1) (tyin.map Prod.fst) →
      term_ok sig (INST tyin tm) := by
  rintro sig tyin tm ⟨h1, h2⟩
  exact Aux.term_ok_INST_CORE sig tyin h2 _ [] tm _ rfl h1 (by simp)
    (Aux.INST_spec (term_ok_welltyped _ _ h1)).1

/- HOL4:
Theorem term_ok_raconv:
   ∀env tp. RACONV env tp ⇒
      ∀sig.
      EVERY (λ(s,s'). welltyped s ∧ welltyped s' ∧ typeof s = typeof s' ∧ type_ok (FST sig) (typeof s)) env ⇒
      term_ok sig (FST tp) ∧ welltyped (SND tp) ⇒ term_ok sig (SND tp) -/
theorem term_ok_raconv :
    ∀ (env : List (term × term)) (tp : term × term), RACONV env tp →
        ∀ (sig : sig),
        EVERY (fun (p : term × term) => welltyped p.1 ∧ welltyped p.2 ∧ typeof p.1 = typeof p.2 ∧
          type_ok sig.1 (typeof p.1)) env →
        term_ok sig tp.1 ∧ welltyped tp.2 → term_ok sig tp.2 := by
  intro env tp h sig
  induction h with
  | Var ha =>
    rintro he ⟨h1, _⟩
    rcases ALPHAVARS_MEM _ _ ha with hm | hm
    · obtain ⟨_, _, e, h'⟩ := (Aux.EVERY_iff _ _).mp he _ hm
      simp only at e h'
      rw [e] at h'
      exact h'
    · have hm' : Var _ _ = Var _ _ := hm
      rw [← hm']; exact h1
  | Const => rintro _ ⟨h1, _⟩; exact h1
  | Comb _ _ ih1 ih2 =>
    rintro he ⟨h1, h2⟩
    obtain ⟨w1, w2, _⟩ := Aux.welltyped_Comb.mp h2
    exact ⟨ih1 he ⟨h1.1, w1⟩, ih2 he ⟨h1.2.1, w2⟩, h2⟩
  | Abs e _ ih =>
    rintro he ⟨⟨x, ty, rfl, h1, h3⟩, h2⟩
    obtain ⟨y, uy, rfl, w2⟩ := Aux.welltyped_Abs.mp h2
    have e' : ty = uy := e
    subst e'
    exact ⟨y, ty, rfl, h1, ih ⟨⟨Aux.welltyped_Var, Aux.welltyped_Var, rfl, h1⟩, he⟩ ⟨h3, w2⟩⟩

/- HOL4:
Theorem term_ok_aconv:
   ∀sig t1 t2. ACONV t1 t2 ∧ term_ok sig t1 ∧ welltyped t2 ⇒ term_ok sig t2 -/
theorem term_ok_aconv :
    ∀ (sig : sig) (t1 t2 : term), ACONV t1 t2 ∧ term_ok sig t1 ∧ welltyped t2 → term_ok sig t2 := by
  rintro sig t1 t2 ⟨h, h1, h2⟩
  exact term_ok_raconv [] (t1, t2) h sig trivial ⟨h1, h2⟩

/- HOL4:
Theorem bind_not_free:
   ∀t n v. ¬dbVFREE_IN (UNCURRY dbVar v) t ⇒ bind v n t = t -/
theorem bind_not_free :
    ∀ (t : dbterm_t) (n : Nat) (v : mlstring × type), ¬ dbVFREE_IN (UNCURRY dbVar v) t → bind v n t = t := by
  intro t
  induction t with
  | dbVar x ty =>
    rintro n ⟨a, b⟩ h
    simp only [bind]
    rw [if_neg]
    intro e
    cases e
    exact h rfl
  | dbBound m => intro n v _; rfl
  | dbConst x ty => intro n v _; rfl
  | dbComb a b iha ihb =>
    intro n v h
    simp only [dbVFREE_IN, not_or] at h
    simp only [bind, iha n v h.1, ihb n v h.2]
  | dbAbs ty b ihb =>
    intro n v h
    simp only [bind, ihb (n + 1) v h]

/- HOL4:
Theorem bind_dbVSUBST:
   ∀tm v n ls.
    (UNCURRY dbVar v) ∉ set (MAP SND ls) ∧
    (∀k. dbVFREE_IN k tm ∧ MEM k (MAP SND ls) ⇒
        ¬dbVFREE_IN (UNCURRY dbVar v) (REV_ASSOCD k ls k))
    ⇒
    bind v n (dbVSUBST ls tm) = dbVSUBST ls (bind v n tm) -/
theorem bind_dbVSUBST :
    ∀ (tm : dbterm_t) (v : mlstring × type) (n : Nat) (ls : List (dbterm_t × dbterm_t)),
      UNCURRY dbVar v ∉ LIST_TO_SET (ls.map Prod.snd) ∧
      (∀ (k : dbterm_t), dbVFREE_IN k tm ∧ k ∈ ls.map Prod.snd →
          ¬ dbVFREE_IN (UNCURRY dbVar v) (REV_ASSOCD k ls k))
      →
      bind v n (dbVSUBST ls tm) = dbVSUBST ls (bind v n tm) := by
  intro tm
  induction tm with
  | dbVar x ty =>
    rintro ⟨a, b⟩ n ls ⟨h1, h2⟩
    rw [Aux.mem_LIST_TO_SET] at h1
    simp only [bind, dbVSUBST]
    by_cases e : (a, b) = (x, ty)
    · cases e
      rw [if_pos rfl, Aux.REV_ASSOCD_not_mem _ _ _ h1]
      simp [bind, dbVSUBST]
    · rw [if_neg e]
      simp only [dbVSUBST]
      apply bind_not_free
      by_cases hm : dbVar x ty ∈ ls.map Prod.snd
      · exact h2 _ ⟨rfl, hm⟩
      · rw [Aux.REV_ASSOCD_not_mem _ _ _ hm]
        intro h
        simp only [dbVFREE_IN, UNCURRY, dbterm_t.dbVar.injEq] at h
        exact e (by rw [h.1, h.2])
  | dbBound m => intro n v _ _; rfl
  | dbConst x ty => intro n v _ _; rfl
  | dbComb s t ihs iht =>
    rintro v n ls ⟨h1, h2⟩
    simp only [bind, dbVSUBST]
    rw [ihs v n ls ⟨h1, fun k hk => h2 k ⟨Or.inl hk.1, hk.2⟩⟩,
      iht v n ls ⟨h1, fun k hk => h2 k ⟨Or.inr hk.1, hk.2⟩⟩]
  | dbAbs ty b ihb =>
    rintro v n ls h
    simp only [bind, dbVSUBST]
    rw [ihb v (n + 1) ls h]

/- HOL4:
Theorem bind_dbVSUBST_cons:
   ∀tm z x n ls.
    ¬dbVFREE_IN (UNCURRY dbVar z) (dbVSUBST ls (bind x n tm))
    ⇒
    bind z n (dbVSUBST ((UNCURRY dbVar z,UNCURRY dbVar x)::ls) tm) = dbVSUBST ls (bind x n tm) -/
theorem bind_dbVSUBST_cons :
    ∀ (tm : dbterm_t) (z x : mlstring × type) (n : Nat) (ls : List (dbterm_t × dbterm_t)),
      ¬ dbVFREE_IN (UNCURRY dbVar z) (dbVSUBST ls (bind x n tm))
      →
      bind z n (dbVSUBST ((UNCURRY dbVar z, UNCURRY dbVar x) :: ls) tm) = dbVSUBST ls (bind x n tm) := by
  intro tm
  induction tm with
  | dbVar a ty =>
    rintro ⟨z1, z2⟩ ⟨x1, x2⟩ n ls h
    simp only [bind, dbVSUBST, REV_ASSOCD, UNCURRY, dbterm_t.dbVar.injEq, Prod.mk.injEq] at h ⊢
    by_cases e : x1 = a ∧ x2 = ty
    · rw [if_pos e, if_pos e]
      simp [bind, dbVSUBST]
    · rw [if_neg e] at h
      rw [if_neg e, if_neg e]
      simp only [dbVSUBST] at h ⊢
      exact bind_not_free _ n (z1, z2) h
  | dbBound m => intro z x n ls _; rfl
  | dbConst a ty => intro z x n ls _; rfl
  | dbComb s t ihs iht =>
    intro z x n ls h
    simp only [bind, dbVSUBST, dbVFREE_IN, not_or] at h ⊢
    rw [ihs z x n ls h.1, iht z x n ls h.2]
  | dbAbs ty b ihb =>
    intro z x n ls h
    simp only [bind, dbVSUBST, dbVFREE_IN] at h ⊢
    rw [ihb z x (n + 1) ls h]

/- HOL4:
Theorem dbVSUBST_frees:
   ∀tm ls ls'.
    (∀k. dbVFREE_IN k tm ⇒ REV_ASSOCD k ls k = REV_ASSOCD k ls' k)
     ⇒
      dbVSUBST ls tm = dbVSUBST ls' tm -/
theorem dbVSUBST_frees :
    ∀ (tm : dbterm_t) (ls ls' : List (dbterm_t × dbterm_t)),
      (∀ (k : dbterm_t), dbVFREE_IN k tm → REV_ASSOCD k ls k = REV_ASSOCD k ls' k)
       →
        dbVSUBST ls tm = dbVSUBST ls' tm := by
  intro tm ls ls'
  induction tm with
  | dbVar x ty => intro h; exact h _ rfl
  | dbBound m => intro _; rfl
  | dbConst x ty => intro _; rfl
  | dbComb s t ihs iht =>
    intro h
    simp only [dbVSUBST]
    rw [ihs (fun k hk => h k (Or.inl hk)), iht (fun k hk => h k (Or.inr hk))]
  | dbAbs ty b ihb =>
    intro h
    simp only [dbVSUBST]
    rw [ihb h]

theorem Aux.dbVFREE_IN_bind (tm x : dbterm_t) (v : mlstring × type) :
    ∀ n, dbVFREE_IN x (bind v n tm) ↔ x ≠ UNCURRY dbVar v ∧ dbVFREE_IN x tm := by
  obtain ⟨a, b⟩ := v
  induction tm with
  | dbVar y ty =>
    intro n
    simp only [bind]
    by_cases e : (a, b) = (y, ty)
    · rw [if_pos e]
      cases e
      simp only [dbVFREE_IN, UNCURRY]
      constructor
      · intro h; exact h.elim
      · rintro ⟨h1, h2⟩; exact h1 h2.symm
    · rw [if_neg e]
      simp only [dbVFREE_IN, UNCURRY]
      constructor
      · rintro rfl
        refine ⟨fun h => e ?_, rfl⟩
        rw [dbterm_t.dbVar.injEq] at h
        rw [h.1, h.2]
      · exact fun h => h.2
  | dbBound m => intro n; simp [bind, dbVFREE_IN]
  | dbConst y ty =>
    intro n
    simp only [bind, dbVFREE_IN, UNCURRY]
    constructor
    · rintro rfl; exact ⟨by simp, rfl⟩
    · exact fun h => h.2
  | dbComb s t ihs iht =>
    intro n
    simp only [bind, dbVFREE_IN, ihs, iht]
    grind
  | dbAbs ty b ihb =>
    intro n
    simp only [bind, dbVFREE_IN, ihb]

/- HOL4:
Theorem dbVFREE_IN_bind:
   ∀tm x v n b. dbVFREE_IN x (bind v n tm) ⇔ (x ≠ UNCURRY dbVar v) ∧ dbVFREE_IN x tm -/
theorem dbVFREE_IN_bind {α : Type u} :
    ∀ (tm x : dbterm_t) (v : mlstring × type) (n : Nat) (b : α),
        dbVFREE_IN x (bind v n tm) ↔ x ≠ UNCURRY dbVar v ∧ dbVFREE_IN x tm := by
  intro tm x v n _
  exact Aux.dbVFREE_IN_bind tm x v n

theorem Aux.db_eq_dbVar (x : term) (y : mlstring) (ty : type) : dbVar y ty = db x ↔ Var y ty = x := by
  cases x <;> simp [db]

theorem Aux.db_eq_dbConst (x : term) (y : mlstring) (ty : type) :
    dbConst y ty = db x ↔ Const y ty = x := by
  cases x <;> simp [db]

/- HOL4:
Theorem dbVFREE_IN_VFREE_IN:
   ∀tm x. welltyped tm ⇒ (dbVFREE_IN (db x) (db tm) ⇔ VFREE_IN x tm) -/
theorem dbVFREE_IN_VFREE_IN :
    ∀ (tm x : term), welltyped tm → (dbVFREE_IN (db x) (db tm) ↔ VFREE_IN x tm) := by
  intro tm x
  induction tm with
  | Var y ty => intro _; exact Aux.db_eq_dbVar x y ty
  | Const y ty => intro _; exact Aux.db_eq_dbConst x y ty
  | Comb a b iha ihb =>
    intro hw
    obtain ⟨wa, wb, _⟩ := Aux.welltyped_Comb.mp hw
    simp only [db, dbVFREE_IN, VFREE_IN, iha wa, ihb wb]
  | Abs v b _ ihb =>
    intro hw
    obtain ⟨y, ty, rfl, wb⟩ := Aux.welltyped_Abs.mp hw
    simp only [db, dbVFREE_IN, VFREE_IN, dest_var_def, Aux.dbVFREE_IN_bind, ihb wb, UNCURRY]
    rw [ne_eq, eq_comm, Aux.db_eq_dbVar]

/- HOL4:
Theorem MAP_db_FILTER_neq:
   ∀ls z ty. MAP (λ(x,y). (db x, db y)) (FILTER (λ(x,y). y ≠ Var z ty) ls) = FILTER (λ(x,y). y ≠ dbVar z ty) (MAP (λ(x,y). (db x, db y)) ls) -/
theorem MAP_db_FILTER_neq :
    ∀ (ls : List (term × term)) (z : mlstring) (ty : type),
        (FILTER (fun (p : term × term) => p.2 ≠ Var z ty) ls).map (fun (p : term × term) => (db p.1, db p.2)) =
        FILTER (fun (p : dbterm_t × dbterm_t) => p.2 ≠ dbVar z ty) (ls.map (fun (p : term × term) => (db p.1, db p.2))) := by
  intro ls z ty
  induction ls with
  | nil => rfl
  | cons p t ih =>
    obtain ⟨a, b⟩ := p
    simp only [FILTER, List.map_cons]
    have e : db b = dbVar z ty ↔ b = Var z ty := by
      rw [eq_comm, Aux.db_eq_dbVar, eq_comm]
    by_cases h : b = Var z ty
    · have h' := e.mpr h
      rw [if_neg (fun hh => hh h), if_neg (fun hh => hh h'), ih]
    · have h' : ¬ db b = dbVar z ty := fun hh => h (e.mp hh)
      rw [if_pos h, if_pos h', List.map_cons, ih]

/- HOL4:
Theorem REV_ASSOCD_MAP_db:
   ∀ls k ky.
    (∀k v. MEM (v,k) ls ⇒ ∃x ty. k = Var x ty)
    ⇒
    REV_ASSOCD (dbVar k ky) (MAP (λ(x,y). (db x, db y)) ls) (dbVar k ky) = db (REV_ASSOCD (Var k ky) ls (Var k ky)) -/
theorem REV_ASSOCD_MAP_db :
    ∀ (ls : List (term × term)) (k : mlstring) (ky : type),
      (∀ (k v : term), (v, k) ∈ ls → ∃ (x : mlstring) (ty : type), k = Var x ty)
      →
      REV_ASSOCD (dbVar k ky) (ls.map (fun (p : term × term) => (db p.1, db p.2))) (dbVar k ky) =
        db (REV_ASSOCD (Var k ky) ls (Var k ky)) := by
  intro ls k ky _
  induction ls with
  | nil => rfl
  | cons p t ih =>
    obtain ⟨a, b⟩ := p
    simp only [REV_ASSOCD, List.map_cons]
    have e : db b = dbVar k ky ↔ b = Var k ky := by
      rw [eq_comm, Aux.db_eq_dbVar, eq_comm]
    by_cases h : b = Var k ky
    · rw [if_pos h, if_pos (e.mpr h)]
    · rw [if_neg h, if_neg (fun hh => h (e.mp hh))]
      apply ih
      rename_i hh
      exact fun k v hm => hh k v (List.mem_cons_of_mem _ hm)

/- HOL4:
Theorem dbVFREE_IN_dbVSUBST:
   ∀tm u uty ilist.
      dbVFREE_IN (dbVar u uty) (dbVSUBST ilist tm) ⇔
      ∃y ty. dbVFREE_IN (dbVar y ty) tm ∧
             dbVFREE_IN (dbVar u uty)
               (REV_ASSOCD (dbVar y ty) ilist (dbVar y ty)) -/
theorem dbVFREE_IN_dbVSUBST :
    ∀ (tm : dbterm_t) (u : mlstring) (uty : type) (ilist : List (dbterm_t × dbterm_t)),
        dbVFREE_IN (dbVar u uty) (dbVSUBST ilist tm) ↔
        ∃ (y : mlstring) (ty : type), dbVFREE_IN (dbVar y ty) tm ∧
               dbVFREE_IN (dbVar u uty)
                 (REV_ASSOCD (dbVar y ty) ilist (dbVar y ty)) := by
  intro tm u uty ilist
  induction tm with
  | dbVar x ty =>
    constructor
    · intro h; exact ⟨x, ty, rfl, h⟩
    · rintro ⟨y, t, h1, h2⟩
      have h1' : dbVar x ty = dbVar y t := h1
      show dbVFREE_IN (dbVar u uty) (REV_ASSOCD (dbVar x ty) ilist (dbVar x ty))
      rw [h1']; exact h2
  | dbBound m => simp [dbVSUBST, dbVFREE_IN]
  | dbConst x ty => simp [dbVSUBST, dbVFREE_IN]
  | dbComb s t ihs iht =>
    simp only [dbVSUBST, dbVFREE_IN, ihs, iht]
    constructor
    · rintro (⟨y, ty, h1, h2⟩ | ⟨y, ty, h1, h2⟩)
      · exact ⟨y, ty, Or.inl h1, h2⟩
      · exact ⟨y, ty, Or.inr h1, h2⟩
    · rintro ⟨y, ty, h1 | h1, h2⟩
      · exact Or.inl ⟨y, ty, h1, h2⟩
      · exact Or.inr ⟨y, ty, h1, h2⟩
  | dbAbs ty b ihb =>
    simp only [dbVSUBST, dbVFREE_IN, ihb]

/- HOL4:
Theorem VSUBST_dbVSUBST:
   ∀tm ilist.
    welltyped tm ∧
    (∀k v. MEM (v,k) ilist ⇒ welltyped v ∧ ∃x ty. k = Var x ty)
    ⇒
    db (VSUBST ilist tm) = dbVSUBST (MAP (λ(x,y). (db x, db y)) ilist) (db tm) -/
theorem VSUBST_dbVSUBST :
    ∀ (tm : term) (ilist : List (term × term)),
      welltyped tm ∧
      (∀ (k v : term), (v, k) ∈ ilist → welltyped v ∧ ∃ (x : mlstring) (ty : type), k = Var x ty)
      →
      db (VSUBST ilist tm) = dbVSUBST (ilist.map (fun (p : term × term) => (db p.1, db p.2))) (db tm) := by
  intro tm
  induction tm with
  | Var x ty =>
    rintro ilist ⟨_, hi⟩
    simp only [VSUBST, db, dbVSUBST]
    exact (REV_ASSOCD_MAP_db ilist x ty (fun k v hm => (hi k v hm).2)).symm
  | Const x ty => rintro ilist _; rfl
  | Comb a b iha ihb =>
    rintro ilist ⟨hw, hi⟩
    obtain ⟨wa, wb, _⟩ := Aux.welltyped_Comb.mp hw
    simp only [VSUBST, db, dbVSUBST]
    rw [iha ilist ⟨wa, hi⟩, ihb ilist ⟨wb, hi⟩]
  | Abs v b _ ihb =>
    rintro ilist ⟨hw, hi⟩
    obtain ⟨x, ty, rfl, wb⟩ := Aux.welltyped_Abs.mp hw
    have hf : ∀ (k v : term), (v, k) ∈ FILTER (fun p => ¬ (p.2 = Var x ty)) ilist →
        welltyped v ∧ ∃ (x : mlstring) (ty : type), k = Var x ty :=
      fun k v hm => hi k v (Aux.mem_FILTER_imp _ _ _ hm)
    have hL : (FILTER (fun (p : term × term) => ¬ (p.2 = Var x ty)) ilist).map
        (fun (p : term × term) => (db p.1, db p.2)) =
        FILTER (fun (p : dbterm_t × dbterm_t) => ¬ (p.2 = dbVar x ty))
          (ilist.map (fun (p : term × term) => (db p.1, db p.2))) := MAP_db_FILTER_neq ilist x ty
    -- replacing the filtered list by the full list below the binder
    have hS : dbVSUBST ((FILTER (fun (p : term × term) => ¬ (p.2 = Var x ty)) ilist).map
        (fun (p : term × term) => (db p.1, db p.2))) (bind (x, ty) 0 (db b)) =
        dbVSUBST (ilist.map (fun (p : term × term) => (db p.1, db p.2))) (bind (x, ty) 0 (db b)) := by
      apply dbVSUBST_frees
      intro k hk
      rw [Aux.dbVFREE_IN_bind] at hk
      rw [hL, Aux.REV_ASSOCD_FILTER' (fun s => ¬ s = dbVar x ty), if_pos hk.1]
    rw [Aux.VSUBST_Abs]
    split
    · have hv := VARIANT_THM (VSUBST (FILTER (fun p => ¬ (p.2 = Var x ty)) ilist) b) (explode x) ty
      generalize VARIANT (VSUBST (FILTER (fun p => ¬ (p.2 = Var x ty)) ilist) b) (explode x) ty = z at hv ⊢
      simp only [db, dbVSUBST, dest_var_def, typeof]
      congr 1
      rw [ihb _ ⟨wb, ?_⟩]
      · rw [List.map_cons, ← hS]
        apply bind_dbVSUBST_cons (db b) (z, ty) (x, ty) 0
        intro hfree
        rw [dbVFREE_IN_dbVSUBST] at hfree
        obtain ⟨y, t, g1, g2⟩ := hfree
        rw [Aux.dbVFREE_IN_bind] at g1
        have g3 : VFREE_IN (Var y t) b := (dbVFREE_IN_VFREE_IN b (Var y t) wb).mp g1.2
        rw [REV_ASSOCD_MAP_db _ y t (fun k v hm => (hf k v hm).2)] at g2
        apply hv
        rw [VFREE_IN_VSUBST b z ty _ wb]
        refine ⟨y, t, g3, (dbVFREE_IN_VFREE_IN _ (Var z ty) ?_).mp g2⟩
        rcases REV_ASSOCD_MEM (FILTER (fun p => ¬ (p.2 = Var x ty)) ilist) (Var y t) (Var y t) with hm | hm
        · exact (hf _ _ hm).1
        · rw [hm]; exact Aux.welltyped_Var
      · intro k v hm
        rcases List.mem_cons.mp hm with hm | hm
        · cases hm; exact ⟨Aux.welltyped_Var, x, ty, rfl⟩
        · exact hf k v hm
    · next hne =>
      simp only [db, dbVSUBST, dest_var_def, typeof]
      congr 1
      rw [ihb _ ⟨wb, hf⟩, ← hS]
      apply bind_dbVSUBST
      constructor
      · rw [Aux.mem_LIST_TO_SET]
        intro hm
        obtain ⟨p, hp, e⟩ := List.mem_map.mp hm
        rw [hL, Aux.mem_FILTER] at hp
        exact hp.2 e
      · rintro k ⟨hk, hm⟩ hfree
        obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hm
        obtain ⟨⟨v, w⟩, hq, rfl⟩ := List.mem_map.mp hp
        obtain ⟨_, y, t, rfl⟩ := hf w v hq
        have g3 : VFREE_IN (Var y t) b := (dbVFREE_IN_VFREE_IN b (Var y t) wb).mp hk
        have hne2 := ((Aux.mem_FILTER _ _ _).mp hq).2
        have e := REV_ASSOCD_MAP_db _ y t (fun k v hm => (hf k v hm).2)
        simp only [db] at hfree
        rw [e] at hfree
        rcases REV_ASSOCD_MEM (FILTER (fun p => ¬ (p.2 = Var x ty)) ilist) (Var y t) (Var y t) with hm | hm
        · apply hne
          rw [Aux.EXISTS_iff]
          exact ⟨_, hm, (dbVFREE_IN_VFREE_IN _ (Var x ty) (hf _ _ hm).1).mp hfree, g3⟩
        · rw [hm] at hfree
          have g4 : dbVar y t = dbVar x ty := hfree
          rw [dbterm_t.dbVar.injEq] at g4
          exact hne2 (by rw [g4.1, g4.2])

/- HOL4:
Theorem dbINST_bind:
   ∀tm v n ls.
      (∀ty. dbVFREE_IN (dbVar (FST v) ty) tm ∧ (TYPE_SUBST ls ty = TYPE_SUBST ls (SND v)) ⇒ ty = SND v)
      ⇒ dbINST ls (bind v n tm) = bind (FST v,TYPE_SUBST ls (SND v)) n (dbINST ls tm) -/
theorem dbINST_bind :
    ∀ (tm : dbterm_t) (v : mlstring × type) (n : Nat) (ls : List (type × type)),
        (∀ (ty : type), dbVFREE_IN (dbVar v.1 ty) tm ∧ TYPE_SUBST ls ty = TYPE_SUBST ls v.2 → ty = v.2)
        → dbINST ls (bind v n tm) = bind (v.1, TYPE_SUBST ls v.2) n (dbINST ls tm) := by
  intro tm
  induction tm with
  | dbVar x t =>
    rintro ⟨a, ty⟩ n ls h
    simp only [bind, dbINST] at h ⊢
    by_cases e : (a, ty) = (x, t)
    · cases e
      rw [if_pos rfl, if_pos rfl]; rfl
    · rw [if_neg e, if_neg]
      · rfl
      · intro e2
        rw [Prod.mk.injEq] at e2
        obtain ⟨rfl, e2⟩ := e2
        exact e (by rw [h t ⟨rfl, e2.symm⟩])
  | dbBound m => intro v n ls _; rfl
  | dbConst x t => intro v n ls _; rfl
  | dbComb s t ihs iht =>
    intro v n ls h
    simp only [bind, dbINST]
    rw [ihs v n ls (fun ty hh => h ty ⟨Or.inl hh.1, hh.2⟩),
      iht v n ls (fun ty hh => h ty ⟨Or.inr hh.1, hh.2⟩)]
  | dbAbs t b ihb =>
    intro v n ls h
    simp only [bind, dbINST]
    rw [ihb v (n + 1) ls h]

/- HOL4:
Theorem dbVSUBST_nil[simp]:
   ∀tm. dbVSUBST [] tm = tm -/
theorem dbVSUBST_nil :
    ∀ (tm : dbterm_t), dbVSUBST [] tm = tm := by
  intro tm
  induction tm with
  | dbVar x ty => rfl
  | dbBound m => rfl
  | dbConst x ty => rfl
  | dbComb s t ihs iht => simp only [dbVSUBST, ihs, iht]
  | dbAbs ty b ihb => simp only [dbVSUBST, ihb]

theorem Aux.INST_CORE_dbINST_bind {tyin : List (type × type)} {env : List (term × term)} {x : mlstring}
    {ty : type} {b b' : term} (wb : welltyped b)
    (he : ∀ (s s' : term), (s, s') ∈ env →
      ∃ (x : mlstring) (ty : type), s = Var x ty ∧ s' = Var x (TYPE_SUBST tyin ty))
    (hb : INST_CORE ((Var x ty, Var x (TYPE_SUBST tyin ty)) :: env) tyin b = Result b') :
    dbINST tyin (bind (x, ty) 0 (db b)) = bind (x, TYPE_SUBST tyin ty) 0 (dbINST tyin (db b)) := by
  refine dbINST_bind (db b) (x, ty) 0 tyin ?_
  rintro t ⟨h1, h2⟩
  have h1' : VFREE_IN (Var x t) b := (dbVFREE_IN_VFREE_IN b (Var x t) wb).mp h1
  have hc : ∀ (s s' : term), (s, s') ∈ (Var x ty, Var x (TYPE_SUBST tyin ty)) :: env →
      ∃ (x : mlstring) (ty : type), s = Var x ty ∧ s' = Var x (TYPE_SUBST tyin ty) := by
    intro s s' hm
    rcases List.mem_cons.mp hm with hm | hm
    · cases hm; exact ⟨x, ty, rfl, rfl⟩
    · exact he s s' hm
  rcases INST_CORE_HAS_TYPE _ b _ tyin ⟨wb, rfl, hc⟩ with ⟨_, _, h, _⟩ | ⟨h, _⟩
  · rw [hb] at h; cases h
  · have h3 := h x t h1'
    simp only at h2
    simp only [REV_ASSOCD, h2, if_true] at h3
    exact (term.Var.inj h3).2.symm

theorem Aux.INST_CORE_dbINST (tyin : List (type × type)) (n : Nat) :
    ∀ (tm : term) (env : List (term × term)) (tmi : term), sizeof tm = n → welltyped tm →
      (∀ (s s' : term), (s, s') ∈ env →
        ∃ (x : mlstring) (ty : type), s = Var x ty ∧ s' = Var x (TYPE_SUBST tyin ty)) →
      INST_CORE env tyin tm = Result tmi → db tmi = dbINST tyin (db tm) := by
  induction n using Nat.strongRecOn with
  | ind n IH =>
    intro tm env r hn hw he hr
    cases tm with
    | Var x ty =>
      rw [Aux.INST_CORE_Var] at hr
      split at hr
      · cases hr; rfl
      · cases hr
    | Const x ty =>
      rw [Aux.INST_CORE_Const] at hr
      cases hr; rfl
    | Comb s t =>
      simp only [sizeof] at hn
      obtain ⟨ws, wt, _⟩ := Aux.welltyped_Comb.mp hw
      obtain ⟨s', t', hs, ht', rfl⟩ := Aux.INST_CORE_Comb_Result hr
      simp only [db, dbINST]
      rw [IH (sizeof s) (by omega) s env s' rfl ws he hs, IH (sizeof t) (by omega) t env t' rfl wt he ht']
    | Abs v b =>
      simp only [sizeof] at hn
      obtain ⟨x, ty, rfl, wb⟩ := Aux.welltyped_Abs.mp hw
      have hcons : ∀ x' : mlstring, ∀ (s s' : term),
          (s, s') ∈ (Var x' ty, Var x' (TYPE_SUBST tyin ty)) :: env →
          ∃ (x : mlstring) (ty : type), s = Var x ty ∧ s' = Var x (TYPE_SUBST tyin ty) := by
        intro x' s s' hm
        rcases List.mem_cons.mp hm with hm | hm
        · cases hm; exact ⟨x', ty, rfl, rfl⟩
        · exact he s s' hm
      simp only [db, dbINST, dest_var_def, typeof]
      rcases Aux.INST_CORE_Abs_Result hr with ⟨b', hb, rfl⟩ | ⟨x', b', hx', hb, rfl⟩
      · simp only [db, dest_var_def, typeof]
        rw [IH (sizeof b) (by omega) b _ b' rfl wb (hcons x) hb,
          Aux.INST_CORE_dbINST_bind wb he hb]
      · simp only [db, dest_var_def, typeof]
        have hwb2 : welltyped (VSUBST [(Var x' ty, Var x ty)] b) :=
          VSUBST_WELLTYPED b ty _ ⟨wb, Aux.single_subst_ok x x' ty⟩
        rw [IH (sizeof b) (by omega) _ _ b' (SIZEOF_VSUBST b _ (Aux.single_subst_ok' x x' ty)) hwb2
          (hcons x') hb, ← Aux.INST_CORE_dbINST_bind hwb2 he hb,
          VSUBST_dbVSUBST b _ ⟨wb, ?_⟩]
        · congr 2
          have h := bind_dbVSUBST_cons (db b) (x', ty) (x, ty) 0 []
          rw [dbVSUBST_nil] at h
          refine h ?_
          rw [Aux.dbVFREE_IN_bind]
          rintro ⟨_, h2⟩
          have h3 : VFREE_IN (Var x' ty) b := (dbVFREE_IN_VFREE_IN b (Var x' ty) wb).mp h2
          obtain ⟨r, k1, _, k3⟩ := Aux.INST_CORE_nil (tyin := tyin) wb
          have hv := VARIANT_THM (RESULT (INST_CORE [] tyin b)) (explode x) (TYPE_SUBST tyin ty)
          rw [← hx', k1, RESULT_def, k3] at hv
          exact hv ⟨ty, h3, rfl⟩
        · intro k v hm
          cases List.mem_singleton.mp hm
          exact ⟨Aux.welltyped_Var, x, ty, rfl⟩

/- HOL4:
Theorem INST_CORE_dbINST:
   ∀tm tyin env tmi.
      welltyped tm ∧ (∀s s'. MEM (s,s') env ⇒ ∃x ty. s = Var x ty ∧ s' = Var x (TYPE_SUBST tyin ty)) ∧
      INST_CORE env tyin tm = Result tmi ⇒
        db tmi = dbINST tyin (db tm) -/
theorem INST_CORE_dbINST :
    ∀ (tm : term) (tyin : List (type × type)) (env : List (term × term)) (tmi : term),
        welltyped tm ∧ (∀ (s s' : term), (s, s') ∈ env → ∃ (x : mlstring) (ty : type), s = Var x ty ∧ s' = Var x (TYPE_SUBST tyin ty)) ∧
        INST_CORE env tyin tm = Result tmi →
          db tmi = dbINST tyin (db tm) := by
  rintro tm tyin env tmi ⟨hw, he, hr⟩
  exact Aux.INST_CORE_dbINST tyin _ tm env tmi rfl hw he hr

/- HOL4:
Theorem INST_dbINST:
   ∀tm tyin.
      welltyped tm ⇒
      db (INST tyin tm) = dbINST tyin (db tm) -/
theorem INST_dbINST :
    ∀ (tm : term) (tyin : List (type × type)),
        welltyped tm →
        db (INST tyin tm) = dbINST tyin (db tm) := by
  intro tm tyin hw
  exact INST_CORE_dbINST tm tyin [] _ ⟨hw, by simp, (Aux.INST_spec hw).1⟩

/- HOL4:
Theorem bind_list_aux_clauses:
   (∀env m. bind_list_aux m env (dbBound n) = dbBound n) ∧
    (∀env m. bind_list_aux m env (dbConst x ty) = dbConst x ty) ∧
    (∀env m t1 t2. bind_list_aux m env (dbComb t1 t2) = dbComb (bind_list_aux m env t1) (bind_list_aux m env t2)) ∧
    (∀env m ty tm. bind_list_aux m env (dbAbs ty tm) = dbAbs ty (bind_list_aux (m+1) env tm)) -/
theorem bind_list_aux_clauses (n : Nat) (x : mlstring) (ty : type) :
    (∀ (env : List (mlstring × type)) (m : Nat), bind_list_aux m env (dbBound n) = dbBound n) ∧
      (∀ (env : List (mlstring × type)) (m : Nat), bind_list_aux m env (dbConst x ty) = dbConst x ty) ∧
      (∀ (env : List (mlstring × type)) (m : Nat) (t1 t2 : dbterm_t),
        bind_list_aux m env (dbComb t1 t2) = dbComb (bind_list_aux m env t1) (bind_list_aux m env t2)) ∧
      (∀ (env : List (mlstring × type)) (m : Nat) (ty : type) (tm : dbterm_t),
        bind_list_aux m env (dbAbs ty tm) = dbAbs ty (bind_list_aux (m + 1) env tm)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro env
    induction env with
    | nil => intro m; rfl
    | cons v vs ih => intro m; simp only [bind_list_aux, bind, ih]
  · intro env
    induction env with
    | nil => intro m; rfl
    | cons v vs ih => intro m; simp only [bind_list_aux, bind, ih]
  · intro env
    induction env with
    | nil => intro m t1 t2; rfl
    | cons v vs ih => intro m t1 t2; simp only [bind_list_aux, bind, ih]
  · intro env
    induction env with
    | nil => intro m t1 t2; rfl
    | cons v vs ih => intro m t1 t2; simp only [bind_list_aux, bind, ih]

/-- `dbterm` of a variable, with an offset. -/
def Aux.fidb (env : List (mlstring × type)) (s : mlstring) (ty : type) (m : Nat) : dbterm_t :=
  match find_index (s, ty) env m with
  | some n => dbBound n
  | none => dbVar s ty

theorem Aux.dbterm_Var (env : List (mlstring × type)) (s : mlstring) (ty : type) :
    dbterm env (Var s ty) = Aux.fidb env s ty 0 := rfl

theorem Aux.bind_list_aux_Var (s : mlstring) (ty : type) (env : List (mlstring × type)) :
    ∀ m, bind_list_aux m env (dbVar s ty) = Aux.fidb env s ty m := by
  induction env with
  | nil => intro m; rfl
  | cons v vs ih =>
    intro m
    simp only [bind_list_aux, bind, Aux.fidb, find_index]
    by_cases h : v = (s, ty)
    · rw [if_pos h, if_pos h]
      exact (bind_list_aux_clauses m s ty).1 vs (m + 1)
    · rw [if_neg h, if_neg h]
      exact ih (m + 1)

theorem Aux.find_index_ge {α : Type u} (y : α) (xs : List α) :
    ∀ m n, find_index y xs m = some n → m ≤ n := by
  induction xs with
  | nil => intro m n h; simp [find_index] at h
  | cons x xs ih =>
    intro m n h
    simp only [find_index] at h
    by_cases e : x = y
    · rw [if_pos e] at h; cases h; exact Nat.le_refl _
    · rw [if_neg e] at h
      have := ih (m + 1) n h
      omega

theorem Aux.fidb_ne (env : List (mlstring × type)) (b : mlstring) (tb : type) (m : Nat) :
    dbBound m ≠ Aux.fidb env b tb (m + 1) := by
  unfold Aux.fidb
  cases h : find_index (b, tb) env (m + 1) with
  | none => simp
  | some n =>
    intro e
    simp only [dbterm_t.dbBound.injEq] at e
    have := Aux.find_index_ge _ _ _ _ h
    omega

theorem Aux.fidb_cons (v : mlstring × type) (env : List (mlstring × type)) (b : mlstring) (tb : type)
    (m : Nat) : Aux.fidb (v :: env) b tb m =
      if v = (b, tb) then dbBound m else Aux.fidb env b tb (m + 1) := by
  simp only [Aux.fidb, find_index]
  by_cases e : v = (b, tb)
  · rw [if_pos e, if_pos e]
  · rw [if_neg e, if_neg e]

theorem Aux.fidb_ALPHAVARS (a : mlstring) (ta : type) (b : mlstring) (tb : type) :
    ∀ (env1 env2 : List (mlstring × type)) (m : Nat), env1.length = env2.length →
      Aux.fidb env1 a ta m = Aux.fidb env2 b tb m →
      ALPHAVARS (ZIP (env1.map (UNCURRY Var), env2.map (UNCURRY Var))) (Var a ta, Var b tb)
  | [], [], m, _, h => by
    simp only [Aux.fidb, find_index, dbterm_t.dbVar.injEq] at h
    simp only [List.map_nil, ZIP, ALPHAVARS]
    rw [h.1, h.2]
  | [], _ :: _, _, hl, _ => by simp at hl
  | _ :: _, [], _, hl, _ => by simp at hl
  | (x, tx) :: env1, (y, ty) :: env2, m, hl, h => by
    rw [Aux.fidb_cons, Aux.fidb_cons] at h
    simp only [List.map_cons, ZIP, ALPHAVARS, UNCURRY, Prod.mk.injEq, term.Var.injEq] at h ⊢
    by_cases h1 : x = a ∧ tx = ta
    · rw [if_pos h1] at h
      by_cases h2 : y = b ∧ ty = tb
      · exact Or.inl ⟨⟨h1.1.symm, h1.2.symm⟩, h2.1.symm, h2.2.symm⟩
      · rw [if_neg h2] at h
        exact absurd h (Aux.fidb_ne _ _ _ _)
    · rw [if_neg h1] at h
      by_cases h2 : y = b ∧ ty = tb
      · rw [if_pos h2] at h
        exact absurd h.symm (Aux.fidb_ne _ _ _ _)
      · rw [if_neg h2] at h
        refine Or.inr ⟨fun e => h1 (term.Var.inj e), fun e => h2 (term.Var.inj e), ?_⟩
        exact Aux.fidb_ALPHAVARS a ta b tb env1 env2 (m + 1) (by simpa using hl) h

theorem Aux.ALPHAVARS_fidb (a : mlstring) (ta : type) (b : mlstring) (tb : type)
    (env : List (term × term)) :
    (∀ (vp : term × term), vp ∈ env → (∃ (x : mlstring) (ty : type), vp.1 = Var x ty) ∧
        (∃ (x : mlstring) (ty : type), vp.2 = Var x ty)) →
    ∀ m, ALPHAVARS env (Var a ta, Var b tb) →
      Aux.fidb (env.map (dest_var ∘ Prod.fst)) a ta m =
        Aux.fidb (env.map (dest_var ∘ Prod.snd)) b tb m := by
  induction env with
  | nil =>
    intro _ m h
    have h' : Var a ta = Var b tb := h
    obtain ⟨rfl, rfl⟩ := term.Var.inj h'
    rfl
  | cons p env ih =>
    intro hv m h
    obtain ⟨v, w⟩ := p
    obtain ⟨⟨x, tx, e1⟩, ⟨y, ty, e2⟩⟩ := hv _ List.mem_cons_self
    simp only at e1 e2
    subst e1; subst e2
    simp only [List.map_cons, Function.comp, dest_var_def, Aux.fidb_cons]
    simp only [ALPHAVARS, Prod.mk.injEq] at h
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2, h⟩
    · obtain ⟨rfl, rfl⟩ := term.Var.inj h1
      obtain ⟨rfl, rfl⟩ := term.Var.inj h2
      rw [if_pos rfl, if_pos rfl]
    · rw [if_neg (fun e => h1 (by cases e; rfl)), if_neg (fun e => h2 (by cases e; rfl))]
      exact ih (fun vp hm => hv vp (List.mem_cons_of_mem _ hm)) (m + 1) h

/- HOL4:
Theorem dbterm_bind:
   ∀tm env. dbterm env tm = bind_list_aux 0 env (db tm) -/
theorem dbterm_bind :
    ∀ (tm : term) (env : List (mlstring × type)), dbterm env tm = bind_list_aux 0 env (db tm) := by
  intro tm
  induction tm with
  | Var x ty =>
    intro env
    rw [Aux.dbterm_Var]
    exact (Aux.bind_list_aux_Var x ty env 0).symm
  | Const x ty => intro env; exact ((bind_list_aux_clauses 0 x ty).2.1 env 0).symm
  | Comb a b iha ihb =>
    intro env
    simp only [dbterm, db]
    rw [(bind_list_aux_clauses 0 default default).2.2.1, iha, ihb]
  | Abs v b _ ihb =>
    intro env
    simp only [dbterm, db]
    rw [(bind_list_aux_clauses 0 default default).2.2.2, ihb]
    rfl

/- HOL4:
Theorem dbterm_db:
   ∀tm. dbterm [] tm = db tm -/
theorem dbterm_db :
    ∀ (tm : term), dbterm [] tm = db tm := by
  intro tm
  rw [dbterm_bind]
  rfl

theorem Aux.fidb_cases (env : List (mlstring × type)) (s : mlstring) (ty : type) (m : Nat) :
    (∃ n, Aux.fidb env s ty m = dbBound n) ∨ Aux.fidb env s ty m = dbVar s ty := by
  unfold Aux.fidb
  cases find_index (s, ty) env m with
  | none => exact Or.inr rfl
  | some n => exact Or.inl ⟨n, rfl⟩

/- HOL4:
Theorem dbterm_RACONV:
   ∀t1 env1 t2 env2. welltyped t1 ∧ welltyped t2 ∧ dbterm env1 t1 = dbterm env2 t2 ∧ LENGTH env1 = LENGTH env2 ⇒
      RACONV (ZIP(MAP (UNCURRY Var) env1,MAP (UNCURRY Var) env2)) (t1,t2) -/
theorem dbterm_RACONV :
    ∀ (t1 : term) (env1 : List (mlstring × type)) (t2 : term) (env2 : List (mlstring × type)),
        welltyped t1 ∧ welltyped t2 ∧ dbterm env1 t1 = dbterm env2 t2 ∧ env1.length = env2.length →
        RACONV (ZIP (env1.map (UNCURRY Var), env2.map (UNCURRY Var))) (t1, t2) := by
  intro t1
  induction t1 with
  | Var a ta =>
    rintro env1 t2 env2 ⟨_, _, h, hl⟩
    rw [Aux.dbterm_Var] at h
    cases t2 with
    | Var b tb =>
      rw [Aux.dbterm_Var] at h
      exact RACONV.Var (Aux.fidb_ALPHAVARS a ta b tb env1 env2 0 hl h)
    | _ => rcases Aux.fidb_cases env1 a ta 0 with ⟨n, e⟩ | e <;> rw [e] at h <;> cases h
  | Const a ta =>
    rintro env1 t2 env2 ⟨_, _, h, hl⟩
    cases t2 with
    | Var b tb =>
      rw [Aux.dbterm_Var] at h
      rcases Aux.fidb_cases env2 b tb 0 with ⟨n, e⟩ | e <;> rw [e] at h <;> cases h
    | Const b tb => cases h; exact RACONV.Const
    | _ => cases h
  | Comb a b iha ihb =>
    rintro env1 t2 env2 ⟨w1, w2, h, hl⟩
    cases t2 with
    | Var b tb =>
      rw [Aux.dbterm_Var] at h
      rcases Aux.fidb_cases env2 b tb 0 with ⟨n, e⟩ | e <;> rw [e] at h <;> cases h
    | Comb c d =>
      simp only [dbterm, dbterm_t.dbComb.injEq] at h
      obtain ⟨wa, wb, _⟩ := Aux.welltyped_Comb.mp w1
      obtain ⟨wc, wd, _⟩ := Aux.welltyped_Comb.mp w2
      exact RACONV.Comb (iha env1 c env2 ⟨wa, wc, h.1, hl⟩) (ihb env1 d env2 ⟨wb, wd, h.2, hl⟩)
    | _ => cases h
  | Abs v b _ ihb =>
    rintro env1 t2 env2 ⟨w1, w2, h, hl⟩
    cases t2 with
    | Var b tb =>
      rw [Aux.dbterm_Var] at h
      rcases Aux.fidb_cases env2 b tb 0 with ⟨n, e⟩ | e <;> rw [e] at h <;> cases h
    | Abs w d =>
      obtain ⟨x, tx, rfl, wb⟩ := Aux.welltyped_Abs.mp w1
      obtain ⟨y, ty, rfl, wd⟩ := Aux.welltyped_Abs.mp w2
      simp only [dbterm, dbterm_t.dbAbs.injEq, dest_var_def] at h
      have ih := ihb ((x, tx) :: env1) d ((y, ty) :: env2) ⟨wb, wd, h.2, by simp [hl]⟩
      simp only [List.map_cons, ZIP, UNCURRY] at ih
      exact RACONV.Abs h.1 ih
    | _ => cases h

/- HOL4:
Theorem RACONV_dbterm:
   ∀env tp. RACONV env tp ⇒
    welltyped (FST tp) ∧ welltyped (SND tp) ∧
    (∀vp. MEM vp env ⇒ (∃x ty. (FST vp = Var x ty)) ∧ (∃x ty. (SND vp = Var x ty)))
     ⇒ dbterm (MAP (dest_var o FST) env) (FST tp) = dbterm (MAP (dest_var o SND) env) (SND tp) -/
theorem RACONV_dbterm :
    ∀ (env : List (term × term)) (tp : term × term), RACONV env tp →
      welltyped tp.1 ∧ welltyped tp.2 ∧
      (∀ (vp : term × term), vp ∈ env → (∃ (x : mlstring) (ty : type), vp.1 = Var x ty) ∧
        (∃ (x : mlstring) (ty : type), vp.2 = Var x ty))
       → dbterm (env.map (dest_var ∘ Prod.fst)) tp.1 = dbterm (env.map (dest_var ∘ Prod.snd)) tp.2 := by
  intro env tp h
  induction h with
  | Var ha =>
    rintro ⟨_, _, hv⟩
    exact Aux.ALPHAVARS_fidb _ _ _ _ _ hv 0 ha
  | Const => intro _; rfl
  | Comb _ _ ih1 ih2 =>
    rintro ⟨w1, w2, hv⟩
    obtain ⟨wa, wb, _⟩ := Aux.welltyped_Comb.mp w1
    obtain ⟨wc, wd, _⟩ := Aux.welltyped_Comb.mp w2
    simp only [dbterm]
    rw [ih1 ⟨wa, wc, hv⟩, ih2 ⟨wb, wd, hv⟩]
  | Abs e _ ih =>
    rintro ⟨w1, w2, hv⟩
    obtain ⟨x, tx, rfl, wb⟩ := Aux.welltyped_Abs.mp w1
    obtain ⟨y, ty, rfl, wd⟩ := Aux.welltyped_Abs.mp w2
    have := ih ⟨wb, wd, fun vp hm => by
      rcases List.mem_cons.mp hm with rfl | hm
      · exact ⟨⟨x, tx, rfl⟩, ⟨y, ty, rfl⟩⟩
      · exact hv vp hm⟩
    simp only [List.map_cons, Function.comp] at this
    simp only [dbterm, e]
    rw [this]

/- HOL4:
Theorem dbterm_ACONV:
   ∀t1 t2. welltyped t1 ∧ welltyped t2 ⇒ (ACONV t1 t2 ⇔ dbterm [] t1 = dbterm [] t2) -/
theorem dbterm_ACONV :
    ∀ (t1 t2 : term), welltyped t1 ∧ welltyped t2 → (ACONV t1 t2 ↔ dbterm [] t1 = dbterm [] t2) := by
  rintro t1 t2 ⟨w1, w2⟩
  constructor
  · intro h
    exact RACONV_dbterm [] (t1, t2) h ⟨w1, w2, by simp⟩
  · intro h
    have := dbterm_RACONV t1 [] t2 [] ⟨w1, w2, h, rfl⟩
    simp only [List.map_nil, ZIP] at this
    exact this

/- HOL4:
Theorem ACONV_db:
   ∀t1 t2. welltyped t1 ∧ welltyped t2 ⇒ (ACONV t1 t2 ⇔ db t1 = db t2) -/
theorem ACONV_db :
    ∀ (t1 t2 : term), welltyped t1 ∧ welltyped t2 → (ACONV t1 t2 ↔ db t1 = db t2) := by
  intro t1 t2 h
  rw [dbterm_ACONV t1 t2 h, dbterm_db, dbterm_db]

/- HOL4:
Theorem ACONV_VSUBST:
   ∀t1 t2 ilist.
    welltyped t1 ∧ welltyped t2 ∧
    (∀k v. MEM (v,k) ilist ⇒ ∃x ty. k = Var x ty ∧ v has_type ty) ∧
    ACONV t1 t2 ⇒
    ACONV (VSUBST ilist t1) (VSUBST ilist t2) -/
theorem ACONV_VSUBST :
    ∀ (t1 t2 : term) (ilist : List (term × term)),
      welltyped t1 ∧ welltyped t2 ∧
      (∀ (k v : term), (v, k) ∈ ilist → ∃ (x : mlstring) (ty : type), k = Var x ty ∧ has_type v ty) ∧
      ACONV t1 t2 →
      ACONV (VSUBST ilist t1) (VSUBST ilist t2) := by
  rintro t1 t2 ilist ⟨w1, w2, hi, h⟩
  have hi' : ∀ (k v : term), (v, k) ∈ ilist → welltyped v ∧ ∃ (x : mlstring) (ty : type), k = Var x ty := by
    intro k v hm
    obtain ⟨x, ty, e, ht⟩ := hi k v hm
    exact ⟨⟨ty, ht⟩, x, ty, e⟩
  rw [ACONV_db _ _ ⟨VSUBST_WELLTYPED t1 (Tyvar default) ilist ⟨w1, hi⟩,
    VSUBST_WELLTYPED t2 (Tyvar default) ilist ⟨w2, hi⟩⟩,
    VSUBST_dbVSUBST t1 ilist ⟨w1, hi'⟩, VSUBST_dbVSUBST t2 ilist ⟨w2, hi'⟩,
    (ACONV_db t1 t2 ⟨w1, w2⟩).mp h]

/- HOL4:
Theorem ACONV_INST:
   ∀t1 t2 tyin. welltyped t1 ∧ welltyped t2 ∧ ACONV t1 t2 ⇒ ACONV (INST tyin t1) (INST tyin t2) -/
theorem ACONV_INST :
    ∀ (t1 t2 : term) (tyin : List (type × type)),
        welltyped t1 ∧ welltyped t2 ∧ ACONV t1 t2 → ACONV (INST tyin t1) (INST tyin t2) := by
  rintro t1 t2 tyin ⟨w1, w2, h⟩
  rw [ACONV_db _ _ ⟨INST_WELLTYPED t1 tyin w1, INST_WELLTYPED t2 tyin w2⟩,
    INST_dbINST t1 tyin w1, INST_dbINST t2 tyin w2, (ACONV_db t1 t2 ⟨w1, w2⟩).mp h]

theorem Aux.DISJOINT_iff {α : Type u} (s t : Set α) : DISJOINT s t ↔ ∀ x, x ∈ s → ¬ x ∈ t := by
  constructor
  · intro h x hs ht
    have h' : INTER s t = EMPTY := h
    have : x ∈ INTER s t := ⟨hs, ht⟩
    rw [h'] at this
    exact this
  · intro h
    apply Aux.set_ext
    intro x
    exact ⟨fun hx => h x hx.1 hx.2, fun hx => hx.elim⟩

/- HOL4:
Theorem VSUBST_simple_subst:
   ∀tm ilist. DISJOINT (set (bv_names tm)) {y | ∃ty u. VFREE_IN (Var y ty) u ∧ MEM u (MAP FST ilist)} ∧
               (∀s s'. MEM (s',s) ilist ⇒ ∃x ty. s = Var x ty) ∧
               welltyped tm
               ⇒ VSUBST ilist tm = simple_subst ilist tm -/
theorem VSUBST_simple_subst :
    ∀ (tm : term) (ilist : List (term × term)),
        DISJOINT (LIST_TO_SET (bv_names tm))
          (setOf (fun (y : mlstring) => ∃ (ty : type) (u : term), VFREE_IN (Var y ty) u ∧ u ∈ ilist.map Prod.fst)) ∧
        (∀ (s s' : term), (s', s) ∈ ilist → ∃ (x : mlstring) (ty : type), s = Var x ty) ∧
        welltyped tm
        → VSUBST ilist tm = simple_subst ilist tm := by
  intro tm
  induction tm with
  | Var x ty => intro ilist _; rfl
  | Const x ty => intro ilist _; rfl
  | Comb a b iha ihb =>
    rintro ilist ⟨hd, hi, hw⟩
    obtain ⟨wa, wb, _⟩ := Aux.welltyped_Comb.mp hw
    rw [Aux.DISJOINT_iff] at hd
    simp only [Aux.mem_LIST_TO_SET, bv_names, List.mem_append] at hd
    simp only [VSUBST, simple_subst]
    rw [iha ilist ⟨?_, hi, wa⟩, ihb ilist ⟨?_, hi, wb⟩]
    · rw [Aux.DISJOINT_iff]
      intro x hx
      exact hd x (Or.inr ((Aux.mem_LIST_TO_SET _ _).mp hx))
    · rw [Aux.DISJOINT_iff]
      intro x hx
      exact hd x (Or.inl ((Aux.mem_LIST_TO_SET _ _).mp hx))
  | Abs v b _ ihb =>
    rintro ilist ⟨hd, hi, hw⟩
    obtain ⟨x, ty, rfl, wb⟩ := Aux.welltyped_Abs.mp hw
    rw [Aux.DISJOINT_iff] at hd
    simp only [Aux.mem_LIST_TO_SET, bv_names, dest_var_def, List.mem_cons] at hd
    rw [Aux.VSUBST_Abs, if_neg]
    · simp only [simple_subst]
      congr 1
      refine ihb _ ⟨?_, fun s s' hm => hi s s' (Aux.mem_FILTER_imp _ _ _ hm), wb⟩
      rw [Aux.DISJOINT_iff]
      rintro y hy ⟨ty', u, h1, h2⟩
      refine hd y (Or.inr ((Aux.mem_LIST_TO_SET _ _).mp hy)) ⟨ty', u, h1, ?_⟩
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp h2
      exact List.mem_map.mpr ⟨p, Aux.mem_FILTER_imp _ _ _ hp, rfl⟩
    · rw [Aux.EXISTS_iff]
      rintro ⟨p, hp, h1, _⟩
      exact hd x (Or.inl rfl) ⟨ty, p.1, h1, List.mem_map.mpr ⟨p, Aux.mem_FILTER_imp _ _ _ hp, rfl⟩⟩

/- HOL4:
Theorem INST_CORE_simple_inst:
   ∀env tyin tm.
      ALL_DISTINCT (bv_names tm ++ (MAP (FST o dest_var o SND) env)) ∧
      DISJOINT (set(bv_names tm)) {x | ∃ty. VFREE_IN (Var x ty) tm} ∧
      (∀s s'. MEM (s,s') env ⇒ ∃x ty. s = Var x ty ∧ s' = Var x (TYPE_SUBST tyin ty)) ∧
      (∀x ty ty'. VFREE_IN (Var x ty) tm ∧ MEM (Var x ty') (MAP FST env) ⇒ ty' = ty) ∧
      welltyped tm
      ⇒ INST_CORE env tyin tm = Result (simple_inst tyin tm) -/
theorem INST_CORE_simple_inst :
    ∀ (env : List (term × term)) (tyin : List (type × type)) (tm : term),
        ALL_DISTINCT (bv_names tm ++ env.map (Prod.fst ∘ dest_var ∘ Prod.snd)) ∧
        DISJOINT (LIST_TO_SET (bv_names tm)) (setOf (fun (x : mlstring) => ∃ (ty : type), VFREE_IN (Var x ty) tm)) ∧
        (∀ (s s' : term), (s, s') ∈ env → ∃ (x : mlstring) (ty : type), s = Var x ty ∧ s' = Var x (TYPE_SUBST tyin ty)) ∧
        (∀ (x : mlstring) (ty ty' : type), VFREE_IN (Var x ty) tm ∧ Var x ty' ∈ env.map Prod.fst → ty' = ty) ∧
        welltyped tm
        → INST_CORE env tyin tm = Result (simple_inst tyin tm) := by
  intro env tyin tm
  induction tm generalizing env with
  | Var x ty =>
    rintro ⟨_, _, he, hv, _⟩
    rw [Aux.INST_CORE_Var, if_pos]
    · rfl
    · rcases REV_ASSOCD_MEM env (Var x (TYPE_SUBST tyin ty)) (Var x ty) with h | h
      · obtain ⟨y, t, e1, e2⟩ := he _ _ h
        obtain ⟨rfl, _⟩ := term.Var.inj e2
        rw [e1]
        rw [hv x ty t ⟨rfl, List.mem_map.mpr ⟨_, h, e1⟩⟩]
      · exact h
  | Const x ty => intro _; rw [Aux.INST_CORE_Const]; rfl
  | Comb a b iha ihb =>
    rintro ⟨had, hd, he, hv, hw⟩
    obtain ⟨wa, wb, _⟩ := Aux.welltyped_Comb.mp hw
    rw [Aux.ALL_DISTINCT_iff_nodup] at had
    simp only [bv_names] at had
    rw [Aux.DISJOINT_iff] at hd
    simp only [Aux.mem_LIST_TO_SET, bv_names, List.mem_append] at hd
    have ha := iha env ⟨by
        rw [Aux.ALL_DISTINCT_iff_nodup]
        refine had.sublist ?_
        exact (List.sublist_append_left _ _).append_right _, by
        rw [Aux.DISJOINT_iff]
        rintro x hx ⟨ty, h⟩
        exact hd x (Or.inl ((Aux.mem_LIST_TO_SET _ _).mp hx)) ⟨ty, Or.inl h⟩,
      he, fun x ty ty' h => hv x ty ty' ⟨Or.inl h.1, h.2⟩, wa⟩
    have hb := ihb env ⟨by
        rw [Aux.ALL_DISTINCT_iff_nodup]
        refine had.sublist ?_
        exact (List.sublist_append_right _ _).append_right _, by
        rw [Aux.DISJOINT_iff]
        rintro x hx ⟨ty, h⟩
        exact hd x (Or.inr ((Aux.mem_LIST_TO_SET _ _).mp hx)) ⟨ty, Or.inr h⟩,
      he, fun x ty ty' h => hv x ty ty' ⟨Or.inr h.1, h.2⟩, wb⟩
    rw [Aux.INST_CORE_Comb, ha, hb]
    rfl
  | Abs v b _ ihb =>
    rintro ⟨had, hd, he, hv, hw⟩
    obtain ⟨x, ty, rfl, wb⟩ := Aux.welltyped_Abs.mp hw
    rw [Aux.ALL_DISTINCT_iff_nodup] at had
    simp only [bv_names, dest_var_def, List.cons_append] at had
    rw [Aux.DISJOINT_iff] at hd
    simp only [Aux.mem_LIST_TO_SET, bv_names, dest_var_def, List.mem_cons] at hd
    have hx1 : ¬ x ∈ bv_names b := fun h =>
      (List.nodup_cons.mp had).1 (List.mem_append_left _ h)
    have hx2 : ¬ x ∈ env.map (Prod.fst ∘ dest_var ∘ Prod.snd) := fun h =>
      (List.nodup_cons.mp had).1 (List.mem_append_right _ h)
    have hb := ihb ((Var x ty, Var x (TYPE_SUBST tyin ty)) :: env) ⟨by
        rw [Aux.ALL_DISTINCT_iff_nodup]
        simp only [List.map_cons, Function.comp, dest_var_def]
        exact (List.perm_middle.nodup_iff).mpr had, by
        rw [Aux.DISJOINT_iff]
        rintro y hy ⟨t, h⟩
        have hy' := (Aux.mem_LIST_TO_SET _ _).mp hy
        by_cases e : Var x ty = Var y t
        · obtain ⟨rfl, _⟩ := term.Var.inj e
          exact hx1 hy'
        · exact hd y (Or.inr hy') ⟨t, e, h⟩, by
        intro s s' hm
        rcases List.mem_cons.mp hm with hm | hm
        · cases hm; exact ⟨x, ty, rfl, rfl⟩
        · exact he s s' hm, by
        rintro y t t' ⟨h1, h2⟩
        have hyx : y = x → t = ty := by
          rintro rfl
          apply Classical.byContradiction
          intro hne
          refine hd y (Or.inl rfl) ⟨t, ?_, h1⟩
          intro e
          exact hne (term.Var.inj e).2.symm
        simp only [List.map_cons, List.mem_cons, term.Var.injEq] at h2
        rcases h2 with ⟨e1, e2⟩ | h2
        · rw [e2, hyx e1]
        · by_cases e1 : y = x
          · exfalso
            subst e1
            obtain ⟨p, hp, e⟩ := List.mem_map.mp h2
            obtain ⟨s, s'⟩ := p
            obtain ⟨z, uz, e3, e4⟩ := he s s' hp
            simp only at e
            rw [e] at e3
            obtain ⟨rfl, _⟩ := term.Var.inj e3
            apply hx2
            refine List.mem_map.mpr ⟨_, hp, ?_⟩
            simp only [Function.comp, e4, dest_var_def]
          · refine hv y t t' ⟨⟨fun e => e1 (term.Var.inj e).1.symm, h1⟩, h2⟩, wb⟩
    rw [Aux.INST_CORE_Abs, hb]
    rfl

/- HOL4:
Theorem INST_simple_inst:
   ∀tyin tm.
      ALL_DISTINCT (bv_names tm) ∧
      DISJOINT (set (bv_names tm)) {x | ∃ty. VFREE_IN (Var x ty) tm} ∧
      welltyped tm
      ⇒
      INST tyin tm = simple_inst tyin tm -/
theorem INST_simple_inst :
    ∀ (tyin : List (type × type)) (tm : term),
        ALL_DISTINCT (bv_names tm) ∧
        DISJOINT (LIST_TO_SET (bv_names tm)) (setOf (fun (x : mlstring) => ∃ (ty : type), VFREE_IN (Var x ty) tm)) ∧
        welltyped tm
        →
        INST tyin tm = simple_inst tyin tm := by
  rintro tyin tm ⟨h1, h2, h3⟩
  rw [INST, INST_CORE_simple_inst [] tyin tm ⟨by simpa using h1, h2, by simp, by simp, h3⟩, RESULT_def]

/- HOL4:
Theorem simple_subst_has_type:
   ∀tm ty.
      tm has_type ty ⇒
      ∀subst.
        EVERY (λ(s',s). s' has_type typeof s) subst ⇒
        simple_subst subst tm has_type ty -/
theorem simple_subst_has_type :
    ∀ (tm : term) (ty : type),
        has_type tm ty →
        ∀ (subst : List (term × term)),
          EVERY (fun (p : term × term) => has_type p.1 (typeof p.2)) subst →
          has_type (simple_subst subst tm) ty := by
  intro tm ty h
  induction h with
  | @Var n ty =>
    intro subst hs
    simp only [simple_subst]
    rcases REV_ASSOCD_MEM subst (Var n ty) (Var n ty) with h | h
    · exact (Aux.EVERY_iff _ _).mp hs _ h
    · rw [h]; exact has_type.Var
  | Const => intro subst _; exact has_type.Const
  | Comb _ _ ih1 ih2 => intro subst hs; exact has_type.Comb (ih1 subst hs) (ih2 subst hs)
  | Abs _ ih =>
    intro subst hs
    refine has_type.Abs (ih _ ?_)
    rw [Aux.EVERY_iff] at hs ⊢
    exact fun p hp => hs p (Aux.mem_FILTER_imp _ _ _ hp)

/- HOL4:
Theorem simple_inst_has_type:
   ∀tm tyin. welltyped tm ⇒ simple_inst tyin tm has_type (TYPE_SUBST tyin (typeof tm)) -/
theorem simple_inst_has_type :
    ∀ (tm : term) (tyin : List (type × type)),
        welltyped tm → has_type (simple_inst tyin tm) (TYPE_SUBST tyin (typeof tm)) := by
  intro tm tyin
  induction tm with
  | Var x ty => intro _; exact has_type.Var
  | Const x ty => intro _; exact has_type.Const
  | Comb a b iha ihb =>
    intro hw
    obtain ⟨wa, wb, rty, e⟩ := Aux.welltyped_Comb.mp hw
    have ha := iha wa
    rw [e, Aux.TYPE_SUBST_Fun] at ha
    have : typeof (Comb a b) = rty := by rw [typeof, e]; rfl
    rw [this]
    exact has_type.Comb ha (ihb wb)
  | Abs v b _ ihb =>
    intro hw
    obtain ⟨x, ty, rfl, wb⟩ := Aux.welltyped_Abs.mp hw
    have : TYPE_SUBST tyin (typeof (Abs (Var x ty) b)) =
        Fun (TYPE_SUBST tyin ty) (TYPE_SUBST tyin (typeof b)) := by
      simp only [typeof]; exact Aux.TYPE_SUBST_Fun _ _ _
    rw [this]
    exact has_type.Abs (ihb wb)

/- HOL4:
Theorem FST_rename_bvars:
   ∀names env tm. LENGTH (bv_names tm) ≤ LENGTH names ⇒ (FST (rename_bvars names env tm) = DROP (LENGTH (bv_names tm)) names) -/
theorem FST_rename_bvars :
    ∀ (names : List mlstring) (env : List (mlstring × (mlstring × type))) (tm : term),
        (bv_names tm).length ≤ names.length →
        (rename_bvars names env tm).1 = names.drop (bv_names tm).length := by
  intro names env tm
  induction tm generalizing names env with
  | Var x ty => intro _; simp [rename_bvars, bv_names]
  | Const x ty => intro _; simp [rename_bvars, bv_names]
  | Comb a b iha ihb =>
    intro h
    simp only [bv_names, List.length_append] at h
    simp only [rename_bvars, bv_names, List.length_append]
    rw [ihb _ env (by rw [iha names env (by omega), List.length_drop]; omega),
      iha names env (by omega), List.drop_drop]
  | Abs v b _ ihb =>
    intro h
    simp only [bv_names, List.length_cons] at h
    cases names with
    | nil => simp at h
    | cons s names =>
      simp only [rename_bvars, bv_names, List.length_cons, List.drop_succ_cons]
      exact ihb names _ (by simpa using h)

theorem Aux.rename_ALPHAVARS (s : mlstring) (ty : type) (env : List (mlstring × (mlstring × type))) :
    (∀ x, x ∈ env.map Prod.fst → ¬ x ∈ env.map (Prod.fst ∘ Prod.snd)) →
    ¬ s ∈ env.map Prod.fst → (env.map Prod.fst).Nodup →
    ALPHAVARS (env.map (fun (p : mlstring × (mlstring × type)) => (Var p.2.1 p.2.2, Var p.1 p.2.2)))
      (Var s ty, Var (REV_ASSOCD (s, ty) env s) ty) := by
  induction env with
  | nil => intro _ _ _; rfl
  | cons p env ih =>
    obtain ⟨s', s0, t0⟩ := p
    intro h1 h2 h3
    simp only [List.map_cons, List.mem_cons, Function.comp, not_or, List.nodup_cons] at h1 h2 h3
    simp only [List.map_cons, ALPHAVARS, REV_ASSOCD]
    by_cases e : (s0, t0) = (s, ty)
    · cases e
      rw [if_pos rfl]
      exact Or.inl rfl
    · rw [if_neg e]
      refine Or.inr ⟨fun h => e ?_, fun h => ?_, ih (fun x hx => (h1 x (Or.inr hx)).2) h2.2 h3.2⟩
      · rw [term.Var.injEq] at h; rw [h.1, h.2]
      · have h' := (term.Var.inj h).1
        rcases REV_ASSOCD_MEM env (s, ty) s with hm | hm
        · apply h3.1
          rw [h']
          exact List.mem_map.mpr ⟨_, hm, rfl⟩
        · rw [hm] at h'
          exact h2.1 h'.symm

/- HOL4:
Theorem rename_bvars_RACONV:
   ∀names env tm.
    LENGTH (bv_names tm) ≤ LENGTH names ∧
    DISJOINT (set (MAP FST env ++ names)) (set (MAP (FST o SND) env ++ bv_names tm)) ∧
    DISJOINT (set (MAP FST env ++ names)) {x | ∃ty. VFREE_IN (Var x ty) tm} ∧
    ALL_DISTINCT (MAP FST env ++ names) ∧
    welltyped tm
    ⇒ RACONV (MAP (λ(s',(s,ty)). (Var s ty, Var s' ty)) env) (tm, SND (rename_bvars names env tm)) -/
theorem rename_bvars_RACONV :
    ∀ (names : List mlstring) (env : List (mlstring × (mlstring × type))) (tm : term),
      (bv_names tm).length ≤ names.length ∧
      DISJOINT (LIST_TO_SET (env.map Prod.fst ++ names))
        (LIST_TO_SET (env.map (Prod.fst ∘ Prod.snd) ++ bv_names tm)) ∧
      DISJOINT (LIST_TO_SET (env.map Prod.fst ++ names))
        (setOf (fun (x : mlstring) => ∃ (ty : type), VFREE_IN (Var x ty) tm)) ∧
      ALL_DISTINCT (env.map Prod.fst ++ names) ∧
      welltyped tm
      → RACONV (env.map (fun (p : mlstring × (mlstring × type)) => (Var p.2.1 p.2.2, Var p.1 p.2.2)))
          (tm, (rename_bvars names env tm).2) := by
  intro names env tm
  induction tm generalizing names env with
  | Var s ty =>
    rintro ⟨_, h2, h3, h4, _⟩
    rw [Aux.DISJOINT_iff] at h2 h3
    rw [Aux.ALL_DISTINCT_iff_nodup] at h4
    simp only [Aux.mem_LIST_TO_SET, bv_names, List.append_nil, List.mem_append] at h2 h3
    simp only [rename_bvars]
    refine RACONV.Var (Aux.rename_ALPHAVARS s ty env (fun x hx => h2 x (Or.inl hx))
      (fun hs => h3 s (Or.inl hs) ⟨ty, rfl⟩) (List.nodup_append.mp h4).1)
  | Const s ty => intro _; exact RACONV.Const
  | Comb a b iha ihb =>
    rintro ⟨h1, h2, h3, h4, hw⟩
    obtain ⟨wa, wb, _⟩ := Aux.welltyped_Comb.mp hw
    rw [Aux.DISJOINT_iff] at h2 h3
    rw [Aux.ALL_DISTINCT_iff_nodup] at h4
    simp only [Aux.mem_LIST_TO_SET, bv_names, List.mem_append, not_or] at h2 h3
    simp only [bv_names, List.length_append] at h1
    simp only [rename_bvars]
    have hd : (rename_bvars names env a).1 = names.drop (bv_names a).length :=
      FST_rename_bvars names env a (by omega)
    refine RACONV.Comb (iha names env ⟨by omega, ?_, ?_, ?_, wa⟩) ?_
    · rw [Aux.DISJOINT_iff]
      simp only [Aux.mem_LIST_TO_SET, List.mem_append, not_or]
      exact fun x hx => ⟨(h2 x hx).1, (h2 x hx).2.1⟩
    · rw [Aux.DISJOINT_iff]
      simp only [Aux.mem_LIST_TO_SET, List.mem_append]
      rintro x hx ⟨ty, h⟩
      exact h3 x hx ⟨ty, Or.inl h⟩
    · rw [Aux.ALL_DISTINCT_iff_nodup]; exact h4
    · rw [hd]
      refine ihb _ env ⟨by rw [List.length_drop]; omega, ?_, ?_, ?_, wb⟩
      · rw [Aux.DISJOINT_iff]
        simp only [Aux.mem_LIST_TO_SET, List.mem_append, not_or]
        intro x hx
        have := h2 x (hx.imp_right List.mem_of_mem_drop)
        exact ⟨this.1, this.2.2⟩
      · rw [Aux.DISJOINT_iff]
        simp only [Aux.mem_LIST_TO_SET, List.mem_append]
        rintro x hx ⟨ty, h⟩
        exact h3 x (hx.imp_right List.mem_of_mem_drop) ⟨ty, Or.inr h⟩
      · rw [Aux.ALL_DISTINCT_iff_nodup]
        exact h4.sublist ((List.drop_sublist _ _).append_left _)
  | Abs v b _ ihb =>
    rintro ⟨h1, h2, h3, h4, hw⟩
    obtain ⟨x, ty, rfl, wb⟩ := Aux.welltyped_Abs.mp hw
    rw [Aux.DISJOINT_iff] at h2 h3
    rw [Aux.ALL_DISTINCT_iff_nodup] at h4
    simp only [bv_names, List.length_cons] at h1
    cases names with
    | nil => simp at h1
    | cons s' names =>
      simp only [Aux.mem_LIST_TO_SET, bv_names, dest_var_def, List.mem_append, List.mem_cons,
        not_or] at h2 h3
      simp only [rename_bvars, dest_var_def, typeof]
      refine RACONV.Abs rfl ?_
      refine ihb names ((s', (x, ty)) :: env) ⟨by simpa using h1, ?_, ?_, ?_, wb⟩
      · rw [Aux.DISJOINT_iff]
        simp only [Aux.mem_LIST_TO_SET, List.map_cons, Function.comp, List.cons_append,
          List.mem_append, List.mem_cons, not_or]
        intro y hy
        have := h2 y (by grind)
        exact ⟨this.2.1, this.1, this.2.2⟩
      · rw [Aux.DISJOINT_iff]
        simp only [Aux.mem_LIST_TO_SET, List.map_cons, List.cons_append, List.mem_append,
          List.mem_cons]
        rintro y hy ⟨t, h⟩
        have hy' : y ∈ env.map Prod.fst ∨ y = s' ∨ y ∈ names := by grind
        by_cases e : Var x ty = Var y t
        · exact (h2 y hy').2.1 (term.Var.inj e).1.symm
        · exact h3 y hy' ⟨t, e, h⟩
      · rw [Aux.ALL_DISTINCT_iff_nodup]
        simp only [List.map_cons, List.cons_append]
        exact (List.perm_middle.nodup_iff).mp h4

/- HOL4:
Theorem rename_bvars_ACONV:
   ∀names tm.
    LENGTH (bv_names tm) ≤ LENGTH names ∧ ALL_DISTINCT names ∧
    DISJOINT (set names) {x | MEM x (bv_names tm) ∨ ∃ty. VFREE_IN (Var x ty) tm} ∧
    welltyped tm
    ⇒
    ACONV tm (SND (rename_bvars names [] tm)) -/
theorem rename_bvars_ACONV :
    ∀ (names : List mlstring) (tm : term),
      (bv_names tm).length ≤ names.length ∧ ALL_DISTINCT names ∧
      DISJOINT (LIST_TO_SET names)
        (setOf (fun (x : mlstring) => x ∈ bv_names tm ∨ ∃ (ty : type), VFREE_IN (Var x ty) tm)) ∧
      welltyped tm
      →
      ACONV tm (rename_bvars names [] tm).2 := by
  rintro names tm ⟨h1, h2, h3, hw⟩
  rw [Aux.DISJOINT_iff] at h3
  refine rename_bvars_RACONV names [] tm ⟨h1, ?_, ?_, ?_, hw⟩
  · rw [Aux.DISJOINT_iff]
    intro x hx hm
    exact h3 x hx (Or.inl ((Aux.mem_LIST_TO_SET _ _).mp hm))
  · rw [Aux.DISJOINT_iff]
    intro x hx hm
    exact h3 x hx (Or.inr hm)
  · exact h2

/- HOL4:
Theorem rename_bvars_has_type:
   ∀names env tm ty. tm has_type ty ⇒ SND (rename_bvars names env tm) has_type ty -/
theorem rename_bvars_has_type :
    ∀ (names : List mlstring) (env : List (mlstring × (mlstring × type))) (tm : term) (ty : type),
        has_type tm ty → has_type (rename_bvars names env tm).2 ty := by
  intro names env tm
  induction tm generalizing names env with
  | Var x t =>
    intro ty h
    cases h
    exact has_type.Var
  | Const x t => intro ty h; exact h
  | Comb a b iha ihb =>
    intro ty h
    cases h with
    | Comb h1 h2 => exact has_type.Comb (iha names env _ h1) (ihb _ env _ h2)
  | Abs v b _ ihb =>
    intro ty h
    cases h with
    | Abs h =>
      cases names with
      | nil => exact has_type.Abs (ihb [] env _ h)
      | cons s names => exact has_type.Abs (ihb names _ _ h)

/- HOL4:
Theorem rename_bvars_welltyped:
   ∀names env tm. welltyped tm ⇒ welltyped (SND (rename_bvars names env tm)) -/
theorem rename_bvars_welltyped :
    ∀ (names : List mlstring) (env : List (mlstring × (mlstring × type))) (tm : term),
        welltyped tm → welltyped (rename_bvars names env tm).2 := by
  rintro names env tm ⟨ty, h⟩
  exact ⟨ty, rename_bvars_has_type names env tm ty h⟩

theorem Aux.FINITE_UNION {α : Type u} {s t : Set α} (hs : FINITE s) (ht : FINITE t) :
    FINITE (UNION s t) := by
  obtain ⟨l1, h1⟩ := Aux.FINITE_list_bound s hs
  obtain ⟨l2, h2⟩ := Aux.FINITE_list_bound t ht
  refine Aux.FINITE_of_list_bound (l1 ++ l2) _ ?_
  rintro x (h | h)
  · exact List.mem_append_left _ (h1 x h)
  · exact List.mem_append_right _ (h2 x h)

theorem Aux.FINITE_LIST_TO_SET {α : Type u} (l : List α) : FINITE (LIST_TO_SET l) :=
  Aux.FINITE_of_list_bound l _ (fun x hx => (Aux.mem_LIST_TO_SET x l).mp hx)

/- HOL4:
Theorem fresh_union:
   FINITE s ∧ FINITE t ⇒ fresh (s ∪ t) ∉ s ∧ fresh (s ∪ t) ∉ t -/
theorem fresh_union (s t : Set string) :
    FINITE s ∧ FINITE t → fresh (UNION s t) ∉ s ∧ fresh (UNION s t) ∉ t := by
  rintro ⟨hs, ht⟩
  have h := fresh_def (UNION s t) (Aux.FINITE_UNION hs ht)
  exact ⟨fun h1 => h (Or.inl h1), fun h1 => h (Or.inr h1)⟩

/- HOL4:
Theorem fresh_names_exist:
   ∀s n. FINITE (s:string set) ⇒ ∃names. LENGTH names = n ∧ ALL_DISTINCT names ∧ DISJOINT (set names) s -/
theorem fresh_names_exist :
    ∀ (s : Set string) (n : Nat), FINITE s →
        ∃ (names : List string), names.length = n ∧ ALL_DISTINCT names ∧ DISJOINT (LIST_TO_SET names) s := by
  intro s n hs
  induction n with
  | zero =>
    refine ⟨[], rfl, trivial, ?_⟩
    rw [Aux.DISJOINT_iff]
    intro x hx
    exact hx.elim
  | succ n ih =>
    obtain ⟨names, h1, h2, h3⟩ := ih
    have hf := fresh_union s (LIST_TO_SET names) ⟨hs, Aux.FINITE_LIST_TO_SET names⟩
    refine ⟨fresh (UNION s (LIST_TO_SET names)) :: names, by simp [h1], ⟨?_, h2⟩, ?_⟩
    · intro h
      exact hf.2 ((Aux.mem_LIST_TO_SET _ _).mpr h)
    · rw [Aux.DISJOINT_iff] at h3 ⊢
      rintro x (rfl | hx)
      · exact hf.1
      · exact h3 x hx

/- HOL4:
Theorem bv_names_rename_bvars:
   ∀names env tm.
    LENGTH (bv_names tm) ≤ LENGTH names ⇒
    bv_names (SND (rename_bvars names env tm)) = TAKE (LENGTH (bv_names tm)) names -/
theorem bv_names_rename_bvars :
    ∀ (names : List mlstring) (env : List (mlstring × (mlstring × type))) (tm : term),
      (bv_names tm).length ≤ names.length →
      bv_names (rename_bvars names env tm).2 = names.take (bv_names tm).length := by
  intro names env tm
  induction tm generalizing names env with
  | Var x ty => intro _; simp [rename_bvars, bv_names]
  | Const x ty => intro _; simp [rename_bvars, bv_names]
  | Comb a b iha ihb =>
    intro h
    simp only [bv_names, List.length_append] at h
    have hd : (rename_bvars names env a).1 = names.drop (bv_names a).length :=
      FST_rename_bvars names env a (by omega)
    simp only [rename_bvars, bv_names, List.length_append]
    rw [iha names env (by omega), hd, ihb _ env (by rw [List.length_drop]; omega), List.take_add]
  | Abs v b _ ihb =>
    intro h
    simp only [bv_names, List.length_cons] at h
    cases names with
    | nil => simp at h
    | cons s names =>
      simp only [rename_bvars, bv_names, dest_var_def, List.length_cons, List.take_succ_cons]
      rw [ihb names _ (by simpa using h)]

/- HOL4:
Theorem FINITE_VFREE_IN[simp]:
   ∀tm. FINITE {x | ∃ty. VFREE_IN (Var x ty) tm} -/
theorem FINITE_VFREE_IN :
    ∀ (tm : term), FINITE (setOf (fun (x : mlstring) => ∃ (ty : type), VFREE_IN (Var x ty) tm)) := by
  intro tm
  obtain ⟨l, hl⟩ := Aux.frees_list tm
  refine Aux.FINITE_of_list_bound (l.map (fun t => (dest_var t).1)) _ ?_
  rintro x ⟨ty, h⟩
  exact List.mem_map.mpr ⟨_, hl _ h, by rw [dest_var_def]⟩

/- HOL4:
Theorem FINITE_VFREE_IN_2[simp]:
   ∀tm. FINITE {(x,ty) | VFREE_IN (Var x ty) tm} -/
theorem FINITE_VFREE_IN_2 :
    ∀ (tm : term), FINITE (GSPEC (fun (p : mlstring × type) => ((p.1, p.2), VFREE_IN (Var p.1 p.2) tm))) := by
  intro tm
  obtain ⟨l, hl⟩ := Aux.frees_list tm
  refine Aux.FINITE_of_list_bound (l.map dest_var) _ ?_
  intro x hx
  rw [Aux.mem_GSPEC] at hx
  obtain ⟨p, rfl, h⟩ := hx
  exact List.mem_map.mpr ⟨_, hl _ h, by rw [dest_var_def]⟩

theorem Aux.frees_list_list (ls : List term) :
    ∃ l : List term, ∀ x u, VFREE_IN x u → u ∈ ls → x ∈ l := by
  induction ls with
  | nil => exact ⟨[], fun x u _ hu => by simp at hu⟩
  | cons a t ih =>
    obtain ⟨l1, h1⟩ := ih
    obtain ⟨l2, h2⟩ := Aux.frees_list a
    refine ⟨l2 ++ l1, fun x u h hu => ?_⟩
    rcases List.mem_cons.mp hu with rfl | hu
    · exact List.mem_append_left _ (h2 x h)
    · exact List.mem_append_right _ (h1 x u h hu)

/- HOL4:
Theorem FINITE_VFREE_IN_list[simp]:
   ∀ls. FINITE {x | ∃ty u. VFREE_IN (Var x ty) u ∧ MEM u ls} -/
theorem FINITE_VFREE_IN_list :
    ∀ (ls : List term),
        FINITE (setOf (fun (x : mlstring) => ∃ (ty : type) (u : term), VFREE_IN (Var x ty) u ∧ u ∈ ls)) := by
  intro ls
  obtain ⟨l, hl⟩ := Aux.frees_list_list ls
  refine Aux.FINITE_of_list_bound (l.map (fun t => (dest_var t).1)) _ ?_
  rintro x ⟨ty, u, h, hu⟩
  exact List.mem_map.mpr ⟨_, hl _ u h hu, by rw [dest_var_def]⟩

/- HOL4:
Theorem FINITE_MEM_Var[simp]:
   ∀ls. FINITE {(x,ty) | MEM (Var x ty) ls} -/
theorem FINITE_MEM_Var :
    ∀ (ls : List term), FINITE (GSPEC (fun (p : mlstring × type) => ((p.1, p.2), Var p.1 p.2 ∈ ls))) := by
  intro ls
  refine Aux.FINITE_of_list_bound (ls.map dest_var) _ ?_
  intro x hx
  rw [Aux.mem_GSPEC] at hx
  obtain ⟨p, rfl, h⟩ := hx
  exact List.mem_map.mpr ⟨_, h, by rw [dest_var_def]⟩

/- HOL4:
Theorem theory_ok_sig:
   ∀thy. theory_ok thy ⇒ is_std_sig (sigof thy) -/
theorem theory_ok_sig :
    ∀ (thy : thy), theory_ok thy → is_std_sig (sigof thy) := by
  intro thy h
  exact h.2.2

/- HOL4:
Theorem arities_match_nil[simp]:
   (arities_match [] ls = (ls = [])) ∧
    (arities_match ls [] = (ls = [])) -/
theorem arities_match_nil (ls : List type) :
    (arities_match [] ls = (ls = [])) ∧
      (arities_match ls [] = (ls = [])) := by
  cases ls <;> simp [arities_match]

/- HOL4:
Theorem arities_match_Tyvar[simp]:
   arities_match (Tyvar v::ps) (ty::obs) = arities_match ps obs -/
theorem arities_match_Tyvar (v : mlstring) (ps : List type) (ty : type) (obs : List type) :
    arities_match (Tyvar v :: ps) (ty :: obs) = arities_match ps obs := by
  cases ty <;> simp [arities_match]

end

end Candle
