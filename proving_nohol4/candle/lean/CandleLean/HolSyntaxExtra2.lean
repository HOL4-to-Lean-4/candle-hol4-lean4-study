/-
  HOL4 theory `holSyntaxExtra` (candle/standard/syntax/holSyntaxExtraScript.sml):
  target theorems, second part (split from `HolSyntaxExtra.lean` for parallel translation).
-/
import CandleLean.HolSyntaxExtra

namespace Candle

open HOL Classical

noncomputable section

universe u

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
    simp only [VSUBST, VFREE_IN]
    constructor
    · intro h; exact ⟨x, ty, rfl, h⟩
    · rintro ⟨y, ty', e, h⟩
      cases e
      exact h
  | Const x ty =>
    intro ilist _
    simp [VSUBST, VFREE_IN]
  | Comb s t ihs iht =>
    intro ilist hw
    obtain ⟨h1, h2, _⟩ := Aux.welltyped_Comb hw
    simp only [VSUBST, VFREE_IN]
    rw [ihs ilist h1, iht ilist h2]
    constructor
    · rintro (⟨y, ty, ha, hb⟩ | ⟨y, ty, ha, hb⟩)
      · exact ⟨y, ty, Or.inl ha, hb⟩
      · exact ⟨y, ty, Or.inr ha, hb⟩
    · rintro ⟨y, ty, ha | ha, hb⟩
      · exact Or.inl ⟨y, ty, ha, hb⟩
      · exact Or.inr ⟨y, ty, ha, hb⟩
  | Abs v t _ iht =>
    intro ilist hw
    obtain ⟨n, nty, rfl, hwt⟩ := Aux.welltyped_Abs hw
    have hf : ∀ a b : term, REV_ASSOCD a (FILTER (fun p : term × term => ¬ p.2 = Var n nty) ilist) b =
        if ¬ a = Var n nty then REV_ASSOCD a ilist b else b := by
      intro a b
      refine (REV_ASSOCD_FILTER (fun s => ¬ s = Var n nty) ilist a b ()).trans ?_
      by_cases h : a = Var n nty <;> simp [h]
    simp only [VSUBST, dest_var_def]
    split
    · simp only [VFREE_IN]
      rw [iht _ hwt]
      have hvar := VARIANT_THM (VSUBST (FILTER (fun p : term × term => ¬ p.2 = Var n nty) ilist) t)
        (explode n) nty
      generalize VARIANT (VSUBST (FILTER (fun p : term × term => ¬ p.2 = Var n nty) ilist) t)
        (explode n) nty = z at hvar ⊢
      constructor
      · rintro ⟨h1, y, ty, h2, h3⟩
        by_cases hy : Var n nty = Var y ty
        · simp only [REV_ASSOCD, hy, if_true, VFREE_IN] at h3
          exact absurd h3 h1
        · have hy' : ¬ Var y ty = Var n nty := fun e => hy e.symm
          simp only [REV_ASSOCD, hy, if_false, hf, hy', not_false_eq_true, if_true] at h3
          exact ⟨y, ty, ⟨hy, h2⟩, h3⟩
      · rintro ⟨y, ty, ⟨h1, h2⟩, h3⟩
        have hy' : ¬ Var y ty = Var n nty := fun e => h1 e.symm
        refine ⟨?_, y, ty, h2, ?_⟩
        · intro e
          cases e
          refine hvar ((iht _ hwt).mpr ⟨y, ty, h2, ?_⟩)
          simp only [hf, hy', not_false_eq_true, if_true]
          exact h3
        · simp only [REV_ASSOCD, h1, if_false, hf, hy', not_false_eq_true, if_true]
          exact h3
    · rename_i hc
      rw [Aux.EXISTS_iff] at hc
      simp only [VFREE_IN]
      rw [iht _ hwt]
      constructor
      · rintro ⟨h1, y, ty, h2, h3⟩
        by_cases hy : Var n nty = Var y ty
        · rw [hf, if_neg (by simp [hy])] at h3
          simp only [VFREE_IN] at h3
          exact absurd (hy.trans h3) h1
        · have hy' : ¬ Var y ty = Var n nty := fun e => hy e.symm
          simp only [hf, hy', not_false_eq_true, if_true] at h3
          exact ⟨y, ty, ⟨hy, h2⟩, h3⟩
      · rintro ⟨y, ty, ⟨h1, h2⟩, h3⟩
        have hy' : ¬ Var y ty = Var n nty := fun e => h1 e.symm
        refine ⟨?_, y, ty, h2, ?_⟩
        · intro e
          rcases REV_ASSOCD_MEM ilist (Var y ty) (Var y ty) with hm | hm
          · refine hc ⟨_, Aux.mem_FILTER.mpr ⟨hm, hy'⟩, ?_, h2⟩
            rw [e]; exact h3
          · rw [hm] at h3
            simp only [VFREE_IN] at h3
            exact h1 (e.trans h3.symm)
        · simp only [hf, hy', not_false_eq_true, if_true]
          exact h3

/- HOL4:
Theorem VSUBST_NIL[simp]:
   ∀tm. VSUBST [] tm = tm -/
theorem VSUBST_NIL :
    ∀ (tm : term), VSUBST [] tm = tm := by
  intro tm
  induction tm with
  | Var x ty => rfl
  | Const x ty => rfl
  | Comb s t ihs iht => simp [VSUBST, ihs, iht]
  | Abs v t _ iht => simp [VSUBST, FILTER, EXISTS, iht]

theorem Aux.INST_CORE_Comb_cases (env : List (term × term)) (tyin : List (type × type))
    (s t : term) :
    (∃ w, INST_CORE env tyin s = Clash w ∧ INST_CORE env tyin (Comb s t) = Clash w) ∨
    (∃ s' w, INST_CORE env tyin s = Result s' ∧ INST_CORE env tyin t = Clash w ∧
      INST_CORE env tyin (Comb s t) = Clash w) ∨
    (∃ s' t', INST_CORE env tyin s = Result s' ∧ INST_CORE env tyin t = Result t' ∧
      INST_CORE env tyin (Comb s t) = Result (Comb s' t')) := by
  rw [INST_CORE]
  cases hs : INST_CORE env tyin s with
  | Clash w => left; exact ⟨w, rfl, by simp [IS_CLASH]⟩
  | Result s' =>
    right
    cases ht : INST_CORE env tyin t with
    | Clash w => left; exact ⟨s', w, rfl, rfl, by simp [IS_CLASH]⟩
    | Result t' => right; exact ⟨s', t', rfl, rfl, by simp [IS_CLASH, RESULT_def]⟩

/-- the new name chosen by `INST_CORE` when the bound variable clashes -/
def Aux.newname (tyin : List (type × type)) (x : mlstring) (ty : type) (t : term) : mlstring :=
  VARIANT (RESULT (INST_CORE [] tyin t)) (explode x) (TYPE_SUBST tyin ty)

theorem Aux.INST_CORE_Abs_cases (env : List (term × term)) (tyin : List (type × type))
    (x : mlstring) (ty : type) (t : term) :
    (∃ r, INST_CORE ((Var x ty, Var x (TYPE_SUBST tyin ty)) :: env) tyin t = Result r ∧
      INST_CORE env tyin (Abs (Var x ty) t) = Result (Abs (Var x (TYPE_SUBST tyin ty)) r)) ∨
    (∃ w, INST_CORE ((Var x ty, Var x (TYPE_SUBST tyin ty)) :: env) tyin t = Clash w ∧
      w ≠ Var x (TYPE_SUBST tyin ty) ∧ INST_CORE env tyin (Abs (Var x ty) t) = Clash w) ∨
    (∃ r, INST_CORE ((Var (Aux.newname tyin x ty t) ty,
        Var (Aux.newname tyin x ty t) (TYPE_SUBST tyin ty)) :: env) tyin
        (VSUBST [(Var (Aux.newname tyin x ty t) ty, Var x ty)] t) = Result r ∧
      INST_CORE env tyin (Abs (Var x ty) t) =
        Result (Abs (Var (Aux.newname tyin x ty t) (TYPE_SUBST tyin ty)) r)) ∨
    (∃ w, INST_CORE ((Var (Aux.newname tyin x ty t) ty,
        Var (Aux.newname tyin x ty t) (TYPE_SUBST tyin ty)) :: env) tyin
        (VSUBST [(Var (Aux.newname tyin x ty t) ty, Var x ty)] t) = Clash w ∧
      INST_CORE env tyin (Abs (Var x ty) t) = Clash w) := by
  rw [INST_CORE]
  simp only [dest_var_def]
  cases h1 : INST_CORE ((Var x ty, Var x (TYPE_SUBST tyin ty)) :: env) tyin t with
  | Result r => left; exact ⟨r, rfl, by simp [IS_RESULT, RESULT_def]⟩
  | Clash w =>
    right
    by_cases hw : w = Var x (TYPE_SUBST tyin ty)
    · right
      simp only [IS_RESULT, if_false, CLASH_def, hw, ne_eq, not_true_eq_false]
      change (∃ r, _ ∧ (if IS_RESULT (INST_CORE ((Var (Aux.newname tyin x ty t) ty,
        Var (Aux.newname tyin x ty t) (TYPE_SUBST tyin ty)) :: env) tyin
        (VSUBST [(Var (Aux.newname tyin x ty t) ty, Var x ty)] t)) then _ else _) = _) ∨
        (∃ r, _ ∧ (if IS_RESULT (INST_CORE ((Var (Aux.newname tyin x ty t) ty,
        Var (Aux.newname tyin x ty t) (TYPE_SUBST tyin ty)) :: env) tyin
        (VSUBST [(Var (Aux.newname tyin x ty t) ty, Var x ty)] t)) then _ else _) = _)
      cases h2 : INST_CORE ((Var (Aux.newname tyin x ty t) ty,
        Var (Aux.newname tyin x ty t) (TYPE_SUBST tyin ty)) :: env) tyin
        (VSUBST [(Var (Aux.newname tyin x ty t) ty, Var x ty)] t) with
      | Result r =>
        left
        refine ⟨r, rfl, ?_⟩
        simp only [IS_RESULT, if_true]
        have : RESULT (INST_CORE ((Var (Aux.newname tyin x ty t) ty,
          Var (Aux.newname tyin x ty t) (TYPE_SUBST tyin ty)) :: env) tyin
          (VSUBST [(Var (Aux.newname tyin x ty t) ty, Var x ty)] t)) = r := by
          rw [h2, RESULT_def]
        exact congrArg (fun r => Result (Abs (Var (Aux.newname tyin x ty t)
          (TYPE_SUBST tyin ty)) r)) this
      | Clash w =>
        right
        refine ⟨w, rfl, ?_⟩
        simp only [IS_RESULT, if_false]
        exact h2
    · left
      exact ⟨w, rfl, hw, by simp [IS_RESULT, CLASH_def, hw]⟩

theorem Aux.TYPE_SUBST_Fun (tyin : List (type × type)) (a b : type) :
    TYPE_SUBST tyin (Fun a b) = Fun (TYPE_SUBST tyin a) (TYPE_SUBST tyin b) := by
  simp [TYPE_SUBST]

theorem Aux.sizeof_VSUBST_var (x x' : mlstring) (ty : type) (t : term) :
    sizeof (VSUBST [(Var x' ty, Var x ty)] t) = sizeof t := by
  apply SIZEOF_VSUBST
  intro s' s h
  rcases List.mem_singleton.mp h with h
  cases h
  exact ⟨_, _, rfl⟩

theorem Aux.VSUBST_var_has_type (x x' : mlstring) (ty : type) (t : term) (h : welltyped t) :
    has_type (VSUBST [(Var x' ty, Var x ty)] t) (typeof t) := by
  refine VSUBST_HAS_TYPE t _ _ ⟨(WELLTYPED t).mp h, ?_⟩
  intro s s' h
  rcases List.mem_singleton.mp h with h
  cases h
  exact ⟨x, ty, rfl, has_type.Var⟩

theorem Aux.VFREE_IN_VSUBST_var (x x' : mlstring) (ty : type) (t : term) (h : welltyped t)
    (u : mlstring) (uty : type) :
    VFREE_IN (Var u uty) (VSUBST [(Var x' ty, Var x ty)] t) ↔
      (VFREE_IN (Var x ty) t ∧ Var x' ty = Var u uty) ∨
      (¬ Var x ty = Var u uty ∧ VFREE_IN (Var u uty) t) := by
  rw [VFREE_IN_VSUBST t u uty _ h]
  constructor
  · rintro ⟨y, yty, h1, h2⟩
    by_cases hy : Var x ty = Var y yty
    · left
      simp only [REV_ASSOCD, hy, if_true, VFREE_IN] at h2
      rw [hy]
      exact ⟨h1, h2⟩
    · right
      simp only [REV_ASSOCD, hy, if_false, VFREE_IN] at h2
      rw [← h2]
      exact ⟨hy, h1⟩
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact ⟨x, ty, h1, by simpa [REV_ASSOCD, VFREE_IN] using h2⟩
    · exact ⟨u, uty, h2, by simp [REV_ASSOCD, h1, VFREE_IN]⟩

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
  | ind n ih =>
  intro tm env tyin ⟨hw, hn, henv⟩
  subst hn
  cases tm with
  | Var x ty =>
    rw [INST_CORE]
    by_cases hc : REV_ASSOCD (Var x (TYPE_SUBST tyin ty)) env (Var x ty) = Var x ty
    · right
      refine ⟨?_, Var x (TYPE_SUBST tyin ty), by simp [hc], has_type.Var, ?_⟩
      · intro y yty h
        simp only [VFREE_IN] at h
        cases h
        exact hc
      · intro u uty
        simp only [VFREE_IN, term.Var.injEq]
        constructor
        · rintro ⟨rfl, rfl⟩; exact ⟨ty, ⟨rfl, rfl⟩, rfl⟩
        · rintro ⟨oty, ⟨rfl, rfl⟩, rfl⟩; exact ⟨rfl, rfl⟩
    · left
      exact ⟨x, ty, by simp [hc], rfl, hc⟩
  | Const x ty =>
    right
    rw [INST_CORE]
    refine ⟨?_, _, rfl, has_type.Const, ?_⟩
    · intro y yty h; simp [VFREE_IN] at h
    · intro u uty; simp [VFREE_IN]
  | Comb s t =>
    obtain ⟨hws, hwt, rty, hty⟩ := Aux.welltyped_Comb hw
    have is := ih (sizeof s) (by simp only [sizeof]; omega) s env tyin ⟨hws, rfl, henv⟩
    have it := ih (sizeof t) (by simp only [sizeof]; omega) t env tyin ⟨hwt, rfl, henv⟩
    rcases Aux.INST_CORE_Comb_cases env tyin s t with ⟨w, h1, h2⟩ | ⟨s', w, h1, h2, h3⟩ |
      ⟨s', t', h1, h2, h3⟩
    · left
      rcases is with ⟨x, ty, e, hf, hr⟩ | ⟨_, r, e, _⟩
      · rw [h1] at e
        cases e
        exact ⟨x, ty, h2, Or.inl hf, hr⟩
      · rw [h1] at e; cases e
    · left
      rcases it with ⟨x, ty, e, hf, hr⟩ | ⟨_, r, e, _⟩
      · rw [h2] at e
        cases e
        exact ⟨x, ty, h3, Or.inr hf, hr⟩
      · rw [h2] at e; cases e
    · right
      rcases is with ⟨x, ty, e, _⟩ | ⟨hs1, r, e, hs2, hs3⟩
      · rw [h1] at e; cases e
      rw [h1] at e
      cases e
      rcases it with ⟨x, ty, e, _⟩ | ⟨ht1, r, e, ht2, ht3⟩
      · rw [h2] at e; cases e
      rw [h2] at e
      cases e
      refine ⟨?_, _, h3, ?_, ?_⟩
      · rintro x ty (h | h)
        · exact hs1 x ty h
        · exact ht1 x ty h
      · rw [hty, Aux.TYPE_SUBST_Fun] at hs2
        simp only [typeof, hty, codomain_def]
        exact has_type.Comb hs2 ht2
      · intro u uty
        simp only [VFREE_IN]
        rw [hs3, ht3]
        constructor
        · rintro (⟨oty, ha, hb⟩ | ⟨oty, ha, hb⟩)
          · exact ⟨oty, Or.inl ha, hb⟩
          · exact ⟨oty, Or.inr ha, hb⟩
        · rintro ⟨oty, ha | ha, hb⟩
          · exact Or.inl ⟨oty, ha, hb⟩
          · exact Or.inr ⟨oty, ha, hb⟩
  | Abs v t =>
    obtain ⟨x, ty, rfl, hwt⟩ := Aux.welltyped_Abs hw
    have hlt : sizeof t < sizeof (Abs (Var x ty) t) := by simp only [sizeof]; omega
    have henv1 : ∀ z : mlstring, ∀ (s s' : term),
        (s, s') ∈ (Var z ty, Var z (TYPE_SUBST tyin ty)) :: env →
        ∃ (x : mlstring) (ty : type), s = Var x ty ∧ s' = Var x (TYPE_SUBST tyin ty) := by
      intro z s s' hm
      rcases List.mem_cons.mp hm with hm | hm
      · cases hm; exact ⟨z, ty, rfl, rfl⟩
      · exact henv s s' hm
    have it := ih (sizeof t) hlt t _ tyin ⟨hwt, rfl, henv1 x⟩
    -- freshness of the new name
    have hfresh : ∀ oty, VFREE_IN (Var (Aux.newname tyin x ty t) oty) t →
        ¬ TYPE_SUBST tyin ty = TYPE_SUBST tyin oty := by
      intro oty hf e
      rcases ih (sizeof t) hlt t [] tyin ⟨hwt, rfl, by simp⟩ with ⟨y, yty, _, _, hr⟩ |
        ⟨_, r, e1, _, h3⟩
      · exact hr rfl
      · refine VARIANT_THM (RESULT (INST_CORE [] tyin t)) (explode x) (TYPE_SUBST tyin ty) ?_
        change VFREE_IN (Var (Aux.newname tyin x ty t) (TYPE_SUBST tyin ty)) _
        have e2 : RESULT (INST_CORE [] tyin t) = r := by rw [e1, RESULT_def]
        rw [e2, h3]
        exact ⟨oty, hf, e⟩
    have it' := ih (sizeof t) hlt (VSUBST [(Var (Aux.newname tyin x ty t) ty, Var x ty)] t)
      _ tyin ⟨⟨_, Aux.VSUBST_var_has_type x _ ty t hwt⟩, Aux.sizeof_VSUBST_var _ _ _ _,
        henv1 (Aux.newname tyin x ty t)⟩
    have hfv := Aux.VFREE_IN_VSUBST_var x (Aux.newname tyin x ty t) ty t hwt
    have htyp := WELLTYPED_LEMMA _ _ (Aux.VSUBST_var_has_type x (Aux.newname tyin x ty t) ty t hwt)
    rcases Aux.INST_CORE_Abs_cases env tyin x ty t with ⟨r, h1, h2⟩ | ⟨w, h1, hne, h2⟩ |
      ⟨r, h1, h2⟩ | ⟨w, h1, h2⟩
    · right
      rcases it with ⟨_, _, e, _⟩ | ⟨ha, r', e, hb, hc⟩
      · rw [h1] at e; cases e
      rw [h1] at e
      cases e
      have key : ∀ y yty, VFREE_IN (Var y yty) t → ¬ Var x ty = Var y yty →
          ¬ Var x (TYPE_SUBST tyin ty) = Var y (TYPE_SUBST tyin yty) := by
        intro y yty hf hne e
        have := ha y yty hf
        simp only [REV_ASSOCD, e, if_true] at this
        exact hne this
      refine ⟨?_, _, h2, ?_, ?_⟩
      · rintro y yty ⟨hne, hf⟩
        have := ha y yty hf
        simp only [REV_ASSOCD, key y yty hf hne, if_false] at this
        exact this
      · simp only [typeof]
        rw [Aux.TYPE_SUBST_Fun]
        exact has_type.Abs hb
      · intro u uty
        simp only [VFREE_IN]
        rw [hc]
        constructor
        · rintro ⟨hne, oty, hf, rfl⟩
          refine ⟨oty, ⟨fun e => hne ?_, hf⟩, rfl⟩
          cases e; rfl
        · rintro ⟨oty, ⟨hne, hf⟩, rfl⟩
          exact ⟨key u oty hf hne, oty, hf, rfl⟩
    · left
      rcases it with ⟨y, yty, e, hf, hr⟩ | ⟨_, r', e, _⟩
      · rw [h1] at e
        cases e
        have hne' : ¬ Var x (TYPE_SUBST tyin ty) = Var y (TYPE_SUBST tyin yty) :=
          fun e => hne e.symm
        refine ⟨y, yty, h2, ⟨fun e => hne' ?_, hf⟩, ?_⟩
        · cases e; rfl
        · simp only [REV_ASSOCD, hne', if_false] at hr
          exact hr
      · rw [h1] at e; cases e
    · right
      rcases it' with ⟨_, _, e, _⟩ | ⟨ha, r', e, hb, hc⟩
      · rw [h1] at e; cases e
      rw [h1] at e
      cases e
      generalize Aux.newname tyin x ty t = x' at *
      have key : ∀ y yty, VFREE_IN (Var y yty) t →
          ¬ Var x' (TYPE_SUBST tyin ty) = Var y (TYPE_SUBST tyin yty) := by
        intro y yty hf e
        injection e with e1 e2
        subst e1
        exact hfresh yty hf e2
      refine ⟨?_, _, h2, ?_, ?_⟩
      · rintro y yty ⟨hne, hf⟩
        have := ha y yty ((hfv y yty).mpr (Or.inr ⟨hne, hf⟩))
        simp only [REV_ASSOCD, key y yty hf, if_false] at this
        exact this
      · simp only [typeof]
        rw [Aux.TYPE_SUBST_Fun]
        rw [htyp] at hb
        exact has_type.Abs hb
      · intro u uty
        simp only [VFREE_IN]
        rw [hc]
        constructor
        · rintro ⟨hne, oty, hf, rfl⟩
          rcases (hfv u oty).mp hf with ⟨_, e⟩ | ⟨h3, h4⟩
          · exact absurd (by cases e; rfl) hne
          · exact ⟨oty, ⟨h3, h4⟩, rfl⟩
        · rintro ⟨oty, ⟨hne, hf⟩, rfl⟩
          exact ⟨key u oty hf, oty, (hfv u oty).mpr (Or.inr ⟨hne, hf⟩), rfl⟩
    · left
      rcases it' with ⟨y, yty, e, hf, hr⟩ | ⟨_, r', e, _⟩
      · rw [h1] at e
        cases e
        generalize Aux.newname tyin x ty t = x' at *
        rcases (hfv y yty).mp hf with ⟨_, e⟩ | ⟨h3, h4⟩
        · exfalso
          cases e
          exact hr (by simp [REV_ASSOCD])
        · refine ⟨y, yty, h2, ⟨h3, h4⟩, ?_⟩
          have hne : ¬ Var x' (TYPE_SUBST tyin ty) = Var y (TYPE_SUBST tyin yty) := by
            intro e
            injection e with e1 e2
            subst e1
            exact hfresh yty h4 e2
          simp only [REV_ASSOCD, hne, if_false] at hr
          exact hr
      · rw [h1] at e; cases e

theorem Aux.INST_CORE_nil {tyin : List (type × type)} {tm : term} (h : welltyped tm) :
    ∃ r, INST_CORE [] tyin tm = Result r ∧ has_type r (TYPE_SUBST tyin (typeof tm)) ∧
      ∀ u uty, VFREE_IN (Var u uty) r ↔
        ∃ oty, VFREE_IN (Var u oty) tm ∧ uty = TYPE_SUBST tyin oty := by
  rcases INST_CORE_HAS_TYPE _ tm [] tyin ⟨h, rfl, by simp⟩ with ⟨_, _, _, _, hr⟩ | ⟨_, r, h1, h2, h3⟩
  · exact absurd rfl hr
  · exact ⟨r, h1, h2, h3⟩

theorem Aux.newname_fresh {tyin : List (type × type)} {x : mlstring} {ty : type} {t : term}
    (h : welltyped t) (oty : type) (hf : VFREE_IN (Var (Aux.newname tyin x ty t) oty) t) :
    ¬ TYPE_SUBST tyin oty = TYPE_SUBST tyin ty := by
  intro e
  obtain ⟨r, e1, _, h3⟩ := Aux.INST_CORE_nil (tyin := tyin) h
  refine VARIANT_THM (RESULT (INST_CORE [] tyin t)) (explode x) (TYPE_SUBST tyin ty) ?_
  change VFREE_IN (Var (Aux.newname tyin x ty t) (TYPE_SUBST tyin ty)) _
  have e2 : RESULT (INST_CORE [] tyin t) = r := by rw [e1, RESULT_def]
  rw [e2, h3]
  exact ⟨oty, hf, e.symm⟩

theorem Aux.INST_eq {tyin : List (type × type)} {tm : term} (h : welltyped tm) :
    INST_CORE [] tyin tm = Result (INST tyin tm) := by
  obtain ⟨r, h1, _⟩ := Aux.INST_CORE_nil (tyin := tyin) h
  unfold INST
  rw [h1, RESULT_def]

/- HOL4:
Theorem INST_CORE_NIL_IS_RESULT:
   ∀tyin tm. welltyped tm ⇒ IS_RESULT (INST_CORE [] tyin tm) -/
theorem INST_CORE_NIL_IS_RESULT :
    ∀ (tyin : List (type × type)) (tm : term), welltyped tm → IS_RESULT (INST_CORE [] tyin tm) := by
  intro tyin tm h
  rw [Aux.INST_eq h]
  exact trivial

/- HOL4:
Theorem INST_HAS_TYPE:
   ∀tm ty tyin ty'. tm has_type ty ∧ ty' = TYPE_SUBST tyin ty ⇒ INST tyin tm has_type ty' -/
theorem INST_HAS_TYPE :
    ∀ (tm : term) (ty : type) (tyin : List (type × type)) (ty' : type),
        has_type tm ty ∧ ty' = TYPE_SUBST tyin ty → has_type (INST tyin tm) ty' := by
  rintro tm ty tyin _ ⟨h, rfl⟩
  obtain ⟨r, h1, h2, _⟩ := Aux.INST_CORE_nil (tyin := tyin) ⟨ty, h⟩
  rw [WELLTYPED_LEMMA _ _ h] at h2
  unfold INST
  rw [h1, RESULT_def]
  exact h2

/- HOL4:
Theorem INST_WELLTYPED:
   ∀tm tyin.  welltyped tm ⇒ welltyped (INST tyin tm) -/
theorem INST_WELLTYPED :
    ∀ (tm : term) (tyin : List (type × type)), welltyped tm → welltyped (INST tyin tm) := by
  rintro tm tyin ⟨ty, h⟩
  exact ⟨_, INST_HAS_TYPE tm ty tyin _ ⟨h, rfl⟩⟩

/- HOL4:
Theorem tyvars_ALL_DISTINCT[simp]:
   ∀ty. ALL_DISTINCT (tyvars ty) -/
theorem tyvars_ALL_DISTINCT :
    ∀ (ty : type), ALL_DISTINCT (tyvars ty) := by
  intro ty
  cases ty with
  | Tyvar v => simp [tyvars, ALL_DISTINCT]
  | Tyapp n args =>
    rw [tyvars]
    induction args with
    | nil => exact trivial
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
  | Comb s t _ iht => exact ALL_DISTINCT_LIST_UNION _ _ iht
  | Abs v t _ iht => exact ALL_DISTINCT_LIST_UNION _ _ iht

/- HOL4:
Theorem EQUATION_HAS_TYPE_BOOL:
   ∀s t. (s === t) has_type Bool
          ⇔ welltyped s ∧ welltyped t ∧ (typeof s = typeof t) -/
theorem EQUATION_HAS_TYPE_BOOL :
    ∀ (s t : term), has_type (equation s t) BoolTy
            ↔ welltyped s ∧ welltyped t ∧ typeof s = typeof t := by
  intro s t
  unfold equation
  constructor
  · intro h
    obtain ⟨d1, h1, h2⟩ := Aux.has_type_Comb h
    obtain ⟨d2, h3, h4⟩ := Aux.has_type_Comb h1
    have e := WELLTYPED_LEMMA _ _ h3
    simp only [typeof, type.Tyapp.injEq, List.cons.injEq, true_and, and_true] at e
    obtain ⟨e1, e2⟩ := e
    refine ⟨⟨_, h4⟩, ⟨_, h2⟩, ?_⟩
    rw [WELLTYPED_LEMMA _ _ h2]
    exact e2
  · rintro ⟨h1, h2, h3⟩
    rw [WELLTYPED] at h1 h2
    rw [← h3] at h2
    exact has_type.Comb (has_type.Comb has_type.Const h1) h2

theorem Aux.welltyped_equation {s t : term} (h : welltyped (equation s t)) :
    has_type (equation s t) BoolTy := by
  have := (WELLTYPED _).mp h
  exact this

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
  | hv v =>
    rw [TYPE_SUBST]
    rcases REV_ASSOCD_MEM tyin (Tyvar v) (Tyvar v) with h | h
    · exact h2 _ (List.mem_map.mpr ⟨_, h, rfl⟩)
    · rw [h]; exact h1
  | ha n args ih =>
    rw [type_ok, Aux.EVERY_iff] at h1
    rw [TYPE_SUBST, type_ok, Aux.EVERY_iff, List.length_map]
    refine ⟨h1.1, fun x hx => ?_⟩
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
  | hv v =>
    intro h x hx
    simp only [tyvars, List.mem_singleton] at hx
    rw [hx]; exact h
  | ha n args ih =>
    intro h x hx
    rw [TYPE_SUBST, type_ok, Aux.EVERY_iff] at h
    obtain ⟨a, ha, hxa⟩ := (Aux.mem_tyvars_Tyapp _ _ _).mp hx
    exact ih a ha (h.2 _ (List.mem_map.mpr ⟨a, ha, rfl⟩)) x hxa

/- HOL4:
Theorem term_ok_welltyped:
   ∀sig t. term_ok sig t ⇒ welltyped t -/
theorem term_ok_welltyped :
    ∀ (sig : sig) (t : term), term_ok sig t → welltyped t := by
  intro sig t
  induction t with
  | Var x ty => intro _; exact ⟨_, has_type.Var⟩
  | Const x ty => intro _; exact ⟨_, has_type.Const⟩
  | Comb s t _ _ => intro h; exact h.2.2
  | Abs v t _ iht =>
    rintro ⟨x, ty, rfl, _, h⟩
    exact (WELLTYPED_CLAUSES.2.2.2 _ _).mpr ⟨x, ty, rfl, iht h⟩

theorem Aux.type_ok_Fun (s : tysig) (a b : type) :
    type_ok s (Fun a b) ↔ FLOOKUP s (mls "fun") = some 2 ∧ type_ok s a ∧ type_ok s b := by
  rw [type_ok]
  simp [EVERY]

/- HOL4:
Theorem term_ok_type_ok:
   ∀sig t. is_std_sig sig ∧ term_ok sig t
          ⇒ type_ok (FST sig) (typeof t) -/
theorem term_ok_type_ok :
    ∀ (sig : sig) (t : term), is_std_sig sig ∧ term_ok sig t
            → type_ok sig.1 (typeof t) := by
  rintro sig t ⟨hs, h⟩
  induction t with
  | Var x ty => exact h
  | Const x ty =>
    obtain ⟨ty0, _, h2, _⟩ := h
    exact h2
  | Comb s t ihs _ =>
    obtain ⟨h1, h2, h3⟩ := h
    obtain ⟨_, _, rty, e⟩ := Aux.welltyped_Comb h3
    have := ihs h1
    rw [e, Aux.type_ok_Fun] at this
    simp only [typeof, e, codomain_def]
    exact this.2.2
  | Abs v t _ iht =>
    obtain ⟨x, ty, rfl, h1, h2⟩ := h
    simp only [typeof]
    rw [Aux.type_ok_Fun]
    exact ⟨hs.1, h1, iht h2⟩

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
  · intro h
    have hw := (EQUATION_HAS_TYPE_BOOL s t).mp (Aux.welltyped_equation (term_ok_welltyped _ _ h))
    obtain ⟨⟨_, h1, _⟩, h2, _⟩ := h
    exact ⟨h1, h2, hw.2.2.symm⟩
  · rintro ⟨h1, h2, h3⟩
    have hw := (EQUATION_HAS_TYPE_BOOL s t).mpr
      ⟨term_ok_welltyped _ _ h1, term_ok_welltyped _ _ h2, h3.symm⟩
    obtain ⟨d, hc, _⟩ := Aux.has_type_Comb hw
    refine ⟨⟨?_, h1, ⟨_, hc⟩⟩, h2, ⟨_, hw⟩⟩
    refine ⟨_, hs.2.2, ?_, [(typeof s, Tyvar (mls "A"))], ?_⟩
    · have ht := term_ok_type_ok sig s ⟨hs, h1⟩
      have hb : type_ok sig.1 BoolTy := by
        rw [type_ok]
        exact ⟨hs.2.1, trivial⟩
      exact (Aux.type_ok_Fun _ _ _).mpr ⟨hs.1, ht, (Aux.type_ok_Fun _ _ _).mpr ⟨hs.1, ht, hb⟩⟩
    · simp [TYPE_SUBST, REV_ASSOCD]

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
    rintro ilist ⟨h1, h2⟩
    rw [VSUBST]
    rcases REV_ASSOCD_MEM ilist (Var x ty) (Var x ty) with h | h
    · obtain ⟨_, _, _, _, h3⟩ := h2 _ _ h
      exact h3
    · rw [h]; exact h1
  | Const x ty =>
    rintro ilist ⟨h1, _⟩
    exact h1
  | Comb s t ihs iht =>
    rintro ilist ⟨⟨h1, h3, h4⟩, h2⟩
    have hw := VSUBST_WELLTYPED (Comb s t) BoolTy ilist ⟨h4, fun s s' hm => by
      obtain ⟨x, ty, e, ht, _⟩ := h2 s s' hm
      exact ⟨x, ty, e, ht⟩⟩
    rw [VSUBST] at hw ⊢
    exact ⟨ihs _ ⟨h1, h2⟩, iht _ ⟨h3, h2⟩, hw⟩
  | Abs v t _ iht =>
    rintro ilist ⟨⟨n, nty, rfl, hty, ht⟩, h2⟩
    have h4 : ∀ s s', (s', s) ∈ FILTER (fun p : term × term => ¬ p.2 = Var n nty) ilist →
        ∃ x ty, s = Var x ty ∧ has_type s' ty ∧ term_ok sig s' := by
      intro s s' hm
      exact h2 s s' (Aux.mem_FILTER.mp hm).1
    simp only [VSUBST, dest_var_def]
    split
    · refine ⟨_, _, rfl, hty, iht _ ⟨ht, fun s s' hm => ?_⟩⟩
      rcases List.mem_cons.mp hm with hm | hm
      · cases hm
        exact ⟨n, nty, rfl, has_type.Var, hty⟩
      · exact h4 s s' hm
    · exact ⟨_, _, rfl, hty, iht _ ⟨ht, h4⟩⟩

theorem Aux.term_ok_INST_CORE (sig : sig) (tyin : List (type × type))
    (htyin : EVERY (type_ok sig.1) (tyin.map Prod.fst)) : ∀ (n : Nat) (tm : term)
    (env : List (term × term)) (r : term), sizeof tm = n → term_ok sig tm →
      (∀ (s s' : term), (s, s') ∈ env →
        ∃ (x : mlstring) (ty : type), s = Var x ty ∧ s' = Var x (TYPE_SUBST tyin ty)) →
      INST_CORE env tyin tm = Result r → term_ok sig r := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
  intro tm env r hn hok henv hr
  subst hn
  cases tm with
  | Var x ty =>
    rw [INST_CORE] at hr
    split at hr
    · cases hr
      exact type_ok_TYPE_SUBST _ _ _ ⟨hok, htyin⟩
    · cases hr
  | Const x ty =>
    rw [INST_CORE] at hr
    cases hr
    obtain ⟨ty0, h1, h2, i, rfl⟩ := hok
    exact ⟨ty0, h1, type_ok_TYPE_SUBST _ _ _ ⟨h2, htyin⟩, _, TYPE_SUBST_compose _ _ _⟩
  | Comb s t =>
    have hwr : welltyped r := by
      rcases INST_CORE_HAS_TYPE _ (Comb s t) env tyin ⟨hok.2.2, rfl, henv⟩ with
        ⟨_, _, e, _⟩ | ⟨_, r', e, h, _⟩
      · rw [hr] at e; cases e
      · rw [hr] at e; cases e; exact ⟨_, h⟩
    obtain ⟨h1, h2, _⟩ := hok
    rcases Aux.INST_CORE_Comb_cases env tyin s t with ⟨w, _, e⟩ | ⟨_, w, _, _, e⟩ |
      ⟨s', t', e1, e2, e⟩
    · rw [hr] at e; cases e
    · rw [hr] at e; cases e
    · rw [hr] at e
      cases e
      exact ⟨ih (sizeof s) (by simp only [sizeof]; omega) s env s' rfl h1 henv e1,
        ih (sizeof t) (by simp only [sizeof]; omega) t env t' rfl h2 henv e2, hwr⟩
  | Abs v t =>
    obtain ⟨x, ty, rfl, hty, ht⟩ := hok
    have hlt : sizeof t < sizeof (Abs (Var x ty) t) := by simp only [sizeof]; omega
    have henv1 : ∀ z : mlstring, ∀ (s s' : term),
        (s, s') ∈ (Var z ty, Var z (TYPE_SUBST tyin ty)) :: env →
        ∃ (x : mlstring) (ty : type), s = Var x ty ∧ s' = Var x (TYPE_SUBST tyin ty) := by
      intro z s s' hm
      rcases List.mem_cons.mp hm with hm | hm
      · cases hm; exact ⟨z, ty, rfl, rfl⟩
      · exact henv s s' hm
    have hty' := type_ok_TYPE_SUBST sig.1 tyin ty ⟨hty, htyin⟩
    rcases Aux.INST_CORE_Abs_cases env tyin x ty t with ⟨r', h1, e⟩ | ⟨w, _, _, e⟩ |
      ⟨r', h1, e⟩ | ⟨w, _, e⟩
    · rw [hr] at e
      cases e
      exact ⟨_, _, rfl, hty', ih _ hlt t _ r' rfl ht (henv1 x) h1⟩
    · rw [hr] at e; cases e
    · rw [hr] at e
      cases e
      refine ⟨_, _, rfl, hty', ih _ hlt _ _ r' (Aux.sizeof_VSUBST_var _ _ _ _) ?_ (henv1 _) h1⟩
      refine term_ok_VSUBST sig t _ ⟨ht, fun s s' hm => ?_⟩
      rcases List.mem_singleton.mp hm with hm
      cases hm
      exact ⟨x, ty, rfl, has_type.Var, hty⟩
    · rw [hr] at e; cases e

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
  | Clash w => rw [h] at h4; exact h4.elim
  | Result r =>
    rw [RESULT_def]
    exact Aux.term_ok_INST_CORE sig tyin h2 _ tm env r rfl h1 h3 h

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
  exact term_ok_INST_CORE sig [] tyin tm
    ⟨h1, h2, by simp, INST_CORE_NIL_IS_RESULT tyin tm (term_ok_welltyped _ _ h1)⟩

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
  intro env tp h
  induction h with
  | Var ha =>
    rintro sig henv ⟨h1, _⟩
    rcases ALPHAVARS_MEM _ _ ha with hm | hm
    · obtain ⟨_, _, e, ht⟩ := Aux.EVERY_iff.mp henv _ hm
      rw [e] at ht
      exact ht
    · exact hm ▸ h1
  | Const => rintro sig henv ⟨h1, _⟩; exact h1
  | Comb _ _ ih1 ih2 =>
    rintro sig henv ⟨⟨h1, h2, _⟩, hw⟩
    obtain ⟨w1, w2, _⟩ := Aux.welltyped_Comb hw
    exact ⟨ih1 sig henv ⟨h1, w1⟩, ih2 sig henv ⟨h2, w2⟩, hw⟩
  | Abs hty _ ih =>
    rintro sig henv ⟨⟨x, ty, rfl, hok, h1⟩, hw⟩
    obtain ⟨x2, ty2, rfl, w2⟩ := Aux.welltyped_Abs hw
    have hty' : ty = ty2 := hty
    subst hty'
    refine ⟨x2, ty, rfl, hok, ih sig ⟨⟨⟨_, has_type.Var⟩, ⟨_, has_type.Var⟩, rfl, hok⟩, henv⟩ ⟨h1, w2⟩⟩

/- HOL4:
Theorem term_ok_aconv:
   ∀sig t1 t2. ACONV t1 t2 ∧ term_ok sig t1 ∧ welltyped t2 ⇒ term_ok sig t2 -/
theorem term_ok_aconv :
    ∀ (sig : sig) (t1 t2 : term), ACONV t1 t2 ∧ term_ok sig t1 ∧ welltyped t2 → term_ok sig t2 := by
  rintro sig t1 t2 ⟨h1, h2, h3⟩
  exact term_ok_raconv [] (t1, t2) h1 sig trivial ⟨h2, h3⟩

/- HOL4:
Theorem bind_not_free:
   ∀t n v. ¬dbVFREE_IN (UNCURRY dbVar v) t ⇒ bind v n t = t -/
theorem bind_not_free :
    ∀ (t : dbterm_t) (n : Nat) (v : mlstring × type), ¬ dbVFREE_IN (UNCURRY dbVar v) t → bind v n t = t := by
  intro t
  induction t with
  | dbVar x ty =>
    rintro n ⟨a, b⟩ h
    simp only [dbVFREE_IN, UNCURRY, dbterm_t.dbVar.injEq] at h
    simp only [bind, Prod.mk.injEq]
    rw [if_neg (fun e => h ⟨e.1.symm, e.2.symm⟩)]
  | dbBound m => intro n v h; rfl
  | dbConst x ty => intro n v h; rfl
  | dbComb s t ihs iht =>
    intro n v h
    simp only [dbVFREE_IN, not_or] at h
    simp only [bind, ihs n v h.1, iht n v h.2]
  | dbAbs ty t iht =>
    intro n v h
    simp only [dbVFREE_IN] at h
    simp only [bind, iht (n + 1) v h]

theorem Aux.REV_ASSOCD_not_mem {α : Type u} {β : Type u} (a : β) (d : α) :
    ∀ ls : List (α × β), ¬ a ∈ ls.map Prod.snd → REV_ASSOCD a ls d = d
  | [], _ => rfl
  | p :: ls, h => by
    simp only [List.map_cons, List.mem_cons, not_or] at h
    have h1 : ¬ p.2 = a := fun e => h.1 e.symm
    simp only [REV_ASSOCD, h1, if_false]
    exact Aux.REV_ASSOCD_not_mem a d ls h.2

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
    by_cases hv : (a, b) = (x, ty)
    · cases hv
      simp only [dbVSUBST, bind, if_true]
      rw [Aux.REV_ASSOCD_not_mem _ _ ls h1]
      simp [bind]
    · simp only [dbVSUBST, bind, hv, if_false]
      by_cases hm : dbVar x ty ∈ ls.map Prod.snd
      · exact bind_not_free _ _ _ (h2 _ ⟨rfl, hm⟩)
      · rw [Aux.REV_ASSOCD_not_mem _ _ ls hm]
        simp only [bind, hv, if_false]
  | dbBound m => intro v n ls _; rfl
  | dbConst x ty => intro v n ls _; rfl
  | dbComb s t ihs iht =>
    rintro v n ls ⟨h1, h2⟩
    simp only [dbVSUBST, bind]
    rw [ihs v n ls ⟨h1, fun k hk => h2 k ⟨Or.inl hk.1, hk.2⟩⟩,
      iht v n ls ⟨h1, fun k hk => h2 k ⟨Or.inr hk.1, hk.2⟩⟩]
  | dbAbs ty t iht =>
    rintro v n ls ⟨h1, h2⟩
    simp only [dbVSUBST, bind]
    rw [iht v (n + 1) ls ⟨h1, fun k hk => h2 k hk⟩]

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
  | dbVar y ty =>
    rintro ⟨z1, z2⟩ ⟨x1, x2⟩ n ls h
    simp only [UNCURRY] at h ⊢
    by_cases hx : x1 = y ∧ x2 = ty
    · obtain ⟨rfl, rfl⟩ := hx
      simp [dbVSUBST, bind, REV_ASSOCD]
    · simp only [bind, Prod.mk.injEq, hx, if_false, dbVSUBST] at h
      simp only [dbVSUBST, REV_ASSOCD, dbterm_t.dbVar.injEq, hx, if_false, bind, Prod.mk.injEq]
      exact bind_not_free _ _ (z1, z2) h
  | dbBound m => intro z x n ls _; rfl
  | dbConst x ty => intro z x n ls _; rfl
  | dbComb s t ihs iht =>
    intro z x n ls h
    simp only [dbVSUBST, bind, dbVFREE_IN, not_or] at h ⊢
    rw [ihs z x n ls h.1, iht z x n ls h.2]
  | dbAbs ty t iht =>
    intro z x n ls h
    simp only [dbVSUBST, bind, dbVFREE_IN] at h ⊢
    rw [iht z x (n + 1) ls h]

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
  | dbAbs ty t iht =>
    intro h
    simp only [dbVSUBST]
    rw [iht (fun k hk => h k hk)]

theorem Aux.dbVFREE_IN_bind (tm x : dbterm_t) (v : mlstring × type) (n : Nat) :
    dbVFREE_IN x (bind v n tm) ↔ x ≠ UNCURRY dbVar v ∧ dbVFREE_IN x tm := by
  obtain ⟨a, b⟩ := v
  induction tm generalizing n with
  | dbVar y ty =>
    by_cases h : a = y ∧ b = ty
    · obtain ⟨rfl, rfl⟩ := h
      simp only [bind, if_true, dbVFREE_IN, UNCURRY, false_iff]
      rintro ⟨h1, h2⟩
      exact h1 h2.symm
    · simp only [bind, Prod.mk.injEq, h, if_false, dbVFREE_IN, UNCURRY]
      constructor
      · rintro rfl
        refine ⟨fun e => h ?_, rfl⟩
        cases e
        exact ⟨rfl, rfl⟩
      · exact fun h => h.2
  | dbBound m => simp [bind, dbVFREE_IN]
  | dbConst y ty =>
    simp only [bind, dbVFREE_IN, UNCURRY]
    constructor
    · rintro rfl
      exact ⟨by simp, rfl⟩
    · exact fun h => h.2
  | dbComb s t ihs iht =>
    simp only [bind, dbVFREE_IN, ihs, iht]
    grind
  | dbAbs ty t iht =>
    simp only [bind, dbVFREE_IN, iht]

/- HOL4:
Theorem dbVFREE_IN_bind:
   ∀tm x v n b. dbVFREE_IN x (bind v n tm) ⇔ (x ≠ UNCURRY dbVar v) ∧ dbVFREE_IN x tm -/
theorem dbVFREE_IN_bind {α : Type u} :
    ∀ (tm x : dbterm_t) (v : mlstring × type) (n : Nat) (b : α),
        dbVFREE_IN x (bind v n tm) ↔ x ≠ UNCURRY dbVar v ∧ dbVFREE_IN x tm := by
  intro tm x v n _
  exact Aux.dbVFREE_IN_bind tm x v n

theorem Aux.db_eq_dbVar (y : term) (z : mlstring) (ty : type) :
    db y = dbVar z ty ↔ y = Var z ty := by
  cases y <;> simp [db]

/- HOL4:
Theorem dbVFREE_IN_VFREE_IN:
   ∀tm x. welltyped tm ⇒ (dbVFREE_IN (db x) (db tm) ⇔ VFREE_IN x tm) -/
theorem dbVFREE_IN_VFREE_IN :
    ∀ (tm x : term), welltyped tm → (dbVFREE_IN (db x) (db tm) ↔ VFREE_IN x tm) := by
  intro tm x
  induction tm with
  | Var y ty =>
    intro _
    simp only [db, dbVFREE_IN, VFREE_IN]
    rw [eq_comm, Aux.db_eq_dbVar, eq_comm]
  | Const y ty =>
    intro _
    simp only [db, dbVFREE_IN, VFREE_IN]
    cases x <;> simp [db]
  | Comb s t ihs iht =>
    intro h
    obtain ⟨h1, h2, _⟩ := Aux.welltyped_Comb h
    simp only [db, dbVFREE_IN, VFREE_IN, ihs h1, iht h2]
  | Abs v t _ iht =>
    intro h
    obtain ⟨n, ty, rfl, hw⟩ := Aux.welltyped_Abs h
    simp only [db, dbVFREE_IN, VFREE_IN, dest_var_def]
    rw [Aux.dbVFREE_IN_bind, iht hw]
    simp only [UNCURRY, ne_eq, Aux.db_eq_dbVar]
    rw [eq_comm]

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
  | cons p ls ih =>
    by_cases h : p.2 = Var z ty
    · have h' : db p.2 = dbVar z ty := (Aux.db_eq_dbVar _ _ _).mpr h
      rw [List.map_cons]
      simp only [FILTER]
      rw [if_neg (by simp [h]), if_neg (by simp [h'])]
      exact ih
    · have h' : ¬ db p.2 = dbVar z ty := fun e => h ((Aux.db_eq_dbVar _ _ _).mp e)
      simp only [FILTER, List.map_cons, ne_eq, h, h', not_false_eq_true, if_true]
      exact congrArg _ ih

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
  intro ls k ky h
  clear h
  induction ls with
  | nil => rfl
  | cons p ls ih =>
    simp only [List.map_cons, REV_ASSOCD, Aux.db_eq_dbVar]
    split
    · rfl
    · exact ih

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
    simp only [dbVSUBST, dbVFREE_IN, dbterm_t.dbVar.injEq]
    constructor
    · intro h; exact ⟨x, ty, ⟨rfl, rfl⟩, h⟩
    · rintro ⟨y, yty, ⟨rfl, rfl⟩, h⟩; exact h
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
  | dbAbs ty t iht => simp only [dbVSUBST, dbVFREE_IN, iht]

theorem Aux.REV_ASSOCD_FILTER_ne {β : Type} (v k : β) (ls : List (β × β)) (d : β) (h : ¬ k = v) :
    REV_ASSOCD k (FILTER (fun p : β × β => ¬ p.2 = v) ls) d = REV_ASSOCD k ls d := by
  refine (REV_ASSOCD_FILTER (fun s => ¬ s = v) ls k d ()).trans ?_
  rw [if_pos h]


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
    rintro ilist ⟨_, h⟩
    rw [VSUBST]
    exact (REV_ASSOCD_MAP_db ilist x ty (fun k v hm => (h k v hm).2)).symm
  | Const x ty => rintro ilist _; rfl
  | Comb s t ihs iht =>
    rintro ilist ⟨hw, h⟩
    obtain ⟨h1, h2, _⟩ := Aux.welltyped_Comb hw
    simp only [VSUBST, db, dbVSUBST]
    rw [ihs ilist ⟨h1, h⟩, iht ilist ⟨h2, h⟩]
  | Abs v t _ iht =>
    rintro ilist ⟨hw, h⟩
    obtain ⟨n, nty, rfl, hwt⟩ := Aux.welltyped_Abs hw
    have h' : ∀ (k v : term), (v, k) ∈ FILTER (fun p : term × term => ¬ p.2 = Var n nty) ilist →
        welltyped v ∧ ∃ (x : mlstring) (ty : type), k = Var x ty :=
      fun k v hm => h k v (Aux.mem_FILTER.mp hm).1
    have hmap : (FILTER (fun p : term × term => ¬ p.2 = Var n nty) ilist).map
        (fun (p : term × term) => (db p.1, db p.2)) =
        FILTER (fun p : dbterm_t × dbterm_t => ¬ p.2 = dbVar n nty)
          (ilist.map (fun (p : term × term) => (db p.1, db p.2))) := MAP_db_FILTER_neq ilist n nty
    have hfr : dbVSUBST ((FILTER (fun p : term × term => ¬ p.2 = Var n nty) ilist).map
        (fun (p : term × term) => (db p.1, db p.2))) (bind (n, nty) 0 (db t)) =
        dbVSUBST (ilist.map (fun (p : term × term) => (db p.1, db p.2)))
          (bind (n, nty) 0 (db t)) := by
      rw [hmap]
      apply dbVSUBST_frees
      intro k hk
      exact Aux.REV_ASSOCD_FILTER_ne _ _ _ _ ((Aux.dbVFREE_IN_bind _ _ _ _).mp hk).1
    have hRA : ∀ y yty, welltyped (REV_ASSOCD (Var y yty)
        (FILTER (fun p : term × term => ¬ p.2 = Var n nty) ilist) (Var y yty)) := by
      intro y yty
      rcases REV_ASSOCD_MEM (FILTER (fun p : term × term => ¬ p.2 = Var n nty) ilist)
        (Var y yty) (Var y yty) with hm | hm
      · exact (h' _ _ hm).1
      · rw [hm]; exact ⟨_, has_type.Var⟩
    simp only [VSUBST, dest_var_def]
    split
    · simp only [db, dest_var_def, typeof, dbVSUBST]
      rw [iht _ ⟨hwt, ?_⟩, ← hfr]
      · congr 1
        refine bind_dbVSUBST_cons (db t) (_, nty) (n, nty) 0 _ ?_
        rw [UNCURRY, dbVFREE_IN_dbVSUBST]
        rintro ⟨y, yty, h1, h2⟩
        have h3 := ((Aux.dbVFREE_IN_bind _ _ _ _).mp h1).2
        have h4 := (dbVFREE_IN_VFREE_IN t (Var y yty) hwt).mp h3
        rw [REV_ASSOCD_MAP_db _ _ _ (fun k v hm => (h' k v hm).2)] at h2
        have h5 := (dbVFREE_IN_VFREE_IN _ (Var _ nty) (hRA y yty)).mp h2
        exact VARIANT_THM _ _ _ ((VFREE_IN_VSUBST t _ _ _ hwt).mpr ⟨y, yty, h4, h5⟩)
      · intro k v hm
        rcases List.mem_cons.mp hm with hm | hm
        · cases hm
          exact ⟨⟨_, has_type.Var⟩, _, _, rfl⟩
        · exact h' k v hm
    · rename_i hc
      rw [Aux.EXISTS_iff] at hc
      simp only [db, dest_var_def, typeof, dbVSUBST]
      rw [iht _ ⟨hwt, h'⟩, ← hfr]
      congr 1
      refine bind_dbVSUBST (db t) (n, nty) 0 _ ⟨?_, ?_⟩
      · rw [Aux.mem_LIST_TO_SET]
        intro hm
        obtain ⟨p, hp, e⟩ := List.mem_map.mp hm
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
        exact (Aux.mem_FILTER.mp hq).2 ((Aux.db_eq_dbVar _ _ _).mp e)
      · rintro k ⟨hk, hm⟩ hf
        obtain ⟨p, hp, e⟩ := List.mem_map.mp hm
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
        obtain ⟨_, y, yty, e2⟩ := h' q.2 q.1 hq
        have hne := (Aux.mem_FILTER.mp hq).2
        have e : db q.2 = k := e
        rw [e2] at e hne
        subst e
        have hk' := (dbVFREE_IN_VFREE_IN t (Var y yty) hwt).mp hk
        simp only [db] at hf
        rw [REV_ASSOCD_MAP_db _ _ _ (fun k v hm => (h' k v hm).2)] at hf
        have hf' := (dbVFREE_IN_VFREE_IN _ (Var n nty) (hRA y yty)).mp hf
        rcases REV_ASSOCD_MEM (FILTER (fun p : term × term => ¬ p.2 = Var n nty) ilist)
          (Var y yty) (Var y yty) with hm | hm
        · exact hc ⟨_, hm, hf', hk'⟩
        · rw [hm] at hf'
          exact hne hf'

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
  | dbVar x ty =>
    rintro ⟨a, b⟩ n ls h
    simp only [dbVFREE_IN, dbterm_t.dbVar.injEq] at h
    simp only [bind, dbINST, Prod.mk.injEq]
    by_cases hv : a = x ∧ b = ty
    · obtain ⟨rfl, rfl⟩ := hv
      simp [dbINST]
    · have hv' : ¬ (a = x ∧ TYPE_SUBST ls b = TYPE_SUBST ls ty) := by
        rintro ⟨rfl, e⟩
        exact hv ⟨rfl, (h ty ⟨⟨rfl, rfl⟩, e.symm⟩).symm⟩
      rw [if_neg hv, if_neg hv', dbINST]
  | dbBound m => intro v n ls _; rfl
  | dbConst x ty => intro v n ls _; rfl
  | dbComb s t ihs iht =>
    intro v n ls h
    simp only [bind, dbINST]
    rw [ihs v n ls (fun ty hk => h ty ⟨Or.inl hk.1, hk.2⟩),
      iht v n ls (fun ty hk => h ty ⟨Or.inr hk.1, hk.2⟩)]
  | dbAbs ty t iht =>
    intro v n ls h
    simp only [bind, dbINST]
    rw [iht v (n + 1) ls (fun ty hk => h ty hk)]

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
  | dbAbs ty t iht => simp only [dbVSUBST, iht]

theorem Aux.INST_CORE_dbINST (tyin : List (type × type)) : ∀ (n : Nat) (tm : term)
    (env : List (term × term)) (tmi : term), sizeof tm = n → welltyped tm →
      (∀ (s s' : term), (s, s') ∈ env →
        ∃ (x : mlstring) (ty : type), s = Var x ty ∧ s' = Var x (TYPE_SUBST tyin ty)) →
      INST_CORE env tyin tm = Result tmi → db tmi = dbINST tyin (db tm) := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
  intro tm env tmi hn hw henv hr
  subst hn
  cases tm with
  | Var x ty =>
    rw [INST_CORE] at hr
    split at hr
    · cases hr; rfl
    · cases hr
  | Const x ty =>
    rw [INST_CORE] at hr
    cases hr
    rfl
  | Comb s t =>
    obtain ⟨hws, hwt, _⟩ := Aux.welltyped_Comb hw
    rcases Aux.INST_CORE_Comb_cases env tyin s t with ⟨w, _, e⟩ | ⟨_, w, _, _, e⟩ |
      ⟨s', t', e1, e2, e⟩
    · rw [hr] at e; cases e
    · rw [hr] at e; cases e
    · rw [hr] at e
      cases e
      simp only [db, dbINST]
      rw [ih (sizeof s) (by simp only [sizeof]; omega) s env s' rfl hws henv e1,
        ih (sizeof t) (by simp only [sizeof]; omega) t env t' rfl hwt henv e2]
  | Abs v t =>
    obtain ⟨x, ty, rfl, hwt⟩ := Aux.welltyped_Abs hw
    have hlt : sizeof t < sizeof (Abs (Var x ty) t) := by simp only [sizeof]; omega
    have henv1 : ∀ z : mlstring, ∀ (s s' : term),
        (s, s') ∈ (Var z ty, Var z (TYPE_SUBST tyin ty)) :: env →
        ∃ (x : mlstring) (ty : type), s = Var x ty ∧ s' = Var x (TYPE_SUBST tyin ty) := by
      intro z s s' hm
      rcases List.mem_cons.mp hm with hm | hm
      · cases hm; exact ⟨z, ty, rfl, rfl⟩
      · exact henv s s' hm
    -- no two types of the bound variable are identified by the instantiation
    have key : ∀ (z : mlstring) (t : term) (r : term), welltyped t →
        INST_CORE ((Var z ty, Var z (TYPE_SUBST tyin ty)) :: env) tyin t = Result r →
        ∀ ty2, dbVFREE_IN (dbVar z ty2) (db t) ∧ TYPE_SUBST tyin ty2 = TYPE_SUBST tyin ty →
          ty2 = ty := by
      rintro z t r hwt h1 ty2 ⟨hf, e⟩
      have hf' := (dbVFREE_IN_VFREE_IN t (Var z ty2) hwt).mp hf
      rcases INST_CORE_HAS_TYPE _ t _ tyin ⟨hwt, rfl, henv1 z⟩ with ⟨_, _, e', _⟩ | ⟨ha, _⟩
      · rw [h1] at e'; cases e'
      · have := ha z ty2 hf'
        simp only [REV_ASSOCD, e, if_true] at this
        cases this
        rfl
    rcases Aux.INST_CORE_Abs_cases env tyin x ty t with ⟨r', h1, e⟩ | ⟨w, _, _, e⟩ |
      ⟨r', h1, e⟩ | ⟨w, _, e⟩
    · rw [hr] at e
      cases e
      simp only [db, dest_var_def, typeof, dbINST]
      rw [ih _ hlt t _ r' rfl hwt (henv1 x) h1,
        dbINST_bind (db t) (x, ty) 0 tyin (key x t r' hwt h1)]
    · rw [hr] at e; cases e
    · rw [hr] at e
      cases e
      have hwt' : welltyped (VSUBST [(Var (Aux.newname tyin x ty t) ty, Var x ty)] t) :=
        ⟨_, Aux.VSUBST_var_has_type x _ ty t hwt⟩
      have hfresh : ¬ VFREE_IN (Var (Aux.newname tyin x ty t) ty) t :=
        fun hf => Aux.newname_fresh hwt ty hf rfl
      generalize Aux.newname tyin x ty t = x' at *
      simp only [db, dest_var_def, typeof, dbINST]
      rw [ih _ hlt _ _ r' (Aux.sizeof_VSUBST_var _ _ _ _) hwt' (henv1 x') h1]
      have hb := dbINST_bind (db (VSUBST [(Var x' ty, Var x ty)] t)) (x', ty) 0 tyin
        (key x' _ r' hwt' h1)
      rw [← hb]
      congr 1
      rw [VSUBST_dbVSUBST t [(Var x' ty, Var x ty)] ⟨hwt, ?_⟩]
      · have hc := bind_dbVSUBST_cons (db t) (x', ty) (x, ty) 0 [] (by
          rw [dbVSUBST_nil, Aux.dbVFREE_IN_bind]
          intro h
          exact hfresh ((dbVFREE_IN_VFREE_IN t (Var x' ty) hwt).mp h.2))
        rw [dbVSUBST_nil] at hc
        exact congrArg (dbINST tyin) hc
      · intro k v hm
        rcases List.mem_singleton.mp hm with hm
        cases hm
        exact ⟨⟨_, has_type.Var⟩, _, _, rfl⟩
    · rw [hr] at e; cases e

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
  rintro tm tyin env tmi ⟨h1, h2, h3⟩
  exact Aux.INST_CORE_dbINST tyin _ tm env tmi rfl h1 h2 h3

/- HOL4:
Theorem INST_dbINST:
   ∀tm tyin.
      welltyped tm ⇒
      db (INST tyin tm) = dbINST tyin (db tm) -/
theorem INST_dbINST :
    ∀ (tm : term) (tyin : List (type × type)),
        welltyped tm →
        db (INST tyin tm) = dbINST tyin (db tm) := by
  intro tm tyin h
  exact INST_CORE_dbINST tm tyin [] _ ⟨h, by simp, Aux.INST_eq h⟩

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
    | cons v vs ih => intro m; exact ih (m + 1)
  · intro env
    induction env with
    | nil => intro m; rfl
    | cons v vs ih => intro m; exact ih (m + 1)
  · intro env
    induction env with
    | nil => intro m t1 t2; rfl
    | cons v vs ih => intro m t1 t2; exact ih (m + 1) _ _
  · intro env
    induction env with
    | nil => intro m ty t; rfl
    | cons v vs ih => intro m ty t; exact ih (m + 1) ty _

theorem Aux.bind_list_aux_Var (s : mlstring) (ty : type) : ∀ (env : List (mlstring × type)) (n : Nat),
    bind_list_aux n env (dbVar s ty) =
      match find_index (s, ty) env n with
      | some k => dbBound k
      | none => dbVar s ty
  | [], n => rfl
  | v :: vs, n => by
    simp only [bind_list_aux, bind, find_index]
    by_cases h : v = (s, ty)
    · rw [if_pos h, if_pos h]
      exact (bind_list_aux_clauses n s ty).1 vs (n + 1)
    · rw [if_neg h, if_neg h]
      exact Aux.bind_list_aux_Var s ty vs (n + 1)

/- HOL4:
Theorem dbterm_bind:
   ∀tm env. dbterm env tm = bind_list_aux 0 env (db tm) -/
theorem dbterm_bind :
    ∀ (tm : term) (env : List (mlstring × type)), dbterm env tm = bind_list_aux 0 env (db tm) := by
  intro tm
  induction tm with
  | Var x ty => intro env; rw [db, Aux.bind_list_aux_Var]; rfl
  | Const x ty => intro env; exact ((bind_list_aux_clauses 0 x ty).2.1 env 0).symm
  | Comb s t ihs iht =>
    intro env
    rw [db, (bind_list_aux_clauses 0 (mls "") BoolTy).2.2.1, dbterm, ihs, iht]
  | Abs v t _ iht =>
    intro env
    rw [db, (bind_list_aux_clauses 0 (mls "") BoolTy).2.2.2, dbterm, iht]
    rfl

/- HOL4:
Theorem dbterm_db:
   ∀tm. dbterm [] tm = db tm -/
theorem dbterm_db :
    ∀ (tm : term), dbterm [] tm = db tm := by
  intro tm
  rw [dbterm_bind]
  rfl

/-- the value of `dbterm` on variables -/
def Aux.fi (a : mlstring × type) (env : List (mlstring × type)) (n : Nat) : dbterm_t :=
  match find_index a env n with
  | some k => dbBound k
  | none => dbVar a.1 a.2

theorem Aux.find_index_ge {α : Type} (a : α) : ∀ (l : List α) (n k : Nat),
    find_index a l n = some k → n ≤ k
  | [], n, k, h => by simp [find_index] at h
  | x :: l, n, k, h => by
    simp only [find_index] at h
    split at h
    · cases h; exact Nat.le_refl _
    · have := Aux.find_index_ge a l (n + 1) k h
      omega

theorem Aux.fi_ne (a : mlstring × type) (env : List (mlstring × type)) (n : Nat) :
    ¬ Aux.fi a env (n + 1) = dbBound n := by
  unfold Aux.fi
  split
  · rename_i k h
    have := Aux.find_index_ge a env (n + 1) k h
    intro e
    cases e
    omega
  · intro e; cases e

theorem Aux.fi_cons (a v : mlstring × type) (env : List (mlstring × type)) (n : Nat) :
    Aux.fi a (v :: env) n = if v = a then dbBound n else Aux.fi a env (n + 1) := by
  unfold Aux.fi
  simp only [find_index]
  by_cases h : v = a
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h]

theorem Aux.fi_ALPHAVARS (a b : mlstring × type) : ∀ (env1 env2 : List (mlstring × type)) (n : Nat),
    env1.length = env2.length → Aux.fi a env1 n = Aux.fi b env2 n →
    ALPHAVARS (ZIP (env1.map (UNCURRY Var), env2.map (UNCURRY Var))) (UNCURRY Var a, UNCURRY Var b)
  | [], [], n, _, h => by
    simp only [Aux.fi, find_index, dbterm_t.dbVar.injEq] at h
    simp only [List.map_nil, ZIP, ALPHAVARS, UNCURRY, h.1, h.2]
  | [], _ :: _, _, h, _ => by simp at h
  | _ :: _, [], _, h, _ => by simp at h
  | x :: env1, y :: env2, n, hl, h => by
    have hinj : ∀ p q : mlstring × type, UNCURRY Var p = UNCURRY Var q → p = q := by
      intro p q e
      simp only [UNCURRY, term.Var.injEq] at e
      exact Prod.ext e.1 e.2
    rw [Aux.fi_cons, Aux.fi_cons] at h
    simp only [List.map_cons, ZIP]
    by_cases hx : x = a
    · by_cases hy : y = b
      · left; rw [hx, hy]
      · rw [if_pos hx, if_neg hy] at h
        exact absurd h.symm (Aux.fi_ne _ _ _)
    · by_cases hy : y = b
      · rw [if_neg hx, if_pos hy] at h
        exact absurd h (Aux.fi_ne _ _ _)
      · rw [if_neg hx, if_neg hy] at h
        right
        exact ⟨fun e => hx (hinj _ _ e), fun e => hy (hinj _ _ e),
          Aux.fi_ALPHAVARS a b env1 env2 (n + 1) (by simpa using hl) h⟩

theorem Aux.ALPHAVARS_fi (a b : mlstring × type) : ∀ (env : List (term × term)) (n : Nat),
    (∀ (vp : term × term), vp ∈ env → (∃ (x : mlstring) (ty : type), vp.1 = Var x ty) ∧
        (∃ (x : mlstring) (ty : type), vp.2 = Var x ty)) →
    ALPHAVARS env (UNCURRY Var a, UNCURRY Var b) →
    Aux.fi a (env.map (dest_var ∘ Prod.fst)) n = Aux.fi b (env.map (dest_var ∘ Prod.snd)) n
  | [], n, _, h => by
    simp only [ALPHAVARS, UNCURRY, term.Var.injEq] at h
    rw [Prod.ext h.1 h.2]
    rfl
  | (p, q) :: env, n, hv, h => by
    obtain ⟨⟨x, ty, hp⟩, ⟨y, ty', hq⟩⟩ := hv (p, q) List.mem_cons_self
    have hp : p = Var x ty := hp
    have hq : q = Var y ty' := hq
    subst hp hq
    simp only [List.map_cons, Function.comp_apply, dest_var_def]
    rw [Aux.fi_cons, Aux.fi_cons]
    rcases h with h | ⟨h1, h2, h3⟩
    · simp only [UNCURRY, Prod.mk.injEq, term.Var.injEq] at h
      rw [if_pos (Prod.ext h.1.1.symm h.1.2.symm), if_pos (Prod.ext h.2.1.symm h.2.2.symm)]
    · rw [if_neg (fun e => h1 (by rw [← e])), if_neg (fun e => h2 (by rw [← e]))]
      exact Aux.ALPHAVARS_fi a b env (n + 1) (fun vp hm => hv vp (List.mem_cons_of_mem _ hm)) h3

theorem Aux.dbterm_Var (env : List (mlstring × type)) (x : mlstring) (ty : type) :
    dbterm env (Var x ty) = Aux.fi (x, ty) env 0 := rfl

theorem Aux.fi_cases (a : mlstring × type) (env : List (mlstring × type)) (n : Nat) :
    (∃ k, Aux.fi a env n = dbBound k) ∨ ∃ x ty, Aux.fi a env n = dbVar x ty := by
  unfold Aux.fi
  split
  · exact Or.inl ⟨_, rfl⟩
  · exact Or.inr ⟨_, _, rfl⟩

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
  | Var x ty =>
    rintro env1 t2 env2 ⟨_, _, h, hl⟩
    rw [Aux.dbterm_Var] at h
    cases t2 with
    | Var y ty' =>
      rw [Aux.dbterm_Var] at h
      exact RACONV.Var (Aux.fi_ALPHAVARS (x, ty) (y, ty') env1 env2 0 hl h)
    | _ =>
      simp only [dbterm] at h
      rcases Aux.fi_cases (x, ty) env1 0 with ⟨k, e⟩ | ⟨a, b, e⟩ <;> rw [e] at h <;> cases h
  | Const x ty =>
    rintro env1 t2 env2 ⟨_, _, h, hl⟩
    cases t2 with
    | Var y ty' =>
      rw [Aux.dbterm_Var] at h
      simp only [dbterm] at h
      rcases Aux.fi_cases (y, ty') env2 0 with ⟨k, e⟩ | ⟨a, b, e⟩ <;> rw [e] at h <;> cases h
    | Const y ty' => cases h; exact RACONV.Const
    | Comb => cases h
    | Abs => cases h
  | Comb s t ihs iht =>
    rintro env1 t2 env2 ⟨h1, h2, h, hl⟩
    cases t2 with
    | Var y ty' =>
      rw [Aux.dbterm_Var] at h
      simp only [dbterm] at h
      rcases Aux.fi_cases (y, ty') env2 0 with ⟨k, e⟩ | ⟨a, b, e⟩ <;> rw [e] at h <;> cases h
    | Const => cases h
    | Comb s' t' =>
      obtain ⟨w1, w2, _⟩ := Aux.welltyped_Comb h1
      obtain ⟨w3, w4, _⟩ := Aux.welltyped_Comb h2
      simp only [dbterm, dbterm_t.dbComb.injEq] at h
      exact RACONV.Comb (ihs _ _ _ ⟨w1, w3, h.1, hl⟩) (iht _ _ _ ⟨w2, w4, h.2, hl⟩)
    | Abs => cases h
  | Abs v t _ iht =>
    rintro env1 t2 env2 ⟨h1, h2, h, hl⟩
    cases t2 with
    | Var y ty' =>
      rw [Aux.dbterm_Var] at h
      simp only [dbterm] at h
      rcases Aux.fi_cases (y, ty') env2 0 with ⟨k, e⟩ | ⟨a, b, e⟩ <;> rw [e] at h <;> cases h
    | Const => cases h
    | Comb => cases h
    | Abs v' t' =>
      obtain ⟨n1, ty1, rfl, w1⟩ := Aux.welltyped_Abs h1
      obtain ⟨n2, ty2, rfl, w2⟩ := Aux.welltyped_Abs h2
      simp only [dbterm, dbterm_t.dbAbs.injEq, dest_var_def] at h
      have := iht _ _ _ ⟨w1, w2, h.2, by simp [hl]⟩
      exact RACONV.Abs h.1 (by simpa [ZIP] using this)

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
  | @Var env x1 ty1 x2 ty2 ha =>
    rintro ⟨_, _, hv⟩
    exact Aux.ALPHAVARS_fi (x1, ty1) (x2, ty2) env 0 hv ha
  | Const => intro _; rfl
  | Comb _ _ ih1 ih2 =>
    rintro ⟨h1, h2, hv⟩
    obtain ⟨w1, w2, _⟩ := Aux.welltyped_Comb h1
    obtain ⟨w3, w4, _⟩ := Aux.welltyped_Comb h2
    have e1 := ih1 ⟨w1, w3, hv⟩
    have e2 := ih2 ⟨w2, w4, hv⟩
    simp only [dbterm]
    rw [e1, e2]
  | Abs hty _ ih =>
    rintro ⟨h1, h2, hv⟩
    obtain ⟨n1, ty1, rfl, w1⟩ := Aux.welltyped_Abs h1
    obtain ⟨n2, ty2, rfl, w2⟩ := Aux.welltyped_Abs h2
    have e := ih ⟨w1, w2, fun vp hm => by
      rcases List.mem_cons.mp hm with hm | hm
      · subst hm; exact ⟨⟨_, _, rfl⟩, ⟨_, _, rfl⟩⟩
      · exact hv vp hm⟩
    simp only [dbterm]
    rw [hty]
    exact congrArg _ e

/- HOL4:
Theorem dbterm_ACONV:
   ∀t1 t2. welltyped t1 ∧ welltyped t2 ⇒ (ACONV t1 t2 ⇔ dbterm [] t1 = dbterm [] t2) -/
theorem dbterm_ACONV :
    ∀ (t1 t2 : term), welltyped t1 ∧ welltyped t2 → (ACONV t1 t2 ↔ dbterm [] t1 = dbterm [] t2) := by
  rintro t1 t2 ⟨h1, h2⟩
  constructor
  · intro h
    exact RACONV_dbterm [] (t1, t2) h ⟨h1, h2, by simp⟩
  · intro h
    have := dbterm_RACONV t1 [] t2 [] ⟨h1, h2, h, rfl⟩
    simpa [ZIP] using this

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
  rintro t1 t2 ilist ⟨h1, h2, h3, h4⟩
  have h3' : ∀ (k v : term), (v, k) ∈ ilist → welltyped v ∧ ∃ (x : mlstring) (ty : type), k = Var x ty := by
    intro k v hm
    obtain ⟨x, ty, e, ht⟩ := h3 k v hm
    exact ⟨⟨ty, ht⟩, x, ty, e⟩
  rw [ACONV_db _ _ ⟨VSUBST_WELLTYPED t1 BoolTy ilist ⟨h1, h3⟩,
    VSUBST_WELLTYPED t2 BoolTy ilist ⟨h2, h3⟩⟩, VSUBST_dbVSUBST t1 ilist ⟨h1, h3'⟩,
    VSUBST_dbVSUBST t2 ilist ⟨h2, h3'⟩, (ACONV_db t1 t2 ⟨h1, h2⟩).mp h4]

/- HOL4:
Theorem ACONV_INST:
   ∀t1 t2 tyin. welltyped t1 ∧ welltyped t2 ∧ ACONV t1 t2 ⇒ ACONV (INST tyin t1) (INST tyin t2) -/
theorem ACONV_INST :
    ∀ (t1 t2 : term) (tyin : List (type × type)),
        welltyped t1 ∧ welltyped t2 ∧ ACONV t1 t2 → ACONV (INST tyin t1) (INST tyin t2) := by
  rintro t1 t2 tyin ⟨h1, h2, h3⟩
  rw [ACONV_db _ _ ⟨INST_WELLTYPED t1 tyin h1, INST_WELLTYPED t2 tyin h2⟩, INST_dbINST t1 tyin h1,
    INST_dbINST t2 tyin h2, (ACONV_db t1 t2 ⟨h1, h2⟩).mp h3]

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
  | Comb s t ihs iht =>
    rintro ilist ⟨h1, h2, h3⟩
    obtain ⟨w1, w2, _⟩ := Aux.welltyped_Comb h3
    rw [Aux.DISJOINT_iff] at h1
    simp only [VSUBST, simple_subst]
    rw [ihs ilist ⟨Aux.DISJOINT_iff.mpr fun x hx => h1 x ?_, h2, w1⟩,
      iht ilist ⟨Aux.DISJOINT_iff.mpr fun x hx => h1 x ?_, h2, w2⟩]
    · rw [Aux.mem_LIST_TO_SET] at hx ⊢
      exact List.mem_append_right _ hx
    · rw [Aux.mem_LIST_TO_SET] at hx ⊢
      exact List.mem_append_left _ hx
  | Abs v t _ iht =>
    rintro ilist ⟨h1, h2, h3⟩
    obtain ⟨n, nty, rfl, hwt⟩ := Aux.welltyped_Abs h3
    rw [Aux.DISJOINT_iff] at h1
    have hsub : ∀ u, u ∈ (FILTER (fun p : term × term => ¬ p.2 = Var n nty) ilist).map Prod.fst →
        u ∈ ilist.map Prod.fst := by
      intro u hu
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hu
      exact List.mem_map.mpr ⟨p, (Aux.mem_FILTER.mp hp).1, rfl⟩
    have hi := iht (FILTER (fun p : term × term => ¬ p.2 = Var n nty) ilist)
      ⟨Aux.DISJOINT_iff.mpr fun x hx hm => by
        obtain ⟨ty, u, hf, hu⟩ := hm
        rw [Aux.mem_LIST_TO_SET] at hx
        refine h1 x ?_ ⟨ty, u, hf, hsub u hu⟩
        rw [Aux.mem_LIST_TO_SET]
        exact List.mem_cons_of_mem _ hx,
      fun s s' hm => h2 s s' (Aux.mem_FILTER.mp hm).1, hwt⟩
    simp only [VSUBST, dest_var_def, simple_subst]
    rw [if_neg, hi]
    rw [Aux.EXISTS_iff]
    rintro ⟨p, hp, hf, _⟩
    refine h1 n ?_ ⟨nty, p.1, hf, hsub _ (List.mem_map.mpr ⟨p, hp, rfl⟩)⟩
    rw [Aux.mem_LIST_TO_SET]
    simp [bv_names, dest_var_def]

theorem Aux.INST_CORE_simple_inst (tyin : List (type × type)) : ∀ (tm : term)
    (env : List (term × term)),
    (bv_names tm ++ env.map (Prod.fst ∘ dest_var ∘ Prod.snd)).Nodup →
    (∀ x, x ∈ bv_names tm → ∀ ty, ¬ VFREE_IN (Var x ty) tm) →
    (∀ (s s' : term), (s, s') ∈ env →
      ∃ (x : mlstring) (ty : type), s = Var x ty ∧ s' = Var x (TYPE_SUBST tyin ty)) →
    (∀ (x : mlstring) (ty ty' : type),
      VFREE_IN (Var x ty) tm ∧ Var x ty' ∈ env.map Prod.fst → ty' = ty) →
    welltyped tm → INST_CORE env tyin tm = Result (simple_inst tyin tm) := by
  intro tm
  induction tm with
  | Var x ty =>
    intro env _ _ h3 h4 _
    rw [INST_CORE, if_pos]
    · rfl
    · rcases REV_ASSOCD_MEM env (Var x (TYPE_SUBST tyin ty)) (Var x ty) with hm | hm
      · obtain ⟨x1, ty1, e1, e2⟩ := h3 _ _ hm
        injection e2 with e2 _
        subst e2
        have := h4 x ty ty1 ⟨rfl, List.mem_map.mpr ⟨_, hm, e1⟩⟩
        rw [e1, this]
      · exact hm
  | Const x ty => intro env _ _ _ _ _; rw [INST_CORE]; rfl
  | Comb s t ihs iht =>
    intro env h1 h2 h3 h4 h5
    obtain ⟨w1, w2, _⟩ := Aux.welltyped_Comb h5
    simp only [bv_names, List.append_assoc] at h1 h2
    have hns : (bv_names s ++ env.map (Prod.fst ∘ dest_var ∘ Prod.snd)).Nodup :=
      List.Nodup.sublist
        (List.Sublist.append (List.Sublist.refl _) (List.sublist_append_right _ _)) h1
    have hnt : (bv_names t ++ env.map (Prod.fst ∘ dest_var ∘ Prod.snd)).Nodup :=
      List.Nodup.sublist (List.sublist_append_right _ _) h1
    have es := ihs env hns (fun x hx ty hf => h2 x (List.mem_append_left _ hx) ty (Or.inl hf)) h3
      (fun x ty ty' h => h4 x ty ty' ⟨Or.inl h.1, h.2⟩) w1
    have et := iht env hnt (fun x hx ty hf => h2 x (List.mem_append_right _ hx) ty (Or.inr hf)) h3
      (fun x ty ty' h => h4 x ty ty' ⟨Or.inr h.1, h.2⟩) w2
    rw [INST_CORE, es, et]
    simp [IS_CLASH, RESULT_def, simple_inst]
  | Abs v t _ iht =>
    intro env h1 h2 h3 h4 h5
    obtain ⟨n, nty, rfl, hwt⟩ := Aux.welltyped_Abs h5
    simp only [bv_names, dest_var_def] at h1 h2
    have h1' : (bv_names t ++ n :: env.map (Prod.fst ∘ dest_var ∘ Prod.snd)).Nodup :=
      List.perm_middle.nodup_iff.mpr h1
    have hn : n ∉ bv_names t ++ env.map (Prod.fst ∘ dest_var ∘ Prod.snd) :=
      (List.nodup_cons.mp h1).1
    rw [List.mem_append, not_or] at hn
    have hi := iht ((Var n nty, Var n (TYPE_SUBST tyin nty)) :: env)
      (by simpa [dest_var_def] using h1')
      (by
        intro x hx ty hf
        refine h2 x (List.mem_cons_of_mem _ hx) ty ⟨fun e => ?_, hf⟩
        injection e with e _
        subst e
        exact hn.1 hx)
      (by
        intro s s' hm
        rcases List.mem_cons.mp hm with hm | hm
        · cases hm; exact ⟨n, nty, rfl, rfl⟩
        · exact h3 s s' hm)
      (by
        rintro x ty ty' ⟨hf, hm⟩
        rw [List.map_cons, List.mem_cons] at hm
        have hnf : Var n nty = Var x ty ∨ ¬ Var n nty = Var x ty := Classical.em _
        rcases hm with hm | hm
        · injection hm with e1 e2
          subst e1 e2
          rcases hnf with e | e
          · injection e
          · exact absurd ⟨e, hf⟩ (h2 x List.mem_cons_self ty)
        · rcases hnf with e | e
          · injection e with e1 e2
            subst e1
            exfalso
            obtain ⟨p, hp, e3⟩ := List.mem_map.mp hm
            obtain ⟨y, yty, e4, e5⟩ := h3 p.1 p.2 hp
            rw [e4] at e3
            injection e3 with e3 _
            subst e3
            refine hn.2 (List.mem_map.mpr ⟨p, hp, ?_⟩)
            simp [e5, dest_var_def]
          · exact h4 x ty ty' ⟨⟨e, hf⟩, hm⟩)
      hwt
    rw [INST_CORE]
    simp only [dest_var_def, hi, IS_RESULT, if_true, RESULT_def, simple_inst]

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
  rintro env tyin tm ⟨h1, h2, h3, h4, h5⟩
  rw [Aux.DISJOINT_iff] at h2
  exact Aux.INST_CORE_simple_inst tyin tm env (Aux.ALL_DISTINCT_iff.mp h1)
    (fun x hx ty hf => h2 x (Aux.mem_LIST_TO_SET.mpr hx) ⟨ty, hf⟩) h3 h4 h5

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
  unfold INST
  rw [INST_CORE_simple_inst [] tyin tm ⟨by simpa using h1, h2, by simp, by simp, h3⟩, RESULT_def]

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
  intro tm
  induction tm with
  | Var x ty' =>
    intro ty h subst hs
    cases h
    rw [simple_subst]
    rcases REV_ASSOCD_MEM subst (Var x ty') (Var x ty') with hm | hm
    · exact Aux.EVERY_iff.mp hs _ hm
    · rw [hm]; exact has_type.Var
  | Const x ty' => intro ty h subst _; exact h
  | Comb s t ihs iht =>
    intro ty h subst hs
    obtain ⟨dty, h1, h2⟩ := Aux.has_type_Comb h
    exact has_type.Comb (ihs _ h1 subst hs) (iht _ h2 subst hs)
  | Abs v t _ iht =>
    intro ty h subst hs
    obtain ⟨n, dty, rty, rfl, rfl, h1⟩ := Aux.has_type_Abs h
    refine has_type.Abs (iht _ h1 _ ?_)
    rw [Aux.EVERY_iff] at *
    exact fun p hp => hs p (Aux.mem_FILTER.mp hp).1

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
  | Comb s t ihs iht =>
    intro h
    obtain ⟨h1, h2, rty, e⟩ := Aux.welltyped_Comb h
    have hs := ihs h1
    rw [e, Aux.TYPE_SUBST_Fun] at hs
    simp only [simple_inst, typeof, e, codomain_def]
    exact has_type.Comb hs (iht h2)
  | Abs v t _ iht =>
    intro h
    obtain ⟨n, ty, rfl, h1⟩ := Aux.welltyped_Abs h
    simp only [simple_inst, typeof]
    rw [Aux.TYPE_SUBST_Fun]
    exact has_type.Abs (iht h1)

theorem Aux.FST_rename_bvars : ∀ (tm : term) (names : List mlstring)
    (env : List (mlstring × (mlstring × type))), (bv_names tm).length ≤ names.length →
    (rename_bvars names env tm).1 = names.drop (bv_names tm).length := by
  intro tm
  induction tm with
  | Var x ty => intro names env _; simp [rename_bvars, bv_names]
  | Const x ty => intro names env _; simp [rename_bvars, bv_names]
  | Comb s t ihs iht =>
    intro names env h
    simp only [bv_names, List.length_append] at h ⊢
    simp only [rename_bvars]
    have e := ihs names env (by omega)
    rw [iht _ _ (by rw [e, List.length_drop]; omega), e, List.drop_drop]
  | Abs v t _ iht =>
    intro names env h
    cases names with
    | nil => simp [bv_names] at h
    | cons s' names =>
      simp only [bv_names, List.length_cons] at h ⊢
      simp only [rename_bvars, List.drop_succ_cons]
      exact iht names _ (by omega)

/- HOL4:
Theorem FST_rename_bvars:
   ∀names env tm. LENGTH (bv_names tm) ≤ LENGTH names ⇒ (FST (rename_bvars names env tm) = DROP (LENGTH (bv_names tm)) names) -/
theorem FST_rename_bvars :
    ∀ (names : List mlstring) (env : List (mlstring × (mlstring × type))) (tm : term),
        (bv_names tm).length ≤ names.length →
        (rename_bvars names env tm).1 = names.drop (bv_names tm).length := by
  intro names env tm
  exact Aux.FST_rename_bvars tm names env

theorem Aux.rename_ALPHAVARS (x : mlstring) (ty : type) :
    ∀ env : List (mlstring × (mlstring × type)), (∀ s, s ∈ env.map Prod.fst → ¬ s = x) →
      (env.map Prod.fst).Nodup →
      ALPHAVARS (env.map (fun (p : mlstring × (mlstring × type)) => (Var p.2.1 p.2.2, Var p.1 p.2.2)))
        (Var x ty, Var (REV_ASSOCD (x, ty) env x) ty)
  | [], _, _ => rfl
  | (s', (s, sty)) :: env, h1, h2 => by
    rw [List.map_cons, List.nodup_cons] at h2
    have ih := Aux.rename_ALPHAVARS x ty env
      (fun s hs => h1 s (List.mem_cons_of_mem _ hs)) h2.2
    simp only [List.map_cons, REV_ASSOCD]
    by_cases h : (s, sty) = (x, ty)
    · rw [if_pos h]
      cases h
      left; rfl
    · rw [if_neg h]
      right
      refine ⟨fun e => h ?_, fun e => ?_, ih⟩
      · simp only [term.Var.injEq] at e
        rw [e.1, e.2]
      · simp only [term.Var.injEq] at e
        rcases REV_ASSOCD_MEM env (x, ty) x with hm | hm
        · refine h2.1 ?_
          rw [show (s', s, sty).1 = REV_ASSOCD (x, ty) env x from e.1]
          exact List.mem_map.mpr ⟨_, hm, rfl⟩
        · exact h1 s' List.mem_cons_self (e.1.trans hm)

theorem Aux.rename_bvars_RACONV : ∀ (tm : term) (names : List mlstring)
    (env : List (mlstring × (mlstring × type))),
    (bv_names tm).length ≤ names.length →
    (∀ x, x ∈ env.map Prod.fst ++ names →
      ¬ x ∈ env.map (Prod.fst ∘ Prod.snd) ++ bv_names tm) →
    (∀ x, x ∈ env.map Prod.fst ++ names → ∀ ty, ¬ VFREE_IN (Var x ty) tm) →
    (env.map Prod.fst ++ names).Nodup → welltyped tm →
    RACONV (env.map (fun (p : mlstring × (mlstring × type)) => (Var p.2.1 p.2.2, Var p.1 p.2.2)))
      (tm, (rename_bvars names env tm).2) := by
  intro tm
  induction tm with
  | Var x ty =>
    intro names env _ _ h3 h4 _
    simp only [rename_bvars]
    refine RACONV.Var (Aux.rename_ALPHAVARS x ty env ?_ ?_)
    · rintro s hs rfl
      exact h3 s (List.mem_append_left _ hs) ty rfl
    · exact List.Nodup.sublist (List.sublist_append_left _ _) h4
  | Const x ty => intro names env _ _ _ _ _; exact RACONV.Const
  | Comb s t ihs iht =>
    intro names env h1 h2 h3 h4 h5
    obtain ⟨w1, w2, _⟩ := Aux.welltyped_Comb h5
    simp only [bv_names, List.length_append] at h1 h2
    simp only [rename_bvars]
    rw [Aux.FST_rename_bvars s names env (by omega)]
    have hsub : ∀ x, x ∈ env.map Prod.fst ++ names.drop (bv_names s).length →
        x ∈ env.map Prod.fst ++ names := by
      intro x hx
      rcases List.mem_append.mp hx with h | h
      · exact List.mem_append_left _ h
      · exact List.mem_append_right _ (List.mem_of_mem_drop h)
    refine RACONV.Comb (ihs names env (by omega) ?_ ?_ h4 w1) (iht _ env ?_ ?_ ?_ ?_ w2)
    · intro x hx hm
      apply h2 x hx
      rcases List.mem_append.mp hm with h | h
      · exact List.mem_append_left _ h
      · exact List.mem_append_right _ (List.mem_append_left _ h)
    · exact fun x hx ty hf => h3 x hx ty (Or.inl hf)
    · rw [List.length_drop]; omega
    · intro x hx hm
      apply h2 x (hsub x hx)
      rcases List.mem_append.mp hm with h | h
      · exact List.mem_append_left _ h
      · exact List.mem_append_right _ (List.mem_append_right _ h)
    · exact fun x hx ty hf => h3 x (hsub x hx) ty (Or.inr hf)
    · exact List.Nodup.sublist
        (List.Sublist.append (List.Sublist.refl _) (List.drop_sublist _ _)) h4
  | Abs v t _ iht =>
    intro names env h1 h2 h3 h4 h5
    obtain ⟨n, nty, rfl, hwt⟩ := Aux.welltyped_Abs h5
    cases names with
    | nil => simp [bv_names] at h1
    | cons s' names =>
      simp only [bv_names, dest_var_def, List.length_cons] at h1 h2
      simp only [rename_bvars, dest_var_def, typeof]
      have hsub : ∀ x, x ∈ s' :: env.map Prod.fst ++ names → x ∈ env.map Prod.fst ++ s' :: names := by
        intro x hx
        simp only [List.cons_append, List.mem_cons, List.mem_append] at hx ⊢
        grind
      have hi := iht names ((s', (n, nty)) :: env) (by omega)
        (by
          intro x hx hm
          refine h2 x (hsub x hx) ?_
          simp only [List.map_cons, Function.comp_apply, List.cons_append, List.mem_cons,
            List.mem_append] at hm ⊢
          grind)
        (by
          intro x hx ty hf
          refine h3 x (hsub x hx) ty ⟨fun e => ?_, hf⟩
          injection e with e _
          subst e
          exact h2 n (hsub n hx) (by simp))
        (List.perm_middle.nodup_iff.mp h4) hwt
      exact RACONV.Abs rfl hi

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
  rintro names env tm ⟨h1, h2, h3, h4, h5⟩
  rw [Aux.DISJOINT_iff] at h2 h3
  refine Aux.rename_bvars_RACONV tm names env h1 ?_ ?_ (Aux.ALL_DISTINCT_iff.mp h4) h5
  · exact fun x hx hm => h2 x (Aux.mem_LIST_TO_SET.mpr hx) (Aux.mem_LIST_TO_SET.mpr hm)
  · exact fun x hx ty hf => h3 x (Aux.mem_LIST_TO_SET.mpr hx) ⟨ty, hf⟩

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
  rintro names tm ⟨h1, h2, h3, h4⟩
  rw [Aux.DISJOINT_iff] at h3
  refine Aux.rename_bvars_RACONV tm names [] h1 ?_ ?_ (Aux.ALL_DISTINCT_iff.mp h2) h4
  · exact fun x hx hm => h3 x (Aux.mem_LIST_TO_SET.mpr hx) (Or.inl hm)
  · exact fun x hx ty hf => h3 x (Aux.mem_LIST_TO_SET.mpr hx) (Or.inr ⟨ty, hf⟩)

theorem Aux.rename_bvars_has_type : ∀ (tm : term) (names : List mlstring)
    (env : List (mlstring × (mlstring × type))) (ty : type),
    has_type tm ty → has_type (rename_bvars names env tm).2 ty := by
  intro tm
  induction tm with
  | Var x ty' => intro names env ty h; cases h; simp only [rename_bvars]; exact has_type.Var
  | Const x ty' => intro names env ty h; simp only [rename_bvars]; exact h
  | Comb s t ihs iht =>
    intro names env ty h
    obtain ⟨dty, h1, h2⟩ := Aux.has_type_Comb h
    simp only [rename_bvars]
    exact has_type.Comb (ihs _ _ _ h1) (iht _ _ _ h2)
  | Abs v t _ iht =>
    intro names env ty h
    obtain ⟨n, dty, rty, rfl, rfl, h1⟩ := Aux.has_type_Abs h
    cases names with
    | nil =>
      simp only [rename_bvars]
      exact has_type.Abs (iht _ _ _ h1)
    | cons s' names =>
      simp only [rename_bvars, typeof]
      exact has_type.Abs (iht _ _ _ h1)

/- HOL4:
Theorem rename_bvars_has_type:
   ∀names env tm ty. tm has_type ty ⇒ SND (rename_bvars names env tm) has_type ty -/
theorem rename_bvars_has_type :
    ∀ (names : List mlstring) (env : List (mlstring × (mlstring × type))) (tm : term) (ty : type),
        has_type tm ty → has_type (rename_bvars names env tm).2 ty := by
  intro names env tm ty
  exact Aux.rename_bvars_has_type tm names env ty

/- HOL4:
Theorem rename_bvars_welltyped:
   ∀names env tm. welltyped tm ⇒ welltyped (SND (rename_bvars names env tm)) -/
theorem rename_bvars_welltyped :
    ∀ (names : List mlstring) (env : List (mlstring × (mlstring × type))) (tm : term),
        welltyped tm → welltyped (rename_bvars names env tm).2 := by
  rintro names env tm ⟨ty, h⟩
  exact ⟨ty, rename_bvars_has_type names env tm ty h⟩

/- HOL4:
Theorem fresh_union:
   FINITE s ∧ FINITE t ⇒ fresh (s ∪ t) ∉ s ∧ fresh (s ∪ t) ∉ t -/
theorem fresh_union (s t : Set string) :
    FINITE s ∧ FINITE t → fresh (UNION s t) ∉ s ∧ fresh (UNION s t) ∉ t := by
  rintro ⟨h1, h2⟩
  have h := fresh_def (UNION s t) (Aux.FINITE_UNION h1 h2)
  exact ⟨fun hm => h (Or.inl hm), fun hm => h (Or.inr hm)⟩

theorem Aux.FINITE_LIST_TO_SET {α : Type u} (l : List α) : FINITE (LIST_TO_SET l) :=
  Aux.FINITE_iff.mpr ⟨l, fun _ h => Aux.mem_LIST_TO_SET.mp h⟩

/- HOL4:
Theorem fresh_names_exist:
   ∀s n. FINITE (s:string set) ⇒ ∃names. LENGTH names = n ∧ ALL_DISTINCT names ∧ DISJOINT (set names) s -/
theorem fresh_names_exist :
    ∀ (s : Set string) (n : Nat), FINITE s →
        ∃ (names : List string), names.length = n ∧ ALL_DISTINCT names ∧ DISJOINT (LIST_TO_SET names) s := by
  intro s n hs
  induction n with
  | zero =>
    refine ⟨[], rfl, trivial, Aux.DISJOINT_iff.mpr fun x hx => ?_⟩
    rw [Aux.mem_LIST_TO_SET] at hx
    simp at hx
  | succ n ih =>
    obtain ⟨names, h1, h2, h3⟩ := ih
    obtain ⟨h4, h5⟩ := fresh_union (LIST_TO_SET names) s ⟨Aux.FINITE_LIST_TO_SET names, hs⟩
    rw [Aux.mem_LIST_TO_SET] at h4
    rw [Aux.DISJOINT_iff] at h3
    refine ⟨fresh (UNION (LIST_TO_SET names) s) :: names, by simp [h1], ⟨h4, h2⟩,
      Aux.DISJOINT_iff.mpr fun x hx => ?_⟩
    rw [Aux.mem_LIST_TO_SET] at hx
    rcases List.mem_cons.mp hx with h | h
    · rw [h]; exact h5
    · exact h3 x (Aux.mem_LIST_TO_SET.mpr h)

theorem Aux.bv_names_rename_bvars : ∀ (tm : term) (names : List mlstring)
    (env : List (mlstring × (mlstring × type))), (bv_names tm).length ≤ names.length →
    bv_names (rename_bvars names env tm).2 = names.take (bv_names tm).length := by
  intro tm
  induction tm with
  | Var x ty => intro names env _; simp [rename_bvars, bv_names]
  | Const x ty => intro names env _; simp [rename_bvars, bv_names]
  | Comb s t ihs iht =>
    intro names env h
    simp only [bv_names, List.length_append] at h ⊢
    simp only [rename_bvars, bv_names]
    rw [Aux.FST_rename_bvars s names env (by omega), ihs names env (by omega),
      iht _ env (by rw [List.length_drop]; omega), List.take_add]
  | Abs v t _ iht =>
    intro names env h
    cases names with
    | nil => simp [bv_names] at h
    | cons s' names =>
      simp only [bv_names, List.length_cons] at h ⊢
      simp only [rename_bvars, bv_names, dest_var_def, List.take_succ_cons]
      rw [iht names _ (by omega)]

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
  exact Aux.bv_names_rename_bvars tm names env

/- HOL4:
Theorem FINITE_VFREE_IN[simp]:
   ∀tm. FINITE {x | ∃ty. VFREE_IN (Var x ty) tm} -/
theorem FINITE_VFREE_IN :
    ∀ (tm : term), FINITE (setOf (fun (x : mlstring) => ∃ (ty : type), VFREE_IN (Var x ty) tm)) := by
  intro tm
  obtain ⟨l, hl⟩ := Aux.VFREE_IN_bound tm
  refine Aux.FINITE_iff.mpr ⟨l.map (fun t => (dest_var t).1), ?_⟩
  rintro x ⟨ty, hf⟩
  exact List.mem_map.mpr ⟨_, hl _ hf, by rw [dest_var_def]⟩

/- HOL4:
Theorem FINITE_VFREE_IN_2[simp]:
   ∀tm. FINITE {(x,ty) | VFREE_IN (Var x ty) tm} -/
theorem FINITE_VFREE_IN_2 :
    ∀ (tm : term), FINITE (GSPEC (fun (p : mlstring × type) => ((p.1, p.2), VFREE_IN (Var p.1 p.2) tm))) := by
  intro tm
  obtain ⟨l, hl⟩ := Aux.VFREE_IN_bound tm
  refine Aux.FINITE_iff.mpr ⟨l.map dest_var, fun x hx => ?_⟩
  obtain ⟨p, rfl, hf⟩ := Aux.mem_GSPEC.mp hx
  exact List.mem_map.mpr ⟨_, hl _ hf, by rw [dest_var_def]⟩

/- HOL4:
Theorem FINITE_VFREE_IN_list[simp]:
   ∀ls. FINITE {x | ∃ty u. VFREE_IN (Var x ty) u ∧ MEM u ls} -/
theorem FINITE_VFREE_IN_list :
    ∀ (ls : List term),
        FINITE (setOf (fun (x : mlstring) => ∃ (ty : type) (u : term), VFREE_IN (Var x ty) u ∧ u ∈ ls)) := by
  intro ls
  induction ls with
  | nil =>
    refine Aux.FINITE_iff.mpr ⟨[], ?_⟩
    rintro x ⟨ty, u, _, h⟩
    simp at h
  | cons a ls ih =>
    refine Aux.FINITE_subset (Aux.FINITE_UNION (FINITE_VFREE_IN a) ih) ?_
    rintro x ⟨ty, u, hf, h⟩
    rcases List.mem_cons.mp h with h | h
    · subst h; exact Or.inl ⟨ty, hf⟩
    · exact Or.inr ⟨ty, u, hf, h⟩

/- HOL4:
Theorem FINITE_MEM_Var[simp]:
   ∀ls. FINITE {(x,ty) | MEM (Var x ty) ls} -/
theorem FINITE_MEM_Var :
    ∀ (ls : List term), FINITE (GSPEC (fun (p : mlstring × type) => ((p.1, p.2), Var p.1 p.2 ∈ ls))) := by
  intro ls
  refine Aux.FINITE_iff.mpr ⟨ls.map dest_var, fun x hx => ?_⟩
  obtain ⟨p, rfl, hf⟩ := Aux.mem_GSPEC.mp hx
  exact List.mem_map.mpr ⟨_, hf, by rw [dest_var_def]⟩

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
  constructor <;> cases ls <;> simp [arities_match]

/- HOL4:
Theorem arities_match_Tyvar[simp]:
   arities_match (Tyvar v::ps) (ty::obs) = arities_match ps obs -/
theorem arities_match_Tyvar (v : mlstring) (ps : List type) (ty : type) (obs : List type) :
    arities_match (Tyvar v :: ps) (ty :: obs) = arities_match ps obs := by
  rw [arities_match]
  simp

end

end Candle
