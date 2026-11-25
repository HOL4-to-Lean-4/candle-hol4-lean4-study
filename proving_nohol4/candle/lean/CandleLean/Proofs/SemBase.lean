import CandleLean.HolSemantics
import CandleLean.HolSyntaxExtra2

/-! Auxiliary lemmas about the semantics (all in `Candle.Aux`). -/

universe u

namespace Candle

open HOL Classical

variable {U : Type u}

theorem Aux.termsem_Var (mem : U → U → Prop) (Γ : tmsig) (i : interpretation U) (v : valuation U)
    (x : mlstring) (ty : type) : termsem0 mem Γ i v (Var x ty) = v.2 (x, ty) :=
  (termsem0_def mem Γ i).1 v x ty

theorem Aux.termsem_Const (mem : U → U → Prop) (Γ : tmsig) (i : interpretation U) (v : valuation U)
    (x : mlstring) (ty : type) : termsem0 mem Γ i v (Const x ty) = instance_ Γ i x ty v.1 :=
  (termsem0_def mem Γ i).2.1 v x ty

theorem Aux.termsem_Comb (mem : U → U → Prop) (Γ : tmsig) (i : interpretation U) (v : valuation U)
    (s t : term) : termsem0 mem Γ i v (Comb s t) =
      apply mem (termsem0 mem Γ i v s) (termsem0 mem Γ i v t) :=
  (termsem0_def mem Γ i).2.2.1 v s t

theorem Aux.termsem_Abs (mem : U → U → Prop) (Γ : tmsig) (i : interpretation U) (v : valuation U)
    (x : mlstring) (ty : type) (b : term) : termsem0 mem Γ i v (Abs (Var x ty) b) =
      abstract mem (typesem i.1 v.1 ty) (typesem i.1 v.1 (typeof b))
        (fun m => termsem0 mem Γ i (v.1, UPDATE (x, ty) m v.2) b) :=
  (termsem0_def mem Γ i).2.2.2 v x ty b

theorem Aux.instance_eq {Γ : tmsig} {i : interpretation U} {name : mlstring} {ty0 : type}
    {tyin : List (type × type)} {τ : tyval U} (h : FLOOKUP Γ name = some ty0) :
    instance_ Γ i name (TYPE_SUBST tyin ty0) τ =
      i.2 name (((STRING_SORT ((tyvars ty0).map explode)).map implode).map
        (fun x => typesem i.1 τ (TYPE_SUBST tyin (Tyvar x)))) :=
  congrFun (instance_def Γ i name _ ty0 tyin ⟨h, rfl⟩) τ

theorem Aux.mem_sorted_tyvars (x : mlstring) (l : List mlstring) :
    x ∈ (STRING_SORT (l.map explode)).map implode ↔ x ∈ l := by
  simp only [List.mem_map, Aux.mem_STRING_SORT_iff]
  constructor
  · rintro ⟨s, ⟨a, ha, rfl⟩, rfl⟩
    rw [implode_explode]
    exact ha
  · intro h
    exact ⟨_, ⟨x, h, rfl⟩, implode_explode x⟩

theorem Aux.UPDATE_same {α : Type u} {β : Type v} (a : α) (b : β) (f : α → β) :
    UPDATE a b f a = b := by
  simp [UPDATE]

theorem Aux.UPDATE_ne {α : Type u} {β : Type v} {a c : α} (b : β) (f : α → β) (h : ¬ a = c) :
    UPDATE a b f c = f c := by
  simp [UPDATE, h]

/-- the updated valuation used in `termsem_VSUBST` -/
noncomputable def Aux.upd (mem : U → U → Prop) (Γ : tmsig) (i : interpretation U) (v : valuation U)
    (ilist : List (term × term)) : tmval U :=
  UPDATE_LIST v.2 ((ilist.reverse).map
    (PAIR_MAP dest_var (termsem0 mem Γ i v) ∘ (fun (s', s) => (s, s'))))

theorem Aux.upd_val (mem : U → U → Prop) (Γ : tmsig) (i : interpretation U) (v : valuation U)
    (ilist : List (term × term)) (h : ∀ s s', (s', s) ∈ ilist → ∃ x ty, s = Var x ty)
    (x : mlstring) (ty : type) :
    Aux.upd mem Γ i v ilist (x, ty) =
      termsem0 mem Γ i v (REV_ASSOCD (Var x ty) ilist (Var x ty)) := by
  unfold Aux.upd
  rw [APPLY_UPDATE_LIST_ALOOKUP, ← List.map_reverse, List.reverse_reverse]
  induction ilist with
  | nil => exact (Aux.termsem_Var mem Γ i v x ty).symm
  | cons p l ih =>
    obtain ⟨s', s⟩ := p
    obtain ⟨y, yty, e⟩ := h s s' List.mem_cons_self
    subst e
    have ih := ih (fun s s' hm => h s s' (List.mem_cons_of_mem _ hm))
    simp only [List.map_cons, Function.comp_apply, PAIR_MAP, dest_var_def, ALOOKUP, REV_ASSOCD,
      Prod.mk.injEq, term.Var.injEq]
    by_cases hc : y = x ∧ yty = ty
    · rw [if_pos hc, if_pos hc]
    · rw [if_neg hc, if_neg hc]
      exact ih

end Candle
