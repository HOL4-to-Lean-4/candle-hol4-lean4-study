import CandleLean.HolSemantics
/-
  Translation of the definitions of `candle/standard/semantics/holSemanticsExtraScript.sml`.
  The only non-theorem item is the SML value `Equalsem` (a HOL term extracted from
  `is_std_interpretation_def`).  Namespace `Candle.HolSemanticsExtra`.
-/
namespace Candle.HolSemanticsExtra

open HOL Candle.Misc Candle.Mlstring Candle.HolSyntaxLib Candle.HolSyntax Candle.HolSyntaxExtra
open Candle.SetSpec Candle.HolSemantics
universe u

open Classical

noncomputable section

variable {U : Type u}

/- HOL4: val Equalsem =
  is_std_interpretation_def
  |> SPEC_ALL |> concl |> rhs
  |> strip_conj |> last
  |> strip_comb |> snd |> last
   i.e. the term
     λl. Abstract (HD l) (Funspace (HD l) boolset) (λx. Abstract (HD l) boolset (λy. Boolean (x = y)))
   (the last argument of `interprets` in `is_std_interpretation_def`; it depends on `mem`). -/
def Equalsem [Inhabited U] (mem : U → U → Prop) : List U → U :=
  fun l => abstract mem (HD l) (funspace mem (HD l) (boolset mem))
    (fun x => abstract mem (HD l) (boolset mem) (fun y => boolean mem (x = y)))


/- HOL4: Theorem is_std_interpretation_is_type:
   is_std_interpretation i ⇒ is_std_type_assignment (FST i)
   (`mem` is a free HOL4 variable, hence an explicit argument) -/
theorem is_std_interpretation_is_type [Inhabited U] (mem : U → U → Prop) (i : interpretation U) :
    is_std_interpretation mem i → is_std_type_assignment mem (FST i) := by sorry

/- HOL4: Theorem typesem_inhabited:
   is_set_theory ^mem ⇒
    ∀tyenv δ τ ty.
    is_type_valuation τ ∧
    is_type_assignment tyenv δ ∧
    type_ok tyenv ty
    ⇒
    inhabited (typesem δ τ ty) -/
theorem typesem_inhabited (mem : U → U → Prop) : is_set_theory mem →
    ∀ (tyenv : tysig) (δ : tyass U) (τ : tyval U) (ty : type),
      is_type_valuation mem τ ∧
      is_type_assignment mem tyenv δ ∧
      type_ok tyenv ty
      →
      inhabited mem (typesem δ τ ty) := by sorry

/- HOL4: Theorem typesem_Fun:
   ∀δ τ dom rng.
    is_std_type_assignment δ ⇒
    typesem δ τ (Fun dom rng) =
    Funspace (typesem δ τ dom) (typesem δ τ rng) -/
theorem typesem_Fun [Inhabited U] (mem : U → U → Prop) :
    ∀ (δ : tyass U) (τ : tyval U) (dom rng : type),
      is_std_type_assignment mem δ →
      typesem δ τ (Fun dom rng) =
      funspace mem (typesem δ τ dom) (typesem δ τ rng) := by sorry

/- HOL4: Theorem typesem_Bool:
   ∀δ τ.
    is_std_type_assignment δ ⇒
    typesem δ τ Bool = boolset -/
theorem typesem_Bool [Inhabited U] (mem : U → U → Prop) :
    ∀ (δ : tyass U) (τ : tyval U),
      is_std_type_assignment mem δ →
      typesem δ τ BoolTy = boolset mem := by sorry

/- HOL4: Theorem typesem_TYPE_SUBST:
   ∀tyin ty δ τ.
      typesem δ τ (TYPE_SUBST tyin ty) =
      typesem δ (λx. typesem δ τ (TYPE_SUBST tyin (Tyvar x))) ty -/
theorem typesem_TYPE_SUBST : ∀ (tyin : List (type × type)) (ty : type) (δ : tyass U) (τ : tyval U),
    typesem δ τ (TYPE_SUBST tyin ty) =
    typesem δ (fun x => typesem δ τ (TYPE_SUBST tyin (Tyvar x))) ty := by sorry

/- HOL4: Theorem typesem_tyvars:
   ∀δ τ ty τ'.
    (∀x. MEM x (tyvars ty) ⇒ τ' x = τ x) ⇒
    typesem δ τ' ty = typesem δ τ ty -/
theorem typesem_tyvars : ∀ (δ : tyass U) (τ : tyval U) (ty : type) (τ' : tyval U),
    (∀ x, MEM x (tyvars ty) → τ' x = τ x) →
    typesem δ τ' ty = typesem δ τ ty := by sorry

/- HOL4: Theorem termsem_typesem:
   is_set_theory ^mem ⇒
    ∀sig i tm v δ τ tmenv.
      δ = FST i ∧ τ = FST v ∧
      is_valuation (tysof sig) δ v ∧
      is_interpretation sig i ∧
      is_std_type_assignment δ ∧
      term_ok sig tm ∧ tmenv = tmsof sig
      ⇒
      termsem tmenv i v tm <: typesem δ τ (typeof tm) -/
theorem termsem_typesem [Inhabited U] (mem : U → U → Prop) : is_set_theory mem →
    ∀ (sig : sig) (i : interpretation U) (tm : term) (v : valuation U) (δ : tyass U) (τ : tyval U)
      (tmenv : tmsig),
      δ = FST i ∧ τ = FST v ∧
      is_valuation mem (tysof sig) δ v ∧
      is_interpretation mem sig i ∧
      is_std_type_assignment mem δ ∧
      term_ok sig tm ∧ tmenv = tmsof sig
      →
      mem (termsem mem tmenv i v tm) (typesem δ τ (typeof tm)) := by sorry

/- HOL4: Theorem termsem_Equal:
   is_set_theory ^mem ⇒
    ∀Γ i v ty.
      is_structure Γ i v ∧ type_ok (tysof Γ) ty ⇒
      termsem (tmsof Γ) i v (Equal ty) = ^Equalsem [typesem (FST i) (FST v) ty] -/
theorem termsem_Equal [Inhabited U] (mem : U → U → Prop) : is_set_theory mem →
    ∀ (Γ : sig) (i : interpretation U) (v : valuation U) (ty : type),
      is_structure mem Γ i v ∧ type_ok (tysof Γ) ty →
      termsem mem (tmsof Γ) i v (Equal ty) = Equalsem mem [typesem (FST i) (FST v) ty] := by sorry

/- HOL4: Theorem termsem_equation:
   is_set_theory ^mem ⇒
    ∀sig i v s t tmenv.
    is_structure sig i v ∧
    term_ok sig (s === t) ∧
    tmenv = tmsof sig
    ⇒ termsem tmenv i v (s === t) = Boolean (termsem tmenv i v s = termsem tmenv i v t) -/
theorem termsem_equation [Inhabited U] (mem : U → U → Prop) : is_set_theory mem →
    ∀ (sig : sig) (i : interpretation U) (v : valuation U) (s t : term) (tmenv : tmsig),
      is_structure mem sig i v ∧
      term_ok sig (equation s t) ∧
      tmenv = tmsof sig
      → termsem mem tmenv i v (equation s t) =
        boolean mem (termsem mem tmenv i v s = termsem mem tmenv i v t) := by sorry

/- HOL4: Theorem termsem_raconv:
   ∀env tp. RACONV env tp ⇒
      ∀Γ i v1 v2.
        (FST v1 = FST v2) ∧
        (∀x1 ty1 x2 ty2.
          ALPHAVARS env (Var x1 ty1,Var x2 ty2) ⇒
            (termsem Γ i v1 (Var x1 ty1) =
             termsem Γ i v2 (Var x2 ty2))) ∧
        EVERY (λ(x,y). welltyped x ∧ welltyped y ∧ typeof x = typeof y) env ∧
        welltyped (FST tp) ∧ welltyped (SND tp)
        ⇒
        termsem Γ i v1 (FST tp) = termsem Γ i v2 (SND tp) -/
theorem termsem_raconv [Inhabited U] (mem : U → U → Prop) :
    ∀ (env : List (term × term)) (tp : term × term), RACONV env tp →
      ∀ (Γ : tmsig) (i : interpretation U) (v1 v2 : valuation U),
        (FST v1 = FST v2) ∧
        (∀ x1 ty1 x2 ty2,
          ALPHAVARS env (Var x1 ty1, Var x2 ty2) →
            (termsem mem Γ i v1 (Var x1 ty1) =
             termsem mem Γ i v2 (Var x2 ty2))) ∧
        EVERY (fun p : term × term => welltyped p.1 ∧ welltyped p.2 ∧ typeof p.1 = typeof p.2) env ∧
        welltyped (FST tp) ∧ welltyped (SND tp)
        →
        termsem mem Γ i v1 (FST tp) = termsem mem Γ i v2 (SND tp) := by sorry

/- HOL4: Theorem termsem_aconv:
   ∀Γ i v t1 t2. ACONV t1 t2 ∧ welltyped t1 ∧ welltyped t2 ⇒ termsem Γ i v t1 = termsem Γ i v t2 -/
theorem termsem_aconv [Inhabited U] (mem : U → U → Prop) :
    ∀ (Γ : tmsig) (i : interpretation U) (v : valuation U) (t1 t2 : term),
      ACONV t1 t2 ∧ welltyped t1 ∧ welltyped t2 →
      termsem mem Γ i v t1 = termsem mem Γ i v t2 := by sorry

/- HOL4: Theorem termsem_frees:
   ∀Γ i t v1 v2.
      welltyped t ∧ FST v1 = FST v2 ∧
      (∀x ty. VFREE_IN (Var x ty) t ⇒ SND v1 (x,ty) = SND v2 (x,ty))
      ⇒ termsem Γ i v1 t = termsem Γ i v2 t -/
theorem termsem_frees [Inhabited U] (mem : U → U → Prop) :
    ∀ (Γ : tmsig) (i : interpretation U) (t : term) (v1 v2 : valuation U),
      welltyped t ∧ FST v1 = FST v2 ∧
      (∀ x ty, VFREE_IN (Var x ty) t → SND v1 (x, ty) = SND v2 (x, ty))
      → termsem mem Γ i v1 t = termsem mem Γ i v2 t := by sorry

/- HOL4: Theorem termsem_simple_subst:
   ∀tm ilist.
      welltyped tm ∧
      DISJOINT (set (bv_names tm)) {y | ∃ty u. VFREE_IN (Var y ty) u ∧ MEM u (MAP FST ilist)} ∧
      (∀s s'. MEM (s',s) ilist ⇒ ∃x ty. s = Var x ty ∧ s' has_type ty)
      ⇒
      ∀Γ i v.
        termsem Γ i v (simple_subst ilist tm) =
        termsem Γ i
          (FST v, SND v =++
                  MAP ((dest_var ## termsem Γ i v) o (λ(s',s). (s,s')))
                      (REVERSE ilist))
          tm -/
theorem termsem_simple_subst [Inhabited U] (mem : U → U → Prop) :
    ∀ (tm : term) (ilist : List (term × term)),
      welltyped tm ∧
      DISJOINT (LIST_TO_SET (bv_names tm))
        { y | ∃ ty u, VFREE_IN (Var y ty) u ∧ MEM u (MAP FST ilist) } ∧
      (∀ s s', MEM (s', s) ilist → ∃ x ty, s = Var x ty ∧ has_type s' ty)
      →
      ∀ (Γ : tmsig) (i : interpretation U) (v : valuation U),
        termsem mem Γ i v (simple_subst ilist tm) =
        termsem mem Γ i
          (FST v, (SND v) =++
                  MAP ((dest_var ## termsem mem Γ i v) ∘ (fun p : term × term => (p.2, p.1)))
                      (REVERSE ilist))
          tm := by sorry

/- HOL4: Theorem termsem_VSUBST:
    ∀tm ilist.
      welltyped tm ∧
      (∀s s'. MEM (s',s) ilist ⇒ ∃x ty. s = Var x ty ∧ s' has_type ty) ⇒
      ∀Γ i v.
       termsem Γ i v (VSUBST ilist tm) =
       termsem Γ i (FST v,
                    SND v =++
                    MAP ((dest_var ## termsem Γ i v) o (λ(s',s). (s,s')))
                      (REVERSE ilist)) tm -/
theorem termsem_VSUBST [Inhabited U] (mem : U → U → Prop) :
    ∀ (tm : term) (ilist : List (term × term)),
      welltyped tm ∧
      (∀ s s', MEM (s', s) ilist → ∃ x ty, s = Var x ty ∧ has_type s' ty) →
      ∀ (Γ : tmsig) (i : interpretation U) (v : valuation U),
       termsem mem Γ i v (VSUBST ilist tm) =
       termsem mem Γ i (FST v,
                    (SND v) =++
                    MAP ((dest_var ## termsem mem Γ i v) ∘ (fun p : term × term => (p.2, p.1)))
                      (REVERSE ilist)) tm := by sorry

/- HOL4: Theorem termsem_simple_inst:
   ∀Γ tm tyin tmenv.
      welltyped tm ∧ term_ok Γ tm ∧
      ALL_DISTINCT (bv_names tm) ∧
      DISJOINT (set (bv_names tm)) {x | ∃ty. VFREE_IN (Var x ty) tm} ∧
      tmenv = tmsof Γ
      ⇒
      ∀i v.
        termsem tmenv i v (simple_inst tyin tm) =
        termsem tmenv i
          ((λx. typesem (FST i) (FST v) (TYPE_SUBST tyin (Tyvar x))),
           (λ(x,ty). SND v (x, TYPE_SUBST tyin ty)))
          tm -/
theorem termsem_simple_inst [Inhabited U] (mem : U → U → Prop) :
    ∀ (Γ : sig) (tm : term) (tyin : List (type × type)) (tmenv : tmsig),
      welltyped tm ∧ term_ok Γ tm ∧
      ALL_DISTINCT (bv_names tm) ∧
      DISJOINT (LIST_TO_SET (bv_names tm)) { x | ∃ ty, VFREE_IN (Var x ty) tm } ∧
      tmenv = tmsof Γ
      →
      ∀ (i : interpretation U) (v : valuation U),
        termsem mem tmenv i v (simple_inst tyin tm) =
        termsem mem tmenv i
          ((fun x => typesem (FST i) (FST v) (TYPE_SUBST tyin (Tyvar x))),
           (fun p : mlstring × type => SND v (p.1, TYPE_SUBST tyin p.2)))
          tm := by sorry

/- HOL4: Theorem termsem_INST:
   ∀Γ tm tyin tmenv.
      term_ok Γ tm ∧ tmenv = tmsof Γ ⇒
      ∀i v.
        termsem tmenv i v (INST tyin tm) =
        termsem tmenv i
          ((λx. typesem (FST i) (FST v) (TYPE_SUBST tyin (Tyvar x))),
           (λ(x,ty). SND v (x, TYPE_SUBST tyin ty)))
          tm -/
theorem termsem_INST [Inhabited U] (mem : U → U → Prop) :
    ∀ (Γ : sig) (tm : term) (tyin : List (type × type)) (tmenv : tmsig),
      term_ok Γ tm ∧ tmenv = tmsof Γ →
      ∀ (i : interpretation U) (v : valuation U),
        termsem mem tmenv i v (INST tyin tm) =
        termsem mem tmenv i
          ((fun x => typesem (FST i) (FST v) (TYPE_SUBST tyin (Tyvar x))),
           (fun p : mlstring × type => SND v (p.1, TYPE_SUBST tyin p.2)))
          tm := by sorry

end

end Candle.HolSemanticsExtra
