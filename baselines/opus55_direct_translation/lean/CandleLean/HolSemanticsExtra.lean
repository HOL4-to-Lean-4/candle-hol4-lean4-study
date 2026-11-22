import CandleLean.HolSemantics

/-!
# holSemanticsExtra (CakeML `candle/standard/semantics/holSemanticsExtraScript.sml`)

This theory defines no constants.  The ML value used in the statement of `termsem_Equal`,

    val Equalsem =
      is_std_interpretation_def
      |> SPEC_ALL |> concl |> rhs
      |> strip_conj |> last
      |> strip_comb |> snd |> last

is the last argument of `interprets` in `is_std_interpretation_def`, i.e. the term

    λl. Abstract (HD l) (Funspace (HD l) boolset)
          (λx. Abstract (HD l) boolset (λy. Boolean (x = y)))

which in Lean is written
`fun l => abstract mem (HD l) (funspace mem (HD l) (boolset mem))
            (fun x => abstract mem (HD l) (boolset mem) (fun y => boolean mem (x = y)))`.
-/

universe u

namespace Candle

open HOL Classical

noncomputable section

variable {U : Type u}

/- HOL4:
Theorem is_std_interpretation_is_type:
   is_std_interpretation i ⇒ is_std_type_assignment (FST i)
-/
theorem is_std_interpretation_is_type [Nonempty U] (mem : U → U → Prop) (i : interpretation U) :
    is_std_interpretation0 mem i → is_std_type_assignment0 mem i.1 := by sorry

/- HOL4:
Theorem typesem_inhabited:
   is_set_theory ^mem ⇒
    ∀tyenv δ τ ty.
    is_type_valuation τ ∧
    is_type_assignment tyenv δ ∧
    type_ok tyenv ty
    ⇒
    inhabited (typesem δ τ ty)
-/
theorem typesem_inhabited (mem : U → U → Prop) :
    is_set_theory mem →
      ∀ (tyenv : tysig) (δ : tyass U) (τ : tyval U) (ty : type),
        is_type_valuation0 mem τ ∧
        is_type_assignment0 mem tyenv δ ∧
        type_ok tyenv ty →
        inhabited mem (typesem δ τ ty) := by sorry

/- HOL4:
Theorem typesem_Fun:
   ∀δ τ dom rng.
    is_std_type_assignment δ ⇒
    typesem δ τ (Fun dom rng) =
    Funspace (typesem δ τ dom) (typesem δ τ rng)
-/
theorem typesem_Fun [Nonempty U] (mem : U → U → Prop) :
    ∀ (δ : tyass U) (τ : tyval U) (dom rng : type),
      is_std_type_assignment0 mem δ →
      typesem δ τ (Fun dom rng) =
        funspace mem (typesem δ τ dom) (typesem δ τ rng) := by sorry

/- HOL4:
Theorem typesem_Bool:
   ∀δ τ.
    is_std_type_assignment δ ⇒
    typesem δ τ Bool = boolset
-/
theorem typesem_Bool [Nonempty U] (mem : U → U → Prop) :
    ∀ (δ : tyass U) (τ : tyval U),
      is_std_type_assignment0 mem δ →
      typesem δ τ BoolTy = boolset mem := by sorry

/- HOL4:
Theorem typesem_TYPE_SUBST:
   ∀tyin ty δ τ.
      typesem δ τ (TYPE_SUBST tyin ty) =
      typesem δ (λx. typesem δ τ (TYPE_SUBST tyin (Tyvar x))) ty
-/
theorem typesem_TYPE_SUBST :
    ∀ (tyin : List (type × type)) (ty : type) (δ : tyass U) (τ : tyval U),
      typesem δ τ (TYPE_SUBST tyin ty) =
        typesem δ (fun x => typesem δ τ (TYPE_SUBST tyin (Tyvar x))) ty := by sorry

/- HOL4:
Theorem typesem_tyvars:
   ∀δ τ ty τ'.
    (∀x. MEM x (tyvars ty) ⇒ τ' x = τ x) ⇒
    typesem δ τ' ty = typesem δ τ ty
-/
theorem typesem_tyvars :
    ∀ (δ : tyass U) (τ : tyval U) (ty : type) (τ' : tyval U),
      (∀ x, x ∈ tyvars ty → τ' x = τ x) →
      typesem δ τ' ty = typesem δ τ ty := by sorry

/- HOL4:
Theorem termsem_typesem:
   is_set_theory ^mem ⇒
    ∀sig i tm v δ τ tmenv.
      δ = FST i ∧ τ = FST v ∧
      is_valuation (tysof sig) δ v ∧
      is_interpretation sig i ∧
      is_std_type_assignment δ ∧
      term_ok sig tm ∧ tmenv = tmsof sig
      ⇒
      termsem tmenv i v tm <: typesem δ τ (typeof tm)
-/
theorem termsem_typesem [Nonempty U] (mem : U → U → Prop) :
    is_set_theory mem →
      ∀ (sig : sig) (i : interpretation U) (tm : term) (v : valuation U) (δ : tyass U)
        (τ : tyval U) (tmenv : tmsig),
        δ = i.1 ∧ τ = v.1 ∧
        is_valuation0 mem (tysof sig) δ v ∧
        is_interpretation0 mem sig i ∧
        is_std_type_assignment0 mem δ ∧
        term_ok sig tm ∧ tmenv = tmsof sig →
        mem (termsem0 mem tmenv i v tm) (typesem δ τ (typeof tm)) := by sorry

/- HOL4:
Theorem termsem_Equal:
   is_set_theory ^mem ⇒
    ∀Γ i v ty.
      is_structure Γ i v ∧ type_ok (tysof Γ) ty ⇒
      termsem (tmsof Γ) i v (Equal ty) = ^Equalsem [typesem (FST i) (FST v) ty]
   (`^Equalsem` is the term given in CONVENTIONS.md §8) -/
theorem termsem_Equal [Nonempty U] (mem : U → U → Prop) :
    is_set_theory mem →
      ∀ (Γ : sig) (i : interpretation U) (v : valuation U) (ty : type),
        is_structure0 mem Γ i v ∧ type_ok (tysof Γ) ty →
        termsem0 mem (tmsof Γ) i v (Equal ty) =
          (fun l => abstract mem (HD l) (funspace mem (HD l) (boolset mem))
            (fun x => abstract mem (HD l) (boolset mem) (fun y => boolean mem (x = y))))
            [typesem i.1 v.1 ty] := by sorry

/- HOL4:
Theorem termsem_equation:
   is_set_theory ^mem ⇒
    ∀sig i v s t tmenv.
    is_structure sig i v ∧
    term_ok sig (s === t) ∧
    tmenv = tmsof sig
    ⇒ termsem tmenv i v (s === t) = Boolean (termsem tmenv i v s = termsem tmenv i v t)
-/
theorem termsem_equation [Nonempty U] (mem : U → U → Prop) :
    is_set_theory mem →
      ∀ (sig : sig) (i : interpretation U) (v : valuation U) (s t : term) (tmenv : tmsig),
        is_structure0 mem sig i v ∧
        term_ok sig (equation s t) ∧
        tmenv = tmsof sig →
        termsem0 mem tmenv i v (equation s t) =
          boolean mem (termsem0 mem tmenv i v s = termsem0 mem tmenv i v t) := by sorry

/- HOL4:
Theorem termsem_raconv:
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
        termsem Γ i v1 (FST tp) = termsem Γ i v2 (SND tp)
-/
theorem termsem_raconv (mem : U → U → Prop) :
    ∀ (env : List (term × term)) (tp : term × term), RACONV env tp →
      ∀ (Γ : tmsig) (i : interpretation U) (v1 v2 : valuation U),
        v1.1 = v2.1 ∧
        (∀ x1 ty1 x2 ty2,
          ALPHAVARS env (Var x1 ty1, Var x2 ty2) →
            termsem0 mem Γ i v1 (Var x1 ty1) = termsem0 mem Γ i v2 (Var x2 ty2)) ∧
        EVERY (fun (x, y) => welltyped x ∧ welltyped y ∧ typeof x = typeof y) env ∧
        welltyped tp.1 ∧ welltyped tp.2 →
        termsem0 mem Γ i v1 tp.1 = termsem0 mem Γ i v2 tp.2 := by sorry

/- HOL4:
Theorem termsem_aconv:
   ∀Γ i v t1 t2. ACONV t1 t2 ∧ welltyped t1 ∧ welltyped t2 ⇒ termsem Γ i v t1 = termsem Γ i v t2
-/
theorem termsem_aconv (mem : U → U → Prop) :
    ∀ (Γ : tmsig) (i : interpretation U) (v : valuation U) (t1 t2 : term),
      ACONV t1 t2 ∧ welltyped t1 ∧ welltyped t2 →
      termsem0 mem Γ i v t1 = termsem0 mem Γ i v t2 := by sorry

/- HOL4:
Theorem termsem_frees:
   ∀Γ i t v1 v2.
      welltyped t ∧ FST v1 = FST v2 ∧
      (∀x ty. VFREE_IN (Var x ty) t ⇒ SND v1 (x,ty) = SND v2 (x,ty))
      ⇒ termsem Γ i v1 t = termsem Γ i v2 t
-/
theorem termsem_frees (mem : U → U → Prop) :
    ∀ (Γ : tmsig) (i : interpretation U) (t : term) (v1 v2 : valuation U),
      welltyped t ∧ v1.1 = v2.1 ∧
      (∀ x ty, VFREE_IN (Var x ty) t → v1.2 (x, ty) = v2.2 (x, ty)) →
      termsem0 mem Γ i v1 t = termsem0 mem Γ i v2 t := by sorry

/- HOL4:
Theorem termsem_simple_subst:
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
          tm
-/
theorem termsem_simple_subst (mem : U → U → Prop) :
    ∀ (tm : term) (ilist : List (term × term)),
      welltyped tm ∧
      DISJOINT (LIST_TO_SET (bv_names tm))
        (setOf (fun y => ∃ ty u, VFREE_IN (Var y ty) u ∧ u ∈ ilist.map Prod.fst)) ∧
      (∀ s s', (s', s) ∈ ilist → ∃ x ty, s = Var x ty ∧ has_type s' ty) →
      ∀ (Γ : tmsig) (i : interpretation U) (v : valuation U),
        termsem0 mem Γ i v (simple_subst ilist tm) =
          termsem0 mem Γ i
            (v.1, UPDATE_LIST v.2
                    ((ilist.reverse).map
                      (PAIR_MAP dest_var (termsem0 mem Γ i v) ∘ (fun (s', s) => (s, s')))))
            tm := by sorry

/- HOL4:
Theorem termsem_VSUBST:
    ∀tm ilist.
      welltyped tm ∧
      (∀s s'. MEM (s',s) ilist ⇒ ∃x ty. s = Var x ty ∧ s' has_type ty) ⇒
      ∀Γ i v.
       termsem Γ i v (VSUBST ilist tm) =
       termsem Γ i (FST v,
                    SND v =++
                    MAP ((dest_var ## termsem Γ i v) o (λ(s',s). (s,s')))
                      (REVERSE ilist)) tm
-/
theorem termsem_VSUBST (mem : U → U → Prop) :
    ∀ (tm : term) (ilist : List (term × term)),
      welltyped tm ∧
      (∀ s s', (s', s) ∈ ilist → ∃ x ty, s = Var x ty ∧ has_type s' ty) →
      ∀ (Γ : tmsig) (i : interpretation U) (v : valuation U),
        termsem0 mem Γ i v (VSUBST ilist tm) =
          termsem0 mem Γ i
            (v.1, UPDATE_LIST v.2
                    ((ilist.reverse).map
                      (PAIR_MAP dest_var (termsem0 mem Γ i v) ∘ (fun (s', s) => (s, s')))))
            tm := by sorry

/- HOL4:
Theorem termsem_simple_inst:
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
          tm
-/
theorem termsem_simple_inst (mem : U → U → Prop) :
    ∀ (Γ : sig) (tm : term) (tyin : List (type × type)) (tmenv : tmsig),
      welltyped tm ∧ term_ok Γ tm ∧
      ALL_DISTINCT (bv_names tm) ∧
      DISJOINT (LIST_TO_SET (bv_names tm)) (setOf (fun x => ∃ ty, VFREE_IN (Var x ty) tm)) ∧
      tmenv = tmsof Γ →
      ∀ (i : interpretation U) (v : valuation U),
        termsem0 mem tmenv i v (simple_inst tyin tm) =
          termsem0 mem tmenv i
            ((fun x => typesem i.1 v.1 (TYPE_SUBST tyin (Tyvar x))),
             (fun (x, ty) => v.2 (x, TYPE_SUBST tyin ty)))
            tm := by sorry

/- HOL4:
Theorem termsem_INST:
   ∀Γ tm tyin tmenv.
      term_ok Γ tm ∧ tmenv = tmsof Γ ⇒
      ∀i v.
        termsem tmenv i v (INST tyin tm) =
        termsem tmenv i
          ((λx. typesem (FST i) (FST v) (TYPE_SUBST tyin (Tyvar x))),
           (λ(x,ty). SND v (x, TYPE_SUBST tyin ty)))
          tm
-/
theorem termsem_INST (mem : U → U → Prop) :
    ∀ (Γ : sig) (tm : term) (tyin : List (type × type)) (tmenv : tmsig),
      term_ok Γ tm ∧ tmenv = tmsof Γ →
      ∀ (i : interpretation U) (v : valuation U),
        termsem0 mem tmenv i v (INST tyin tm) =
          termsem0 mem tmenv i
            ((fun x => typesem i.1 v.1 (TYPE_SUBST tyin (Tyvar x))),
             (fun (x, ty) => v.2 (x, TYPE_SUBST tyin ty)))
            tm := by sorry

end

end Candle
