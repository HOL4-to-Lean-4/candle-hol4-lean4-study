import CandleLean.HolSemanticsExtra

/-!
# holSoundness (CakeML `candle/standard/semantics/holSoundnessScript.sml`)

This theory defines no constants; its theorems (stage 2) use the constants of
`HolSyntax`, `HolSemantics` and `SetSpec`.
-/

universe u

namespace Candle

open HOL Classical

noncomputable section

variable {U : Type u}

/- HOL4:
Theorem binary_inference_rule:
   is_set_theory ^mem ⇒
    ∀thy h1 h2 p1 p2 q.
    q has_type Bool ∧ term_ok (sigof thy) q ∧
    (∀i v. is_structure (sigof thy) i v ∧
           termsem (tmsof thy) i v p1 = True ∧
           termsem (tmsof thy) i v p2 = True ⇒
           termsem (tmsof thy) i v q = True) ∧
    (thy,h1) |= p1 ∧ (thy,h2) |= p2
    ⇒ (thy, term_union h1 h2) |= q
-/
theorem binary_inference_rule [Nonempty U] (mem : U → U → Prop) :
    is_set_theory mem →
      ∀ (thy : thy) (h1 h2 : List term) (p1 p2 q : term),
        has_type q BoolTy ∧ term_ok (sigof thy) q ∧
        (∀ (i : interpretation U) (v : valuation U),
          is_structure0 mem (sigof thy) i v ∧
          termsem0 mem (thy_tmsof thy) i v p1 = true_ mem ∧
          termsem0 mem (thy_tmsof thy) i v p2 = true_ mem →
          termsem0 mem (thy_tmsof thy) i v q = true_ mem) ∧
        entails0 mem (thy, h1) p1 ∧ entails0 mem (thy, h2) p2 →
        entails0 mem (thy, term_union h1 h2) q := by sorry

/- HOL4:
Theorem ABS_correct:
   is_set_theory ^mem ⇒
    ∀thy x ty h l r.
    ¬EXISTS (VFREE_IN (Var x ty)) h ∧ type_ok (tysof thy) ty ∧
    (thy,h) |= l === r
    ⇒ (thy,h) |= Abs (Var x ty) l === Abs (Var x ty) r
-/
theorem ABS_correct [Nonempty U] (mem : U → U → Prop) :
    is_set_theory mem →
      ∀ (thy : thy) (x : mlstring) (ty : type) (h : List term) (l r : term),
        ¬ EXISTS (VFREE_IN (Var x ty)) h ∧ type_ok (thy_tysof thy) ty ∧
        entails0 mem (thy, h) (equation l r) →
        entails0 mem (thy, h) (equation (Abs (Var x ty) l) (Abs (Var x ty) r)) := by sorry

/- HOL4:
Theorem ASSUME_correct:
   ∀thy p.
      theory_ok thy ∧ p has_type Bool ∧ term_ok (sigof thy) p
      ⇒ (thy,[p]) |= p
-/
theorem ASSUME_correct [Nonempty U] (mem : U → U → Prop) :
    ∀ (thy : thy) (p : term),
      theory_ok thy ∧ has_type p BoolTy ∧ term_ok (sigof thy) p →
      entails0 mem (thy, [p]) p := by sorry

/- HOL4:
Theorem BETA_correct:
   is_set_theory ^mem ⇒
    ∀thy x ty t.
      theory_ok thy ∧ type_ok (tysof thy) ty ∧ term_ok (sigof thy) t ⇒
      (thy,[]) |= Comb (Abs (Var x ty) t) (Var x ty) === t
-/
theorem BETA_correct [Nonempty U] (mem : U → U → Prop) :
    is_set_theory mem →
      ∀ (thy : thy) (x : mlstring) (ty : type) (t : term),
        theory_ok thy ∧ type_ok (thy_tysof thy) ty ∧ term_ok (sigof thy) t →
        entails0 mem (thy, []) (equation (Comb (Abs (Var x ty) t) (Var x ty)) t) := by sorry

/- HOL4:
Theorem DEDUCT_ANTISYM_correct:
   is_set_theory ^mem ⇒
    ∀thy h1 p1 h2 p2.
      (thy,h1) |= p1 ∧ (thy,h2) |= p2 ⇒
      (thy,
       term_union (term_remove p2 h1)
                  (term_remove p1 h2))
      |= p1 === p2
-/
theorem DEDUCT_ANTISYM_correct [Nonempty U] (mem : U → U → Prop) :
    is_set_theory mem →
      ∀ (thy : thy) (h1 : List term) (p1 : term) (h2 : List term) (p2 : term),
        entails0 mem (thy, h1) p1 ∧ entails0 mem (thy, h2) p2 →
        entails0 mem
          (thy, term_union (term_remove p2 h1) (term_remove p1 h2))
          (equation p1 p2) := by sorry

/- HOL4:
Theorem EQ_MP_correct:
   is_set_theory ^mem ⇒
    ∀thy h1 h2 p q p'.
      (thy,h1) |= p === q ∧ (thy,h2) |= p' ∧ ACONV p p' ⇒
      (thy,term_union h1 h2) |= q
-/
theorem EQ_MP_correct [Nonempty U] (mem : U → U → Prop) :
    is_set_theory mem →
      ∀ (thy : thy) (h1 h2 : List term) (p q p' : term),
        entails0 mem (thy, h1) (equation p q) ∧ entails0 mem (thy, h2) p' ∧ ACONV p p' →
        entails0 mem (thy, term_union h1 h2) q := by sorry

/- HOL4:
Theorem INST_correct:
   is_set_theory ^mem ⇒
    ∀thy h c.
      (∀s s'. MEM (s',s) ilist ⇒
              ∃x ty. (s = Var x ty) ∧ s' has_type ty ∧ term_ok (sigof thy) s') ∧
      (thy, h) |= c
    ⇒ (thy, term_image (VSUBST ilist) h) |= VSUBST ilist c
-/
theorem INST_correct [Nonempty U] (mem : U → U → Prop) (ilist : List (term × term)) :
    is_set_theory mem →
      ∀ (thy : thy) (h : List term) (c : term),
        (∀ s s', (s', s) ∈ ilist →
          ∃ x ty, s = Var x ty ∧ has_type s' ty ∧ term_ok (sigof thy) s') ∧
        entails0 mem (thy, h) c →
        entails0 mem (thy, term_image (VSUBST ilist) h) (VSUBST ilist c) := by sorry

/- HOL4:
Theorem INST_TYPE_correct:
   is_set_theory ^mem ⇒
    ∀thy h c.
      EVERY (type_ok (tysof thy)) (MAP FST tyin) ∧
      (thy, h) |= c
    ⇒ (thy, term_image (INST tyin) h) |= INST tyin c
-/
theorem INST_TYPE_correct [Nonempty U] (mem : U → U → Prop) (tyin : List (type × type)) :
    is_set_theory mem →
      ∀ (thy : thy) (h : List term) (c : term),
        EVERY (type_ok (thy_tysof thy)) (tyin.map Prod.fst) ∧
        entails0 mem (thy, h) c →
        entails0 mem (thy, term_image (INST tyin) h) (INST tyin c) := by sorry

/- HOL4:
Theorem MK_COMB_correct:
   is_set_theory ^mem ⇒
    ∀thy h1 h2 l1 r1 l2 r2.
      (thy,h1) |= l1 === r1 ∧ (thy,h2) |= l2 === r2 ∧
      welltyped (Comb l1 l2)
      ⇒ (thy,term_union h1 h2) |= Comb l1 l2 === Comb r1 r2
-/
theorem MK_COMB_correct [Nonempty U] (mem : U → U → Prop) :
    is_set_theory mem →
      ∀ (thy : thy) (h1 h2 : List term) (l1 r1 l2 r2 : term),
        entails0 mem (thy, h1) (equation l1 r1) ∧ entails0 mem (thy, h2) (equation l2 r2) ∧
        welltyped (Comb l1 l2) →
        entails0 mem (thy, term_union h1 h2) (equation (Comb l1 l2) (Comb r1 r2)) := by sorry

/- HOL4:
Theorem REFL_correct:
   is_set_theory ^mem ⇒
    ∀thy t.
      theory_ok thy ∧ term_ok (sigof thy) t ⇒
      (thy,[]) |= t === t
-/
theorem REFL_correct [Nonempty U] (mem : U → U → Prop) :
    is_set_theory mem →
      ∀ (thy : thy) (t : term),
        theory_ok thy ∧ term_ok (sigof thy) t →
        entails0 mem (thy, []) (equation t t) := by sorry

/- HOL4:
Theorem proves_sound:
   is_set_theory ^mem ⇒ ∀thyh c. thyh |- c ⇒ thyh |= c
-/
theorem proves_sound [Nonempty U] (mem : U → U → Prop) :
    is_set_theory mem →
      ∀ (thyh : thy × List term) (c : term), proves thyh c → entails0 mem thyh c := by sorry

end

end Candle
