import CandleLean
universe u
namespace Candle
open HOL Classical
noncomputable section
variable {U : Type u}
theorem restated_termsem_simple_inst (mem : U → U → Prop) :
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
            tm := termsem_simple_inst mem
#print axioms restated_termsem_simple_inst
theorem restated_termsem_INST (mem : U → U → Prop) :
    ∀ (Γ : sig) (tm : term) (tyin : List (type × type)) (tmenv : tmsig),
      term_ok Γ tm ∧ tmenv = tmsof Γ →
      ∀ (i : interpretation U) (v : valuation U),
        termsem0 mem tmenv i v (INST tyin tm) =
          termsem0 mem tmenv i
            ((fun x => typesem i.1 v.1 (TYPE_SUBST tyin (Tyvar x))),
             (fun (x, ty) => v.2 (x, TYPE_SUBST tyin ty)))
            tm := termsem_INST mem
#print axioms restated_termsem_INST
