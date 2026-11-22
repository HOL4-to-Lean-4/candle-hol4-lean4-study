import CandleLean.HolSyntaxExtra
/-
  Translation of `candle/standard/semantics/holSemanticsScript.sml`.
  Namespace `Candle.HolSemantics`.
  HOL4 writes `is_type_assignment0 ^mem ...` for the definitions and overloads
  `is_type_assignment = is_type_assignment0 ^mem` (with the variable `mem:'U->'U->bool` fixed).
  In Lean the definitions are called without the trailing `0` and take `mem` as first explicit argument.
-/
namespace Candle.HolSemantics

open HOL Candle.Misc Candle.Mlstring Candle.HolSyntaxLib Candle.HolSyntax Candle.HolSyntaxExtra
open Candle.SetSpec
universe u

open Classical

noncomputable section

variable {U : Type u}

/- HOL4: Overload inhabited = ``λs. ∃x. x <: s`` -/
def inhabited (mem : U → U → Prop) (s : U) : Prop := ∃ x, mem x s

/- HOL4: Type tyass = ``:mlstring -> 'U list -> 'U`` -/
abbrev tyass (U : Type u) := mlstring → List U → U

/- HOL4: Definition is_type_assignment_def:
  is_type_assignment0 ^mem tysig (δ:'U tyass) ⇔
    FEVERY
      (λ(name,arity).
        ∀ls. LENGTH ls = arity ∧ EVERY inhabited ls ⇒
             inhabited ((δ name) ls))
      tysig
End -/
def is_type_assignment (mem : U → U → Prop) (tysig : tysig) (δ : tyass U) : Prop :=
  FEVERY (fun p => ∀ ls, LENGTH ls = p.2 ∧ EVERY (inhabited mem) ls → inhabited mem ((δ p.1) ls)) tysig

/- HOL4: Type tyval = ``:mlstring -> 'U`` -/
abbrev tyval (U : Type u) := mlstring → U

/- HOL4: Definition is_type_valuation_def:
  is_type_valuation0 ^mem (τ:'U tyval) ⇔ ∀x. inhabited (τ x)
End -/
def is_type_valuation (mem : U → U → Prop) (τ : tyval U) : Prop := ∀ x, inhabited mem (τ x)

/- HOL4: Definition typesem_def:
  (typesem δ (τ:'U tyval) (Tyvar s) = τ s) ∧
  (typesem δ τ (Tyapp name args) =
    (δ name) (MAP (typesem δ τ) args))
Termination
  type_rec_tac "SND o SND"
End
   (nested recursion through MAP is expressed with the auxiliary `typesem_list δ τ args`,
    `= MAP (typesem δ τ) args`, see `typesem_list_eq`.) -/
mutual
def typesem (δ : tyass U) (τ : tyval U) : type → U
  | .Tyvar s => τ s
  | .Tyapp name args => (δ name) (typesem_list δ τ args)
def typesem_list (δ : tyass U) (τ : tyval U) : List type → List U
  | [] => []
  | t :: ts => typesem δ τ t :: typesem_list δ τ ts
end

/-- Helper: the auxiliary function is `MAP (typesem δ τ)`. -/
theorem typesem_list_eq (δ : tyass U) (τ : tyval U) (tys : List type) :
    typesem_list δ τ tys = MAP (typesem δ τ) tys := by
  induction tys with
  | nil => rfl
  | cons t ts ih => simp [typesem_list, MAP, ih]

/- HOL4: Type tmass = ``:mlstring -> 'U list -> 'U`` -/
abbrev tmass (U : Type u) := mlstring → List U → U

/- HOL4: Definition is_term_assignment_def:
  is_term_assignment0 ^mem tmsig δ (γ:'U tmass) ⇔
    FEVERY
      (λ(name,ty).
        ∀τ. is_type_valuation τ ⇒
              γ name (MAP τ (MAP implode (STRING_SORT (MAP explode (tyvars ty))))) <: typesem δ τ ty)
      tmsig
End -/
def is_term_assignment (mem : U → U → Prop) (tmsig : tmsig) (δ : tyass U) (γ : tmass U) : Prop :=
  FEVERY (fun p => ∀ τ, is_type_valuation mem τ →
      mem (γ p.1 (MAP τ (MAP .implode (STRING_SORT (MAP explode (tyvars p.2)))))) (typesem δ τ p.2))
    tmsig

/- HOL4: Type tmval = ``:mlstring # type -> 'U`` -/
abbrev tmval (U : Type u) := mlstring × type → U

/- HOL4: Definition is_term_valuation_def:
  is_term_valuation0 ^mem tysig δ τ (σ:'U tmval) ⇔
    ∀v ty. type_ok tysig ty ⇒ σ (v,ty) <: typesem δ τ ty
End -/
def is_term_valuation (mem : U → U → Prop) (tysig : tysig) (δ : tyass U) (τ : tyval U) (σ : tmval U) : Prop :=
  ∀ v ty, type_ok tysig ty → mem (σ (v, ty)) (typesem δ τ ty)

/- HOL4: Type interpretation = ``:'U tyass # 'U tmass`` -/
abbrev interpretation (U : Type u) := tyass U × tmass U
/- HOL4: Overload tyaof = ``FST:'U interpretation->'U tyass`` -/
abbrev tyaof (i : interpretation U) : tyass U := i.1
/- HOL4: Overload tmaof = ``SND:'U interpretation->'U tmass`` -/
abbrev tmaof (i : interpretation U) : tmass U := i.2
/- HOL4: Type valuation = ``:'U tyval # 'U tmval`` -/
abbrev valuation (U : Type u) := tyval U × tmval U
/- HOL4: Overload tyvof = ``FST:'U valuation->'U tyval`` -/
abbrev tyvof (v : valuation U) : tyval U := v.1
/- HOL4: Overload tmvof = ``SND:'U valuation->'U tmval`` -/
abbrev tmvof (v : valuation U) : tmval U := v.2

/- HOL4: Definition is_valuation_def:
  is_valuation0 ^mem tysig δ v ⇔
    is_type_valuation (tyvof v) ∧
    is_term_valuation tysig δ (tyvof v) (tmvof v)
End -/
def is_valuation (mem : U → U → Prop) (tysig : tysig) (δ : tyass U) (v : valuation U) : Prop :=
  is_type_valuation mem (tyvof v) ∧ is_term_valuation mem tysig δ (tyvof v) (tmvof v)

/- HOL4: val instance_def = new_specification("instance_def",["instance"],
  Q.prove(`∃f. ∀tmsig (i:'U interpretation) name ty ty0 tyin.
              FLOOKUP tmsig name = SOME ty0 ∧
              ty = TYPE_SUBST tyin ty0
              ⇒
              f tmsig i name ty =
              λτ. tmaof i name
                (MAP (typesem (tyaof i) τ o TYPE_SUBST tyin o Tyvar) (MAP implode (STRING_SORT (MAP explode (tyvars ty0)))))`, ...))
   The Lean name is `instance_` (`instance` is a Lean keyword).  The specification is met by
   choosing `ty0`, `tyin` when they exist (the value does not depend on the choice); otherwise
   (unspecified in HOL4) the value is `tmaof i name []`, independent of the valuation. -/
def instance_ (tmsig : tmsig) (i : interpretation U) (name : mlstring) (ty : type) : tyval U → U :=
  if h : ∃ ty0 tyin, FLOOKUP tmsig name = some ty0 ∧ ty = TYPE_SUBST tyin ty0 then
    fun τ => tmaof i name
      (MAP (typesem (tyaof i) τ ∘ TYPE_SUBST (Classical.choose (Classical.choose_spec h)) ∘ Tyvar)
        (MAP .implode (STRING_SORT (MAP explode (tyvars (Classical.choose h))))))
  else fun _ => tmaof i name []

/- HOL4: Definition termsem_def:
  (termsem0 ^mem (tmsig:tmsig) (i:'U interpretation) (v:'U valuation) (Var x ty) = tmvof v (x,ty)) ∧
  (termsem0 ^mem tmsig i v (Const name ty) = instance tmsig i name ty (tyvof v)) ∧
  (termsem0 ^mem tmsig i v (Comb t1 t2) =
   termsem0 ^mem tmsig i v t1 ' (termsem0 ^mem tmsig i v t2)) ∧
  (termsem0 ^mem tmsig i v (Abs (Var x ty) b) =
   Abstract (typesem (tyaof i) (tyvof v) ty) (typesem (tyaof i) (tyvof v) (typeof b))
     (λm. termsem0 ^mem tmsig i (tyvof v, ((x,ty)=+m)(tmvof v)) b))
End
   (`Abs` of a non-variable is unspecified in HOL4; here `ARB`.  `f ' x` is `apply mem f x`.) -/
def termsem [Inhabited U] (mem : U → U → Prop) (tmsig : tmsig) (i : interpretation U) :
    valuation U → term → U
  | v, .Var x ty => tmvof v (x, ty)
  | v, .Const name ty => instance_ tmsig i name ty (tyvof v)
  | v, .Comb t1 t2 => apply mem (termsem mem tmsig i v t1) (termsem mem tmsig i v t2)
  | v, .Abs (.Var x ty) b =>
    abstract mem (typesem (tyaof i) (tyvof v) ty) (typesem (tyaof i) (tyvof v) (typeof b))
      (fun m => termsem mem tmsig i (tyvof v, (UPDATE (x, ty) m) (tmvof v)) b)
  | _, .Abs _ _ => ARB

/- HOL4: Definition satisfies_def:
  satisfies0 ^mem i (sig:sig,h,c) ⇔
    ∀v. is_valuation (tysof sig) (tyaof i) v ∧
      EVERY (λt. termsem (tmsof sig) i v t = True) h
      ⇒ termsem (tmsof sig) i v c = True
End   (infix `i satisfies (sig,h,c)`) -/
def satisfies [Inhabited U] (mem : U → U → Prop) (i : interpretation U) (s : sig × List term × term) : Prop :=
  ∀ v, is_valuation mem (tysof s.1) (tyaof i) v ∧
      EVERY (fun t => termsem mem (tmsof s.1) i v t = mtrue mem) s.2.1
      → termsem mem (tmsof s.1) i v s.2.2 = mtrue mem

/- HOL4: Definition is_interpretation_def:
  is_interpretation0 ^mem (sig:sig) int ⇔
    is_type_assignment (tysof sig) (tyaof int) ∧
    is_term_assignment (tmsof sig) (tyaof int) (tmaof int)
End -/
def is_interpretation (mem : U → U → Prop) (sig : sig) (int : interpretation U) : Prop :=
  is_type_assignment mem (tysof sig) (tyaof int) ∧
  is_term_assignment mem (tmsof sig) (tyaof int) (tmaof int)

/- HOL4: Definition is_std_type_assignment_def:
  is_std_type_assignment0 ^mem (δ:'U tyass) ⇔
    (∀dom rng. δ «fun» [dom;rng] = Funspace dom rng) ∧
    (δ «bool» [] = boolset)
End -/
def is_std_type_assignment [Inhabited U] (mem : U → U → Prop) (δ : tyass U) : Prop :=
  (∀ dom rng, δ (ml "fun") [dom, rng] = funspace mem dom rng) ∧
  (δ (ml "bool") [] = boolset mem)

/- HOL4: Definition interprets_def:
  interprets0 ^mem γ name vs f ⇔ ∀τ. is_type_valuation τ ⇒ γ name (MAP τ vs) = f (MAP τ vs)
End   (infix `γ interprets name on vs as f`) -/
def interprets (mem : U → U → Prop) (γ : tmass U) (name : mlstring) (vs : List mlstring)
    (f : List U → U) : Prop :=
  ∀ τ, is_type_valuation mem τ → γ name (MAP τ vs) = f (MAP τ vs)

/- HOL4: Definition is_std_interpretation_def:
  is_std_interpretation0 ^mem (i:'U interpretation) ⇔
    is_std_type_assignment (tyaof i) ∧
    tmaof i interprets «=» on [«A»] as
    λl. (Abstract (HD l) (Funspace (HD l) boolset)
          (λx. Abstract (HD l) boolset (λy. Boolean (x = y))))
End -/
def is_std_interpretation [Inhabited U] (mem : U → U → Prop) (i : interpretation U) : Prop :=
  is_std_type_assignment mem (tyaof i) ∧
  interprets mem (tmaof i) (ml "=") [ml "A"]
    (fun l => abstract mem (HD l) (funspace mem (HD l) (boolset mem))
      (fun x => abstract mem (HD l) (boolset mem) (fun y => boolean mem (x = y))))

/- HOL4: Definition models_def:
  models0 ^mem i (thy:thy) ⇔
    is_interpretation (sigof thy) i ∧
    is_std_interpretation i ∧
    ∀p. p ∈ (axsof thy) ⇒ i satisfies (sigof thy,[],p)
End   (infix `i models thy`) -/
def models [Inhabited U] (mem : U → U → Prop) (i : interpretation U) (thy : thy) : Prop :=
  is_interpretation mem (sigof thy) i ∧
  is_std_interpretation mem i ∧
  ∀ p, p ∈ axsof thy → satisfies mem i (sigof thy, [], p)

/- HOL4: Definition entails_def:
  entails0 ^mem (thy,h) c ⇔
    theory_ok thy ∧
    EVERY (term_ok (sigof thy)) (c::h) ∧
    EVERY (λp. p has_type Bool) (c::h) ∧
    hypset_ok h ∧
    ∀i. i models thy
        ⇒ i satisfies (sigof thy,h,c)
End   (infix `(thy,h) |= c`, i.e. `entails mem (thy,h) c`) -/
def entails [Inhabited U] (mem : U → U → Prop) (p : thy × List term) (c : term) : Prop :=
  theory_ok p.1 ∧
  EVERY (term_ok (sigof p.1)) (c :: p.2) ∧
  EVERY (fun q => has_type q BoolTy) (c :: p.2) ∧
  hypset_ok p.2 ∧
  ∀ i, models mem i p.1 → satisfies mem i (sigof p.1, p.2, c)

/- HOL4: Definition is_structure_def:
  is_structure0 ^mem sig int val ⇔
    is_std_sig sig ∧
    is_std_interpretation int ∧
    is_interpretation sig int ∧
    is_valuation (tysof sig) (tyaof int) val
End -/
def is_structure [Inhabited U] (mem : U → U → Prop) (sig : sig) (int : interpretation U) (val : valuation U) : Prop :=
  is_std_sig sig ∧
  is_std_interpretation mem int ∧
  is_interpretation mem sig int ∧
  is_valuation mem (tysof sig) (tyaof int) val

end

end Candle.HolSemantics
