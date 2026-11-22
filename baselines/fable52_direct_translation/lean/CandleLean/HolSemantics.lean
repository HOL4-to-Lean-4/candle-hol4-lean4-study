/-
  HOL4 theory `holSemantics` (candle/standard/semantics/holSemanticsScript.sml):
  semantics of HOL sequents.

  HOL4 hides `mem` behind overloads (`is_type_assignment = is_type_assignment0 ^mem`,
  `termsem = termsem0 ^mem`, ...).  In Lean the constants keep their HOL4 names
  (`is_type_assignment0`, `termsem0`, ...) and take `mem` explicitly as first argument.
-/
import CandleLean.HolSyntax
import CandleLean.HolSyntaxExtra
import CandleLean.SetSpec

namespace Candle

noncomputable section
open Classical

variable {U : Type}

/- HOL4:
Overload inhabited = ``λs. ∃x. x <: s``
   (HOL `inhabited s` is `inhabited mem s`) -/
abbrev inhabited (mem : U → U → Prop) (s : U) : Prop := ∃ x, mem x s

/- HOL4:
Type tyass = ``:mlstring -> 'U list -> 'U`` -/
abbrev tyass (U : Type) : Type := mlstring → List U → U

/- HOL4:
Definition is_type_assignment_def:
  is_type_assignment0 ^mem tysig (δ:'U tyass) ⇔
    FEVERY
      (λ(name,arity).
        ∀ls. LENGTH ls = arity ∧ EVERY inhabited ls ⇒
             inhabited ((δ name) ls))
      tysig
End
Overload is_type_assignment = ``is_type_assignment0 ^mem`` -/
def is_type_assignment0 (mem : U → U → Prop) (tysig : Candle.tysig) (δ : tyass U) : Prop :=
  FEVERY
    (fun (p : mlstring × Nat) =>
      ∀ ls, LENGTH ls = SND p ∧ EVERY (inhabited mem) ls →
            inhabited mem ((δ (FST p)) ls))
    tysig

/- HOL4:
Type tyval = ``:mlstring -> 'U`` -/
abbrev tyval (U : Type) : Type := mlstring → U

/- HOL4:
Definition is_type_valuation_def:
  is_type_valuation0 ^mem (τ:'U tyval) ⇔ ∀x. inhabited (τ x)
End
Overload is_type_valuation = ``is_type_valuation0 ^mem`` -/
def is_type_valuation0 (mem : U → U → Prop) (τ : tyval U) : Prop := ∀ x, inhabited mem (τ x)

/- HOL4:
Definition typesem_def:
  (typesem δ (τ:'U tyval) (Tyvar s) = τ s) ∧
  (typesem δ τ (Tyapp name args) =
    (δ name) (MAP (typesem δ τ) args))
Termination
  type_rec_tac "SND o SND"
End -/
def typesem (δ : tyass U) (τ : tyval U) : type → U
  | Tyvar s => τ s
  | Tyapp name args => (δ name) (MAP (typesem δ τ) args)

/- HOL4:
Type tmass = ``:mlstring -> 'U list -> 'U`` -/
abbrev tmass (U : Type) : Type := mlstring → List U → U

/- HOL4:
Definition is_term_assignment_def:
  is_term_assignment0 ^mem tmsig δ (γ:'U tmass) ⇔
    FEVERY
      (λ(name,ty).
        ∀τ. is_type_valuation τ ⇒
              γ name (MAP τ (MAP implode (STRING_SORT (MAP explode (tyvars ty))))) <: typesem δ τ ty)
      tmsig
End
Overload is_term_assignment = ``is_term_assignment0 ^mem`` -/
def is_term_assignment0 (mem : U → U → Prop) (tmsig : Candle.tmsig) (δ : tyass U)
    (γ : tmass U) : Prop :=
  FEVERY
    (fun (p : mlstring × type) =>
      ∀ τ, is_type_valuation0 mem τ →
        mem (γ (FST p) (MAP τ (MAP implode (STRING_SORT (MAP explode (tyvars (SND p)))))))
            (typesem δ τ (SND p)))
    tmsig

/- HOL4:
Type tmval = ``:mlstring # type -> 'U`` -/
abbrev tmval (U : Type) : Type := mlstring × type → U

/- HOL4:
Definition is_term_valuation_def:
  is_term_valuation0 ^mem tysig δ τ (σ:'U tmval) ⇔
    ∀v ty. type_ok tysig ty ⇒ σ (v,ty) <: typesem δ τ ty
End
Overload is_term_valuation = ``is_term_valuation0 ^mem`` -/
def is_term_valuation0 (mem : U → U → Prop) (tysig : Candle.tysig) (δ : tyass U)
    (τ : tyval U) (σ : tmval U) : Prop :=
  ∀ v ty, type_ok tysig ty → mem (σ (v, ty)) (typesem δ τ ty)

/- HOL4:
Type interpretation = ``:'U tyass # 'U tmass`` -/
abbrev interpretation (U : Type) : Type := tyass U × tmass U

/- HOL4:
Overload tyaof = ``FST:'U interpretation->'U tyass`` -/
abbrev tyaof (i : interpretation U) : tyass U := FST i

/- HOL4:
Overload tmaof = ``SND:'U interpretation->'U tmass`` -/
abbrev tmaof (i : interpretation U) : tmass U := SND i

/- HOL4:
Type valuation = ``:'U tyval # 'U tmval`` -/
abbrev valuation (U : Type) : Type := tyval U × tmval U

/- HOL4:
Overload tyvof = ``FST:'U valuation->'U tyval`` -/
abbrev tyvof (v : valuation U) : tyval U := FST v

/- HOL4:
Overload tmvof = ``SND:'U valuation->'U tmval`` -/
abbrev tmvof (v : valuation U) : tmval U := SND v

/- HOL4:
Definition is_valuation_def:
  is_valuation0 ^mem tysig δ v ⇔
    is_type_valuation (tyvof v) ∧
    is_term_valuation tysig δ (tyvof v) (tmvof v)
End
Overload is_valuation = ``is_valuation0 ^mem`` -/
def is_valuation0 (mem : U → U → Prop) (tysig : Candle.tysig) (δ : tyass U)
    (v : valuation U) : Prop :=
  is_type_valuation0 mem (tyvof v) ∧
  is_term_valuation0 mem tysig δ (tyvof v) (tmvof v)

/- HOL4:
val instance_def = new_specification("instance_def",["instance"],
  Q.prove(`∃f. ∀tmsig (i:'U interpretation) name ty ty0 tyin.
              FLOOKUP tmsig name = SOME ty0 ∧
              ty = TYPE_SUBST tyin ty0
              ⇒
              f tmsig i name ty =
              λτ. tmaof i name
                (MAP (typesem (tyaof i) τ o TYPE_SUBST tyin o Tyvar) (MAP implode (STRING_SORT (MAP explode (tyvars ty0)))))`,
    ...))
   (renamed: HOL `instance` is `instance'` in Lean, because `instance` is a Lean keyword.
   `new_specification`: an arbitrary function that satisfies the specification.) -/
def instance' [Nonempty U] :
    tmsig → interpretation U → mlstring → type → tyval U → U :=
  select (fun f =>
    ∀ (tmsig : Candle.tmsig) (i : interpretation U) (name : mlstring) (ty ty0 : type)
      (tyin : List (type × type)),
      FLOOKUP tmsig name = some ty0 ∧
      ty = TYPE_SUBST tyin ty0
      →
      f tmsig i name ty =
      fun τ => tmaof i name
        (MAP (typesem (tyaof i) τ ∘ TYPE_SUBST tyin ∘ Tyvar)
          (MAP implode (STRING_SORT (MAP explode (tyvars ty0))))))

/- HOL4:
Definition termsem_def:
  (termsem0 ^mem (tmsig:tmsig) (i:'U interpretation) (v:'U valuation) (Var x ty) = tmvof v (x,ty)) ∧
  (termsem0 ^mem tmsig i v (Const name ty) = instance tmsig i name ty (tyvof v)) ∧
  (termsem0 ^mem tmsig i v (Comb t1 t2) =
   termsem0 ^mem tmsig i v t1 ' (termsem0 ^mem tmsig i v t2)) ∧
  (termsem0 ^mem tmsig i v (Abs (Var x ty) b) =
   Abstract (typesem (tyaof i) (tyvof v) ty) (typesem (tyaof i) (tyvof v) (typeof b))
     (λm. termsem0 ^mem tmsig i (tyvof v, ((x,ty)=+m)(tmvof v)) b))
End
Overload termsem = ``termsem0 ^mem``
   (the clauses for `Abs` of a non-variable are missing: the definition goes through
   well-founded recursion with pattern completion, which gives `ARB` there.) -/
def termsem0 [Nonempty U] (mem : U → U → Prop) (tmsig : Candle.tmsig) (i : interpretation U) :
    valuation U → term → U
  | v, Var x ty => tmvof v (x, ty)
  | v, Const name ty => instance' tmsig i name ty (tyvof v)
  | v, Comb t1 t2 => apply mem (termsem0 mem tmsig i v t1) (termsem0 mem tmsig i v t2)
  | v, Abs (Var x ty) b =>
    abstract mem (typesem (tyaof i) (tyvof v) ty) (typesem (tyaof i) (tyvof v) (typeof b))
      (fun m => termsem0 mem tmsig i (tyvof v, UPDATE (x, ty) m (tmvof v)) b)
  | _, Abs _ _ => ARB

/- HOL4:
Definition satisfies_def:
  satisfies0 ^mem i (sig:sig,h,c) ⇔
    ∀v. is_valuation (tysof sig) (tyaof i) v ∧
      EVERY (λt. termsem (tmsof sig) i v t = True) h
      ⇒ termsem (tmsof sig) i v c = True
End
val _ = Parse.add_infix("satisfies",450,Parse.NONASSOC)
Overload satisfies = ``satisfies0 ^mem``
   (HOL `i satisfies (sig,h,c)` is `satisfies0 mem i (sig, h, c)`) -/
def satisfies0 [Nonempty U] (mem : U → U → Prop) (i : interpretation U) :
    sig × List term × term → Prop
  | (sig, h, c) =>
    ∀ v, is_valuation0 mem (tysof sig) (tyaof i) v ∧
      EVERY (fun t => termsem0 mem (tmsof sig) i v t = true0 mem) h
      → termsem0 mem (tmsof sig) i v c = true0 mem

/- HOL4:
Definition is_interpretation_def:
  is_interpretation0 ^mem (sig:sig) int ⇔
    is_type_assignment (tysof sig) (tyaof int) ∧
    is_term_assignment (tmsof sig) (tyaof int) (tmaof int)
End
Overload is_interpretation = ``is_interpretation0 ^mem`` -/
def is_interpretation0 (mem : U → U → Prop) (sig : Candle.sig) (int : interpretation U) : Prop :=
  is_type_assignment0 mem (tysof sig) (tyaof int) ∧
  is_term_assignment0 mem (tmsof sig) (tyaof int) (tmaof int)

/- HOL4:
Definition is_std_type_assignment_def:
  is_std_type_assignment0 ^mem (δ:'U tyass) ⇔
    (∀dom rng. δ «fun» [dom;rng] = Funspace dom rng) ∧
    (δ «bool» [] = boolset)
End
Overload is_std_type_assignment = ``is_std_type_assignment0 ^mem`` -/
def is_std_type_assignment0 [Nonempty U] (mem : U → U → Prop) (δ : tyass U) : Prop :=
  (∀ dom rng, δ ml!"fun" [dom, rng] = funspace mem dom rng) ∧
  (δ ml!"bool" [] = boolset mem)

/- HOL4:
Definition interprets_def:
  interprets0 ^mem γ name vs f ⇔ ∀τ. is_type_valuation τ ⇒ γ name (MAP τ vs) = f (MAP τ vs)
End
Overload interprets = ``interprets0 ^mem``
   (HOL mixfix `γ interprets name on vs as f` is `interprets0 mem γ name vs f`) -/
def interprets0 (mem : U → U → Prop) (γ : tmass U) (name : mlstring) (vs : List mlstring)
    (f : List U → U) : Prop :=
  ∀ τ, is_type_valuation0 mem τ → γ name (MAP τ vs) = f (MAP τ vs)

/- HOL4:
Definition is_std_interpretation_def:
  is_std_interpretation0 ^mem (i:'U interpretation) ⇔
    is_std_type_assignment (tyaof i) ∧
    tmaof i interprets «=» on [«A»] as
    λl. (Abstract (HD l) (Funspace (HD l) boolset)
          (λx. Abstract (HD l) boolset (λy. Boolean (x = y))))
End
Overload is_std_interpretation = ``is_std_interpretation0 ^mem`` -/
def is_std_interpretation0 [Nonempty U] (mem : U → U → Prop) (i : interpretation U) : Prop :=
  is_std_type_assignment0 mem (tyaof i) ∧
  interprets0 mem (tmaof i) ml!"=" [ml!"A"]
    (fun l => abstract mem (HD l) (funspace mem (HD l) (boolset mem))
      (fun x => abstract mem (HD l) (boolset mem) (fun y => boolean mem (x = y))))

/- HOL4:
Definition models_def:
  models0 ^mem i (thy:thy) ⇔
    is_interpretation (sigof thy) i ∧
    is_std_interpretation i ∧
    ∀p. p ∈ (axsof thy) ⇒ i satisfies (sigof thy,[],p)
End
val _ = Parse.add_infix("models",450,Parse.NONASSOC)
Overload models = ``models0 ^mem``
   (HOL `i models thy` is `models0 mem i thy`) -/
def models0 [Nonempty U] (mem : U → U → Prop) (i : interpretation U) (thy : Candle.thy) : Prop :=
  is_interpretation0 mem (sigof thy) i ∧
  is_std_interpretation0 mem i ∧
  ∀ p, p ∈ axsof thy → satisfies0 mem i (sigof thy, [], p)

/- HOL4:
Definition entails_def:
  entails0 ^mem (thy,h) c ⇔
    theory_ok thy ∧
    EVERY (term_ok (sigof thy)) (c::h) ∧
    EVERY (λp. p has_type Bool) (c::h) ∧
    hypset_ok h ∧
    ∀i. i models thy
        ⇒ i satisfies (sigof thy,h,c)
End
val _ = Parse.add_infix("|=",450,Parse.NONASSOC)
Overload "|=" = ``entails0 ^mem``
   (HOL `(thy,h) |= c` is `entails0 mem (thy, h) c`) -/
def entails0 [Nonempty U] (mem : U → U → Prop) : thy × List term → term → Prop
  | (thy, h), c =>
    theory_ok thy ∧
    EVERY (term_ok (sigof thy)) (c :: h) ∧
    EVERY (fun p => has_type p Bool') (c :: h) ∧
    hypset_ok h ∧
    ∀ i : interpretation U, models0 mem i thy
        → satisfies0 mem i (sigof thy, h, c)

/- HOL4:
Definition is_structure_def:
  is_structure0 ^mem sig int val ⇔
    is_std_sig sig ∧
    is_std_interpretation int ∧
    is_interpretation sig int ∧
    is_valuation (tysof sig) (tyaof int) val
End
Overload is_structure = ``is_structure0 ^mem`` -/
def is_structure0 [Nonempty U] (mem : U → U → Prop) (sig : Candle.sig) (int : interpretation U)
    (val : valuation U) : Prop :=
  is_std_sig sig ∧
  is_std_interpretation0 mem int ∧
  is_interpretation0 mem sig int ∧
  is_valuation0 mem (tysof sig) (tyaof int) val

end

end Candle
