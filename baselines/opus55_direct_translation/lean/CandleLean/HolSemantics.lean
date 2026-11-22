import CandleLean.HolSyntaxExtra
import CandleLean.SetSpec

/-!
# holSemantics (CakeML `candle/standard/semantics/holSemanticsScript.sml`)

As in HOL4, constants whose name ends in `0` take the membership relation `mem` explicitly;
the HOL4 overloads without the `0` (`is_type_assignment`, `termsem`, `|=`, ...) are the `0`
constants applied to `mem`.  `inhabited s` is `inhabited mem s`.
Constants mentioning `boolset`/`True`/`HD` (which need an unspecified element of `U`)
take `[Nonempty U]`.
-/

universe u

namespace Candle

open HOL Classical

noncomputable section

variable {U : Type u}

/- HOL4: Overload inhabited = ``λs. ∃x. x <: s`` -/
@[reducible] def inhabited (mem : U → U → Prop) (s : U) : Prop := ∃ x, mem x s

/- HOL4: Type tyass = ``:mlstring -> 'U list -> 'U`` -/
abbrev tyass (U : Type u) := mlstring → List U → U

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
def is_type_assignment0 (mem : U → U → Prop) (tysig : tysig) (δ : tyass U) : Prop :=
  FEVERY (fun p : mlstring × Nat =>
      ∀ ls : List U, ls.length = p.2 ∧ EVERY (inhabited mem) ls → inhabited mem (δ p.1 ls))
    tysig

/- HOL4: Type tyval = ``:mlstring -> 'U`` -/
abbrev tyval (U : Type u) := mlstring → U

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
  | Tyapp name args => δ name (args.map (typesem δ τ))

/- HOL4: Type tmass = ``:mlstring -> 'U list -> 'U`` -/
abbrev tmass (U : Type u) := mlstring → List U → U

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
def is_term_assignment0 (mem : U → U → Prop) (tmsig : tmsig) (δ : tyass U) (γ : tmass U) :
    Prop :=
  FEVERY (fun p : mlstring × type =>
      ∀ τ : tyval U, is_type_valuation0 mem τ →
        mem (γ p.1 (((STRING_SORT ((tyvars p.2).map explode)).map implode).map τ))
          (typesem δ τ p.2))
    tmsig

/- HOL4: Type tmval = ``:mlstring # type -> 'U`` -/
abbrev tmval (U : Type u) := mlstring × type → U

/- HOL4:
Definition is_term_valuation_def:
  is_term_valuation0 ^mem tysig δ τ (σ:'U tmval) ⇔
    ∀v ty. type_ok tysig ty ⇒ σ (v,ty) <: typesem δ τ ty
End
Overload is_term_valuation = ``is_term_valuation0 ^mem`` -/
def is_term_valuation0 (mem : U → U → Prop) (tysig : tysig) (δ : tyass U) (τ : tyval U)
    (σ : tmval U) : Prop :=
  ∀ v ty, type_ok tysig ty → mem (σ (v, ty)) (typesem δ τ ty)

/- HOL4: Type interpretation = ``:'U tyass # 'U tmass`` -/
abbrev interpretation (U : Type u) := tyass U × tmass U

/- HOL4: Overload tyaof = ``FST:'U interpretation->'U tyass`` -/
@[reducible] def tyaof (i : interpretation U) : tyass U := i.1

/- HOL4: Overload tmaof = ``SND:'U interpretation->'U tmass`` -/
@[reducible] def tmaof (i : interpretation U) : tmass U := i.2

/- HOL4: Type valuation = ``:'U tyval # 'U tmval`` -/
abbrev valuation (U : Type u) := tyval U × tmval U

/- HOL4: Overload tyvof = ``FST:'U valuation->'U tyval`` -/
@[reducible] def tyvof (v : valuation U) : tyval U := v.1

/- HOL4: Overload tmvof = ``SND:'U valuation->'U tmval`` -/
@[reducible] def tmvof (v : valuation U) : tmval U := v.2

/- HOL4:
Definition is_valuation_def:
  is_valuation0 ^mem tysig δ v ⇔
    is_type_valuation (tyvof v) ∧
    is_term_valuation tysig δ (tyvof v) (tmvof v)
End
Overload is_valuation = ``is_valuation0 ^mem`` -/
def is_valuation0 (mem : U → U → Prop) (tysig : tysig) (δ : tyass U) (v : valuation U) : Prop :=
  is_type_valuation0 mem (tyvof v) ∧ is_term_valuation0 mem tysig δ (tyvof v) (tmvof v)

/- HOL4:
val instance_def = new_specification("instance_def",["instance"],
  Q.prove(`∃f. ∀tmsig (i:'U interpretation) name ty ty0 tyin.
              FLOOKUP tmsig name = SOME ty0 ∧
              ty = TYPE_SUBST tyin ty0
              ⇒
              f tmsig i name ty =
              λτ. tmaof i name
                (MAP (typesem (tyaof i) τ o TYPE_SUBST tyin o Tyvar)
                     (MAP implode (STRING_SORT (MAP explode (tyvars ty0)))))`, ...))
   (Lean name `instance_`, since `instance` is a Lean keyword.)
   Encoded as Hilbert choice of a function satisfying the specification; the function type is
   inhabited (e.g. by `λtmsig i name ty τ. tmaof i name []`). -/
def instance_spec (f : tmsig → interpretation U → mlstring → type → tyval U → U) : Prop :=
  ∀ (tmsig : tmsig) (i : interpretation U) (name : mlstring) (ty ty0 : type)
    (tyin : List (type × type)),
    FLOOKUP tmsig name = some ty0 ∧ ty = TYPE_SUBST tyin ty0 →
    f tmsig i name ty =
      fun τ => tmaof i name
        (((STRING_SORT ((tyvars ty0).map explode)).map implode).map
          (typesem (tyaof i) τ ∘ TYPE_SUBST tyin ∘ Tyvar))

def instance_ : tmsig → interpretation U → mlstring → type → tyval U → U :=
  @Classical.epsilon _ ⟨fun _ i name _ _ => tmaof i name []⟩ instance_spec

/-- The HOL4 defining theorem `instance_def` (from `new_specification`). -/
theorem instance_def : instance_spec (U := U) instance_ := by
  apply Classical.epsilon_spec (p := instance_spec)
  refine ⟨fun tmsig i name ty τ =>
    let p := Classical.epsilon (fun p : type × List (type × type) =>
      FLOOKUP tmsig name = some p.1 ∧ ty = TYPE_SUBST p.2 p.1)
    tmaof i name (((STRING_SORT ((tyvars p.1).map explode)).map implode).map
      (typesem (tyaof i) τ ∘ TYPE_SUBST p.2 ∘ Tyvar)), ?_⟩
  intro tmsig i name ty ty0 tyin ⟨hf, hty⟩
  funext τ
  dsimp only
  have hp := Classical.epsilon_spec (p := fun p : type × List (type × type) =>
      FLOOKUP tmsig name = some p.1 ∧ ty = TYPE_SUBST p.2 p.1) ⟨(ty0, tyin), hf, hty⟩
  generalize Classical.epsilon (fun p : type × List (type × type) =>
      FLOOKUP tmsig name = some p.1 ∧ ty = TYPE_SUBST p.2 p.1) = p at hp ⊢
  obtain ⟨hf', hty'⟩ := hp
  have e : p.1 = ty0 := Option.some.inj (hf'.symm.trans hf)
  obtain ⟨a, b⟩ := p
  simp only at e hty' ⊢
  subst e
  congr 1
  apply List.map_congr_left
  intro x hx
  simp only [Function.comp]
  congr 1
  simp only [List.mem_map] at hx
  obtain ⟨s, hs, rfl⟩ := hx
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp (Aux.mem_STRING_SORT s _ hs)
  rw [Aux.implode_explode_aux]
  exact Aux.TYPE_SUBST_tyvars_imp b tyin a (hty'.symm.trans hty) y hy

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
   (pattern completion: termsem0 of `Abs v b` with `v` not a variable is ARB;
   `((x,ty) =+ m) f` is `UPDATE (x,ty) m f`) -/
def termsem0 (mem : U → U → Prop) (tmsig : tmsig) (i : interpretation U) :
    valuation U → term → U
  | v, Var x ty => tmvof v (x, ty)
  | v, Const name ty => instance_ tmsig i name ty (tyvof v)
  | v, Comb t1 t2 => apply mem (termsem0 mem tmsig i v t1) (termsem0 mem tmsig i v t2)
  | v, Abs (Var x ty) b =>
    abstract mem (typesem (tyaof i) (tyvof v) ty) (typesem (tyaof i) (tyvof v) (typeof b))
      (fun m => termsem0 mem tmsig i (tyvof v, UPDATE (x, ty) m (tmvof v)) b)
  | v, Abs (Const _ _) _ => @ARB U ⟨tmvof v default⟩
  | v, Abs (Comb _ _) _ => @ARB U ⟨tmvof v default⟩
  | v, Abs (Abs _ _) _ => @ARB U ⟨tmvof v default⟩

/- HOL4:
Definition satisfies_def:
  satisfies0 ^mem i (sig:sig,h,c) ⇔
    ∀v. is_valuation (tysof sig) (tyaof i) v ∧
      EVERY (λt. termsem (tmsof sig) i v t = True) h
      ⇒ termsem (tmsof sig) i v c = True
End
val _ = Parse.add_infix("satisfies",450,Parse.NONASSOC)
Overload satisfies = ``satisfies0 ^mem``
   (`i satisfies (sig,h,c)` is written `satisfies0 mem i (sig, h, c)`) -/
def satisfies0 [Nonempty U] (mem : U → U → Prop) (i : interpretation U)
    (shc : sig × List term × term) : Prop :=
  ∀ v, is_valuation0 mem (tysof shc.1) (tyaof i) v ∧
    EVERY (fun t => termsem0 mem (tmsof shc.1) i v t = true_ mem) shc.2.1 →
    termsem0 mem (tmsof shc.1) i v shc.2.2 = true_ mem

/- HOL4:
Definition is_interpretation_def:
  is_interpretation0 ^mem (sig:sig) int ⇔
    is_type_assignment (tysof sig) (tyaof int) ∧
    is_term_assignment (tmsof sig) (tyaof int) (tmaof int)
End
Overload is_interpretation = ``is_interpretation0 ^mem`` -/
def is_interpretation0 (mem : U → U → Prop) (sig : sig) (int : interpretation U) : Prop :=
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
  (∀ dom rng, δ (mls "fun") [dom, rng] = funspace mem dom rng) ∧
  δ (mls "bool") [] = boolset mem

/- HOL4:
val _ = Parse.add_rule{term_name = "interprets", ... }   (* γ interprets name on vs as f *)
Definition interprets_def:
  interprets0 ^mem γ name vs f ⇔ ∀τ. is_type_valuation τ ⇒ γ name (MAP τ vs) = f (MAP τ vs)
End
Overload interprets = ``interprets0 ^mem``
   (`γ interprets name on vs as f` is written `interprets0 mem γ name vs f`) -/
def interprets0 (mem : U → U → Prop) (γ : tmass U) (name : mlstring) (vs : List mlstring)
    (f : List U → U) : Prop :=
  ∀ τ : tyval U, is_type_valuation0 mem τ → γ name (vs.map τ) = f (vs.map τ)

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
  interprets0 mem (tmaof i) (mls "=") [mls "A"]
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
   (`i models thy` is written `models0 mem i thy`) -/
def models0 [Nonempty U] (mem : U → U → Prop) (i : interpretation U) (thy : thy) : Prop :=
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
   (`(thy,h) |= c` is written `entails0 mem (thy, h) c`) -/
def entails0 [Nonempty U] (mem : U → U → Prop) (thyh : thy × List term) (c : term) : Prop :=
  theory_ok thyh.1 ∧
  EVERY (term_ok (sigof thyh.1)) (c :: thyh.2) ∧
  EVERY (fun p => has_type p BoolTy) (c :: thyh.2) ∧
  hypset_ok thyh.2 ∧
  ∀ i : interpretation U, models0 mem i thyh.1 → satisfies0 mem i (sigof thyh.1, thyh.2, c)

/- HOL4:
Definition is_structure_def:
  is_structure0 ^mem sig int val ⇔
    is_std_sig sig ∧
    is_std_interpretation int ∧
    is_interpretation sig int ∧
    is_valuation (tysof sig) (tyaof int) val
End
Overload is_structure = ``is_structure0 ^mem`` -/
def is_structure0 [Nonempty U] (mem : U → U → Prop) (sig : sig) (int : interpretation U)
    (val : valuation U) : Prop :=
  is_std_sig sig ∧
  is_std_interpretation0 mem int ∧
  is_interpretation0 mem sig int ∧
  is_valuation0 mem (tysof sig) (tyaof int) val

end

end Candle
