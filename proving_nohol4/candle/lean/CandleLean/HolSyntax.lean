import CandleLean.HolSyntaxLib

/-!
# holSyntax (CakeML `candle/standard/syntax/holSyntaxScript.sml`)

Constructors of `type`, `term` and `update` are exported into `Candle`
(`Tyvar`, `Tyapp`, `Var`, `Const`, `Comb`, `Abs`, `ConstSpec`, ...).
HOL4 overloads become reducible definitions: `Fun`, `BoolTy` (HOL4 `Bool`), `Equal`,
`is_instance`, `tysof`, `tmsof`, `sigof`, `axsof`, the context-level projections, ...
-/

universe u

namespace Candle

open HOL Classical

noncomputable section

/-! ## HOL types -/

/- HOL4:
Datatype:
  type
  = Tyvar mlstring
  | Tyapp mlstring (type list)
End -/
inductive type where
  | Tyvar : mlstring → type
  | Tyapp : mlstring → List type → type

export type (Tyvar Tyapp)

instance : Inhabited type := ⟨Tyvar default⟩

/- HOL4: Overload Fun = ``λs t. Tyapp «fun» [s;t]`` -/
@[reducible] def Fun (s t : type) : type := Tyapp (mls "fun") [s, t]

/- HOL4: Overload Bool = ``Tyapp «bool» []``   (Lean name `BoolTy`, to avoid Lean's `Bool`) -/
@[reducible] def BoolTy : type := Tyapp (mls "bool") []

/- HOL4:
Definition domain_raw:
  domain ty = case ty of Tyapp n (x::xs) => x | _ => ty
End -/
def domain (ty : type) : type :=
  match ty with
  | Tyapp _ (x :: _) => x
  | _ => ty

/- HOL4:
Definition codomain_raw:
  codomain ty = case ty of Tyapp n (y::x::xs) => x | _ => ty
End -/
def codomain (ty : type) : type :=
  match ty with
  | Tyapp _ (_ :: x :: _) => x
  | _ => ty

/-! ## HOL terms -/

/- HOL4:
Datatype:
  term = Var mlstring type
       | Const mlstring type
       | Comb term term
       | Abs term term
End -/
inductive term where
  | Var : mlstring → type → term
  | Const : mlstring → type → term
  | Comb : term → term → term
  | Abs : term → term → term
  deriving Inhabited

export term (Var Const Comb Abs)

/- HOL4: Overload Equal = ``λty. Const «=» (Fun ty (Fun ty Bool))`` -/
@[reducible] def Equal (ty : type) : term := Const (mls "=") (Fun ty (Fun ty BoolTy))

/- HOL4:
Definition dest_var_def[simp]:
  dest_var (Var x ty) = (x,ty)
End
   (`dest_var` of a non-variable is unspecified) -/
private opaque dest_var_pkg : {f : term → mlstring × type // ∀ x ty, f (Var x ty) = (x, ty)} :=
  ⟨fun t => match t with | Var x ty => (x, ty) | _ => default, fun _ _ => rfl⟩

def dest_var : term → mlstring × type := dest_var_pkg.1

theorem dest_var_def (x : mlstring) (ty : type) : dest_var (Var x ty) = (x, ty) :=
  dest_var_pkg.2 x ty

/- HOL4:
val _ = Parse.add_infix("has_type",450,Parse.NONASSOC)
Inductive has_type:
  ((Var   n ty) has_type ty) ∧
  ((Const n ty) has_type ty) ∧
  (s has_type (Fun dty rty) ∧
   t has_type dty
   ⇒
   (Comb s t) has_type rty) ∧
  (t has_type rty ⇒
   (Abs (Var n dty) t) has_type (Fun dty rty))
End
   (`tm has_type ty` is written `has_type tm ty`) -/
inductive has_type : term → type → Prop where
  | Var {n : mlstring} {ty : type} : has_type (Var n ty) ty
  | Const {n : mlstring} {ty : type} : has_type (Const n ty) ty
  | Comb {s t : term} {dty rty : type} :
      has_type s (Fun dty rty) → has_type t dty → has_type (Comb s t) rty
  | Abs {n : mlstring} {dty rty : type} {t : term} :
      has_type t rty → has_type (Abs (Var n dty) t) (Fun dty rty)

/- HOL4:
Definition welltyped_def:
  welltyped tm = ∃ty. tm has_type ty
End -/
def welltyped (tm : term) : Prop := ∃ ty, has_type tm ty

/- HOL4:
Definition typeof_def[simp]:
  (typeof (Var n   ty) = ty) ∧
  (typeof (Const n ty) = ty) ∧
  (typeof (Comb s t)   = codomain (typeof s)) ∧
  (typeof (Abs v t) = Fun (typeof v) (typeof t))
End -/
def typeof : term → type
  | Var _ ty => ty
  | Const _ ty => ty
  | Comb s _ => codomain (typeof s)
  | Abs v t => Fun (typeof v) (typeof t)

/- HOL4:
Inductive RACONV:
  (ALPHAVARS env (Var x1 ty1,Var x2 ty2)
    ⇒ RACONV env (Var x1 ty1,Var x2 ty2)) ∧
  (RACONV env (Const x ty,Const x ty)) ∧
  (RACONV env (s1,s2) ∧ RACONV env (t1,t2)
    ⇒ RACONV env (Comb s1 t1,Comb s2 t2)) ∧
  (typeof v1 = typeof v2 ∧ RACONV ((v1,v2)::env) (t1,t2)
    ⇒ RACONV env (Abs v1 t1,Abs v2 t2))
End -/
inductive RACONV : List (term × term) → term × term → Prop where
  | Var {env : List (term × term)} {x1 : mlstring} {ty1 : type} {x2 : mlstring} {ty2 : type} :
      ALPHAVARS env (Var x1 ty1, Var x2 ty2) → RACONV env (Var x1 ty1, Var x2 ty2)
  | Const {env : List (term × term)} {x : mlstring} {ty : type} :
      RACONV env (Const x ty, Const x ty)
  | Comb {env : List (term × term)} {s1 s2 t1 t2 : term} :
      RACONV env (s1, s2) → RACONV env (t1, t2) → RACONV env (Comb s1 t1, Comb s2 t2)
  | Abs {env : List (term × term)} {v1 v2 t1 t2 : term} :
      typeof v1 = typeof v2 → RACONV ((v1, v2) :: env) (t1, t2) →
      RACONV env (Abs v1 t1, Abs v2 t2)

/- HOL4:
Definition ACONV_def:
  ACONV t1 t2 ⇔ RACONV [] (t1,t2)
End -/
def ACONV (t1 t2 : term) : Prop := RACONV [] (t1, t2)

/- HOL4:
Inductive type_lt:
  (mlstring_lt x1 x2 ⇒ type_lt (Tyvar x1) (Tyvar x2)) ∧
  (type_lt (Tyvar x1) (Tyapp x2 args2)) ∧
  ((mlstring_lt LEX LLEX type_lt) (x1,args1) (x2,args2) ⇒
     type_lt (Tyapp x1 args1) (Tyapp x2 args2))
End
   The recursive occurrence of `type_lt` under `LLEX` is not strictly positive syntactically, so
   (exactly as HOL4's IndDef does) the relation is defined as the least relation closed under
   the rules: `type_lt a b` iff every relation closed under the rules relates `a` and `b`. -/
def type_lt (a b : type) : Prop :=
  ∀ type_lt' : type → type → Prop,
    ((∀ x1 x2, mlstring_lt x1 x2 → type_lt' (Tyvar x1) (Tyvar x2)) ∧
     (∀ x1 x2 args2, type_lt' (Tyvar x1) (Tyapp x2 args2)) ∧
     (∀ x1 args1 x2 args2,
        LEX mlstring_lt (LLEX type_lt') (x1, args1) (x2, args2) →
        type_lt' (Tyapp x1 args1) (Tyapp x2 args2))) →
    type_lt' a b

/- HOL4:
Inductive term_lt:
  ((mlstring_lt LEX type_lt) (x1,ty1) (x2,ty2) ⇒
    term_lt (Var x1 ty1) (Var x2 ty2)) ∧
  (term_lt (Var x1 ty1) (Const x2 ty2)) ∧
  (term_lt (Var x1 ty1) (Comb t1 t2)) ∧
  (term_lt (Var x1 ty1) (Abs t1 t2)) ∧
  ((mlstring_lt LEX type_lt) (x1,ty1) (x2,ty2) ⇒
    term_lt (Const x1 ty1) (Const x2 ty2)) ∧
  (term_lt (Const x1 ty1) (Comb t1 t2)) ∧
  (term_lt (Const x1 ty1) (Abs t1 t2)) ∧
  ((term_lt LEX term_lt) (s1,s2) (t1,t2) ⇒
   term_lt (Comb s1 s2) (Comb t1 t2)) ∧
  (term_lt (Comb s1 s2) (Abs t1 t2)) ∧
  ((term_lt LEX term_lt) (s1,s2) (t1,t2) ⇒
   term_lt (Abs s1 s2) (Abs t1 t2))
End
   (least relation closed under the rules, as for `type_lt`) -/
def term_lt (a b : term) : Prop :=
  ∀ term_lt' : term → term → Prop,
    ((∀ x1 ty1 x2 ty2, LEX mlstring_lt type_lt (x1, ty1) (x2, ty2) →
        term_lt' (Var x1 ty1) (Var x2 ty2)) ∧
     (∀ x1 ty1 x2 ty2, term_lt' (Var x1 ty1) (Const x2 ty2)) ∧
     (∀ x1 ty1 t1 t2, term_lt' (Var x1 ty1) (Comb t1 t2)) ∧
     (∀ x1 ty1 t1 t2, term_lt' (Var x1 ty1) (Abs t1 t2)) ∧
     (∀ x1 ty1 x2 ty2, LEX mlstring_lt type_lt (x1, ty1) (x2, ty2) →
        term_lt' (Const x1 ty1) (Const x2 ty2)) ∧
     (∀ x1 ty1 t1 t2, term_lt' (Const x1 ty1) (Comb t1 t2)) ∧
     (∀ x1 ty1 t1 t2, term_lt' (Const x1 ty1) (Abs t1 t2)) ∧
     (∀ s1 s2 t1 t2, LEX term_lt' term_lt' (s1, s2) (t1, t2) →
        term_lt' (Comb s1 s2) (Comb t1 t2)) ∧
     (∀ s1 s2 t1 t2, term_lt' (Comb s1 s2) (Abs t1 t2)) ∧
     (∀ s1 s2 t1 t2, LEX term_lt' term_lt' (s1, s2) (t1, t2) →
        term_lt' (Abs s1 s2) (Abs t1 t2))) →
    term_lt' a b

/- HOL4:
Definition term_cmp_def:
  term_cmp = TO_of_LinearOrder term_lt
End -/
def term_cmp : term → term → ordering := TO_of_LinearOrder term_lt

/- HOL4:
Definition type_cmp_def:
  type_cmp = TO_of_LinearOrder type_lt
End -/
def type_cmp : type → type → ordering := TO_of_LinearOrder type_lt

/- HOL4:
Definition ordav_def:
  (ordav [] x1 x2 ⇔ term_cmp x1 x2) ∧
  (ordav ((t1,t2)::env) x1 x2 ⇔
    if x1 = t1 then
      if x2 = t2 then EQUAL
      else LESS
    else if x2 = t2 then GREATER
    else ordav env x1 x2)
End -/
def ordav : List (term × term) → term → term → ordering
  | [], x1, x2 => term_cmp x1 x2
  | (t1, t2) :: env, x1, x2 =>
    if x1 = t1 then (if x2 = t2 then EQUAL else LESS)
    else if x2 = t2 then GREATER
    else ordav env x1 x2

/- HOL4:
Definition orda_def:
  orda env t1 t2 =
    if t1 = t2 ∧ env = [] then EQUAL else
      case (t1,t2) of
      | (Var _ _, Var _ _) => ordav env t1 t2
      | (Const _ _, Const _ _) => term_cmp t1 t2
      | (Comb s1 t1, Comb s2 t2) =>
        (let c = orda env s1 s2 in
           if c ≠ EQUAL then c else orda env t1 t2)
      | (Abs s1 t1, Abs s2 t2) =>
        (let c = type_cmp (typeof s1) (typeof s2) in
           if c ≠ EQUAL then c else orda ((s1,s2)::env) t1 t2)
      | (Var _ _, _) => LESS
      | (_, Var _ _) => GREATER
      | (Const _ _, _) => LESS
      | (_, Const _ _) => GREATER
      | (Comb _ _, _) => LESS
      | (_, Comb _ _) => GREATER
End -/
def orda (env : List (term × term)) (t1 t2 : term) : ordering :=
  if t1 = t2 ∧ env = [] then EQUAL else
    match t1, t2 with
    | Var _ _, Var _ _ => ordav env t1 t2
    | Const _ _, Const _ _ => term_cmp t1 t2
    | Comb s1 t1', Comb s2 t2' =>
      let c := orda env s1 s2
      if c ≠ EQUAL then c else orda env t1' t2'
    | Abs s1 t1', Abs s2 t2' =>
      let c := type_cmp (typeof s1) (typeof s2)
      if c ≠ EQUAL then c else orda ((s1, s2) :: env) t1' t2'
    | Var _ _, _ => LESS
    | _, Var _ _ => GREATER
    | Const _ _, _ => LESS
    | _, Const _ _ => GREATER
    | Comb _ _, _ => LESS
    | _, Comb _ _ => GREATER
termination_by sizeOf t1

/- HOL4:
Definition term_union_def:
  term_union l1 l2 =
    case (l1,l2) of
    | ([],l2) => l2
    | (l1,[]) => l1
    | (h1::t1,h2::t2) =>
      let c = orda [] h1 h2 in
      if c = EQUAL then h1::(term_union t1 t2)
      else if c = LESS then h1::(term_union t1 l2)
      else h2::(term_union (h1::t1) t2)
End -/
def term_union (l1 l2 : List term) : List term :=
  match l1, l2 with
  | [], l2 => l2
  | l1, [] => l1
  | h1 :: t1, h2 :: t2 =>
    let c := orda [] h1 h2
    if c = EQUAL then h1 :: term_union t1 t2
    else if c = LESS then h1 :: term_union t1 (h2 :: t2)
    else h2 :: term_union (h1 :: t1) t2
termination_by l1.length + l2.length

/- HOL4:
Definition term_remove_def:
  term_remove t l =
  case l of
  | [] => l
  | (s::ss) =>
    let c = orda [] t s in
    if c = GREATER then
      let ss' = term_remove t ss in
      if ss' = ss then l else s::ss'
    else if c = EQUAL then ss else l
End -/
def term_remove (t : term) (l : List term) : List term :=
  match l with
  | [] => l
  | s :: ss =>
    let c := orda [] t s
    if c = GREATER then
      let ss' := term_remove t ss
      if ss' = ss then l else s :: ss'
    else if c = EQUAL then ss else l

/- HOL4:
Definition term_image_def:
  term_image f l =
  case l of
  | [] => l
  | (h::t) =>
    let h' = f h in
    let t' = term_image f t in
    if h' = h ∧ t' = t then l
    else term_union [h'] t'
End -/
def term_image (f : term → term) (l : List term) : List term :=
  match l with
  | [] => l
  | h :: t =>
    let h' := f h
    let t' := term_image f t
    if h' = h ∧ t' = t then l else term_union [h'] t'

/- HOL4:
Definition VFREE_IN_def[simp]:
  (VFREE_IN v (Var x ty) ⇔ (Var x ty = v)) ∧
  (VFREE_IN v (Const x ty) ⇔ (Const x ty = v)) ∧
  (VFREE_IN v (Comb s t) ⇔ VFREE_IN v s ∨ VFREE_IN v t) ∧
  (VFREE_IN v (Abs w t) ⇔ (w ≠ v) ∧ VFREE_IN v t)
End -/
def VFREE_IN (v : term) : term → Prop
  | Var x ty => Var x ty = v
  | Const x ty => Const x ty = v
  | Comb s t => VFREE_IN v s ∨ VFREE_IN v t
  | Abs w t => w ≠ v ∧ VFREE_IN v t

/- HOL4:
Definition CLOSED_def:
  CLOSED tm = ∀x ty. ¬(VFREE_IN (Var x ty) tm)
End -/
def CLOSED (tm : term) : Prop := ∀ x ty, ¬ VFREE_IN (Var x ty) tm

/- HOL4:
val VARIANT_PRIMES_def = new_specification
  ("VARIANT_PRIMES_def"
  ,["VARIANT_PRIMES"]
  [HOL4 proof text removed]
   where
     PRIMED_NAME_EXISTS: ∃n. ¬(VFREE_IN (Var (implode (APPEND x (GENLIST (K #"'") n))) ty) t)
     LEAST_EXISTS:       (∃n:num. P n) ⇒ ∃k. P k ∧ ∀m. m < k ⇒ ¬(P m)
   so the specification is
     ∀t x ty. P t x ty (VARIANT_PRIMES t x ty) ∧
              ∀m. m < VARIANT_PRIMES t x ty ⇒ ¬P t x ty m
   with P t x ty n = ¬VFREE_IN (Var (implode (APPEND x (GENLIST (K #"'") n))) ty) t.
   Encoded as Hilbert choice of a function satisfying the specification
   (the specification determines the function uniquely: the least such n). -/
def VARIANT_PRIMES_P (t : term) (x : string) (ty : type) (n : Nat) : Prop :=
  ¬ VFREE_IN (Var (implode (x ++ GENLIST (K (ch '\'')) n)) ty) t

def VARIANT_PRIMES_spec (f : term → string → type → Nat) : Prop :=
  ∀ t x ty, VARIANT_PRIMES_P t x ty (f t x ty) ∧
    ∀ m, m < f t x ty → ¬ VARIANT_PRIMES_P t x ty m


/-! Proof of the HOL4 defining theorem `VARIANT_PRIMES_def` (auxiliary lemmas in `Candle.Aux`). -/

def Aux.maxlen : term → Nat
  | Var x _ => strlen x
  | Const _ _ => 0
  | Comb s t => max (Aux.maxlen s) (Aux.maxlen t)
  | Abs v t => max (Aux.maxlen v) (Aux.maxlen t)

theorem Aux.VFREE_IN_Var_len (s : mlstring) (ty : type) :
    ∀ t : term, VFREE_IN (Var s ty) t → strlen s ≤ Aux.maxlen t
  | Var x ty', h => by
    simp only [VFREE_IN, term.Var.injEq] at h
    rw [← h.1]; simp [Aux.maxlen]
  | Const _ _, h => by simp [VFREE_IN] at h
  | Comb a b, h => by
    simp only [VFREE_IN] at h
    simp only [Aux.maxlen]
    rcases h with h | h
    · exact Nat.le_trans (Aux.VFREE_IN_Var_len s ty a h) (Nat.le_max_left _ _)
    · exact Nat.le_trans (Aux.VFREE_IN_Var_len s ty b h) (Nat.le_max_right _ _)
  | Abs v b, h => by
    simp only [VFREE_IN] at h
    simp only [Aux.maxlen]
    exact Nat.le_trans (Aux.VFREE_IN_Var_len s ty b h.2) (Nat.le_max_right _ _)

theorem Aux.GENLIST_length {α : Type u} (f : Nat → α) : ∀ n, (GENLIST f n).length = n
  | 0 => rfl
  | n + 1 => by
    simp only [GENLIST]
    have : ∀ (x : α) (l : List α), (SNOC x l).length = l.length + 1 := by
      intro x l; induction l with
      | nil => rfl
      | cons a t ih => simp [SNOC, ih]
    rw [this, Aux.GENLIST_length f n]

theorem Aux.least_exists (P : Nat → Prop) (h : ∃ n, P n) : ∃ k, P k ∧ ∀ m, m < k → ¬ P m := by
  obtain ⟨n, hn⟩ := h
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases hc : ∃ m, m < n ∧ P m
    · obtain ⟨m, hm, hpm⟩ := hc; exact ih m hm hpm
    · exact ⟨n, hn, fun m hm hpm => hc ⟨m, hm, hpm⟩⟩

private theorem VARIANT_PRIMES_exists : ∃ f, VARIANT_PRIMES_spec f := by
  have : ∀ t x ty, ∃ k, VARIANT_PRIMES_P t x ty k ∧ ∀ m, m < k → ¬ VARIANT_PRIMES_P t x ty m := by
    intro t x ty
    apply Aux.least_exists
    refine ⟨Aux.maxlen t + 1, fun h => ?_⟩
    have := Aux.VFREE_IN_Var_len _ ty t h
    simp only [strlen, List.length_append, Aux.GENLIST_length] at this
    omega
  exact ⟨fun t x ty => Classical.choose (this t x ty),
    fun t x ty => Classical.choose_spec (this t x ty)⟩

private opaque VARIANT_PRIMES_pkg : {f : term → string → type → Nat // VARIANT_PRIMES_spec f} :=
  ⟨Classical.choose VARIANT_PRIMES_exists, Classical.choose_spec VARIANT_PRIMES_exists⟩

def VARIANT_PRIMES : term → string → type → Nat := VARIANT_PRIMES_pkg.1

/-- The HOL4 defining theorem `VARIANT_PRIMES_def` (from `new_specification`). -/
theorem VARIANT_PRIMES_def : VARIANT_PRIMES_spec VARIANT_PRIMES := VARIANT_PRIMES_pkg.2

/- HOL4:
Definition VARIANT_def:
  VARIANT t x ty = implode (APPEND x (GENLIST (K #"'") (VARIANT_PRIMES t x ty)))
End -/
def VARIANT (t : term) (x : string) (ty : type) : mlstring :=
  implode (x ++ GENLIST (K (ch '\'')) (VARIANT_PRIMES t x ty))

/- HOL4:
Definition TYPE_SUBST_def[simp]:
  (TYPE_SUBST i (Tyvar v) = REV_ASSOCD (Tyvar v) i (Tyvar v)) ∧
  (TYPE_SUBST i (Tyapp v tys) = Tyapp v (MAP (TYPE_SUBST i) tys)) ∧
  (TYPE_SUBST i (Fun ty1 ty2) = Fun (TYPE_SUBST i ty1) (TYPE_SUBST i ty2))
  [HOL4 proof text removed]
End
   (the third clause is an instance of the second, since `Fun` is an overload for `Tyapp`) -/
def TYPE_SUBST (i : List (type × type)) : type → type
  | Tyvar v => REV_ASSOCD (Tyvar v) i (Tyvar v)
  | Tyapp v tys => Tyapp v (tys.map (TYPE_SUBST i))

/- HOL4: Overload is_instance = ``λty0 ty. ∃i. ty = TYPE_SUBST i ty0`` -/
@[reducible] def is_instance (ty0 ty : type) : Prop := ∃ i, ty = TYPE_SUBST i ty0

/- HOL4:
Definition VSUBST_def:
  (VSUBST ilist (Var x ty) = REV_ASSOCD (Var x ty) ilist (Var x ty)) ∧
  (VSUBST ilist (Const x ty) = Const x ty) ∧
  (VSUBST ilist (Comb s t) = Comb (VSUBST ilist s) (VSUBST ilist t)) ∧
  (VSUBST ilist (Abs v t) =
    let ilist' = FILTER (λ(s',s). ¬(s = v)) ilist in
    let t' = VSUBST ilist' t in
    if EXISTS (λ(s',s). VFREE_IN v s' ∧ VFREE_IN s t) ilist'
    then let (x,ty) = dest_var v in
         let z = Var (VARIANT t' (explode x) ty) ty in
         let ilist'' = CONS (z,v) ilist' in
         Abs z (VSUBST ilist'' t)
    else Abs v t')
End
   (`let (x,ty) = dest_var v` is written with projections) -/
def VSUBST (ilist : List (term × term)) : term → term
  | Var x ty => REV_ASSOCD (Var x ty) ilist (Var x ty)
  | Const x ty => Const x ty
  | Comb s t => Comb (VSUBST ilist s) (VSUBST ilist t)
  | Abs v t =>
    let ilist' := FILTER (fun p => ¬ (p.2 = v)) ilist
    let t' := VSUBST ilist' t
    if EXISTS (fun p => VFREE_IN v p.1 ∧ VFREE_IN p.2 t) ilist'
    then
      let xty := dest_var v
      let z := Var (VARIANT t' (explode xty.1) xty.2) xty.2
      let ilist'' := (z, v) :: ilist'
      Abs z (VSUBST ilist'' t)
    else Abs v t'

/- HOL4:
Definition sizeof_def[simp]:
  sizeof (Var x ty) = 1n ∧
  sizeof (Const x ty) = 1 ∧
  sizeof (Comb s t) = 1 + sizeof s + sizeof t ∧
  sizeof (Abs v t) = 2 + sizeof t
End -/
def sizeof : term → Nat
  | Var _ _ => 1
  | Const _ _ => 1
  | Comb s t => 1 + sizeof s + sizeof t
  | Abs _ t => 2 + sizeof t

/-- Auxiliary lemma (HOL4 `REV_ASSOCD_MEM`-like), used for the termination of `INST_CORE`. -/
theorem Aux.REV_ASSOCD_cases {α β : Type u} (a : β) :
    ∀ (l : List (α × β)) (d : α), (REV_ASSOCD a l d, a) ∈ l ∨ REV_ASSOCD a l d = d
  | [], d => Or.inr rfl
  | p :: t, d => by
    unfold REV_ASSOCD
    by_cases h : p.2 = a
    · simp only [h, if_true]; left; exact h ▸ List.mem_cons_self
    · simp only [h, if_false]
      rcases Aux.REV_ASSOCD_cases a t d with h' | h'
      · exact Or.inl (List.mem_cons_of_mem _ h')
      · exact Or.inr h'

theorem Aux.mem_FILTER_imp {α : Type u} (P : α → Prop) :
    ∀ (l : List α) (x : α), x ∈ FILTER P l → x ∈ l
  | [], x, h => by simp [FILTER] at h
  | y :: l, x, h => by
    unfold FILTER at h
    by_cases hy : P y
    · simp only [hy, if_true, List.mem_cons] at h
      rcases h with h | h
      · exact h ▸ List.mem_cons_self
      · exact List.mem_cons_of_mem _ (Aux.mem_FILTER_imp P l x h)
    · simp only [hy, if_false] at h
      exact List.mem_cons_of_mem _ (Aux.mem_FILTER_imp P l x h)

/-- HOL4 `SIZEOF_VSUBST` (holSyntax), needed for the termination proof of `INST_CORE`:
  ∀t ilist. (∀s' s. MEM (s',s) ilist ⇒ ∃x ty. s' = Var x ty)
              ⇒ sizeof (VSUBST ilist t) = sizeof t -/
theorem Aux.sizeof_VSUBST_aux : ∀ (t : term) (ilist : List (term × term)),
    (∀ s' s, (s', s) ∈ ilist → ∃ x ty, s' = Var x ty) → sizeof (VSUBST ilist t) = sizeof t
  | Var x ty, ilist, h => by
    simp only [VSUBST]
    rcases Aux.REV_ASSOCD_cases (Var x ty) ilist (Var x ty) with hm | hm
    · obtain ⟨x', ty', he⟩ := h _ _ hm
      rw [he]; rfl
    · rw [hm]
  | Const x ty, ilist, _ => rfl
  | Comb s t, ilist, h => by
    simp only [VSUBST, sizeof, Aux.sizeof_VSUBST_aux s ilist h, Aux.sizeof_VSUBST_aux t ilist h]
  | Abs v t, ilist, h => by
    have hf : ∀ s' s, (s', s) ∈ FILTER (fun p => ¬ (p.2 = v)) ilist → ∃ x ty, s' = Var x ty :=
      fun s' s hm => h s' s (Aux.mem_FILTER_imp _ _ _ hm)
    simp only [VSUBST]
    split
    · simp only [sizeof]
      rw [Aux.sizeof_VSUBST_aux t _ (fun s' s hm => by
        rcases List.mem_cons.mp hm with hm | hm
        · cases hm; exact ⟨_, _, rfl⟩
        · exact hf s' s hm)]
    · simp only [sizeof, Aux.sizeof_VSUBST_aux t _ hf]

/- HOL4:
Definition INST_CORE_def:
  (INST_CORE env tyin (Var x ty) =
     let tm = Var x ty in
     let tm' = Var x (TYPE_SUBST tyin ty) in
     if REV_ASSOCD tm' env tm = tm then Result tm' else Clash tm') ∧
  (INST_CORE env tyin (Const x ty) =
    Result(Const x (TYPE_SUBST tyin ty))) ∧
  (INST_CORE env tyin (Comb s t) =
    let sres = INST_CORE env tyin s in
    if IS_CLASH sres then sres else
    let tres = INST_CORE env tyin t in
    if IS_CLASH tres then tres else
    let s' = RESULT sres and t' = RESULT tres in
    Result (Comb s' t')) ∧
  (INST_CORE env tyin (Abs v t) =
    let (x,ty) = dest_var v in
    let ty' = TYPE_SUBST tyin ty in
    let v' = Var x ty' in
    let env' = (v,v')::env in
    let tres = INST_CORE env' tyin t in
    if IS_RESULT tres then Result(Abs v' (RESULT tres)) else
    let w = CLASH tres in
    if (w ≠ v') then tres else
    let x' = VARIANT (RESULT(INST_CORE [] tyin t)) (explode x) ty' in
    let t' = VSUBST [Var x' ty,Var x ty] t in
    let ty' = TYPE_SUBST tyin ty in
    let env' = (Var x' ty,Var x' ty')::env in
    let tres = INST_CORE env' tyin t' in
    if IS_RESULT tres then Result(Abs (Var x' ty') (RESULT tres)) else tres)
  [HOL4 proof text removed]
End
   (`[Var x' ty,Var x ty]` is the one-element list of the pair `(Var x' ty, Var x ty)`) -/
def INST_CORE (env : List (term × term)) (tyin : List (type × type)) : term → result term
  | Var x ty =>
    let tm := Var x ty
    let tm' := Var x (TYPE_SUBST tyin ty)
    if REV_ASSOCD tm' env tm = tm then Result tm' else Clash tm'
  | Const x ty => Result (Const x (TYPE_SUBST tyin ty))
  | Comb s t =>
    let sres := INST_CORE env tyin s
    if IS_CLASH sres then sres else
    let tres := INST_CORE env tyin t
    if IS_CLASH tres then tres else
    let s' := RESULT sres
    let t' := RESULT tres
    Result (Comb s' t')
  | Abs v t =>
    let x := (dest_var v).1
    let ty := (dest_var v).2
    let ty' := TYPE_SUBST tyin ty
    let v' := Var x ty'
    let env' := (v, v') :: env
    let tres := INST_CORE env' tyin t
    if IS_RESULT tres then Result (Abs v' (RESULT tres)) else
    let w := CLASH tres
    if w ≠ v' then tres else
    let x' := VARIANT (RESULT (INST_CORE [] tyin t)) (explode x) ty'
    let t' := VSUBST [(Var x' ty, Var x ty)] t
    let ty' := TYPE_SUBST tyin ty
    let env' := (Var x' ty, Var x' ty') :: env
    let tres := INST_CORE env' tyin t'
    if IS_RESULT tres then Result (Abs (Var x' ty') (RESULT tres)) else tres
termination_by tm => sizeof tm
decreasing_by
  all_goals simp only [sizeof]
  all_goals try omega
  rw [Aux.sizeof_VSUBST_aux t _ (fun s' s hm => by
    rcases List.mem_singleton.mp hm with hm
    cases hm; exact ⟨_, _, rfl⟩)]
  omega

/- HOL4:
Definition INST_def:
  INST tyin tm = RESULT(INST_CORE [] tyin tm)
End -/
def INST (tyin : List (type × type)) (tm : term) : term := RESULT (INST_CORE [] tyin tm)

/- HOL4:
Definition tyvars_def:
  tyvars (Tyvar v) = [v] ∧
  tyvars (Tyapp v tys) = FOLDR (λx y. LIST_UNION (tyvars x) y) [] tys
  [HOL4 proof text removed]
End -/
def tyvars : type → List mlstring
  | Tyvar v => [v]
  | Tyapp _ tys => tys.foldr (fun x y => LIST_UNION (tyvars x) y) []

theorem Aux.mem_tyvars_foldr (x : mlstring) :
    ∀ tys : List type, x ∈ tys.foldr (fun a y => LIST_UNION (tyvars a) y) [] →
      ∃ a, a ∈ tys ∧ x ∈ tyvars a
  | [], h => by simp at h
  | b :: t, h => by
    simp only [List.foldr_cons, Aux.mem_LIST_UNION] at h
    rcases h with h | h
    · exact ⟨b, List.mem_cons_self, h⟩
    · obtain ⟨a, ha, hx⟩ := Aux.mem_tyvars_foldr x t h
      exact ⟨a, List.mem_cons_of_mem _ ha, hx⟩

/-- Auxiliary (one direction of HOL4 `TYPE_SUBST_tyvars`), used for `instance_def`. -/
theorem Aux.TYPE_SUBST_tyvars_imp (i i' : List (type × type)) :
    ∀ ty : type, TYPE_SUBST i ty = TYPE_SUBST i' ty →
      ∀ x, x ∈ tyvars ty → TYPE_SUBST i (Tyvar x) = TYPE_SUBST i' (Tyvar x)
  | Tyvar v, h, x, hx => by
    simp only [tyvars, List.mem_singleton] at hx
    subst hx; exact h
  | Tyapp v tys, h, x, hx => by
    simp only [TYPE_SUBST, type.Tyapp.injEq, true_and] at h
    simp only [tyvars] at hx
    obtain ⟨a, ha, hxa⟩ := Aux.mem_tyvars_foldr x tys hx
    have hma : TYPE_SUBST i a = TYPE_SUBST i' a := (List.map_inj_left.mp h) a ha
    have : sizeOf a < sizeOf (Tyapp v tys) := by
      have := List.sizeOf_lt_of_mem ha
      simp only [type.Tyapp.sizeOf_spec]; omega
    exact Aux.TYPE_SUBST_tyvars_imp i i' a hma x hxa
termination_by ty => sizeOf ty

/- HOL4:
Definition tvars_def:
  (tvars (Var n ty) = tyvars ty) ∧
  (tvars (Const n ty) = tyvars ty) ∧
  (tvars (Comb s t) = LIST_UNION (tvars s) (tvars t)) ∧
  (tvars (Abs v t) = LIST_UNION (tvars v) (tvars t))
End -/
def tvars : term → List mlstring
  | Var _ ty => tyvars ty
  | Const _ ty => tyvars ty
  | Comb s t => LIST_UNION (tvars s) (tvars t)
  | Abs v t => LIST_UNION (tvars v) (tvars t)

/- HOL4:
val _ = Parse.add_infix("===",460,Parse.RIGHT)
Definition equation_def:
  (s === t) = Comb (Comb (Equal(typeof s)) s) t
End
   (`s === t` is written `equation s t`) -/
def equation (s t : term) : term := Comb (Comb (Equal (typeof s)) s) t

/-! ## Signatures and theories -/

/- HOL4: Type tysig = ``:mlstring |-> num`` -/
abbrev tysig := fmap mlstring Nat

/- HOL4: Type tmsig = ``:mlstring |-> type`` -/
abbrev tmsig := fmap mlstring type

/- HOL4: Type sig = ``:tysig # tmsig`` -/
abbrev sig := tysig × tmsig

/- HOL4: Overload tysof = ``FST:sig->tysig`` -/
@[reducible] def tysof (s : sig) : tysig := s.1

/- HOL4: Overload tmsof = ``SND:sig->tmsig`` -/
@[reducible] def tmsof (s : sig) : tmsig := s.2

/- HOL4:
Definition type_ok_def:
   (type_ok tysig (Tyvar _) ⇔ T) ∧
   (type_ok tysig (Tyapp name args) ⇔
      FLOOKUP tysig name = SOME (LENGTH args) ∧
      EVERY (type_ok tysig) args)
  [HOL4 proof text removed]
End -/
def type_ok (tysig : tysig) : type → Prop
  | Tyvar _ => True
  | Tyapp name args => FLOOKUP tysig name = some args.length ∧ EVERY (type_ok tysig) args

/- HOL4:
Definition term_ok_def:
  (term_ok sig (Var x ty) ⇔ type_ok (tysof sig) ty) ∧
  (term_ok sig (Const name ty) ⇔
     ∃ty0. FLOOKUP (tmsof sig) name = SOME ty0 ∧
           type_ok (tysof sig) ty ∧
           is_instance ty0 ty) ∧
  (term_ok sig (Comb tm1 tm2) ⇔
     term_ok sig tm1 ∧
     term_ok sig tm2 ∧
     welltyped (Comb tm1 tm2)) ∧
  (term_ok sig (Abs v tm) ⇔
     ∃x ty.
       v = Var x ty ∧
       type_ok (tysof sig) ty ∧
       term_ok sig tm)
End -/
def term_ok (sig : sig) : term → Prop
  | Var _ ty => type_ok (tysof sig) ty
  | Const name ty =>
    ∃ ty0, FLOOKUP (tmsof sig) name = some ty0 ∧ type_ok (tysof sig) ty ∧ is_instance ty0 ty
  | Comb tm1 tm2 => term_ok sig tm1 ∧ term_ok sig tm2 ∧ welltyped (Comb tm1 tm2)
  | Abs v tm => ∃ x ty, v = Var x ty ∧ type_ok (tysof sig) ty ∧ term_ok sig tm

/- HOL4:
Definition alpha_lt_def:
  alpha_lt t1 t2 ⇔ orda [] t1 t2 = LESS
End -/
def alpha_lt (t1 t2 : term) : Prop := orda [] t1 t2 = LESS

/- HOL4:
Definition hypset_ok_def:
  hypset_ok ls ⇔ SORTED alpha_lt ls
End -/
def hypset_ok (ls : List term) : Prop := SORTED alpha_lt ls

/- HOL4: Type thy = ``:sig # term set`` -/
abbrev thy := sig × Set term

/- HOL4: Overload sigof = ``FST:thy->sig`` -/
@[reducible] def sigof (t : thy) : sig := t.1

/- HOL4: Overload axsof = ``SND:thy->term set`` -/
@[reducible] def axsof (t : thy) : Set term := t.2

/- HOL4: Overload tysof = ``tysof o sigof``   (on theories; Lean name `thy_tysof`,
   equal to `tysof (sigof thy)`) -/
@[reducible] def thy_tysof (t : thy) : tysig := tysof (sigof t)

/- HOL4: Overload tmsof = ``tmsof o sigof``   (on theories; Lean name `thy_tmsof`,
   equal to `tmsof (sigof thy)`) -/
@[reducible] def thy_tmsof (t : thy) : tmsig := tmsof (sigof t)

/- HOL4:
Definition is_std_sig_def:
  is_std_sig (sig:sig) ⇔
    FLOOKUP (tysof sig) «fun» = SOME 2 ∧
    FLOOKUP (tysof sig) «bool» = SOME 0 ∧
    FLOOKUP (tmsof sig) «=» = SOME (Fun (Tyvar «A») (Fun (Tyvar «A») Bool))
End -/
def is_std_sig (sig : sig) : Prop :=
  FLOOKUP (tysof sig) (mls "fun") = some 2 ∧
  FLOOKUP (tysof sig) (mls "bool") = some 0 ∧
  FLOOKUP (tmsof sig) (mls "=") = some (Fun (Tyvar (mls "A")) (Fun (Tyvar (mls "A")) BoolTy))

/- HOL4:
Definition theory_ok_def:
  theory_ok (thy:thy) ⇔
    (∀ty. ty ∈ FRANGE (tmsof thy) ⇒ type_ok (tysof thy) ty) ∧
    (∀p. p ∈ (axsof thy) ⇒ term_ok (sigof thy) p ∧ p has_type Bool) ∧
    is_std_sig (sigof thy)
End -/
def theory_ok (thy : thy) : Prop :=
  (∀ ty, ty ∈ FRANGE (thy_tmsof thy) → type_ok (thy_tysof thy) ty) ∧
  (∀ p, p ∈ axsof thy → term_ok (sigof thy) p ∧ has_type p BoolTy) ∧
  is_std_sig (sigof thy)

/- HOL4:
val _ = Parse.add_infix("|-",450,Parse.NONASSOC)
Inductive proves:
[~ABS:]
  (¬(EXISTS (VFREE_IN (Var x ty)) h) ∧ type_ok (tysof thy) ty ∧
   (thy, h) |- l === r
   ⇒ (thy, h) |- (Abs (Var x ty) l) === (Abs (Var x ty) r))
[~ASSUME:]
  (theory_ok thy ∧ p has_type Bool ∧ term_ok (sigof thy) p
   ⇒ (thy, [p]) |- p)
[~BETA:]
  (theory_ok thy ∧ type_ok (tysof thy) ty ∧ term_ok (sigof thy) t
   ⇒ (thy, []) |- Comb (Abs (Var x ty) t) (Var x ty) === t)
[~DEDUCT_ANTISYM:]
  ((thy, h1) |- c1 ∧
   (thy, h2) |- c2
   ⇒ (thy, term_union (term_remove c2 h1)
                      (term_remove c1 h2))
           |- c1 === c2)
[~EQ_MP:]
  ((thy, h1) |- p === q ∧
   (thy, h2) |- p' ∧ ACONV p p'
   ⇒ (thy, term_union h1 h2) |- q)
[~INST:]
  ((∀s s'. MEM (s',s) ilist ⇒
             ∃x ty. (s = Var x ty) ∧ s' has_type ty ∧ term_ok (sigof thy) s') ∧
   (thy, h) |- c
   ⇒ (thy, term_image (VSUBST ilist) h) |- VSUBST ilist c)
[~INST_TYPE:]
  ((EVERY (type_ok (tysof thy)) (MAP FST tyin)) ∧
   (thy, h) |- c
   ⇒ (thy, term_image (INST tyin) h) |- INST tyin c)
[~MK_COMB:]
  ((thy, h1) |- l1 === r1 ∧
   (thy, h2) |- l2 === r2 ∧
   welltyped(Comb l1 l2)
   ⇒ (thy, term_union h1 h2) |- Comb l1 l2 === Comb r1 r2)
[~REFL:]
  (theory_ok thy ∧ term_ok (sigof thy) t
   ⇒ (thy, []) |- t === t)
[~axioms:]
  (theory_ok thy ∧ c ∈ (axsof thy)
   ⇒ (thy, []) |- c)
End
   (`(thy, h) |- c` is written `proves (thy, h) c`; the rule `proves_X` is the constructor
   `proves.X`) -/
inductive proves : thy × List term → term → Prop where
  | ABS {x : mlstring} {ty : type} {h : List term} {thy : thy} {l r : term} :
      ¬ EXISTS (VFREE_IN (Var x ty)) h → type_ok (thy_tysof thy) ty →
      proves (thy, h) (equation l r) →
      proves (thy, h) (equation (Abs (Var x ty) l) (Abs (Var x ty) r))
  | ASSUME {thy : thy} {p : term} :
      theory_ok thy → has_type p BoolTy → term_ok (sigof thy) p →
      proves (thy, [p]) p
  | BETA {thy : thy} {ty : type} {t : term} {x : mlstring} :
      theory_ok thy → type_ok (thy_tysof thy) ty → term_ok (sigof thy) t →
      proves (thy, []) (equation (Comb (Abs (Var x ty) t) (Var x ty)) t)
  | DEDUCT_ANTISYM {thy : thy} {h1 h2 : List term} {c1 c2 : term} :
      proves (thy, h1) c1 → proves (thy, h2) c2 →
      proves (thy, term_union (term_remove c2 h1) (term_remove c1 h2)) (equation c1 c2)
  | EQ_MP {thy : thy} {h1 h2 : List term} {p q p' : term} :
      proves (thy, h1) (equation p q) → proves (thy, h2) p' → ACONV p p' →
      proves (thy, term_union h1 h2) q
  | INST {ilist : List (term × term)} {thy : thy} {h : List term} {c : term} :
      (∀ s s', (s', s) ∈ ilist →
        ∃ x ty, s = Var x ty ∧ has_type s' ty ∧ term_ok (sigof thy) s') →
      proves (thy, h) c →
      proves (thy, term_image (VSUBST ilist) h) (VSUBST ilist c)
  | INST_TYPE {thy : thy} {tyin : List (type × type)} {h : List term} {c : term} :
      EVERY (type_ok (thy_tysof thy)) (tyin.map Prod.fst) →
      proves (thy, h) c →
      proves (thy, term_image (INST tyin) h) (INST tyin c)
  | MK_COMB {thy : thy} {h1 h2 : List term} {l1 r1 l2 r2 : term} :
      proves (thy, h1) (equation l1 r1) → proves (thy, h2) (equation l2 r2) →
      welltyped (Comb l1 l2) →
      proves (thy, term_union h1 h2) (equation (Comb l1 l2) (Comb r1 r2))
  | REFL {thy : thy} {t : term} :
      theory_ok thy → term_ok (sigof thy) t →
      proves (thy, []) (equation t t)
  | axioms {thy : thy} {c : term} :
      theory_ok thy → c ∈ axsof thy →
      proves (thy, []) c

/-! ## Contexts -/

/- HOL4:
Datatype:
  update
  (* Definition of new constants by specification
     ConstSpec witnesses proposition *)
  = ConstSpec ((mlstring # term) list) term
  (* Definition of a new type operator
     TypeDefn name predicate abs_name rep_name *)
  | TypeDefn mlstring term mlstring mlstring
  (* NewType name arity *)
  | NewType mlstring num
  (* NewConst name type *)
  | NewConst mlstring type
  (* NewAxiom proposition *)
  | NewAxiom term
End -/
inductive update where
  | ConstSpec : List (mlstring × term) → term → update
  | TypeDefn : mlstring → term → mlstring → mlstring → update
  | NewType : mlstring → Nat → update
  | NewConst : mlstring → type → update
  | NewAxiom : term → update
  deriving Inhabited

export update (ConstSpec TypeDefn NewType NewConst NewAxiom)

/- HOL4:
Definition types_of_upd_def[simp]:
  (types_of_upd (ConstSpec _ _) = []) ∧
  (types_of_upd (TypeDefn name pred _ _) = [(name,LENGTH (tvars pred))]) ∧
  (types_of_upd (NewType name arity) = [(name,arity)]) ∧
  (types_of_upd (NewConst _ _) = []) ∧
  (types_of_upd (NewAxiom _) = [])
End -/
def types_of_upd : update → List (mlstring × Nat)
  | ConstSpec _ _ => []
  | TypeDefn name pred _ _ => [(name, (tvars pred).length)]
  | NewType name arity => [(name, arity)]
  | NewConst _ _ => []
  | NewAxiom _ => []

/- HOL4:
Definition consts_of_upd_def[simp]:
  (consts_of_upd (ConstSpec eqs prop) = MAP (λ(s,t). (s, typeof t)) eqs) ∧
  (consts_of_upd (TypeDefn name pred abs rep) =
     let rep_type = domain (typeof pred) in
     let abs_type = Tyapp name (MAP Tyvar (MAP implode (STRING_SORT (MAP explode (tvars pred))))) in
       [(abs, Fun rep_type abs_type);
        (rep, Fun abs_type rep_type)]) ∧
  (consts_of_upd (NewType _ _) = []) ∧
  (consts_of_upd (NewConst name type) = [(name,type)]) ∧
  (consts_of_upd (NewAxiom _) = [])
End -/
def consts_of_upd : update → List (mlstring × type)
  | ConstSpec eqs _ => eqs.map (fun st => (st.1, typeof st.2))
  | TypeDefn name pred abs rep =>
    let rep_type := domain (typeof pred)
    let abs_type := Tyapp name (((STRING_SORT ((tvars pred).map explode)).map implode).map Tyvar)
    [(abs, Fun rep_type abs_type), (rep, Fun abs_type rep_type)]
  | NewType _ _ => []
  | NewConst name type => [(name, type)]
  | NewAxiom _ => []

/- HOL4: Overload type_list = ``λctxt. FLAT (MAP types_of_upd ctxt)`` -/
@[reducible] def type_list (ctxt : List update) : List (mlstring × Nat) :=
  List.flatten (ctxt.map types_of_upd)

/- HOL4: Overload tysof = ``λctxt. alist_to_fmap (type_list ctxt)``
   (on contexts; Lean name `ctxt_tysof`) -/
@[reducible] def ctxt_tysof (ctxt : List update) : tysig := alist_to_fmap (type_list ctxt)

/- HOL4: Overload const_list = ``λctxt. FLAT (MAP consts_of_upd ctxt)`` -/
@[reducible] def const_list (ctxt : List update) : List (mlstring × type) :=
  List.flatten (ctxt.map consts_of_upd)

/- HOL4: Overload tmsof = ``λctxt. alist_to_fmap (const_list ctxt)``
   (on contexts; Lean name `ctxt_tmsof`) -/
@[reducible] def ctxt_tmsof (ctxt : List update) : tmsig := alist_to_fmap (const_list ctxt)

/- HOL4: Overload sigof = ``λctxt:update list. (tysof ctxt, tmsof ctxt)``
   (on contexts; Lean name `ctxt_sigof`) -/
@[reducible] def ctxt_sigof (ctxt : List update) : sig := (ctxt_tysof ctxt, ctxt_tmsof ctxt)

/- HOL4:
Definition axexts_of_upd_def[simp]:
  axexts_of_upd (NewAxiom prop) = [prop] ∧
  axexts_of_upd _ = []
End -/
def axexts_of_upd : update → List term
  | NewAxiom prop => [prop]
  | _ => []

/- HOL4:
Definition conexts_of_upd_def:
  (conexts_of_upd (ConstSpec eqs prop) =
    let ilist = MAP (λ(s,t). let ty = typeof t in (Const s ty,Var s ty)) eqs in
      [VSUBST ilist prop]) ∧
  (conexts_of_upd (TypeDefn name pred abs_name rep_name) =
    let abs_type = Tyapp name (MAP Tyvar (MAP implode (STRING_SORT (MAP explode (tvars pred))))) in
    let rep_type = domain (typeof pred) in
    let abs = Const abs_name (Fun rep_type abs_type) in
    let rep = Const rep_name (Fun abs_type rep_type) in
    let a = Var «a» abs_type in
    let r = Var «r» rep_type in
      [Comb abs (Comb rep a) === a;
       Comb pred r === (Comb rep (Comb abs r) === r)]) ∧
  (conexts_of_upd _ = [])
End -/
def conexts_of_upd : update → List term
  | ConstSpec eqs prop =>
    let ilist := eqs.map (fun st => let ty := typeof st.2; (Const st.1 ty, Var st.1 ty))
    [VSUBST ilist prop]
  | TypeDefn name pred abs_name rep_name =>
    let abs_type := Tyapp name (((STRING_SORT ((tvars pred).map explode)).map implode).map Tyvar)
    let rep_type := domain (typeof pred)
    let abs := Const abs_name (Fun rep_type abs_type)
    let rep := Const rep_name (Fun abs_type rep_type)
    let a := Var (mls "a") abs_type
    let r := Var (mls "r") rep_type
    [equation (Comb abs (Comb rep a)) a,
     equation (Comb pred r) (equation (Comb rep (Comb abs r)) r)]
  | _ => []

/- HOL4: Overload axexts = ``λctxt. FLAT (MAP axexts_of_upd ctxt)`` -/
@[reducible] def axexts (ctxt : List update) : List term := List.flatten (ctxt.map axexts_of_upd)

/- HOL4: Overload conexts = ``λctxt. FLAT (MAP conexts_of_upd ctxt)`` -/
@[reducible] def conexts (ctxt : List update) : List term := List.flatten (ctxt.map conexts_of_upd)

/- HOL4: Overload axioms_of_upd = ``λupd. axexts_of_upd upd ++ conexts_of_upd upd`` -/
@[reducible] def axioms_of_upd (upd : update) : List term := axexts_of_upd upd ++ conexts_of_upd upd

/- HOL4: Overload axiom_list = ``λctxt. FLAT (MAP axioms_of_upd ctxt)`` -/
@[reducible] def axiom_list (ctxt : List update) : List term := List.flatten (ctxt.map axioms_of_upd)

/- HOL4: Overload axsof = ``λctxt. set (axiom_list ctxt)``
   (on contexts; Lean name `ctxt_axsof`) -/
@[reducible] def ctxt_axsof (ctxt : List update) : Set term := LIST_TO_SET (axiom_list ctxt)

/- HOL4: Overload thyof = ``λctxt:update list. (sigof ctxt, axsof ctxt)`` -/
@[reducible] def thyof (ctxt : List update) : thy := (ctxt_sigof ctxt, ctxt_axsof ctxt)

/- HOL4:
val _ = Parse.add_infix("updates",450,Parse.NONASSOC)
Inductive updates:
  (* new_axiom *)
  (prop has_type Bool ∧
   term_ok (sigof ctxt) prop
   ⇒ (NewAxiom prop) updates ctxt) ∧
  (* new_constant *)
  (name ∉ (FDOM (tmsof ctxt)) ∧
   type_ok (tysof ctxt) ty
   ⇒ (NewConst name ty) updates ctxt) ∧
  (* new_specification *)
  ((thyof ctxt, MAP (λ(s,t). Var s (typeof t) === t) eqs) |- prop ∧
   EVERY
     (λt. CLOSED t ∧
          (∀v. MEM v (tvars t) ⇒ MEM v (tyvars (typeof t))))
     (MAP SND eqs) ∧
   (∀x ty. VFREE_IN (Var x ty) prop ⇒
             MEM (x,ty) (MAP (λ(s,t). (s,typeof t)) eqs)) ∧
   (∀s. MEM s (MAP FST eqs) ⇒ s ∉ (FDOM (tmsof ctxt))) ∧
   ALL_DISTINCT (MAP FST eqs)
   ⇒ (ConstSpec eqs prop) updates ctxt) ∧
  (* new_type *)
  (name ∉ (FDOM (tysof ctxt))
   ⇒ (NewType name arity) updates ctxt) ∧
  (* new_type_definition *)
  ((thyof ctxt, []) |- Comb pred witness ∧
   CLOSED pred ∧
   name ∉ (FDOM (tysof ctxt)) ∧
   abs ∉ (FDOM (tmsof ctxt)) ∧
   rep ∉ (FDOM (tmsof ctxt)) ∧
   abs ≠ rep
   ⇒ (TypeDefn name pred abs rep) updates ctxt)
End
   (`upd updates ctxt` is written `updates upd ctxt`) -/
inductive updates : update → List update → Prop where
  | new_axiom {prop : term} {ctxt : List update} :
      has_type prop BoolTy → term_ok (ctxt_sigof ctxt) prop →
      updates (NewAxiom prop) ctxt
  | new_constant {name : mlstring} {ctxt : List update} {ty : type} :
      ¬ name ∈ FDOM (ctxt_tmsof ctxt) → type_ok (ctxt_tysof ctxt) ty →
      updates (NewConst name ty) ctxt
  | new_specification {ctxt : List update} {eqs : List (mlstring × term)} {prop : term} :
      proves (thyof ctxt, eqs.map (fun st => equation (Var st.1 (typeof st.2)) st.2)) prop →
      EVERY (fun t => CLOSED t ∧ (∀ v, v ∈ tvars t → v ∈ tyvars (typeof t))) (eqs.map Prod.snd) →
      (∀ x ty, VFREE_IN (Var x ty) prop → (x, ty) ∈ eqs.map (fun st => (st.1, typeof st.2))) →
      (∀ s, s ∈ eqs.map Prod.fst → ¬ s ∈ FDOM (ctxt_tmsof ctxt)) →
      ALL_DISTINCT (eqs.map Prod.fst) →
      updates (ConstSpec eqs prop) ctxt
  | new_type {name : mlstring} {ctxt : List update} {arity : Nat} :
      ¬ name ∈ FDOM (ctxt_tysof ctxt) →
      updates (NewType name arity) ctxt
  | new_type_definition {ctxt : List update} {pred witness : term} {name abs rep : mlstring} :
      proves (thyof ctxt, []) (Comb pred witness) →
      CLOSED pred →
      ¬ name ∈ FDOM (ctxt_tysof ctxt) →
      ¬ abs ∈ FDOM (ctxt_tmsof ctxt) →
      ¬ rep ∈ FDOM (ctxt_tmsof ctxt) →
      abs ≠ rep →
      updates (TypeDefn name pred abs rep) ctxt

/-! ## Theorems (stage 2) -/

/- HOL4:
Theorem domain_def[compute,simp]:
   !t s. domain (Fun s t) = s
-/
theorem domain_def : ∀ (t s : type), domain (Fun s t) = s := by
  intro t s
  rfl

/- HOL4:
Theorem codomain_def[compute,simp]:
   !t s. codomain (Fun s t) = t
-/
theorem codomain_def : ∀ (t s : type), codomain (Fun s t) = t := by
  intro t s
  rfl

theorem Aux.VFREE_IN_bound (t : term) : ∃ l : List term, ∀ x, VFREE_IN x t → x ∈ l := by
  induction t with
  | Var x ty => exact ⟨[Var x ty], fun y h => by simp only [VFREE_IN] at h; simp [h]⟩
  | Const x ty => exact ⟨[Const x ty], fun y h => by simp only [VFREE_IN] at h; simp [h]⟩
  | Comb s t ihs iht =>
    obtain ⟨l1, h1⟩ := ihs
    obtain ⟨l2, h2⟩ := iht
    refine ⟨l1 ++ l2, fun x h => ?_⟩
    simp only [VFREE_IN] at h
    rcases h with h | h
    · exact List.mem_append_left _ (h1 x h)
    · exact List.mem_append_right _ (h2 x h)
  | Abs v t _ iht =>
    obtain ⟨l, h1⟩ := iht
    refine ⟨l, fun x h => ?_⟩
    simp only [VFREE_IN] at h
    exact h1 x h.2

/- HOL4:
Theorem VFREE_IN_FINITE:
   ∀t. FINITE {x | VFREE_IN x t}
-/
theorem VFREE_IN_FINITE : ∀ (t : term), FINITE (setOf (fun x => VFREE_IN x t)) := by
  intro t
  exact Aux.FINITE_iff.mpr (Aux.VFREE_IN_bound t)

/- HOL4:
Theorem VFREE_IN_FINITE_ALT:
   ∀t ty. FINITE {x | VFREE_IN (Var (implode x) ty) t}
-/
theorem VFREE_IN_FINITE_ALT :
    ∀ (t : term) (ty : type), FINITE (setOf (fun (x : string) => VFREE_IN (Var (implode x) ty) t)) := by
  intro t ty
  obtain ⟨l, hl⟩ := Aux.VFREE_IN_bound t
  refine Aux.FINITE_iff.mpr
    ⟨l.map (fun u => match u with | Var s _ => explode s | _ => []), fun x hx => ?_⟩
  exact List.mem_map.mpr ⟨_, hl _ hx, explode_thm x⟩

/- HOL4:
Theorem PRIMED_NAME_EXISTS:
   ∃n. ¬(VFREE_IN (Var (implode (APPEND x (GENLIST (K #"'") n))) ty) t)
-/
theorem PRIMED_NAME_EXISTS (x : string) (ty : type) (t : term) :
    ∃ n, ¬ VFREE_IN (Var (implode (x ++ GENLIST (K (ch '\'')) n)) ty) t := by
  exact ⟨VARIANT_PRIMES t x ty, (VARIANT_PRIMES_def t x ty).1⟩

/- HOL4:
Theorem VARIANT_THM:
   ∀t x ty. ¬VFREE_IN (Var (VARIANT t x ty) ty) t
-/
theorem VARIANT_THM : ∀ (t : term) (x : string) (ty : type), ¬ VFREE_IN (Var (VARIANT t x ty) ty) t := by
  intro t x ty
  exact (VARIANT_PRIMES_def t x ty).1

/- HOL4:
Theorem SIZEOF_VSUBST:
   ∀t ilist. (∀s' s. MEM (s',s) ilist ⇒ ∃x ty. s' = Var x ty)
              ⇒ sizeof (VSUBST ilist t) = sizeof t
-/
theorem SIZEOF_VSUBST :
    ∀ (t : term) (ilist : List (term × term)),
      (∀ s' s, (s', s) ∈ ilist → ∃ x ty, s' = Var x ty) →
      sizeof (VSUBST ilist t) = sizeof t := by
  exact Aux.sizeof_VSUBST_aux

end

end Candle
