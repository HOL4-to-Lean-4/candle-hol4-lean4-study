import CandleLean.HolSyntaxLib
/-
  Translation of `candle/standard/syntax/holSyntaxScript.sml`.
  Namespace `Candle.HolSyntax`.
-/
namespace Candle.HolSyntax

open HOL Candle.Misc Candle.Mlstring Candle.HolSyntaxLib
universe u

open Classical

noncomputable section

instance : Inhabited mlstring := ⟨.implode []⟩

/- HOL4: Datatype:
  type
  = Tyvar mlstring
  | Tyapp mlstring (type list)
End -/
inductive type where
  | Tyvar : mlstring → type
  | Tyapp : mlstring → List type → type

export type (Tyvar Tyapp)

instance : Inhabited type := ⟨.Tyvar default⟩

/- HOL4: Overload Fun = ``λs t. Tyapp «fun» [s;t]`` -/
def Fun (s t : type) : type := .Tyapp (ml "fun") [s, t]
/- HOL4: Overload Bool = ``Tyapp «bool» []``   (Lean name `BoolTy`, to avoid `Bool`) -/
def BoolTy : type := .Tyapp (ml "bool") []

/- HOL4: Definition domain_raw:
  domain ty = case ty of Tyapp n (x::xs) => x | _ => ty
End   (the constant is called `domain`) -/
def domain : type → type
  | .Tyapp _ (x :: _) => x
  | ty => ty

/- HOL4: Definition codomain_raw:
  codomain ty = case ty of Tyapp n (y::x::xs) => x | _ => ty
End   (the constant is called `codomain`) -/
def codomain : type → type
  | .Tyapp _ (_ :: x :: _) => x
  | ty => ty

/- HOL4: Datatype:
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

export term (Var Const Comb Abs)

instance : Inhabited term := ⟨.Var default default⟩

/- HOL4: Overload Equal = ``λty. Const «=» (Fun ty (Fun ty Bool))`` -/
def Equal (ty : type) : term := .Const (ml "=") (Fun ty (Fun ty BoolTy))

/- HOL4: Definition dest_var_def[simp]:
  dest_var (Var x ty) = (x,ty)
End   (unspecified for non-variables; here `ARB`) -/
def dest_var : term → mlstring × type
  | .Var x ty => (x, ty)
  | _ => ARB

/- HOL4: Inductive has_type:
  ((Var   n ty) has_type ty) ∧
  ((Const n ty) has_type ty) ∧
  (s has_type (Fun dty rty) ∧
   t has_type dty
   ⇒
   (Comb s t) has_type rty) ∧
  (t has_type rty ⇒
   (Abs (Var n dty) t) has_type (Fun dty rty))
End   (infix `s has_type ty`: written `has_type s ty`) -/
inductive has_type : term → type → Prop where
  | Var (n : mlstring) (ty : type) : has_type (.Var n ty) ty
  | Const (n : mlstring) (ty : type) : has_type (.Const n ty) ty
  | Comb (s t : term) (dty rty : type) :
      has_type s (Fun dty rty) → has_type t dty → has_type (.Comb s t) rty
  | Abs (t : term) (rty : type) (n : mlstring) (dty : type) :
      has_type t rty → has_type (.Abs (.Var n dty) t) (Fun dty rty)

/- HOL4: Definition welltyped_def:
  welltyped tm = ∃ty. tm has_type ty
End -/
def welltyped (tm : term) : Prop := ∃ ty, has_type tm ty

/- HOL4: Definition typeof_def[simp]:
  (typeof (Var n   ty) = ty) ∧
  (typeof (Const n ty) = ty) ∧
  (typeof (Comb s t)   = codomain (typeof s)) ∧
  (typeof (Abs v t) = Fun (typeof v) (typeof t))
End -/
def typeof : term → type
  | .Var _ ty => ty
  | .Const _ ty => ty
  | .Comb s _ => codomain (typeof s)
  | .Abs v t => Fun (typeof v) (typeof t)

/- HOL4: Inductive RACONV:
  (ALPHAVARS env (Var x1 ty1,Var x2 ty2)
    ⇒ RACONV env (Var x1 ty1,Var x2 ty2)) ∧
  (RACONV env (Const x ty,Const x ty)) ∧
  (RACONV env (s1,s2) ∧ RACONV env (t1,t2)
    ⇒ RACONV env (Comb s1 t1,Comb s2 t2)) ∧
  (typeof v1 = typeof v2 ∧ RACONV ((v1,v2)::env) (t1,t2)
    ⇒ RACONV env (Abs v1 t1,Abs v2 t2))
End -/
inductive RACONV : List (term × term) → term × term → Prop where
  | Var (env : List (term × term)) (x1 : mlstring) (ty1 : type) (x2 : mlstring) (ty2 : type) :
      ALPHAVARS env (.Var x1 ty1, .Var x2 ty2) → RACONV env (.Var x1 ty1, .Var x2 ty2)
  | Const (env : List (term × term)) (x : mlstring) (ty : type) :
      RACONV env (.Const x ty, .Const x ty)
  | Comb (env : List (term × term)) (s1 s2 t1 t2 : term) :
      RACONV env (s1, s2) → RACONV env (t1, t2) → RACONV env (.Comb s1 t1, .Comb s2 t2)
  | Abs (env : List (term × term)) (v1 v2 t1 t2 : term) :
      typeof v1 = typeof v2 → RACONV ((v1, v2) :: env) (t1, t2) → RACONV env (.Abs v1 t1, .Abs v2 t2)

/- HOL4: Definition ACONV_def:
  ACONV t1 t2 ⇔ RACONV [] (t1,t2)
End -/
def ACONV (t1 t2 : term) : Prop := RACONV [] (t1, t2)

/- HOL4: Inductive type_lt:
  (mlstring_lt x1 x2 ⇒ type_lt (Tyvar x1) (Tyvar x2)) ∧
  (type_lt (Tyvar x1) (Tyapp x2 args2)) ∧
  ((mlstring_lt LEX LLEX type_lt) (x1,args1) (x2,args2) ⇒
     type_lt (Tyapp x1 args1) (Tyapp x2 args2))
End
   Lean cannot take `LLEX type_lt` as a premise of an inductive family defining `type_lt` itself
   (non-positive occurrence).  We therefore unfold `LEX` and `LLEX` into the mutual inductive
   `type_lt` / `type_llex`, where `type_llex l1 l2` is exactly `LLEX type_lt l1 l2`
   (LLEX R [] l2 = l2 ≠ []; LLEX R (h1::t1) (h2::t2) = R h1 h2 ∨ (h1 = h2 ∧ LLEX R t1 t2)). -/
mutual
inductive type_lt : type → type → Prop where
  | tyvar (x1 x2 : mlstring) : mlstring_lt x1 x2 → type_lt (.Tyvar x1) (.Tyvar x2)
  | tyvar_tyapp (x1 x2 : mlstring) (args2 : List type) : type_lt (.Tyvar x1) (.Tyapp x2 args2)
  | tyapp_name (x1 x2 : mlstring) (args1 args2 : List type) :
      mlstring_lt x1 x2 → type_lt (.Tyapp x1 args1) (.Tyapp x2 args2)
  | tyapp_args (x : mlstring) (args1 args2 : List type) :
      type_llex args1 args2 → type_lt (.Tyapp x args1) (.Tyapp x args2)
inductive type_llex : List type → List type → Prop where
  | nil (l2 : List type) : l2 ≠ [] → type_llex [] l2
  | lt (h1 h2 : type) (t1 t2 : List type) : type_lt h1 h2 → type_llex (h1 :: t1) (h2 :: t2)
  | eq (h : type) (t1 t2 : List type) : type_llex t1 t2 → type_llex (h :: t1) (h :: t2)
end

/- HOL4: Inductive term_lt:
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
   (`term_lt LEX term_lt` is unfolded: R1 s1 t1 ∨ (s1 = t1 ∧ R2 s2 t2), as two constructors.) -/
inductive term_lt : term → term → Prop where
  | var_var (x1 x2 : mlstring) (ty1 ty2 : type) :
      LEX mlstring_lt type_lt (x1, ty1) (x2, ty2) → term_lt (.Var x1 ty1) (.Var x2 ty2)
  | var_const (x1 x2 : mlstring) (ty1 ty2 : type) : term_lt (.Var x1 ty1) (.Const x2 ty2)
  | var_comb (x1 : mlstring) (ty1 : type) (t1 t2 : term) : term_lt (.Var x1 ty1) (.Comb t1 t2)
  | var_abs (x1 : mlstring) (ty1 : type) (t1 t2 : term) : term_lt (.Var x1 ty1) (.Abs t1 t2)
  | const_const (x1 x2 : mlstring) (ty1 ty2 : type) :
      LEX mlstring_lt type_lt (x1, ty1) (x2, ty2) → term_lt (.Const x1 ty1) (.Const x2 ty2)
  | const_comb (x1 : mlstring) (ty1 : type) (t1 t2 : term) : term_lt (.Const x1 ty1) (.Comb t1 t2)
  | const_abs (x1 : mlstring) (ty1 : type) (t1 t2 : term) : term_lt (.Const x1 ty1) (.Abs t1 t2)
  | comb_comb_fst (s1 s2 t1 t2 : term) : term_lt s1 t1 → term_lt (.Comb s1 s2) (.Comb t1 t2)
  | comb_comb_snd (s1 s2 t2 : term) : term_lt s2 t2 → term_lt (.Comb s1 s2) (.Comb s1 t2)
  | comb_abs (s1 s2 t1 t2 : term) : term_lt (.Comb s1 s2) (.Abs t1 t2)
  | abs_abs_fst (s1 s2 t1 t2 : term) : term_lt s1 t1 → term_lt (.Abs s1 s2) (.Abs t1 t2)
  | abs_abs_snd (s1 s2 t2 : term) : term_lt s2 t2 → term_lt (.Abs s1 s2) (.Abs s1 t2)

/- HOL4: Definition term_cmp_def:
  term_cmp = TO_of_LinearOrder term_lt
End -/
def term_cmp : term → term → Ordering := TO_of_LinearOrder term_lt

/- HOL4: Definition type_cmp_def:
  type_cmp = TO_of_LinearOrder type_lt
End -/
def type_cmp : type → type → Ordering := TO_of_LinearOrder type_lt

/- HOL4: Definition ordav_def:
  (ordav [] x1 x2 ⇔ term_cmp x1 x2) ∧
  (ordav ((t1,t2)::env) x1 x2 ⇔
    if x1 = t1 then
      if x2 = t2 then EQUAL
      else LESS
    else if x2 = t2 then GREATER
    else ordav env x1 x2)
End -/
def ordav : List (term × term) → term → term → Ordering
  | [], x1, x2 => term_cmp x1 x2
  | (t1, t2) :: env, x1, x2 =>
    if x1 = t1 then (if x2 = t2 then EQUAL else LESS)
    else if x2 = t2 then GREATER
    else ordav env x1 x2

/- HOL4: Definition orda_def:
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
def orda (env : List (term × term)) (t1 t2 : term) : Ordering :=
  if t1 = t2 ∧ env = [] then EQUAL else
    match t1, t2 with
    | .Var _ _, .Var _ _ => ordav env t1 t2
    | .Const _ _, .Const _ _ => term_cmp t1 t2
    | .Comb s1 u1, .Comb s2 u2 =>
      (let c := orda env s1 s2
       if c ≠ EQUAL then c else orda env u1 u2)
    | .Abs s1 u1, .Abs s2 u2 =>
      (let c := type_cmp (typeof s1) (typeof s2)
       if c ≠ EQUAL then c else orda ((s1, s2) :: env) u1 u2)
    | .Var _ _, _ => LESS
    | _, .Var _ _ => GREATER
    | .Const _ _, _ => LESS
    | _, .Const _ _ => GREATER
    | .Comb _ _, _ => LESS
    | _, .Comb _ _ => GREATER
termination_by sizeOf t1
decreasing_by all_goals (simp_wf; omega)

/- HOL4: Definition term_union_def:
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

/- HOL4: Definition term_remove_def:
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
def term_remove (t : term) : List term → List term
  | [] => []
  | s :: ss =>
    let c := orda [] t s
    if c = GREATER then
      let ss' := term_remove t ss
      if ss' = ss then s :: ss else s :: ss'
    else if c = EQUAL then ss else s :: ss

/- HOL4: Definition term_image_def:
  term_image f l =
  case l of
  | [] => l
  | (h::t) =>
    let h' = f h in
    let t' = term_image f t in
    if h' = h ∧ t' = t then l
    else term_union [h'] t'
End -/
def term_image (f : term → term) : List term → List term
  | [] => []
  | h :: t =>
    let h' := f h
    let t' := term_image f t
    if h' = h ∧ t' = t then h :: t
    else term_union [h'] t'

/- HOL4: Definition VFREE_IN_def[simp]:
  (VFREE_IN v (Var x ty) ⇔ (Var x ty = v)) ∧
  (VFREE_IN v (Const x ty) ⇔ (Const x ty = v)) ∧
  (VFREE_IN v (Comb s t) ⇔ VFREE_IN v s ∨ VFREE_IN v t) ∧
  (VFREE_IN v (Abs w t) ⇔ (w ≠ v) ∧ VFREE_IN v t)
End -/
def VFREE_IN (v : term) : term → Prop
  | .Var x ty => .Var x ty = v
  | .Const x ty => .Const x ty = v
  | .Comb s t => VFREE_IN v s ∨ VFREE_IN v t
  | .Abs w t => w ≠ v ∧ VFREE_IN v t

/- HOL4: Definition CLOSED_def:
  CLOSED tm = ∀x ty. ¬(VFREE_IN (Var x ty) tm)
End -/
def CLOSED (tm : term) : Prop := ∀ x ty, ¬ VFREE_IN (.Var x ty) tm

/- HOL4: val VARIANT_PRIMES_def = new_specification ("VARIANT_PRIMES_def", ["VARIANT_PRIMES"], ...)
   with  ∀t x ty. ¬VFREE_IN (Var (implode (APPEND x (GENLIST (K #"'") n))) ty) t  at  n = VARIANT_PRIMES t x ty,
   and n least with this property (from LEAST_EXISTS).  Defined here by Hilbert choice (`LEAST`). -/
def VARIANT_PRIMES (t : term) (x : string) (ty : type) : Nat :=
  LEAST (fun n => ¬ VFREE_IN (.Var (.implode (APPEND x (GENLIST (K (hchar '\'')) n))) ty) t)

/- HOL4: Definition VARIANT_def:
  VARIANT t x ty = implode (APPEND x (GENLIST (K #"'") (VARIANT_PRIMES t x ty)))
End -/
def VARIANT (t : term) (x : string) (ty : type) : mlstring :=
  .implode (APPEND x (GENLIST (K (hchar '\'')) (VARIANT_PRIMES t x ty)))

/- HOL4: Definition TYPE_SUBST_def[simp]:
  (TYPE_SUBST i (Tyvar v) = REV_ASSOCD (Tyvar v) i (Tyvar v)) ∧
  (TYPE_SUBST i (Tyapp v tys) = Tyapp v (MAP (TYPE_SUBST i) tys)) ∧
  (TYPE_SUBST i (Fun ty1 ty2) = Fun (TYPE_SUBST i ty1) (TYPE_SUBST i ty2))
Termination
  type_rec_tac "SND"
End
   Nested recursion through `MAP` is expressed with the mutually recursive auxiliary function
   `TYPE_SUBST_list i tys` (= `MAP (TYPE_SUBST i) tys`, see `TYPE_SUBST_list_eq`).
   The third HOL4 clause is a consequence of the second. -/
mutual
def TYPE_SUBST (i : List (type × type)) : type → type
  | .Tyvar v => REV_ASSOCD (.Tyvar v) i (.Tyvar v)
  | .Tyapp v tys => .Tyapp v (TYPE_SUBST_list i tys)
def TYPE_SUBST_list (i : List (type × type)) : List type → List type
  | [] => []
  | t :: ts => TYPE_SUBST i t :: TYPE_SUBST_list i ts
end

/-- Helper: the auxiliary function is `MAP (TYPE_SUBST i)`. -/
theorem TYPE_SUBST_list_eq (i : List (type × type)) (tys : List type) :
    TYPE_SUBST_list i tys = MAP (TYPE_SUBST i) tys := by
  induction tys with
  | nil => rfl
  | cons t ts ih => simp [TYPE_SUBST_list, MAP, ih]

/- HOL4: Overload is_instance = ``λty0 ty. ∃i. ty = TYPE_SUBST i ty0`` -/
def is_instance (ty0 ty : type) : Prop := ∃ i, ty = TYPE_SUBST i ty0

/- HOL4: Definition VSUBST_def:
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
End -/
def VSUBST : List (term × term) → term → term
  | ilist, .Var x ty => REV_ASSOCD (.Var x ty) ilist (.Var x ty)
  | _, .Const x ty => .Const x ty
  | ilist, .Comb s t => .Comb (VSUBST ilist s) (VSUBST ilist t)
  | ilist, .Abs v t =>
    let ilist' := FILTER (fun p => ¬ (p.2 = v)) ilist
    let t' := VSUBST ilist' t
    if EXISTS (fun p => VFREE_IN v p.1 ∧ VFREE_IN p.2 t) ilist' then
      let xty := dest_var v
      let z := Var (VARIANT t' (explode xty.1) xty.2) xty.2
      let ilist'' := (z, v) :: ilist'
      .Abs z (VSUBST ilist'' t)
    else .Abs v t'

/- HOL4: Definition sizeof_def[simp]:
  sizeof (Var x ty) = 1n ∧
  sizeof (Const x ty) = 1 ∧
  sizeof (Comb s t) = 1 + sizeof s + sizeof t ∧
  sizeof (Abs v t) = 2 + sizeof t
End -/
def sizeof : term → Nat
  | .Var _ _ => 1
  | .Const _ _ => 1
  | .Comb s t => 1 + sizeof s + sizeof t
  | .Abs _ t => 2 + sizeof t

theorem REV_ASSOCD_var_helper (a : term) (l : List (term × term))
    (hl : ∀ s' s, MEM (s', s) l → ∃ x ty, s' = .Var x ty)
    (d : term) (hd : ∃ x ty, d = .Var x ty) : ∃ x' ty', REV_ASSOCD a l d = .Var x' ty' := by
  induction l with
  | nil => simpa [REV_ASSOCD] using hd
  | cons p t ih =>
    unfold REV_ASSOCD
    split
    · obtain ⟨x', ty', h'⟩ := hl p.1 p.2 (by simp [MEM_cons])
      exact ⟨x', ty', h'⟩
    · exact ih (fun s' s hm => hl s' s (by simp [MEM_cons, hm]))

/-- Helper for the termination of `INST_CORE` (HOL4: theorem `SIZEOF_VSUBST`, proved in HOL4
    before `INST_CORE`).  Named differently so that it does not collide with the target theorem. -/
theorem sizeof_VSUBST_helper (t : term) :
    ∀ ilist : List (term × term), (∀ s' s, MEM (s', s) ilist → ∃ x ty, s' = .Var x ty) →
      sizeof (VSUBST ilist t) = sizeof t := by
  induction t with
  | Var x ty =>
    intro ilist h
    obtain ⟨x', ty', h'⟩ := REV_ASSOCD_var_helper (.Var x ty) ilist h (.Var x ty) ⟨x, ty, rfl⟩
    simp only [VSUBST, h', sizeof]
  | Const x ty => intro ilist h; simp [VSUBST, sizeof]
  | Comb s t ihs iht =>
    intro ilist h; simp [VSUBST, sizeof, ihs ilist h, iht ilist h]
  | Abs v t ihs iht =>
    intro ilist h
    have hf : ∀ s' s, MEM (s', s) (FILTER (fun p : term × term => ¬ (p.2 = v)) ilist) →
        ∃ x ty, s' = .Var x ty := fun s' s hm => h s' s ((MEM_FILTER _ _ _).1 hm).1
    simp only [VSUBST]
    split
    · simp only [sizeof]
      rw [iht]
      intro s' s hm
      rw [MEM_cons] at hm
      rcases hm with hm | hm
      · simp only [Prod.mk.injEq] at hm
        exact ⟨_, _, hm.1⟩
      · exact hf s' s hm
    · simp only [sizeof]
      rw [iht _ hf]

/- HOL4: Definition INST_CORE_def:
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
Termination
  WF_REL_TAC`measure (sizeof o SND o SND)` >> simp[SIZEOF_VSUBST]
End -/
def INST_CORE (env : List (term × term)) (tyin : List (type × type)) (tm : term) : result term :=
  match tm with
  | .Var x ty =>
    let tm := Var x ty
    let tm' := Var x (TYPE_SUBST tyin ty)
    if REV_ASSOCD tm' env tm = tm then Result tm' else Clash tm'
  | .Const x ty => Result (Const x (TYPE_SUBST tyin ty))
  | .Comb s t =>
    let sres := INST_CORE env tyin s
    if IS_CLASH sres then sres else
    let tres := INST_CORE env tyin t
    if IS_CLASH tres then tres else
    let s' := RESULT sres
    let t' := RESULT tres
    Result (Comb s' t')
  | .Abs v t =>
    let xty := dest_var v
    let x := xty.1
    let ty := xty.2
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
termination_by sizeof tm
decreasing_by
  all_goals simp_wf
  all_goals first
    | (simp only [sizeof]; omega)
    | (rw [sizeof_VSUBST_helper t [(Var _ ty, Var _ ty)] (by intro s' s hm; simp [MEM_cons] at hm; obtain ⟨h1, _⟩ := hm; exact ⟨_, _, h1⟩)]
       simp only [sizeof]; omega)

/- HOL4: Definition INST_def:
  INST tyin tm = RESULT(INST_CORE [] tyin tm)
End -/
def INST (tyin : List (type × type)) (tm : term) : term := RESULT (INST_CORE [] tyin tm)

/- HOL4: Definition tyvars_def:
  tyvars (Tyvar v) = [v] ∧
  tyvars (Tyapp v tys) = FOLDR (λx y. LIST_UNION (tyvars x) y) [] tys
Termination
  type_rec_tac "I"
End
   (nested recursion through FOLDR, expressed with the auxiliary `tyvars_list`;
    `tyvars_list tys = FOLDR (λx y. LIST_UNION (tyvars x) y) [] tys`, see `tyvars_list_eq`.) -/
mutual
def tyvars : type → List mlstring
  | .Tyvar v => [v]
  | .Tyapp _ tys => tyvars_list tys
def tyvars_list : List type → List mlstring
  | [] => []
  | t :: ts => LIST_UNION (tyvars t) (tyvars_list ts)
end

/-- Helper: the auxiliary function is the `FOLDR` of the HOL4 definition. -/
theorem tyvars_list_eq (tys : List type) :
    tyvars_list tys = FOLDR (fun x y => LIST_UNION (tyvars x) y) [] tys := by
  induction tys with
  | nil => rfl
  | cons t ts ih => simp [tyvars_list, FOLDR, ih]

/- HOL4: Definition tvars_def:
  (tvars (Var n ty) = tyvars ty) ∧
  (tvars (Const n ty) = tyvars ty) ∧
  (tvars (Comb s t) = LIST_UNION (tvars s) (tvars t)) ∧
  (tvars (Abs v t) = LIST_UNION (tvars v) (tvars t))
End -/
def tvars : term → List mlstring
  | .Var _ ty => tyvars ty
  | .Const _ ty => tyvars ty
  | .Comb s t => LIST_UNION (tvars s) (tvars t)
  | .Abs v t => LIST_UNION (tvars v) (tvars t)

/- HOL4: Definition equation_def:
  (s === t) = Comb (Comb (Equal(typeof s)) s) t
End   (infixr `===` at 460) -/
def equation (s t : term) : term := .Comb (.Comb (Equal (typeof s)) s) t
scoped infixr:460 " === " => equation

/- HOL4: Type tysig = ``:mlstring |-> num`` -/
abbrev tysig := FMap mlstring Nat
/- HOL4: Type tmsig = ``:mlstring |-> type`` -/
abbrev tmsig := FMap mlstring type
/- HOL4: Type sig = ``:tysig # tmsig`` -/
abbrev sig := tysig × tmsig
/- HOL4: Type thy = ``:sig # term set`` -/
abbrev thy := sig × Set term

/- HOL4: the overloaded projections
     Overload tysof = ``FST:sig->tysig``       Overload tmsof = ``SND:sig->tmsig``
     Overload sigof = ``FST:thy->sig``         Overload axsof = ``SND:thy->term set``
     Overload tysof = ``tysof o sigof``        Overload tmsof = ``tmsof o sigof``   (on thy)
     and, for contexts (`update list`) further below,
     Overload tysof = ``λctxt. alist_to_fmap (type_list ctxt)``, etc.
   are modelled by type classes, so `tysof x` is resolved by the type of `x`. -/
class TysOf (X : Type) where
  tysof : X → tysig
class TmsOf (X : Type) where
  tmsof : X → tmsig
class SigOf (X : Type) where
  sigof : X → sig
class AxsOf (X : Type) where
  axsof : X → Set term
export TysOf (tysof)
export TmsOf (tmsof)
export SigOf (sigof)
export AxsOf (axsof)

instance : TysOf sig := ⟨FST⟩
instance : TmsOf sig := ⟨SND⟩
instance : SigOf thy := ⟨FST⟩
instance : AxsOf thy := ⟨SND⟩
instance : TysOf thy := ⟨fun t => tysof (sigof t)⟩
instance : TmsOf thy := ⟨fun t => tmsof (sigof t)⟩

/- HOL4: Definition type_ok_def:
   (type_ok tysig (Tyvar _) ⇔ T) ∧
   (type_ok tysig (Tyapp name args) ⇔
      FLOOKUP tysig name = SOME (LENGTH args) ∧
      EVERY (type_ok tysig) args)
Termination
  type_rec_tac "SND"
End
   (auxiliary mutual function `type_ok_list tysig args ⇔ EVERY (type_ok tysig) args`) -/
mutual
def type_ok (tysig : tysig) : type → Prop
  | .Tyvar _ => True
  | .Tyapp name args => FLOOKUP tysig name = some (LENGTH args) ∧ type_ok_list tysig args
def type_ok_list (tysig : tysig) : List type → Prop
  | [] => True
  | t :: ts => type_ok tysig t ∧ type_ok_list tysig ts
end

/-- Helper: the auxiliary function is `EVERY (type_ok tysig)`. -/
theorem type_ok_list_eq (tysig : tysig) (tys : List type) :
    type_ok_list tysig tys ↔ EVERY (type_ok tysig) tys := by
  induction tys with
  | nil => simp [type_ok_list, EVERY]
  | cons t ts ih => simp [type_ok_list, EVERY, ih]

/- HOL4: Definition term_ok_def:
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
  | .Var _ ty => type_ok (tysof sig) ty
  | .Const name ty =>
    ∃ ty0, FLOOKUP (tmsof sig) name = some ty0 ∧ type_ok (tysof sig) ty ∧ is_instance ty0 ty
  | .Comb tm1 tm2 => term_ok sig tm1 ∧ term_ok sig tm2 ∧ welltyped (.Comb tm1 tm2)
  | .Abs v tm => ∃ x ty, v = .Var x ty ∧ type_ok (tysof sig) ty ∧ term_ok sig tm

/- HOL4: Definition alpha_lt_def:
  alpha_lt t1 t2 ⇔ orda [] t1 t2 = LESS
End -/
def alpha_lt (t1 t2 : term) : Prop := orda [] t1 t2 = LESS

/- HOL4: Definition hypset_ok_def:
  hypset_ok ls ⇔ SORTED alpha_lt ls
End -/
def hypset_ok (ls : List term) : Prop := SORTED alpha_lt ls

/- HOL4: Definition is_std_sig_def:
  is_std_sig (sig:sig) ⇔
    FLOOKUP (tysof sig) «fun» = SOME 2 ∧
    FLOOKUP (tysof sig) «bool» = SOME 0 ∧
    FLOOKUP (tmsof sig) «=» = SOME (Fun (Tyvar «A») (Fun (Tyvar «A») Bool))
End -/
def is_std_sig (sig : sig) : Prop :=
  FLOOKUP (tysof sig) (ml "fun") = some 2 ∧
  FLOOKUP (tysof sig) (ml "bool") = some 0 ∧
  FLOOKUP (tmsof sig) (ml "=") = some (Fun (.Tyvar (ml "A")) (Fun (.Tyvar (ml "A")) BoolTy))

/- HOL4: Definition theory_ok_def:
  theory_ok (thy:thy) ⇔
    (∀ty. ty ∈ FRANGE (tmsof thy) ⇒ type_ok (tysof thy) ty) ∧
    (∀p. p ∈ (axsof thy) ⇒ term_ok (sigof thy) p ∧ p has_type Bool) ∧
    is_std_sig (sigof thy)
End -/
def theory_ok (thy : thy) : Prop :=
  (∀ ty, ty ∈ FRANGE (tmsof thy) → type_ok (tysof thy) ty) ∧
  (∀ p, p ∈ axsof thy → term_ok (sigof thy) p ∧ has_type p BoolTy) ∧
  is_std_sig (sigof thy)

/- HOL4: Inductive proves:
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
   (infix `(thy,h) |- c` at 450: written `(thy,h) |- c` with the scoped notation below, which is
    `proves (thy,h) c`.) -/
inductive proves : thy × List term → term → Prop where
  | ABS (thy : thy) (h : List term) (x : mlstring) (ty : type) (l r : term) :
      ¬ EXISTS (VFREE_IN (.Var x ty)) h → type_ok (tysof thy) ty →
      proves (thy, h) (l === r) →
      proves (thy, h) ((.Abs (.Var x ty) l) === (.Abs (.Var x ty) r))
  | ASSUME (thy : thy) (p : term) :
      theory_ok thy → has_type p BoolTy → term_ok (sigof thy) p → proves (thy, [p]) p
  | BETA (thy : thy) (ty : type) (t : term) (x : mlstring) :
      theory_ok thy → type_ok (tysof thy) ty → term_ok (sigof thy) t →
      proves (thy, []) (.Comb (.Abs (.Var x ty) t) (.Var x ty) === t)
  | DEDUCT_ANTISYM (thy : thy) (h1 h2 : List term) (c1 c2 : term) :
      proves (thy, h1) c1 → proves (thy, h2) c2 →
      proves (thy, term_union (term_remove c2 h1) (term_remove c1 h2)) (c1 === c2)
  | EQ_MP (thy : thy) (h1 h2 : List term) (p q p' : term) :
      proves (thy, h1) (p === q) → proves (thy, h2) p' → ACONV p p' →
      proves (thy, term_union h1 h2) q
  | INST (thy : thy) (ilist : List (term × term)) (h : List term) (c : term) :
      (∀ s s', MEM (s', s) ilist → ∃ x ty, s = .Var x ty ∧ has_type s' ty ∧ term_ok (sigof thy) s') →
      proves (thy, h) c →
      proves (thy, term_image (VSUBST ilist) h) (VSUBST ilist c)
  | INST_TYPE (thy : thy) (tyin : List (type × type)) (h : List term) (c : term) :
      EVERY (type_ok (tysof thy)) (MAP FST tyin) → proves (thy, h) c →
      proves (thy, term_image (INST tyin) h) (INST tyin c)
  | MK_COMB (thy : thy) (h1 h2 : List term) (l1 r1 l2 r2 : term) :
      proves (thy, h1) (l1 === r1) → proves (thy, h2) (l2 === r2) → welltyped (.Comb l1 l2) →
      proves (thy, term_union h1 h2) (.Comb l1 l2 === .Comb r1 r2)
  | REFL (thy : thy) (t : term) :
      theory_ok thy → term_ok (sigof thy) t → proves (thy, []) (t === t)
  | axioms (thy : thy) (c : term) :
      theory_ok thy → c ∈ axsof thy → proves (thy, []) c

scoped infix:450 " |- " => proves

/- HOL4: Datatype:
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

export update (ConstSpec TypeDefn NewType NewConst NewAxiom)

/- HOL4: Definition types_of_upd_def[simp]:
  (types_of_upd (ConstSpec _ _) = []) ∧
  (types_of_upd (TypeDefn name pred _ _) = [(name,LENGTH (tvars pred))]) ∧
  (types_of_upd (NewType name arity) = [(name,arity)]) ∧
  (types_of_upd (NewConst _ _) = []) ∧
  (types_of_upd (NewAxiom _) = [])
End -/
def types_of_upd : update → List (mlstring × Nat)
  | .ConstSpec _ _ => []
  | .TypeDefn name pred _ _ => [(name, LENGTH (tvars pred))]
  | .NewType name arity => [(name, arity)]
  | .NewConst _ _ => []
  | .NewAxiom _ => []

/- HOL4: Definition consts_of_upd_def[simp]:
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
  | .ConstSpec eqs _ => MAP (fun p => (p.1, typeof p.2)) eqs
  | .TypeDefn name pred abs rep =>
    let rep_type := domain (typeof pred)
    let abs_type := Tyapp name (MAP Tyvar (MAP .implode (STRING_SORT (MAP explode (tvars pred)))))
    [(abs, Fun rep_type abs_type), (rep, Fun abs_type rep_type)]
  | .NewType _ _ => []
  | .NewConst name ty => [(name, ty)]
  | .NewAxiom _ => []

/- HOL4: Overload type_list = ``λctxt. FLAT (MAP types_of_upd ctxt)`` -/
def type_list (ctxt : List update) : List (mlstring × Nat) := FLAT (MAP types_of_upd ctxt)
/- HOL4: Overload const_list = ``λctxt. FLAT (MAP consts_of_upd ctxt)`` -/
def const_list (ctxt : List update) : List (mlstring × type) := FLAT (MAP consts_of_upd ctxt)

/- HOL4: Overload tysof = ``λctxt. alist_to_fmap (type_list ctxt)``
        Overload tmsof = ``λctxt. alist_to_fmap (const_list ctxt)``
        Overload sigof = ``λctxt:update list. (tysof ctxt, tmsof ctxt)`` -/
instance : TysOf (List update) := ⟨fun ctxt => alist_to_fmap (type_list ctxt)⟩
instance : TmsOf (List update) := ⟨fun ctxt => alist_to_fmap (const_list ctxt)⟩
instance : SigOf (List update) := ⟨fun ctxt => (tysof ctxt, tmsof ctxt)⟩

/- HOL4: Definition axexts_of_upd_def[simp]:
  axexts_of_upd (NewAxiom prop) = [prop] ∧
  axexts_of_upd _ = []
End -/
def axexts_of_upd : update → List term
  | .NewAxiom prop => [prop]
  | _ => []

/- HOL4: Definition conexts_of_upd_def:
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
  | .ConstSpec eqs prop =>
    let ilist := MAP (fun p => let ty := typeof p.2; (Const p.1 ty, Var p.1 ty)) eqs
    [VSUBST ilist prop]
  | .TypeDefn name pred abs_name rep_name =>
    let abs_type := Tyapp name (MAP Tyvar (MAP .implode (STRING_SORT (MAP explode (tvars pred)))))
    let rep_type := domain (typeof pred)
    let abs := Const abs_name (Fun rep_type abs_type)
    let rep := Const rep_name (Fun abs_type rep_type)
    let a := Var (ml "a") abs_type
    let r := Var (ml "r") rep_type
    [Comb abs (Comb rep a) === a,
     Comb pred r === (Comb rep (Comb abs r) === r)]
  | _ => []

/- HOL4: Overload axexts = ``λctxt. FLAT (MAP axexts_of_upd ctxt)`` -/
def axexts (ctxt : List update) : List term := FLAT (MAP axexts_of_upd ctxt)
/- HOL4: Overload conexts = ``λctxt. FLAT (MAP conexts_of_upd ctxt)`` -/
def conexts (ctxt : List update) : List term := FLAT (MAP conexts_of_upd ctxt)
/- HOL4: Overload axioms_of_upd = ``λupd. axexts_of_upd upd ++ conexts_of_upd upd`` -/
def axioms_of_upd (upd : update) : List term := axexts_of_upd upd ++ conexts_of_upd upd
/- HOL4: Overload axiom_list = ``λctxt. FLAT (MAP axioms_of_upd ctxt)`` -/
def axiom_list (ctxt : List update) : List term := FLAT (MAP axioms_of_upd ctxt)
/- HOL4: Overload axsof = ``λctxt. set (axiom_list ctxt)`` -/
instance : AxsOf (List update) := ⟨fun ctxt => LIST_TO_SET (axiom_list ctxt)⟩

/- HOL4: Overload thyof = ``λctxt:update list. (sigof ctxt, axsof ctxt)`` -/
def thyof (ctxt : List update) : thy := (sigof ctxt, axsof ctxt)

/- HOL4: Inductive updates:
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
   (infix `upd updates ctxt`, written `updates upd ctxt`) -/
inductive updates : update → List update → Prop where
  | new_axiom (ctxt : List update) (prop : term) :
      has_type prop BoolTy → term_ok (sigof ctxt) prop → updates (.NewAxiom prop) ctxt
  | new_constant (ctxt : List update) (name : mlstring) (ty : type) :
      name ∉ FDOM (tmsof ctxt) → type_ok (tysof ctxt) ty → updates (.NewConst name ty) ctxt
  | new_specification (ctxt : List update) (eqs : List (mlstring × term)) (prop : term) :
      proves (thyof ctxt, MAP (fun p => Var p.1 (typeof p.2) === p.2) eqs) prop →
      EVERY (fun t => CLOSED t ∧ (∀ v, MEM v (tvars t) → MEM v (tyvars (typeof t)))) (MAP SND eqs) →
      (∀ x ty, VFREE_IN (.Var x ty) prop → MEM (x, ty) (MAP (fun p => (p.1, typeof p.2)) eqs)) →
      (∀ s, MEM s (MAP FST eqs) → s ∉ FDOM (tmsof ctxt)) →
      ALL_DISTINCT (MAP FST eqs) →
      updates (.ConstSpec eqs prop) ctxt
  | new_type (ctxt : List update) (name : mlstring) (arity : Nat) :
      name ∉ FDOM (tysof ctxt) → updates (.NewType name arity) ctxt
  | new_type_definition (ctxt : List update) (pred witness : term) (name abs rep : mlstring) :
      proves (thyof ctxt, []) (.Comb pred witness) → CLOSED pred →
      name ∉ FDOM (tysof ctxt) → abs ∉ FDOM (tmsof ctxt) → rep ∉ FDOM (tmsof ctxt) → abs ≠ rep →
      updates (.TypeDefn name pred abs rep) ctxt


/- HOL4: Theorem domain_def[compute,simp]:
   !t s. domain (Fun s t) = s -/
theorem domain_def : ∀ (t s : type), domain (Fun s t) = s := by sorry

/- HOL4: Theorem codomain_def[compute,simp]:
   !t s. codomain (Fun s t) = t -/
theorem codomain_def : ∀ (t s : type), codomain (Fun s t) = t := by sorry

/- HOL4: Theorem VFREE_IN_FINITE:
   ∀t. FINITE {x | VFREE_IN x t} -/
theorem VFREE_IN_FINITE : ∀ t : term, FINITE { x | VFREE_IN x t } := by sorry

/- HOL4: Theorem VFREE_IN_FINITE_ALT:
   ∀t ty. FINITE {x | VFREE_IN (Var (implode x) ty) t} -/
theorem VFREE_IN_FINITE_ALT : ∀ (t : term) (ty : type),
    FINITE { x | VFREE_IN (Var (implode x) ty) t } := by sorry

/- HOL4: Theorem PRIMED_NAME_EXISTS:
   ∃n. ¬(VFREE_IN (Var (implode (APPEND x (GENLIST (K #"'") n))) ty) t)
   (free variables x, ty, t are universally quantified) -/
theorem PRIMED_NAME_EXISTS : ∀ (x : string) (ty : type) (t : term),
    ∃ n : Nat, ¬ VFREE_IN (Var (implode (APPEND x (GENLIST (K (hchar '\'')) n))) ty) t := by sorry

/- HOL4: Theorem VARIANT_THM:
   ∀t x ty. ¬VFREE_IN (Var (VARIANT t x ty) ty) t -/
theorem VARIANT_THM : ∀ (t : term) (x : string) (ty : type),
    ¬ VFREE_IN (Var (VARIANT t x ty) ty) t := by sorry

/- HOL4: Theorem SIZEOF_VSUBST:
   ∀t ilist. (∀s' s. MEM (s',s) ilist ⇒ ∃x ty. s' = Var x ty)
              ⇒ sizeof (VSUBST ilist t) = sizeof t -/
theorem SIZEOF_VSUBST : ∀ (t : term) (ilist : List (term × term)),
    (∀ s' s, MEM (s', s) ilist → ∃ x ty, s' = Var x ty) →
    sizeof (VSUBST ilist t) = sizeof t := by sorry

end

end Candle.HolSyntax
