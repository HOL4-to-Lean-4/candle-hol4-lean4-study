/-
  HOL4 theory `holSyntax` (candle/standard/syntax/holSyntaxScript.sml):
  the HOL inference system.
-/
import CandleLean.HolSyntaxLib
import CandleLean.Mlstring

namespace Candle

noncomputable section
open Classical

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

instance : Inhabited type := ⟨Tyvar (implode [])⟩

/- HOL4:
Overload Fun = ``λs t. Tyapp «fun» [s;t]`` -/
abbrev Fun (s t : type) : type := Tyapp ml!"fun" [s, t]

/- HOL4:
Overload Bool = ``Tyapp «bool» []``
   (renamed: HOL `Bool` is `Bool'` in Lean, because `Bool` is Lean's Boolean type) -/
abbrev Bool' : type := Tyapp ml!"bool" []

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

export term (Var Const Comb Abs)

instance : Inhabited term := ⟨Var (implode []) default⟩

/- HOL4:
Overload Equal = ``λty. Const «=» (Fun ty (Fun ty Bool))`` -/
abbrev Equal (ty : type) : term := Const ml!"=" (Fun ty (Fun ty Bool'))

/- HOL4:
Definition dest_var_def[simp]:
  dest_var (Var x ty) = (x,ty)
End
   (a constructor pattern with missing clauses: defined by
   `Prim_rec.new_recursive_definition`, so `dest_var` is unspecified on `Const`, `Comb`, `Abs`
   and is an arbitrary function that satisfies the clause.) -/
def dest_var : term → mlstring × type :=
  select (fun f => ∀ x ty, f (Var x ty) = (x, ty))

/- HOL4: dest_var_def (the defining theorem of `dest_var`)  |- dest_var (Var x ty) = (x,ty) -/
theorem dest_var_def (x : mlstring) (ty : type) : dest_var (Var x ty) = (x, ty) :=
  select_spec (P := fun f : term → mlstring × type => ∀ x ty, f (Var x ty) = (x, ty))
    ⟨fun t => match t with | Var x ty => (x, ty) | _ => ARB, fun _ _ => rfl⟩ x ty

/-! ## Assignment of types to terms (where possible) -/

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
   (HOL `tm has_type ty` is `has_type tm ty`) -/
inductive has_type : term → type → Prop
  | var (n : mlstring) (ty : type) : has_type (Var n ty) ty
  | const (n : mlstring) (ty : type) : has_type (Const n ty) ty
  | comb (s t : term) (dty rty : type) :
      has_type s (Fun dty rty) → has_type t dty → has_type (Comb s t) rty
  | abs (n : mlstring) (dty rty : type) (t : term) :
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

/-! ## Alpha-equivalence -/

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
inductive RACONV : List (term × term) → term × term → Prop
  | var (env : List (term × term)) (x1 : mlstring) (ty1 : type) (x2 : mlstring) (ty2 : type) :
      ALPHAVARS env (Var x1 ty1, Var x2 ty2) → RACONV env (Var x1 ty1, Var x2 ty2)
  | const (env : List (term × term)) (x : mlstring) (ty : type) :
      RACONV env (Const x ty, Const x ty)
  | comb (env : List (term × term)) (s1 s2 t1 t2 : term) :
      RACONV env (s1, s2) → RACONV env (t1, t2) → RACONV env (Comb s1 t1, Comb s2 t2)
  | abs (env : List (term × term)) (v1 v2 t1 t2 : term) :
      typeof v1 = typeof v2 → RACONV ((v1, v2) :: env) (t1, t2) →
      RACONV env (Abs v1 t1, Abs v2 t2)

/- HOL4:
Definition ACONV_def:
  ACONV t1 t2 ⇔ RACONV [] (t1,t2)
End -/
def ACONV (t1 t2 : term) : Prop := RACONV [] (t1, t2)

/-! ## Term ordering, respecting alpha-equivalence -/

/- HOL4:
Inductive type_lt:
  (mlstring_lt x1 x2 ⇒ type_lt (Tyvar x1) (Tyvar x2)) ∧
  (type_lt (Tyvar x1) (Tyapp x2 args2)) ∧
  ((mlstring_lt LEX LLEX type_lt) (x1,args1) (x2,args2) ⇒
     type_lt (Tyapp x1 args1) (Tyapp x2 args2))
End
   (`type_lt` occurs as an argument of `LLEX`, which Lean's `inductive` does not accept.
   This is the definition `Inductive` makes in HOL4: the intersection of all relations
   closed under the rules.) -/
def type_lt (a0 a1 : type) : Prop :=
  ∀ type_lt' : type → type → Prop,
    ((∀ x1 x2, mlstring_lt x1 x2 → type_lt' (Tyvar x1) (Tyvar x2)) ∧
     (∀ x1 x2 args2, type_lt' (Tyvar x1) (Tyapp x2 args2)) ∧
     (∀ x1 args1 x2 args2,
        LEX mlstring_lt (LLEX type_lt') (x1, args1) (x2, args2) →
        type_lt' (Tyapp x1 args1) (Tyapp x2 args2))) →
    type_lt' a0 a1

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
   (as for `type_lt`: the intersection of all relations closed under the rules.) -/
def term_lt (a0 a1 : term) : Prop :=
  ∀ term_lt' : term → term → Prop,
    ((∀ x1 ty1 x2 ty2,
        LEX mlstring_lt type_lt (x1, ty1) (x2, ty2) → term_lt' (Var x1 ty1) (Var x2 ty2)) ∧
     (∀ x1 ty1 x2 ty2, term_lt' (Var x1 ty1) (Const x2 ty2)) ∧
     (∀ x1 ty1 t1 t2, term_lt' (Var x1 ty1) (Comb t1 t2)) ∧
     (∀ x1 ty1 t1 t2, term_lt' (Var x1 ty1) (Abs t1 t2)) ∧
     (∀ x1 ty1 x2 ty2,
        LEX mlstring_lt type_lt (x1, ty1) (x2, ty2) → term_lt' (Const x1 ty1) (Const x2 ty2)) ∧
     (∀ x1 ty1 t1 t2, term_lt' (Const x1 ty1) (Comb t1 t2)) ∧
     (∀ x1 ty1 t1 t2, term_lt' (Const x1 ty1) (Abs t1 t2)) ∧
     (∀ s1 s2 t1 t2,
        LEX term_lt' term_lt' (s1, s2) (t1, t2) → term_lt' (Comb s1 s2) (Comb t1 t2)) ∧
     (∀ s1 s2 t1 t2, term_lt' (Comb s1 s2) (Abs t1 t2)) ∧
     (∀ s1 s2 t1 t2,
        LEX term_lt' term_lt' (s1, s2) (t1, t2) → term_lt' (Abs s1 s2) (Abs t1 t2))) →
    term_lt' a0 a1

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
    if x1 = t1 then
      if x2 = t2 then EQUAL
      else LESS
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
    | Comb s1 t1, Comb s2 t2 =>
      (let c := orda env s1 s2
       if c ≠ EQUAL then c else orda env t1 t2)
    | Abs s1 t1, Abs s2 t2 =>
      (let c := type_cmp (typeof s1) (typeof s2)
       if c ≠ EQUAL then c else orda ((s1, s2) :: env) t1 t2)
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
    if h' = h ∧ t' = t then l
    else term_union [h'] t'

/-! ## Free variables -/

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
  ,(PRIMED_NAME_EXISTS
   |> HO_MATCH_MP LEAST_EXISTS
   |> Q.GENL[`t`,`x`,`ty`]
   |> SIMP_RULE std_ss [SKOLEM_THM]))
   i.e. the constant specified by
   VARIANT_PRIMES_def
     |- !t x ty.
          ~VFREE_IN (Var (implode (x ++ GENLIST (K #"'") (VARIANT_PRIMES t x ty))) ty) t /\
          !m. m < VARIANT_PRIMES t x ty ==>
              VFREE_IN (Var (implode (x ++ GENLIST (K #"'") m)) ty) t
   (`new_specification`: an arbitrary function that satisfies this; the specification
   determines it uniquely: the least number of primes that makes the name not free.) -/
def VARIANT_PRIMES : term → string → type → Nat :=
  select (fun f => ∀ t x ty,
    ¬ VFREE_IN (Var (implode (x ++ GENLIST (K chr!"'") (f t x ty))) ty) t ∧
    ∀ m, m < f t x ty → VFREE_IN (Var (implode (x ++ GENLIST (K chr!"'") m)) ty) t)

/- HOL4:
Definition VARIANT_def:
  VARIANT t x ty = implode (APPEND x (GENLIST (K #"'") (VARIANT_PRIMES t x ty)))
End -/
def VARIANT (t : term) (x : string) (ty : type) : mlstring :=
  implode (APPEND x (GENLIST (K chr!"'") (VARIANT_PRIMES t x ty)))

/-! ## Substitution -/

/- HOL4:
Definition TYPE_SUBST_def[simp]:
  (TYPE_SUBST i (Tyvar v) = REV_ASSOCD (Tyvar v) i (Tyvar v)) ∧
  (TYPE_SUBST i (Tyapp v tys) = Tyapp v (MAP (TYPE_SUBST i) tys)) ∧
  (TYPE_SUBST i (Fun ty1 ty2) = Fun (TYPE_SUBST i ty1) (TYPE_SUBST i ty2))
Termination
  type_rec_tac "SND"
End
   (the third clause is an instance of the second) -/
def TYPE_SUBST (i : List (type × type)) : type → type
  | Tyvar v => REV_ASSOCD (Tyvar v) i (Tyvar v)
  | Tyapp v tys => Tyapp v (MAP (TYPE_SUBST i) tys)

/- HOL4:
Overload is_instance = ``λty0 ty. ∃i. ty = TYPE_SUBST i ty0`` -/
abbrev is_instance (ty0 ty : type) : Prop := ∃ i, ty = TYPE_SUBST i ty0

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
   (`let (x,ty) = dest_var v` is written with `FST`/`SND`) -/
def VSUBST : List (term × term) → term → term
  | ilist, Var x ty => REV_ASSOCD (Var x ty) ilist (Var x ty)
  | _, Const x ty => Const x ty
  | ilist, Comb s t => Comb (VSUBST ilist s) (VSUBST ilist t)
  | ilist, Abs v t =>
    let ilist' := FILTER (fun (p : term × term) => ¬ (SND p = v)) ilist
    let t' := VSUBST ilist' t
    if EXISTS (fun (p : term × term) => VFREE_IN v (FST p) ∧ VFREE_IN (SND p) t) ilist'
    then let x := FST (dest_var v)
         let ty := SND (dest_var v)
         let z := Var (VARIANT t' (explode x) ty) ty
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

/-- Termination lemma for `INST_CORE` (membership in a filtered list). -/
theorem MEM_FILTER_imp {α : Type} (P : α → Prop) (x : α) :
    ∀ l : List α, MEM x (FILTER P l) → MEM x l := by
  intro l
  induction l with
  | nil => simp [FILTER]
  | cons h t ih =>
    simp only [FILTER]
    split
    · intro hm
      rcases List.mem_cons.mp hm with rfl | hm
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih hm)
    · intro hm
      exact List.mem_cons_of_mem _ (ih hm)

/-- Termination lemma for `INST_CORE` (`REV_ASSOCD` with variables on the left). -/
theorem sizeof_REV_ASSOCD (a d : term) (hd : sizeof d = 1) :
    ∀ ilist : List (term × term),
      (∀ s' s, MEM (s', s) ilist → ∃ x ty, s' = Var x ty) →
      sizeof (REV_ASSOCD a ilist d) = 1 := by
  intro ilist
  induction ilist with
  | nil => intro _; simpa [REV_ASSOCD] using hd
  | cons p t ih =>
    intro h
    simp only [REV_ASSOCD]
    split
    · obtain ⟨x, ty, hx⟩ := h p.1 p.2 List.mem_cons_self
      simp [FST, hx, sizeof]
    · exact ih (fun s' s hm => h s' s (List.mem_cons_of_mem _ hm))

/-- Termination lemma for `INST_CORE`.  (This is the content of the HOL4 theorem
`SIZEOF_VSUBST`, proved here under another name because the definition of `INST_CORE`
needs it.) -/
theorem sizeof_VSUBST_termination (t : term) :
    ∀ ilist : List (term × term),
      (∀ s' s, MEM (s', s) ilist → ∃ x ty, s' = Var x ty) →
      sizeof (VSUBST ilist t) = sizeof t := by
  induction t with
  | Var x ty =>
    intro ilist h
    simp only [VSUBST]
    exact sizeof_REV_ASSOCD _ _ rfl ilist h
  | Const x ty => intro ilist _; simp [VSUBST]
  | Comb s t ihs iht =>
    intro ilist h
    simp [VSUBST, sizeof, ihs ilist h, iht ilist h]
  | Abs v t _ iht =>
    intro ilist h
    have h' : ∀ s' s, MEM (s', s) (FILTER (fun (p : term × term) => ¬ (SND p = v)) ilist) →
        ∃ x ty, s' = Var x ty := fun s' s hm => h s' s (MEM_FILTER_imp _ _ _ hm)
    simp only [VSUBST]
    split
    · simp only [sizeof]
      rw [iht]
      intro s' s hm
      rcases List.mem_cons.mp hm with heq | hm
      · exact ⟨_, _, (Prod.mk.inj heq).1⟩
      · exact h' s' s hm
    · simp only [sizeof]
      rw [iht _ h']

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
Termination
  WF_REL_TAC`measure (sizeof o SND o SND)` >> simp[SIZEOF_VSUBST]
End
   (`let (x,ty) = dest_var v` is written with `FST`/`SND`) -/
def INST_CORE : List (term × term) → List (type × type) → term → result term
  | env, tyin, Var x ty =>
    let tm := Var x ty
    let tm' := Var x (TYPE_SUBST tyin ty)
    if REV_ASSOCD tm' env tm = tm then Result tm' else Clash tm'
  | _, tyin, Const x ty =>
    Result (Const x (TYPE_SUBST tyin ty))
  | env, tyin, Comb s t =>
    let sres := INST_CORE env tyin s
    if IS_CLASH sres then sres else
    let tres := INST_CORE env tyin t
    if IS_CLASH tres then tres else
    let s' := RESULT sres
    let t' := RESULT tres
    Result (Comb s' t')
  | env, tyin, Abs v t =>
    let x := FST (dest_var v)
    let ty := SND (dest_var v)
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
termination_by _ _ tm => sizeof tm
decreasing_by
  all_goals simp only [sizeof]
  · omega
  · omega
  · omega
  · omega
  · rw [sizeof_VSUBST_termination]
    · omega
    · intro s' s hm
      rcases List.mem_singleton.mp hm with heq
      exact ⟨_, _, (Prod.mk.inj heq).1⟩

/- HOL4:
Definition INST_def:
  INST tyin tm = RESULT(INST_CORE [] tyin tm)
End -/
def INST (tyin : List (type × type)) (tm : term) : term := RESULT (INST_CORE [] tyin tm)

/-! ## Type variables -/

/- HOL4:
Definition tyvars_def:
  tyvars (Tyvar v) = [v] ∧
  tyvars (Tyapp v tys) = FOLDR (λx y. LIST_UNION (tyvars x) y) [] tys
Termination
  type_rec_tac "I"
End -/
def tyvars : type → List mlstring
  | Tyvar v => [v]
  | Tyapp _ tys => FOLDR (fun x y => LIST_UNION (tyvars x) y) [] tys

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

/-! ## Syntax for equations -/

/- HOL4:
val _ = Parse.add_infix("===",460,Parse.RIGHT)

Definition equation_def:
  (s === t) = Comb (Comb (Equal(typeof s)) s) t
End
   (the constant is named `equation`; Lean notation `s === t`, infixr 60) -/
def equation (s t : term) : term := Comb (Comb (Equal (typeof s)) s) t

infixr:60 " === " => equation

/-! ## Signatures -/

/- HOL4:
Type tysig = ``:mlstring |-> num`` -/
abbrev tysig : Type := fmap mlstring Nat

/- HOL4:
Type tmsig = ``:mlstring |-> type`` -/
abbrev tmsig : Type := fmap mlstring type

/- HOL4:
Type sig = ``:tysig # tmsig`` -/
abbrev sig : Type := tysig × tmsig

/- HOL4:
Overload tysof = ``FST:sig->tysig`` -/
abbrev tysof (s : sig) : tysig := FST s

/- HOL4:
Overload tmsof = ``SND:sig->tmsig`` -/
abbrev tmsof (s : sig) : tmsig := SND s

/- HOL4:
Definition type_ok_def:
   (type_ok tysig (Tyvar _) ⇔ T) ∧
   (type_ok tysig (Tyapp name args) ⇔
      FLOOKUP tysig name = SOME (LENGTH args) ∧
      EVERY (type_ok tysig) args)
Termination
  type_rec_tac "SND"
End
   (Lean needs the recursive calls under a membership hypothesis, so `EVERY (type_ok tysig)
   args` is written `∀ a, MEM a args → type_ok tysig a` here; `type_ok_def` below states
   the HOL4 equations.) -/
def type_ok (tysig : Candle.tysig) : type → Prop
  | Tyvar _ => True
  | Tyapp name args =>
    FLOOKUP tysig name = some (LENGTH args) ∧
    ∀ a, (h : MEM a args) → type_ok tysig a
termination_by ty => sizeOf ty
decreasing_by
  have := List.sizeOf_lt_of_mem h
  simp only [type.Tyapp.sizeOf_spec]
  omega

/-- `EVERY P l` holds iff `P` holds of all members (HOL4 `EVERY_MEM`); needed to state
`type_ok_def`. -/
theorem EVERY_iff_forall_MEM {α : Type} (P : α → Prop) :
    ∀ l : List α, EVERY P l ↔ ∀ a, MEM a l → P a := by
  intro l
  induction l with
  | nil => simp [EVERY]
  | cons h t ih => simp [EVERY, ih]

/- HOL4: type_ok_def (the equations of `type_ok`, as HOL4 states them) -/
theorem type_ok_def :
    (∀ (tysig : Candle.tysig) (v : mlstring), type_ok tysig (Tyvar v) ↔ True) ∧
    (∀ (tysig : Candle.tysig) (name : mlstring) (args : List type),
      type_ok tysig (Tyapp name args) ↔
        FLOOKUP tysig name = some (LENGTH args) ∧ EVERY (type_ok tysig) args) := by
  refine ⟨fun tysig v => by simp [type_ok], fun tysig name args => ?_⟩
  rw [type_ok, EVERY_iff_forall_MEM]

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
def term_ok (sig : Candle.sig) : term → Prop
  | Var _ ty => type_ok (tysof sig) ty
  | Const name ty =>
    ∃ ty0, FLOOKUP (tmsof sig) name = some ty0 ∧
           type_ok (tysof sig) ty ∧
           is_instance ty0 ty
  | Comb tm1 tm2 =>
    term_ok sig tm1 ∧
    term_ok sig tm2 ∧
    welltyped (Comb tm1 tm2)
  | Abs v tm =>
    ∃ x ty,
      v = Var x ty ∧
      type_ok (tysof sig) ty ∧
      term_ok sig tm

/-! ## Hypothesis sets -/

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

/-! ## Theories -/

/- HOL4:
Type thy = ``:sig # term set`` -/
abbrev thy : Type := sig × Set term

/- HOL4:
Overload sigof = ``FST:thy->sig`` -/
abbrev sigof (t : thy) : sig := FST t

/- HOL4:
Overload axsof = ``SND:thy->term set`` -/
abbrev axsof (t : thy) : Set term := SND t

/- HOL4:
Overload tysof = ``tysof o sigof``
Overload tmsof = ``tmsof o sigof``
   (no Lean constants: HOL `tysof thy` / `tmsof thy` at a theory `thy` are written
   `tysof (sigof thy)` / `tmsof (sigof thy)`) -/

/- HOL4:
Definition is_std_sig_def:
  is_std_sig (sig:sig) ⇔
    FLOOKUP (tysof sig) «fun» = SOME 2 ∧
    FLOOKUP (tysof sig) «bool» = SOME 0 ∧
    FLOOKUP (tmsof sig) «=» = SOME (Fun (Tyvar «A») (Fun (Tyvar «A») Bool))
End -/
def is_std_sig (sig : Candle.sig) : Prop :=
  FLOOKUP (tysof sig) ml!"fun" = some 2 ∧
  FLOOKUP (tysof sig) ml!"bool" = some 0 ∧
  FLOOKUP (tmsof sig) ml!"=" = some (Fun (Tyvar ml!"A") (Fun (Tyvar ml!"A") Bool'))

/- HOL4:
Definition theory_ok_def:
  theory_ok (thy:thy) ⇔
    (∀ty. ty ∈ FRANGE (tmsof thy) ⇒ type_ok (tysof thy) ty) ∧
    (∀p. p ∈ (axsof thy) ⇒ term_ok (sigof thy) p ∧ p has_type Bool) ∧
    is_std_sig (sigof thy)
End -/
def theory_ok (thy : Candle.thy) : Prop :=
  (∀ ty, ty ∈ FRANGE (tmsof (sigof thy)) → type_ok (tysof (sigof thy)) ty) ∧
  (∀ p, p ∈ axsof thy → term_ok (sigof thy) p ∧ has_type p Bool') ∧
  is_std_sig (sigof thy)

/-! ## Sequents provable from a theory -/

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
   (HOL `(thy,h) |- c` is `proves (thy, h) c`; the rules `proves_ABS`, ... are the
   constructors `proves.ABS`, ...) -/
inductive proves : thy × List term → term → Prop
  | ABS (x : mlstring) (ty : type) (h : List term) (thy : Candle.thy) (l r : term) :
      ¬ EXISTS (VFREE_IN (Var x ty)) h → type_ok (tysof (sigof thy)) ty →
      proves (thy, h) (l === r) →
      proves (thy, h) (Abs (Var x ty) l === Abs (Var x ty) r)
  | ASSUME (thy : Candle.thy) (p : term) :
      theory_ok thy → has_type p Bool' → term_ok (sigof thy) p →
      proves (thy, [p]) p
  | BETA (thy : Candle.thy) (ty : type) (t : term) (x : mlstring) :
      theory_ok thy → type_ok (tysof (sigof thy)) ty → term_ok (sigof thy) t →
      proves (thy, []) (Comb (Abs (Var x ty) t) (Var x ty) === t)
  | DEDUCT_ANTISYM (thy : Candle.thy) (h1 : List term) (c1 : term) (h2 : List term) (c2 : term) :
      proves (thy, h1) c1 →
      proves (thy, h2) c2 →
      proves (thy, term_union (term_remove c2 h1) (term_remove c1 h2)) (c1 === c2)
  | EQ_MP (thy : Candle.thy) (h1 : List term) (p q : term) (h2 : List term) (p' : term) :
      proves (thy, h1) (p === q) →
      proves (thy, h2) p' → ACONV p p' →
      proves (thy, term_union h1 h2) q
  | INST (ilist : List (term × term)) (thy : Candle.thy) (h : List term) (c : term) :
      (∀ s s', MEM (s', s) ilist →
         ∃ x ty, s = Var x ty ∧ has_type s' ty ∧ term_ok (sigof thy) s') →
      proves (thy, h) c →
      proves (thy, term_image (VSUBST ilist) h) (VSUBST ilist c)
  | INST_TYPE (thy : Candle.thy) (tyin : List (type × type)) (h : List term) (c : term) :
      EVERY (type_ok (tysof (sigof thy))) (MAP FST tyin) →
      proves (thy, h) c →
      proves (thy, term_image (INST tyin) h) (INST tyin c)
  | MK_COMB (thy : Candle.thy) (h1 : List term) (l1 r1 : term) (h2 : List term) (l2 r2 : term) :
      proves (thy, h1) (l1 === r1) →
      proves (thy, h2) (l2 === r2) →
      welltyped (Comb l1 l2) →
      proves (thy, term_union h1 h2) (Comb l1 l2 === Comb r1 r2)
  | REFL (thy : Candle.thy) (t : term) :
      theory_ok thy → term_ok (sigof thy) t →
      proves (thy, []) (t === t)
  | axioms (thy : Candle.thy) (c : term) :
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

export update (ConstSpec TypeDefn NewType NewConst NewAxiom)

instance : Inhabited update := ⟨NewAxiom default⟩

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
  | TypeDefn name pred _ _ => [(name, LENGTH (tvars pred))]
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
  | ConstSpec eqs _ => MAP (fun (p : mlstring × term) => (FST p, typeof (SND p))) eqs
  | TypeDefn name pred abs rep =>
    let rep_type := domain (typeof pred)
    let abs_type :=
      Tyapp name (MAP Tyvar (MAP implode (STRING_SORT (MAP explode (tvars pred)))))
    [(abs, Fun rep_type abs_type),
     (rep, Fun abs_type rep_type)]
  | NewType _ _ => []
  | NewConst name ty => [(name, ty)]
  | NewAxiom _ => []

/- HOL4:
Overload type_list = ``λctxt. FLAT (MAP types_of_upd ctxt)`` -/
abbrev type_list (ctxt : List update) : List (mlstring × Nat) := FLAT (MAP types_of_upd ctxt)

/- HOL4:
Overload tysof = ``λctxt. alist_to_fmap (type_list ctxt)``
   (renamed: HOL `tysof ctxt` at a context `ctxt : update list` is `tysof_ctxt ctxt`) -/
abbrev tysof_ctxt (ctxt : List update) : tysig := alist_to_fmap (type_list ctxt)

/- HOL4:
Overload const_list = ``λctxt. FLAT (MAP consts_of_upd ctxt)`` -/
abbrev const_list (ctxt : List update) : List (mlstring × type) := FLAT (MAP consts_of_upd ctxt)

/- HOL4:
Overload tmsof = ``λctxt. alist_to_fmap (const_list ctxt)``
   (renamed: HOL `tmsof ctxt` at a context `ctxt : update list` is `tmsof_ctxt ctxt`) -/
abbrev tmsof_ctxt (ctxt : List update) : tmsig := alist_to_fmap (const_list ctxt)

/- HOL4:
Overload sigof = ``λctxt:update list. (tysof ctxt, tmsof ctxt)``
   (renamed: HOL `sigof ctxt` at a context `ctxt : update list` is `sigof_ctxt ctxt`) -/
abbrev sigof_ctxt (ctxt : List update) : sig := (tysof_ctxt ctxt, tmsof_ctxt ctxt)

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
    let ilist := MAP (fun (p : mlstring × term) =>
      let ty := typeof (SND p)
      (Const (FST p) ty, Var (FST p) ty)) eqs
    [VSUBST ilist prop]
  | TypeDefn name pred abs_name rep_name =>
    let abs_type :=
      Tyapp name (MAP Tyvar (MAP implode (STRING_SORT (MAP explode (tvars pred)))))
    let rep_type := domain (typeof pred)
    let abs := Const abs_name (Fun rep_type abs_type)
    let rep := Const rep_name (Fun abs_type rep_type)
    let a := Var ml!"a" abs_type
    let r := Var ml!"r" rep_type
    [Comb abs (Comb rep a) === a,
     Comb pred r === (Comb rep (Comb abs r) === r)]
  | _ => []

/- HOL4:
Overload axexts = ``λctxt. FLAT (MAP axexts_of_upd ctxt)`` -/
abbrev axexts (ctxt : List update) : List term := FLAT (MAP axexts_of_upd ctxt)

/- HOL4:
Overload conexts = ``λctxt. FLAT (MAP conexts_of_upd ctxt)`` -/
abbrev conexts (ctxt : List update) : List term := FLAT (MAP conexts_of_upd ctxt)

/- HOL4:
Overload axioms_of_upd = ``λupd. axexts_of_upd upd ++ conexts_of_upd upd`` -/
abbrev axioms_of_upd (upd : update) : List term := axexts_of_upd upd ++ conexts_of_upd upd

/- HOL4:
Overload axiom_list = ``λctxt. FLAT (MAP axioms_of_upd ctxt)`` -/
abbrev axiom_list (ctxt : List update) : List term := FLAT (MAP axioms_of_upd ctxt)

/- HOL4:
Overload axsof = ``λctxt. set (axiom_list ctxt)``
   (renamed: HOL `axsof ctxt` at a context `ctxt : update list` is `axsof_ctxt ctxt`) -/
abbrev axsof_ctxt (ctxt : List update) : Set term := set (axiom_list ctxt)

/- HOL4:
Overload thyof = ``λctxt:update list. (sigof ctxt, axsof ctxt)`` -/
abbrev thyof (ctxt : List update) : thy := (sigof_ctxt ctxt, axsof_ctxt ctxt)

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
   (HOL `upd updates ctxt` is `updates upd ctxt`) -/
inductive updates : update → List update → Prop
  | new_axiom (prop : term) (ctxt : List update) :
      has_type prop Bool' →
      term_ok (sigof_ctxt ctxt) prop →
      updates (NewAxiom prop) ctxt
  | new_constant (name : mlstring) (ctxt : List update) (ty : type) :
      name ∉ FDOM (tmsof_ctxt ctxt) →
      type_ok (tysof_ctxt ctxt) ty →
      updates (NewConst name ty) ctxt
  | new_specification (ctxt : List update) (eqs : List (mlstring × term)) (prop : term) :
      proves (thyof ctxt,
              MAP (fun (p : mlstring × term) => Var (FST p) (typeof (SND p)) === SND p) eqs)
        prop →
      EVERY
        (fun t => CLOSED t ∧ (∀ v, MEM v (tvars t) → MEM v (tyvars (typeof t))))
        (MAP SND eqs) →
      (∀ x ty, VFREE_IN (Var x ty) prop →
         MEM (x, ty) (MAP (fun (p : mlstring × term) => (FST p, typeof (SND p))) eqs)) →
      (∀ s, MEM s (MAP FST eqs) → s ∉ FDOM (tmsof_ctxt ctxt)) →
      ALL_DISTINCT (MAP FST eqs) →
      updates (ConstSpec eqs prop) ctxt
  | new_type (name : mlstring) (ctxt : List update) (arity : Nat) :
      name ∉ FDOM (tysof_ctxt ctxt) →
      updates (NewType name arity) ctxt
  | new_type_definition (ctxt : List update) (pred witness : term) (name abs rep : mlstring) :
      proves (thyof ctxt, []) (Comb pred witness) →
      CLOSED pred →
      name ∉ FDOM (tysof_ctxt ctxt) →
      abs ∉ FDOM (tmsof_ctxt ctxt) →
      rep ∉ FDOM (tmsof_ctxt ctxt) →
      abs ≠ rep →
      updates (TypeDefn name pred abs rep) ctxt

end

end Candle

/-! ## Stage 2: the target theorems of the HOL4 theory `holSyntax` (statements only, proofs `sorry`) -/

namespace Candle

noncomputable section
open Classical
set_option autoImplicit false

/- HOL4:
Theorem domain_def[compute,simp]:
   !t s. domain (Fun s t) = s
-/
theorem domain_def :
    ∀ (t s : type), domain (Fun s t) = s := by
  sorry

/- HOL4:
Theorem codomain_def[compute,simp]:
   !t s. codomain (Fun s t) = t
-/
theorem codomain_def :
    ∀ (t s : type), codomain (Fun s t) = t := by
  sorry

/- HOL4:
Theorem VFREE_IN_FINITE:
   ∀t. FINITE {x | VFREE_IN x t}
-/
theorem VFREE_IN_FINITE :
    ∀ (t : term), FINITE {x : term | VFREE_IN x t} := by
  sorry

/- HOL4:
Theorem VFREE_IN_FINITE_ALT:
   ∀t ty. FINITE {x | VFREE_IN (Var (implode x) ty) t}
-/
theorem VFREE_IN_FINITE_ALT :
    ∀ (t : term) (ty : type), FINITE {x : string | VFREE_IN (Var (implode x) ty) t} := by
  sorry

/- HOL4:
Theorem PRIMED_NAME_EXISTS:
   ∃n. ¬(VFREE_IN (Var (implode (APPEND x (GENLIST (K #"'") n))) ty) t)
-/
theorem PRIMED_NAME_EXISTS (x : string) (ty : type) (t : term) :
    ∃ (n : Nat), ¬ (VFREE_IN (Var (implode (APPEND x (GENLIST (K chr!"'") n))) ty) t) := by
  sorry

/- HOL4:
Theorem VARIANT_THM:
   ∀t x ty. ¬VFREE_IN (Var (VARIANT t x ty) ty) t
-/
theorem VARIANT_THM :
    ∀ (t : term) (x : string) (ty : type), ¬ VFREE_IN (Var (VARIANT t x ty) ty) t := by
  sorry

/- HOL4:
Theorem SIZEOF_VSUBST:
   ∀t ilist. (∀s' s. MEM (s',s) ilist ⇒ ∃x ty. s' = Var x ty)
              ⇒ sizeof (VSUBST ilist t) = sizeof t
-/
theorem SIZEOF_VSUBST :
    ∀ (t : term) (ilist : List (term × term)),
      (∀ (s' s : term), MEM (s', s) ilist → ∃ (x : mlstring) (ty : type), s' = Var x ty)
      → sizeof (VSUBST ilist t) = sizeof t := by
  sorry

end

end Candle
