/-
  Translation of CakeML `candle/standard/syntax/holSyntaxExtraScript.sml`
  (theory `holSyntaxExtra`): the definitions it introduces.
-/
import CandleLean.HolSyntax

open Classical

noncomputable section

/-! ## Target theorems (stage 2): HOL4 lines 18–223 -/

/- HOL4:
Theorem ALOOKUP_MAP_dest_var:
   ∀ls f x ty.
      EVERY (λs. ∃x ty. s = Var x ty) (MAP FST ls) ⇒
      ALOOKUP (MAP (dest_var ## f) ls) (x,ty) =
      OPTION_MAP f (ALOOKUP ls (Var x ty)) -/
theorem ALOOKUP_MAP_dest_var {β γ : Type} :
    ∀ (ls : List (term × β)) (f : β → γ) (x : mlstring) (ty : type),
      EVERY (fun s => ∃ x ty, s = Var x ty) (ls.map Prod.fst) →
      ALOOKUP (ls.map (PAIR_MAP dest_var f)) (x, ty) =
      Option.map f (ALOOKUP ls (Var x ty)) := by sorry

/- HOL4:
Theorem TYPE_SUBST_NIL[simp]:
   ∀ty. TYPE_SUBST [] ty = ty -/
theorem TYPE_SUBST_NIL : ∀ ty : type, TYPE_SUBST [] ty = ty := by sorry

/- HOL4:
Theorem TYPE_SUBST_Bool:
   ∀tyin. TYPE_SUBST tyin Bool = Bool -/
theorem TYPE_SUBST_Bool : ∀ tyin : List (type × type), TYPE_SUBST tyin Bool_ = Bool_ := by sorry

/- HOL4:
Theorem is_instance_refl[simp]:
   ∀ty. is_instance ty ty -/
theorem is_instance_refl : ∀ ty : type, is_instance ty ty := by sorry

/- HOL4:
Theorem swap_ff:
   ∀f g. (λ(x,y). (y,x)) o (f ## g) = (g ## f) o (λ(x,y). (y,x)) -/
theorem swap_ff {α β γ δ : Type} :
    ∀ (f : α → γ) (g : β → δ),
      (fun p : γ × δ => (p.2, p.1)) ∘ PAIR_MAP f g =
      PAIR_MAP g f ∘ (fun p : α × β => (p.2, p.1)) := by sorry

/- HOL4:
Theorem ff_def:
   ∀f g. (f ## g) = λ(x,y). (f x, g y) -/
theorem ff_def {α β γ δ : Type} :
    ∀ (f : α → γ) (g : β → δ), PAIR_MAP f g = fun p : α × β => (f p.1, g p.2) := by sorry

/- HOL4:
Theorem TYPE_SUBST_compose:
   ∀tyin1 ty tyin2.
    TYPE_SUBST tyin2 (TYPE_SUBST tyin1 ty) =
    TYPE_SUBST ((MAP (TYPE_SUBST tyin2 ## I) tyin1) ++ tyin2) ty -/
theorem TYPE_SUBST_compose :
    ∀ (tyin1 : List (type × type)) (ty : type) (tyin2 : List (type × type)),
      TYPE_SUBST tyin2 (TYPE_SUBST tyin1 ty) =
      TYPE_SUBST (tyin1.map (PAIR_MAP (TYPE_SUBST tyin2) I) ++ tyin2) ty := by sorry

/- HOL4:
Theorem TYPE_SUBST_tyvars:
   ∀ty tyin tyin'.
    (TYPE_SUBST tyin ty = TYPE_SUBST tyin' ty) ⇔
    ∀x. MEM x (tyvars ty) ⇒
        REV_ASSOCD (Tyvar x) tyin' (Tyvar x) =
        REV_ASSOCD (Tyvar x) tyin  (Tyvar x) -/
theorem TYPE_SUBST_tyvars :
    ∀ (ty : type) (tyin tyin' : List (type × type)),
      (TYPE_SUBST tyin ty = TYPE_SUBST tyin' ty) ↔
      ∀ x, MEM x (tyvars ty) →
        REV_ASSOCD (Tyvar x) tyin' (Tyvar x) =
        REV_ASSOCD (Tyvar x) tyin (Tyvar x) := by sorry

/- HOL4:
Theorem WELLTYPED_LEMMA:
   ∀tm ty. tm has_type ty ⇒ (typeof tm = ty) -/
theorem WELLTYPED_LEMMA : ∀ (tm : term) (ty : type), has_type tm ty → typeof tm = ty := by sorry

/- HOL4:
Theorem WELLTYPED:
   ∀tm. welltyped tm ⇔ tm has_type (typeof tm) -/
theorem WELLTYPED : ∀ tm : term, welltyped tm ↔ has_type tm (typeof tm) := by sorry

/- HOL4:
Theorem WELLTYPED_CLAUSES[simp]:
  (!n ty. welltyped(Var n ty)) /\
   (!n ty. welltyped(Const n ty)) /\
   (!s t. welltyped (Comb s t) <=>
            welltyped s /\ welltyped t /\
            ?rty. typeof s = Fun (typeof t) rty) /\
   (!v t. welltyped (Abs v t) = ∃n ty. v = Var n ty ∧ welltyped t) -/
theorem WELLTYPED_CLAUSES :
    (∀ n ty, welltyped (Var n ty)) ∧
    (∀ n ty, welltyped (Const n ty)) ∧
    (∀ s t, welltyped (Comb s t) ↔
      welltyped s ∧ welltyped t ∧ ∃ rty, typeof s = Fun (typeof t) rty) ∧
    (∀ v t, welltyped (Abs v t) = ∃ n ty, v = Var n ty ∧ welltyped t) := by sorry

/- HOL4:
Theorem RACONV:
  (RACONV env (Var x1 ty1,Var x2 ty2) <=>
        ALPHAVARS env (Var x1 ty1,Var x2 ty2)) /\
   (RACONV env (Var x1 ty1,Const x2 ty2) <=> F) /\
   (RACONV env (Var x1 ty1,Comb l2 r2) <=> F) /\
   (RACONV env (Var x1 ty1,Abs v2 t2) <=> F) /\
   (RACONV env (Const x1 ty1,Var x2 ty2) <=> F) /\
   (RACONV env (Const x1 ty1,Const x2 ty2) <=> (x1 = x2) /\ (ty1 = ty2)) /\
   (RACONV env (Const x1 ty1,Comb l2 r2) <=> F) /\
   (RACONV env (Const x1 ty1,Abs v2 t2) <=> F) /\
   (RACONV env (Comb l1 r1,Var x2 ty2) <=> F) /\
   (RACONV env (Comb l1 r1,Const x2 ty2) <=> F) /\
   (RACONV env (Comb l1 r1,Comb l2 r2) <=>
        RACONV env (l1,l2) /\ RACONV env (r1,r2)) /\
   (RACONV env (Comb l1 r1,Abs v2 t2) <=> F) /\
   (RACONV env (Abs v1 t1,Var x2 ty2) <=> F) /\
   (RACONV env (Abs v1 t1,Const x2 ty2) <=> F) /\
   (RACONV env (Abs v1 t1,Comb l2 r2) <=> F) /\
   (RACONV env (Abs v1 t1,Abs v2 t2) <=>
          typeof v1 = typeof v2 /\
          RACONV (CONS (v1,v2) env) (t1,t2))
   (free variables universally quantified) -/
theorem RACONV_thm :
    ∀ (env : List (term × term)) (x1 x2 : mlstring) (ty1 ty2 : type)
      (l1 r1 l2 r2 v1 t1 v2 t2 : term),
    (RACONV env (Var x1 ty1, Var x2 ty2) ↔ ALPHAVARS env (Var x1 ty1, Var x2 ty2)) ∧
    (RACONV env (Var x1 ty1, Const x2 ty2) ↔ False) ∧
    (RACONV env (Var x1 ty1, Comb l2 r2) ↔ False) ∧
    (RACONV env (Var x1 ty1, Abs v2 t2) ↔ False) ∧
    (RACONV env (Const x1 ty1, Var x2 ty2) ↔ False) ∧
    (RACONV env (Const x1 ty1, Const x2 ty2) ↔ x1 = x2 ∧ ty1 = ty2) ∧
    (RACONV env (Const x1 ty1, Comb l2 r2) ↔ False) ∧
    (RACONV env (Const x1 ty1, Abs v2 t2) ↔ False) ∧
    (RACONV env (Comb l1 r1, Var x2 ty2) ↔ False) ∧
    (RACONV env (Comb l1 r1, Const x2 ty2) ↔ False) ∧
    (RACONV env (Comb l1 r1, Comb l2 r2) ↔ RACONV env (l1, l2) ∧ RACONV env (r1, r2)) ∧
    (RACONV env (Comb l1 r1, Abs v2 t2) ↔ False) ∧
    (RACONV env (Abs v1 t1, Var x2 ty2) ↔ False) ∧
    (RACONV env (Abs v1 t1, Const x2 ty2) ↔ False) ∧
    (RACONV env (Abs v1 t1, Comb l2 r2) ↔ False) ∧
    (RACONV env (Abs v1 t1, Abs v2 t2) ↔
      typeof v1 = typeof v2 ∧ RACONV ((v1, v2) :: env) (t1, t2)) := by sorry

/- HOL4:
Theorem RACONV_REFL:
   ∀t env. EVERY (UNCURRY $=) env ⇒ RACONV env (t,t) -/
theorem RACONV_REFL :
    ∀ (t : term) (env : List (term × term)),
      EVERY (UNCURRY (fun a b => a = b)) env → RACONV env (t, t) := by sorry

/- HOL4:
Theorem ACONV_REFL[simp]:
   ∀t. ACONV t t -/
theorem ACONV_REFL : ∀ t : term, ACONV t t := by sorry

/- HOL4:
Theorem RACONV_TRANS:
   ∀env tp. RACONV env tp ⇒ ∀vs t. LENGTH vs = LENGTH env ∧ RACONV (ZIP(MAP SND env,vs)) (SND tp,t) ⇒ RACONV (ZIP(MAP FST env,vs)) (FST tp, t) -/
theorem RACONV_TRANS :
    ∀ (env : List (term × term)) (tp : term × term), RACONV env tp →
      ∀ (vs : List term) (t : term),
        vs.length = env.length ∧ RACONV (ZIP (env.map Prod.snd, vs)) (tp.2, t) →
        RACONV (ZIP (env.map Prod.fst, vs)) (tp.1, t) := by sorry

/- HOL4:
Theorem ACONV_TRANS:
   ∀t1 t2 t3. ACONV t1 t2 ∧ ACONV t2 t3 ⇒ ACONV t1 t3 -/
theorem ACONV_TRANS : ∀ t1 t2 t3 : term, ACONV t1 t2 ∧ ACONV t2 t3 → ACONV t1 t3 := by sorry

/- HOL4:
Theorem RACONV_SYM:
   ∀env tp. RACONV env tp ⇒ RACONV (MAP (λ(x,y). (y,x)) env) (SND tp,FST tp) -/
theorem RACONV_SYM :
    ∀ (env : List (term × term)) (tp : term × term),
      RACONV env tp → RACONV (env.map (fun p => (p.2, p.1))) (tp.2, tp.1) := by sorry

/- HOL4:
Theorem ACONV_SYM:
   ∀t1 t2. ACONV t1 t2 ⇒ ACONV t2 t1 -/
theorem ACONV_SYM : ∀ t1 t2 : term, ACONV t1 t2 → ACONV t2 t1 := by sorry

/- HOL4:
Theorem ALPHAVARS_TYPE:
   ∀env s t. ALPHAVARS env (s,t) ∧
              EVERY (λ(x,y). welltyped x ∧ welltyped y
                             ∧ (typeof x = typeof y)) env ∧
              welltyped s ∧ welltyped t
              ⇒ typeof s = typeof t -/
theorem ALPHAVARS_TYPE :
    ∀ (env : List (term × term)) (s t : term),
      ALPHAVARS env (s, t) ∧
      EVERY (fun p : term × term => welltyped p.1 ∧ welltyped p.2 ∧ typeof p.1 = typeof p.2) env ∧
      welltyped s ∧ welltyped t →
      typeof s = typeof t := by sorry

/- HOL4:
Theorem RACONV_TYPE:
   ∀env p. RACONV env p
            ⇒ EVERY (λ(x,y). welltyped x ∧ welltyped y
                             ∧ (typeof x = typeof y)) env ∧
              welltyped (FST p) ∧ welltyped (SND p)
              ⇒ typeof (FST p) = typeof (SND p) -/
theorem RACONV_TYPE :
    ∀ (env : List (term × term)) (p : term × term), RACONV env p →
      EVERY (fun q : term × term => welltyped q.1 ∧ welltyped q.2 ∧ typeof q.1 = typeof q.2) env ∧
      welltyped p.1 ∧ welltyped p.2 →
      typeof p.1 = typeof p.2 := by sorry

/- HOL4:
Theorem ACONV_TYPE:
   ∀s t. ACONV s t ⇒ welltyped s ∧ welltyped t ⇒ (typeof s = typeof t) -/
theorem ACONV_TYPE :
    ∀ s t : term, ACONV s t → welltyped s ∧ welltyped t → typeof s = typeof t := by sorry

/- HOL4:
Inductive subtype1:
  MEM a args ⇒ subtype1 a (Tyapp name args)
End -/
inductive subtype1 : type → type → Prop
  | intro (a : type) (args : List type) (name : mlstring) :
      MEM a args → subtype1 a (Tyapp name args)

/- HOL4:
val _ = Parse.add_infix("subtype",401,Parse.NONASSOC)
Overload subtype =``RTC subtype1``
   (HOL4 `ty1 subtype ty2` is `subtype ty1 ty2`) -/
abbrev subtype (ty1 ty2 : type) : Prop := RTC subtype1 ty1 ty2

/- HOL4:
Theorem subtype_Tyvar[simp] =
  ``ty subtype (Tyvar x)``
  |> SIMP_CONV(srw_ss()++boolSimps.DNF_ss)
      [Once relationTheory.RTC_CASES2,subtype1_cases]
   (the resulting theorem is  ⊢ ty subtype Tyvar x ⇔ ty = Tyvar x,
   with free variables ty, x) -/
theorem subtype_Tyvar : ∀ (ty : type) (x : mlstring), subtype ty (Tyvar x) ↔ ty = Tyvar x := by
  sorry

/- HOL4:
Inductive subterm1:
  subterm1 t1 (Comb t1 t2) ∧
  subterm1 t2 (Comb t1 t2) ∧
  subterm1 tm (Abs v tm) ∧
  subterm1 v (Abs v tm)
End -/
inductive subterm1 : term → term → Prop
  | comb_left (t1 t2 : term) : subterm1 t1 (Comb t1 t2)
  | comb_right (t1 t2 : term) : subterm1 t2 (Comb t1 t2)
  | abs_body (tm v : term) : subterm1 tm (Abs v tm)
  | abs_var (v tm : term) : subterm1 v (Abs v tm)

/- HOL4:
val _ = Parse.add_infix("subterm",401,Parse.NONASSOC)
Overload subterm = ``RTC subterm1``
   (HOL4 `t1 subterm t2` is `subterm t1 t2`) -/
abbrev subterm (t1 t2 : term) : Prop := RTC subterm1 t1 t2

/- HOL4:
Theorem subterm_Var[simp] =
  ``tm subterm (Var x ty)``
  |> SIMP_CONV(srw_ss()++boolSimps.DNF_ss)
      [Once relationTheory.RTC_CASES2,subterm1_cases]
   (the resulting theorem is  ⊢ tm subterm Var x ty ⇔ tm = Var x ty,
   with free variables tm, x, ty) -/
theorem subterm_Var :
    ∀ (tm : term) (x : mlstring) (ty : type), subterm tm (Var x ty) ↔ tm = Var x ty := by
  sorry

/- HOL4:
Theorem subterm_Const[simp] =
  ``tm subterm (Const x ty)``
  |> SIMP_CONV(srw_ss()++boolSimps.DNF_ss)
      [Once relationTheory.RTC_CASES2,subterm1_cases]
   (the resulting theorem is  ⊢ tm subterm Const x ty ⇔ tm = Const x ty,
   with free variables tm, x, ty) -/
theorem subterm_Const :
    ∀ (tm : term) (x : mlstring) (ty : type), subterm tm (Const x ty) ↔ tm = Const x ty := by
  sorry

/-! ## Target theorems (stage 2): HOL4 lines 277–1067 -/

/- HOL4:
Theorem type_lt_thm = Q.prove(
  `(type_lt (Tyvar x1) (Tyvar x2) ⇔ mlstring_lt x1 x2) ∧
    (type_lt (Tyvar _) (Tyapp _ _) ⇔ T) ∧
    (type_lt (Tyapp _ _) (Tyvar _) ⇔ F) ∧
    (type_lt (Tyapp x1 args1) (Tyapp x2 args2) ⇔
       (mlstring_lt LEX LLEX type_lt)
         (x1,args1) (x2,args2))`,
  rw[] >> rw[Once type_lt_cases])
  |> CONJUNCTS |> map GEN_ALL |> LIST_CONJ -/
theorem type_lt_thm :
    (∀ x1 x2 : mlstring, type_lt (Tyvar x1) (Tyvar x2) ↔ mlstring_lt x1 x2) ∧
    (∀ (a b : mlstring) (c : List type), type_lt (Tyvar a) (Tyapp b c) ↔ True) ∧
    (∀ (a : mlstring) (b : List type) (c : mlstring), type_lt (Tyapp a b) (Tyvar c) ↔ False) ∧
    (∀ (x1 : mlstring) (args1 : List type) (x2 : mlstring) (args2 : List type),
      type_lt (Tyapp x1 args1) (Tyapp x2 args2) ↔
      LEX mlstring_lt (LLEX type_lt) (x1, args1) (x2, args2)) := by sorry

/- HOL4:
Theorem term_lt_thm = Q.prove(`
  (term_lt (Var x1 ty1) (Var x2 ty2) ⇔
     (mlstring_lt LEX type_lt) (x1,ty1) (x2,ty2)) ∧
  (term_lt (Var _ _) (Const _ _) ⇔ T) ∧
  (term_lt (Var _ _) (Comb _ _) ⇔ T) ∧
  (term_lt (Var _ _) (Abs _ _) ⇔ T) ∧
  (term_lt (Const _ _) (Var _ _) ⇔ F) ∧
  (term_lt (Const x1 ty1) (Const x2 ty2) ⇔
     (mlstring_lt LEX type_lt) (x1,ty1) (x2,ty2)) ∧
  (term_lt (Const _ _) (Comb _ _) ⇔ T) ∧
  (term_lt (Const _ _) (Abs _ _) ⇔ T) ∧
  (term_lt (Comb _ _) (Var _ _) ⇔ F) ∧
  (term_lt (Comb _ _) (Const _ _) ⇔ F) ∧
  (term_lt (Comb s1 s2) (Comb t1 t2) ⇔
     (term_lt LEX term_lt) (s1,s2) (t1,t2)) ∧
  (term_lt (Comb _ _) (Abs _ _) ⇔ T) ∧
  (term_lt (Abs _ _) (Var _ _) ⇔ F) ∧
  (term_lt (Abs _ _) (Const _ _) ⇔ F) ∧
  (term_lt (Abs _ _) (Comb _ _) ⇔ F) ∧
  (term_lt (Abs s1 s2) (Abs t1 t2) ⇔
    (term_lt LEX term_lt) (s1,s2) (t1,t2))`,
  rw[] >> rw[Once term_lt_cases])
  |> CONJUNCTS |> map GEN_ALL |> LIST_CONJ -/
theorem term_lt_thm :
    (∀ (x1 : mlstring) (ty1 : type) (x2 : mlstring) (ty2 : type),
      term_lt (Var x1 ty1) (Var x2 ty2) ↔ LEX mlstring_lt type_lt (x1, ty1) (x2, ty2)) ∧
    (∀ (a : mlstring) (b : type) (c : mlstring) (d : type),
      term_lt (Var a b) (Const c d) ↔ True) ∧
    (∀ (a : mlstring) (b : type) (c d : term), term_lt (Var a b) (Comb c d) ↔ True) ∧
    (∀ (a : mlstring) (b : type) (c d : term), term_lt (Var a b) (Abs c d) ↔ True) ∧
    (∀ (a : mlstring) (b : type) (c : mlstring) (d : type),
      term_lt (Const a b) (Var c d) ↔ False) ∧
    (∀ (x1 : mlstring) (ty1 : type) (x2 : mlstring) (ty2 : type),
      term_lt (Const x1 ty1) (Const x2 ty2) ↔ LEX mlstring_lt type_lt (x1, ty1) (x2, ty2)) ∧
    (∀ (a : mlstring) (b : type) (c d : term), term_lt (Const a b) (Comb c d) ↔ True) ∧
    (∀ (a : mlstring) (b : type) (c d : term), term_lt (Const a b) (Abs c d) ↔ True) ∧
    (∀ (a b : term) (c : mlstring) (d : type), term_lt (Comb a b) (Var c d) ↔ False) ∧
    (∀ (a b : term) (c : mlstring) (d : type), term_lt (Comb a b) (Const c d) ↔ False) ∧
    (∀ s1 s2 t1 t2 : term,
      term_lt (Comb s1 s2) (Comb t1 t2) ↔ LEX term_lt term_lt (s1, s2) (t1, t2)) ∧
    (∀ a b c d : term, term_lt (Comb a b) (Abs c d) ↔ True) ∧
    (∀ (a b : term) (c : mlstring) (d : type), term_lt (Abs a b) (Var c d) ↔ False) ∧
    (∀ (a b : term) (c : mlstring) (d : type), term_lt (Abs a b) (Const c d) ↔ False) ∧
    (∀ a b c d : term, term_lt (Abs a b) (Comb c d) ↔ False) ∧
    (∀ s1 s2 t1 t2 : term,
      term_lt (Abs s1 s2) (Abs t1 t2) ↔ LEX term_lt term_lt (s1, s2) (t1, t2)) := by sorry

/- HOL4:
Theorem type_cmp_refl[simp]:
   type_cmp t t = EQUAL -/
theorem type_cmp_refl : ∀ t : type, type_cmp t t = EQUAL := by sorry

/- HOL4:
Theorem term_cmp_refl[simp]:
   term_cmp t t = EQUAL -/
theorem term_cmp_refl : ∀ t : term, term_cmp t t = EQUAL := by sorry

/- HOL4:
Theorem StrongLinearOrder_type_lt:
   StrongLinearOrder type_lt -/
theorem StrongLinearOrder_type_lt : StrongLinearOrder type_lt := by sorry

/- HOL4:
Theorem TotOrd_type_cmp:
   TotOrd type_cmp -/
theorem TotOrd_type_cmp : TotOrd type_cmp := by sorry

/- HOL4:
Theorem StrongLinearOrder_term_lt:
   StrongLinearOrder term_lt -/
theorem StrongLinearOrder_term_lt : StrongLinearOrder term_lt := by sorry

/- HOL4:
Theorem TotOrd_term_cmp:
   TotOrd term_cmp -/
theorem TotOrd_term_cmp : TotOrd term_cmp := by sorry

/- HOL4:
Theorem ALPHAVARS_eq_ordav:
   ∀env t1 t2. ALPHAVARS env (t1,t2) ⇔ ordav env t1 t2 = EQUAL -/
theorem ALPHAVARS_eq_ordav :
    ∀ (env : List (term × term)) (t1 t2 : term),
      ALPHAVARS env (t1, t2) ↔ ordav env t1 t2 = EQUAL := by sorry

/- HOL4:
Theorem RACONV_eq_orda:
   ∀env t1 t2. RACONV env (t1,t2) ⇔ orda env t1 t2 = EQUAL -/
theorem RACONV_eq_orda :
    ∀ (env : List (term × term)) (t1 t2 : term),
      RACONV env (t1, t2) ↔ orda env t1 t2 = EQUAL := by sorry

/- HOL4:
Theorem ACONV_eq_orda:
   ∀t1 t2. ACONV t1 t2 = (orda [] t1 t2 = EQUAL) -/
theorem ACONV_eq_orda : ∀ t1 t2 : term, ACONV t1 t2 = (orda [] t1 t2 = EQUAL) := by sorry

/- HOL4:
Theorem ordav_sym:
   ∀env v1 v2. flip_ord (ordav env v1 v2) = ordav (MAP (λ(x,y). (y,x)) env) v2 v1 -/
theorem ordav_sym :
    ∀ (env : List (term × term)) (v1 v2 : term),
      flip_ord (ordav env v1 v2) = ordav (env.map (fun p => (p.2, p.1))) v2 v1 := by sorry

/- HOL4:
Theorem orda_sym:
   ∀env t1 t2. flip_ord (orda env t1 t2) = orda (MAP (λ(x,y). (y,x)) env) t2 t1 -/
theorem orda_sym :
    ∀ (env : List (term × term)) (t1 t2 : term),
      flip_ord (orda env t1 t2) = orda (env.map (fun p => (p.2, p.1))) t2 t1 := by sorry

/- HOL4:
Theorem transitive_alpha_lt:
   transitive alpha_lt -/
theorem transitive_alpha_lt : transitive alpha_lt := by sorry

/- HOL4:
Theorem alpha_lt_not_refl[simp]:
   ∀x. ¬alpha_lt x x -/
theorem alpha_lt_not_refl : ∀ x : term, ¬ alpha_lt x x := by sorry

/- HOL4:
Theorem VFREE_IN_RACONV:
   ∀env p. RACONV env p
            ⇒ ∀x ty. VFREE_IN (Var x ty) (FST p) ∧
                     ¬(∃y. MEM (Var x ty,y) env) ⇔
                     VFREE_IN (Var x ty) (SND p) ∧
                     ¬(∃y. MEM (y,Var x ty) env) -/
theorem VFREE_IN_RACONV :
    ∀ (env : List (term × term)) (p : term × term), RACONV env p →
      ∀ (x : mlstring) (ty : type),
        (VFREE_IN (Var x ty) p.1 ∧ ¬ (∃ y, MEM (Var x ty, y) env)) ↔
        (VFREE_IN (Var x ty) p.2 ∧ ¬ (∃ y, MEM (y, Var x ty) env)) := by sorry

/- HOL4:
Theorem VFREE_IN_ACONV:
   ∀s t x ty. ACONV s t ⇒ (VFREE_IN (Var x ty) s ⇔ VFREE_IN (Var x ty) t) -/
theorem VFREE_IN_ACONV :
    ∀ (s t : term) (x : mlstring) (ty : type),
      ACONV s t → (VFREE_IN (Var x ty) s ↔ VFREE_IN (Var x ty) t) := by sorry

/- HOL4:
Theorem hypset_ok_nil[simp]:
   hypset_ok [] -/
theorem hypset_ok_nil : hypset_ok [] := by sorry

/- HOL4:
Theorem hypset_ok_sing[simp]:
   ∀p. hypset_ok [p] -/
theorem hypset_ok_sing : ∀ p : term, hypset_ok [p] := by sorry

/- HOL4:
Theorem hypset_ok_cons:
   hypset_ok (h::hs) ⇔
    EVERY (alpha_lt h) hs ∧ hypset_ok hs -/
theorem hypset_ok_cons :
    ∀ (h : term) (hs : List term), hypset_ok (h :: hs) ↔ EVERY (alpha_lt h) hs ∧ hypset_ok hs := by
  sorry

/- HOL4:
Theorem term_union_idem[simp]:
   ∀ls. term_union ls ls = ls -/
theorem term_union_idem : ∀ ls : List term, term_union ls ls = ls := by sorry

/- HOL4:
Theorem term_union_thm:
   (∀l2. term_union [] l2 = l2) ∧
    (∀l1. term_union l1 [] = l1) ∧
    (∀h1 t1 h2 t2.
          term_union (h1::t1) (h2::t2) =
          case orda [] h1 h2 of
          | EQUAL =>   h1::term_union t1 t2
          | LESS =>    h1::term_union t1 (h2::t2)
          | GREATER => h2::term_union (h1::t1) t2) -/
theorem term_union_thm :
    (∀ l2 : List term, term_union [] l2 = l2) ∧
    (∀ l1 : List term, term_union l1 [] = l1) ∧
    (∀ (h1 : term) (t1 : List term) (h2 : term) (t2 : List term),
      term_union (h1 :: t1) (h2 :: t2) =
      match orda [] h1 h2 with
      | EQUAL => h1 :: term_union t1 t2
      | LESS => h1 :: term_union t1 (h2 :: t2)
      | GREATER => h2 :: term_union (h1 :: t1) t2) := by sorry

/- HOL4:
Theorem MEM_term_union_imp:
   ∀l1 l2 x. MEM x (term_union l1 l2) ⇒ MEM x l1 ∨ MEM x l2 -/
theorem MEM_term_union_imp :
    ∀ (l1 l2 : List term) (x : term), MEM x (term_union l1 l2) → MEM x l1 ∨ MEM x l2 := by sorry

/- HOL4:
Theorem hypset_ok_term_union[simp]:
   ∀l1 l2. hypset_ok l1 ∧ hypset_ok l2 ⇒
            hypset_ok (term_union l1 l2) -/
theorem hypset_ok_term_union :
    ∀ l1 l2 : List term, hypset_ok l1 ∧ hypset_ok l2 → hypset_ok (term_union l1 l2) := by sorry

/- HOL4:
Theorem EVERY_term_union:
   EVERY P l1 ∧ EVERY P l2 ⇒ EVERY P (term_union l1 l2) -/
theorem EVERY_term_union :
    ∀ (P : term → Prop) (l1 l2 : List term),
      EVERY P l1 ∧ EVERY P l2 → EVERY P (term_union l1 l2) := by sorry

/- HOL4:
Theorem MEM_term_union:
   ∀h1 h2 t. hypset_ok h1 ∧ hypset_ok h2 ∧ (MEM t h1 ∨ MEM t h2) ⇒
      ∃y. MEM y (term_union h1 h2) ∧ ACONV t y -/
theorem MEM_term_union :
    ∀ (h1 h2 : List term) (t : term),
      hypset_ok h1 ∧ hypset_ok h2 ∧ (MEM t h1 ∨ MEM t h2) →
      ∃ y, MEM y (term_union h1 h2) ∧ ACONV t y := by sorry

/- HOL4:
Theorem term_remove_nil[simp]:
   ∀a. term_remove a [] = [] -/
theorem term_remove_nil : ∀ a : term, term_remove a [] = [] := by sorry

/- HOL4:
Theorem MEM_term_remove_imp:
   ∀ls x t. MEM t (term_remove x ls) ⇒
      MEM t ls ∧ (hypset_ok ls ⇒ ¬ACONV x t) -/
theorem MEM_term_remove_imp :
    ∀ (ls : List term) (x t : term), MEM t (term_remove x ls) →
      MEM t ls ∧ (hypset_ok ls → ¬ ACONV x t) := by sorry

/- HOL4:
Theorem hypset_ok_term_remove[simp]:
   ∀ls. hypset_ok ls ⇒ ∀t. hypset_ok (term_remove t ls) -/
theorem hypset_ok_term_remove :
    ∀ ls : List term, hypset_ok ls → ∀ t : term, hypset_ok (term_remove t ls) := by sorry

/- HOL4:
Theorem EVERY_term_remove:
   EVERY P ls ⇒ EVERY P (term_remove t ls) -/
theorem EVERY_term_remove :
    ∀ (P : term → Prop) (ls : List term) (t : term),
      EVERY P ls → EVERY P (term_remove t ls) := by sorry

/- HOL4:
Theorem MEM_term_remove:
   ∀h x t. MEM t h ∧ ¬ACONV x t ∧ hypset_ok h
    ⇒ MEM t (term_remove x h) -/
theorem MEM_term_remove :
    ∀ (h : List term) (x t : term),
      MEM t h ∧ ¬ ACONV x t ∧ hypset_ok h → MEM t (term_remove x h) := by sorry

/- HOL4:
Theorem term_image_nil[simp]:
   term_image f [] = [] -/
theorem term_image_nil : ∀ f : term → term, term_image f [] = [] := by sorry

/- HOL4:
Theorem MEM_term_image_imp:
   ∀ls f t. MEM t (term_image f ls) ⇒ ∃x. MEM x ls ∧ t = f x -/
theorem MEM_term_image_imp :
    ∀ (ls : List term) (f : term → term) (t : term),
      MEM t (term_image f ls) → ∃ x, MEM x ls ∧ t = f x := by sorry

/- HOL4:
Theorem hypset_ok_term_image:
   ∀ls f. hypset_ok ls ⇒ hypset_ok (term_image f ls) -/
theorem hypset_ok_term_image :
    ∀ (ls : List term) (f : term → term), hypset_ok ls → hypset_ok (term_image f ls) := by sorry

/- HOL4:
Theorem MEM_term_image:
   ∀ls f t. MEM t ls ∧ hypset_ok ls ⇒ ∃y. MEM y (term_image f ls) ∧ ACONV (f t) y -/
theorem MEM_term_image :
    ∀ (ls : List term) (f : term → term) (t : term),
      MEM t ls ∧ hypset_ok ls → ∃ y, MEM y (term_image f ls) ∧ ACONV (f t) y := by sorry

/- HOL4:
Theorem VSUBST_HAS_TYPE:
   ∀tm ty ilist.
      tm has_type ty ∧
      (∀s s'. MEM (s',s) ilist ⇒ ∃x ty. (s = Var x ty) ∧ s' has_type ty)
      ⇒ (VSUBST ilist tm) has_type ty -/
theorem VSUBST_HAS_TYPE :
    ∀ (tm : term) (ty : type) (ilist : List (term × term)),
      has_type tm ty ∧
      (∀ s s', MEM (s', s) ilist → ∃ x ty, s = Var x ty ∧ has_type s' ty) →
      has_type (VSUBST ilist tm) ty := by sorry

/- HOL4:
Theorem VSUBST_WELLTYPED:
   ∀tm ty ilist.
      welltyped tm ∧
      (∀s s'. MEM (s',s) ilist ⇒ ∃x ty. (s = Var x ty) ∧ s' has_type ty)
      ⇒ welltyped (VSUBST ilist tm) -/
theorem VSUBST_WELLTYPED :
    ∀ (tm : term) (ty : type) (ilist : List (term × term)),
      welltyped tm ∧
      (∀ s s', MEM (s', s) ilist → ∃ x ty, s = Var x ty ∧ has_type s' ty) →
      welltyped (VSUBST ilist tm) := by sorry


/- HOL4:
Datatype:
  dbterm =
    dbVar mlstring type
  | dbBound num
  | dbConst mlstring type
  | dbComb dbterm dbterm
  | dbAbs type dbterm
End
   (Lean type name `dbterm_`: the name `dbterm` is used by the function
   `dbterm` defined below, as in HOL4 where types and constants have separate
   namespaces) -/
inductive dbterm_ where
  | dbVar : mlstring → type → dbterm_
  | dbBound : Nat → dbterm_
  | dbConst : mlstring → type → dbterm_
  | dbComb : dbterm_ → dbterm_ → dbterm_
  | dbAbs : type → dbterm_ → dbterm_
  deriving Inhabited

export dbterm_ (dbVar dbBound dbConst dbComb dbAbs)

/- HOL4:
Definition bind_def[simp]:
  (bind v n (dbVar x ty) = if v = (x,ty) then dbBound n else dbVar x ty) ∧
  bind v n (dbBound m) = dbBound m ∧
  bind v n (dbConst x ty) = dbConst x ty ∧
  bind v n (dbComb t1 t2) = dbComb (bind v n t1) (bind v n t2) ∧
  bind v n (dbAbs ty tm) = dbAbs ty (bind v (n+1) tm)
End
   (Lean name `bind_`: `bind` is Lean's monadic bind) -/
def bind_ (v : mlstring × type) : Nat → dbterm_ → dbterm_
  | n, dbVar x ty => if v = (x, ty) then dbBound n else dbVar x ty
  | _, dbBound m => dbBound m
  | _, dbConst x ty => dbConst x ty
  | n, dbComb t1 t2 => dbComb (bind_ v n t1) (bind_ v n t2)
  | n, dbAbs ty tm => dbAbs ty (bind_ v (n + 1) tm)

/- HOL4:
Definition db_def[simp]:
  db (Var x ty) = dbVar x ty ∧
  db (Const x ty) = dbConst x ty ∧
  db (Comb t1 t2) = dbComb (db t1) (db t2) ∧
  db (Abs v tm) = dbAbs (typeof v) (bind (dest_var v) 0 (db tm))
End -/
def db : term → dbterm_
  | Var x ty => dbVar x ty
  | Const x ty => dbConst x ty
  | Comb t1 t2 => dbComb (db t1) (db t2)
  | Abs v tm => dbAbs (typeof v) (bind_ (dest_var v) 0 (db tm))

/- HOL4:
Definition dbVSUBST_def[simp]:
  dbVSUBST ilist (dbVar x ty) = REV_ASSOCD (dbVar x ty) ilist (dbVar x ty) ∧
  dbVSUBST ilist (dbBound m) = dbBound m ∧
  dbVSUBST ilist (dbConst x ty) = dbConst x ty ∧
  dbVSUBST ilist (dbComb t1 t2) = dbComb (dbVSUBST ilist t1) (dbVSUBST ilist t2) ∧
  dbVSUBST ilist (dbAbs ty t) = dbAbs ty (dbVSUBST ilist t)
End -/
def dbVSUBST (ilist : List (dbterm_ × dbterm_)) : dbterm_ → dbterm_
  | dbVar x ty => REV_ASSOCD (dbVar x ty) ilist (dbVar x ty)
  | dbBound m => dbBound m
  | dbConst x ty => dbConst x ty
  | dbComb t1 t2 => dbComb (dbVSUBST ilist t1) (dbVSUBST ilist t2)
  | dbAbs ty t => dbAbs ty (dbVSUBST ilist t)

/- HOL4:
Definition dbVFREE_IN_def[simp]:
  (dbVFREE_IN v (dbVar x ty) ⇔ dbVar x ty = v) ∧
  (dbVFREE_IN v (dbBound n) ⇔ F) ∧
  (dbVFREE_IN v (dbConst x ty) ⇔ dbConst x ty = v) ∧
  (dbVFREE_IN v (dbComb t1 t2) ⇔ (dbVFREE_IN v t1 ∨ dbVFREE_IN v t2)) ∧
  (dbVFREE_IN v (dbAbs ty t) ⇔ dbVFREE_IN v t)
End -/
def dbVFREE_IN (v : dbterm_) : dbterm_ → Prop
  | dbVar x ty => dbVar x ty = v
  | dbBound _ => False
  | dbConst x ty => dbConst x ty = v
  | dbComb t1 t2 => dbVFREE_IN v t1 ∨ dbVFREE_IN v t2
  | dbAbs _ t => dbVFREE_IN v t

/- HOL4:
Definition dbINST_def[simp]:
  dbINST tyin (dbVar x ty) = dbVar x (TYPE_SUBST tyin ty) ∧
  dbINST tyin (dbBound n) = dbBound n ∧
  dbINST tyin (dbConst x ty) = dbConst x (TYPE_SUBST tyin ty) ∧
  dbINST tyin (dbComb t1 t2) = dbComb (dbINST tyin t1) (dbINST tyin t2) ∧
  dbINST tyin (dbAbs ty t) = dbAbs (TYPE_SUBST tyin ty) (dbINST tyin t)
End -/
def dbINST (tyin : List (type × type)) : dbterm_ → dbterm_
  | dbVar x ty => dbVar x (TYPE_SUBST tyin ty)
  | dbBound n => dbBound n
  | dbConst x ty => dbConst x (TYPE_SUBST tyin ty)
  | dbComb t1 t2 => dbComb (dbINST tyin t1) (dbINST tyin t2)
  | dbAbs ty t => dbAbs (TYPE_SUBST tyin ty) (dbINST tyin t)

/- HOL4:
Definition dbterm_def[simp]:
  (dbterm env (Var s ty) =
     case find_index (s,ty) env 0 of SOME n => dbBound n | NONE => dbVar s ty) ∧
  (dbterm env (Const s ty) = dbConst s ty) ∧
  (dbterm env (Comb t1 t2) = dbComb (dbterm env t1) (dbterm env t2)) ∧
  (dbterm env (Abs v t) = dbAbs (typeof v) (dbterm ((dest_var v)::env) t))
End -/
def dbterm : List (mlstring × type) → term → dbterm_
  | env, Var s ty =>
    match find_index (s, ty) env 0 with
    | some n => dbBound n
    | none => dbVar s ty
  | _, Const s ty => dbConst s ty
  | env, Comb t1 t2 => dbComb (dbterm env t1) (dbterm env t2)
  | env, Abs v t => dbAbs (typeof v) (dbterm (dest_var v :: env) t)

/- HOL4:
Definition bind_list_aux_def[simp]:
  bind_list_aux n [] tm = tm ∧
  bind_list_aux n (v::vs) tm = bind_list_aux (n+1) vs (bind v n tm)
End -/
def bind_list_aux : Nat → List (mlstring × type) → dbterm_ → dbterm_
  | _, [], tm => tm
  | n, v :: vs, tm => bind_list_aux (n + 1) vs (bind_ v n tm)

/- HOL4:
Definition bv_names_def[simp]:
  bv_names (Var _ _) = [] ∧
  bv_names (Const _ _) = [] ∧
  bv_names (Comb s t) = bv_names s ++ bv_names t ∧
  bv_names (Abs v t) = (FST(dest_var v))::bv_names t
End -/
def bv_names : term → List mlstring
  | Var _ _ => []
  | Const _ _ => []
  | Comb s t => bv_names s ++ bv_names t
  | Abs v t => (dest_var v).1 :: bv_names t

/- HOL4:
Definition simple_subst_def[simp]:
  (simple_subst ilist (Var x ty) = REV_ASSOCD (Var x ty) ilist (Var x ty)) ∧
  (simple_subst ilist (Const x ty) = Const x ty) ∧
  (simple_subst ilist (Comb t1 t2) = Comb (simple_subst ilist t1) (simple_subst ilist t2)) ∧
  (simple_subst ilist (Abs v tm) =
    Abs v (simple_subst (FILTER (λ(s',s). (s ≠ v)) ilist) tm))
End -/
def simple_subst (ilist : List (term × term)) : term → term
  | Var x ty => REV_ASSOCD (Var x ty) ilist (Var x ty)
  | Const x ty => Const x ty
  | Comb t1 t2 => Comb (simple_subst ilist t1) (simple_subst ilist t2)
  | Abs v tm => Abs v (simple_subst (FILTER (fun p => p.2 ≠ v) ilist) tm)

/- HOL4:
Definition simple_inst_def[simp]:
  simple_inst tyin (Var x ty) = Var x (TYPE_SUBST tyin ty) ∧
  simple_inst tyin (Const x ty) = Const x (TYPE_SUBST tyin ty) ∧
  simple_inst tyin (Comb s t) = Comb (simple_inst tyin s) (simple_inst tyin t) ∧
  simple_inst tyin (Abs v t) = Abs (simple_inst tyin v) (simple_inst tyin t)
End -/
def simple_inst (tyin : List (type × type)) : term → term
  | Var x ty => Var x (TYPE_SUBST tyin ty)
  | Const x ty => Const x (TYPE_SUBST tyin ty)
  | Comb s t => Comb (simple_inst tyin s) (simple_inst tyin t)
  | Abs v t => Abs (simple_inst tyin v) (simple_inst tyin t)

/- HOL4:
Definition rename_bvars_def:
  rename_bvars names env (Var s ty) = (names, Var (REV_ASSOCD (s,ty) env s) ty) ∧
  rename_bvars names env (Const s ty) = (names, Const s ty) ∧
  (rename_bvars names env (Comb t1 t2) =
     let (names,t1) = rename_bvars names env t1 in
     let (names,t2) = rename_bvars names env t2 in
     (names, Comb t1 t2)) ∧
  (rename_bvars [] env (Abs v tm) =
     let (names, tm) = rename_bvars [] env tm in
     (names, Abs v tm)) ∧
  (rename_bvars (s'::names) env (Abs v tm) =
     let (names,tm) = rename_bvars names ((s',dest_var v)::env) tm in
     (names, Abs (Var s' (typeof v)) tm))
End -/
def rename_bvars : List mlstring → List (mlstring × (mlstring × type)) → term → List mlstring × term
  | names, env, Var s ty => (names, Var (REV_ASSOCD (s, ty) env s) ty)
  | names, _, Const s ty => (names, Const s ty)
  | names, env, Comb t1 t2 =>
    let p1 := rename_bvars names env t1
    let p2 := rename_bvars p1.1 env t2
    (p2.1, Comb p1.2 p2.2)
  | [], env, Abs v tm =>
    let p := rename_bvars [] env tm
    (p.1, Abs v p.2)
  | s' :: names, env, Abs v tm =>
    let p := rename_bvars names ((s', dest_var v) :: env) tm
    (p.1, Abs (Var s' (typeof v)) p.2)

/- HOL4:
val fresh_def = new_specification("fresh_def",["fresh"],
  IN_INFINITE_NOT_FINITE
  |> Q.ISPECL[`UNIV:string set`,`s:string set`]
  |> REWRITE_RULE[INST_TYPE[alpha|->``:char``]INFINITE_LIST_UNIV,IN_UNIV]
  |> SIMP_RULE(srw_ss())[GSYM RIGHT_EXISTS_IMP_THM]
  |> Q.GEN`s`
  |> SIMP_RULE(srw_ss())[SKOLEM_THM])
   i.e. the specification is   ∀s. FINITE s ⇒ fresh s ∉ s
   (with s : string set, HOL4 string = char list).  Encoded as a choice over
   all functions satisfying the specification. -/
def fresh : Set string → string :=
  Classical.epsilon (fun fresh : Set string → string => ∀ s, FINITE s → fresh s ∉ s)

/- HOL4: `Overload ConstDef = ``λx t. ConstSpec [(x,t)] (Var x (typeof t) === t)``` -/
abbrev ConstDef (x : mlstring) (t : term) : update := ConstSpec [(x, t)] (Var x (typeof t) === t)

/- HOL4:
Definition types_in_def[simp]:
  types_in (Var x ty) = {ty} ∧
  types_in (Const c ty) = {ty} ∧
  types_in (Comb t1 t2) = types_in t1 ∪ types_in t2 ∧
  types_in (Abs v t) = types_in v ∪ types_in t
End -/
def types_in : term → Set type
  | Var _ ty => {ty}
  | Const _ ty => {ty}
  | Comb t1 t2 => types_in t1 ∪ types_in t2
  | Abs v t => types_in v ∪ types_in t

/- HOL4:
Definition arities_match_def:
  (arities_match [] [] ⇔ T) ∧
  (arities_match [] _ ⇔ F) ∧
  (arities_match _ [] ⇔ F) ∧
  (arities_match (Tyapp c1 a1::xs) (Tyapp c2 a2::ys) ⇔
   ((c1 = c2) ⇒ arities_match a1 a2) ∧ arities_match xs ys) ∧
  (arities_match (_::xs) (_::ys) ⇔ arities_match xs ys)
End -/
def arities_match : List type → List type → Prop
  | [], [] => True
  | [], _ :: _ => False
  | _ :: _, [] => False
  | Tyapp c1 a1 :: xs, Tyapp c2 a2 :: ys => (c1 = c2 → arities_match a1 a2) ∧ arities_match xs ys
  | _ :: xs, _ :: ys => arities_match xs ys
