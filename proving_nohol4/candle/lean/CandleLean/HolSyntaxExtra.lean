import CandleLean.HolSyntax

/-!
# holSyntaxExtra (CakeML `candle/standard/syntax/holSyntaxExtraScript.sml`),
# reduced to the definitions the targets need

The HOL4 type `dbterm` and the HOL4 constant `dbterm` have the same name; in Lean the type is
`dbterm_t` (constructors `dbVar`, `dbBound`, `dbConst`, `dbComb`, `dbAbs`, exported) and the
function is `dbterm`.
-/

namespace Candle

open HOL Classical

noncomputable section

/- HOL4:
Inductive subtype1:
  MEM a args ⇒ subtype1 a (Tyapp name args)
End -/
inductive subtype1 : type → type → Prop where
  | rule {a : type} {args : List type} {name : mlstring} :
      a ∈ args → subtype1 a (Tyapp name args)

/- HOL4:
val _ = Parse.add_infix("subtype",401,Parse.NONASSOC)
Overload subtype =``RTC subtype1``
   (`a subtype b` is written `subtype a b`) -/
@[reducible] def subtype : type → type → Prop := RTC subtype1

/- HOL4:
Inductive subterm1:
  subterm1 t1 (Comb t1 t2) ∧
  subterm1 t2 (Comb t1 t2) ∧
  subterm1 tm (Abs v tm) ∧
  subterm1 v (Abs v tm)
End -/
inductive subterm1 : term → term → Prop where
  | comb_left {t1 t2 : term} : subterm1 t1 (Comb t1 t2)
  | comb_right {t1 t2 : term} : subterm1 t2 (Comb t1 t2)
  | abs_body {tm v : term} : subterm1 tm (Abs v tm)
  | abs_var {v tm : term} : subterm1 v (Abs v tm)

/- HOL4:
val _ = Parse.add_infix("subterm",401,Parse.NONASSOC)
Overload subterm = ``RTC subterm1``
   (`a subterm b` is written `subterm a b`) -/
@[reducible] def subterm : term → term → Prop := RTC subterm1

/- HOL4:
Datatype:
  dbterm =
    dbVar mlstring type
  | dbBound num
  | dbConst mlstring type
  | dbComb dbterm dbterm
  | dbAbs type dbterm
End
   (Lean type name `dbterm_t`, since `dbterm` is also a HOL4 constant) -/
inductive dbterm_t where
  | dbVar : mlstring → type → dbterm_t
  | dbBound : Nat → dbterm_t
  | dbConst : mlstring → type → dbterm_t
  | dbComb : dbterm_t → dbterm_t → dbterm_t
  | dbAbs : type → dbterm_t → dbterm_t
  deriving Inhabited

export dbterm_t (dbVar dbBound dbConst dbComb dbAbs)

/- HOL4:
Definition bind_def[simp]:
  (bind v n (dbVar x ty) = if v = (x,ty) then dbBound n else dbVar x ty) ∧
  bind v n (dbBound m) = dbBound m ∧
  bind v n (dbConst x ty) = dbConst x ty ∧
  bind v n (dbComb t1 t2) = dbComb (bind v n t1) (bind v n t2) ∧
  bind v n (dbAbs ty tm) = dbAbs ty (bind v (n+1) tm)
End -/
def bind (v : mlstring × type) (n : Nat) : dbterm_t → dbterm_t
  | dbVar x ty => if v = (x, ty) then dbBound n else dbVar x ty
  | dbBound m => dbBound m
  | dbConst x ty => dbConst x ty
  | dbComb t1 t2 => dbComb (bind v n t1) (bind v n t2)
  | dbAbs ty tm => dbAbs ty (bind v (n + 1) tm)

/- HOL4:
Definition db_def[simp]:
  db (Var x ty) = dbVar x ty ∧
  db (Const x ty) = dbConst x ty ∧
  db (Comb t1 t2) = dbComb (db t1) (db t2) ∧
  db (Abs v tm) = dbAbs (typeof v) (bind (dest_var v) 0 (db tm))
End -/
def db : term → dbterm_t
  | Var x ty => dbVar x ty
  | Const x ty => dbConst x ty
  | Comb t1 t2 => dbComb (db t1) (db t2)
  | Abs v tm => dbAbs (typeof v) (bind (dest_var v) 0 (db tm))

/- HOL4:
Definition dbVSUBST_def[simp]:
  dbVSUBST ilist (dbVar x ty) = REV_ASSOCD (dbVar x ty) ilist (dbVar x ty) ∧
  dbVSUBST ilist (dbBound m) = dbBound m ∧
  dbVSUBST ilist (dbConst x ty) = dbConst x ty ∧
  dbVSUBST ilist (dbComb t1 t2) = dbComb (dbVSUBST ilist t1) (dbVSUBST ilist t2) ∧
  dbVSUBST ilist (dbAbs ty t) = dbAbs ty (dbVSUBST ilist t)
End -/
def dbVSUBST (ilist : List (dbterm_t × dbterm_t)) : dbterm_t → dbterm_t
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
def dbVFREE_IN (v : dbterm_t) : dbterm_t → Prop
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
def dbINST (tyin : List (type × type)) : dbterm_t → dbterm_t
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
def dbterm (env : List (mlstring × type)) : term → dbterm_t
  | Var s ty =>
    match find_index (s, ty) env 0 with
    | some n => dbBound n
    | none => dbVar s ty
  | Const s ty => dbConst s ty
  | Comb t1 t2 => dbComb (dbterm env t1) (dbterm env t2)
  | Abs v t => dbAbs (typeof v) (dbterm (dest_var v :: env) t)

/- HOL4:
Definition bind_list_aux_def[simp]:
  bind_list_aux n [] tm = tm ∧
  bind_list_aux n (v::vs) tm = bind_list_aux (n+1) vs (bind v n tm)
End -/
def bind_list_aux : Nat → List (mlstring × type) → dbterm_t → dbterm_t
  | _, [], tm => tm
  | n, v :: vs, tm => bind_list_aux (n + 1) vs (bind v n tm)

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
End
   (the `let (names,t) = ...` bindings are written with projections) -/
def rename_bvars : List mlstring → List (mlstring × (mlstring × type)) → term →
    List mlstring × term
  | names, env, Var s ty => (names, Var (REV_ASSOCD (s, ty) env s) ty)
  | names, _, Const s ty => (names, Const s ty)
  | names, env, Comb t1 t2 =>
    let r1 := rename_bvars names env t1
    let r2 := rename_bvars r1.1 env t2
    (r2.1, Comb r1.2 r2.2)
  | [], env, Abs v tm =>
    let r := rename_bvars [] env tm
    (r.1, Abs v r.2)
  | s' :: names, env, Abs v tm =>
    let r := rename_bvars names ((s', dest_var v) :: env) tm
    (r.1, Abs (Var s' (typeof v)) r.2)

/- HOL4:
val fresh_def = new_specification("fresh_def",["fresh"],
  [HOL4 proof text removed]
   The resulting specification is
     fresh_def: ∀s. FINITE s ⇒ fresh s ∉ s        (s : string set)
   Encoded as Hilbert choice of a function satisfying the specification. -/
def fresh_spec (f : Set string → string) : Prop := ∀ s, FINITE s → ¬ f s ∈ s

private theorem fresh_exists : ∃ f, fresh_spec f := by
  have : ∀ s : Set string, ∃ x, FINITE s → ¬ x ∈ s := by
    intro s
    by_cases hs : FINITE s
    · obtain ⟨l, hl⟩ := Aux.FINITE_list_bound s hs
      let n := (l.map List.length).foldr max 0
      have hlen : ∀ y ∈ l, y.length ≤ n := by
        intro y hy
        have : ∀ (ls : List string), y ∈ ls → y.length ≤ (ls.map List.length).foldr max 0 := by
          intro ls
          induction ls with
          | nil => intro h; simp at h
          | cons a t ih =>
            intro h
            simp only [List.map_cons, List.foldr_cons]
            rcases List.mem_cons.mp h with h | h
            · subst h; exact Nat.le_max_left _ _
            · exact Nat.le_trans (ih h) (Nat.le_max_right _ _)
        exact this l hy
      refine ⟨List.replicate (n + 1) (ch 'a'), fun _ hx => ?_⟩
      have := hlen _ (hl _ hx)
      simp at this
      omega
    · exact ⟨[], fun h => absurd h hs⟩
  exact ⟨fun s => Classical.choose (this s), fun s => Classical.choose_spec (this s)⟩

private opaque fresh_pkg : {f : Set string → string // fresh_spec f} :=
  ⟨Classical.choose fresh_exists, Classical.choose_spec fresh_exists⟩

def fresh : Set string → string := fresh_pkg.1

/-- The HOL4 defining theorem `fresh_def` (from `new_specification`). -/
theorem fresh_def : fresh_spec fresh := fresh_pkg.2

/- HOL4:
Definition types_in_def[simp]:
  types_in (Var x ty) = {ty} ∧
  types_in (Const c ty) = {ty} ∧
  types_in (Comb t1 t2) = types_in t1 ∪ types_in t2 ∧
  types_in (Abs v t) = types_in v ∪ types_in t
End -/
def types_in : term → Set type
  | Var _ ty => INSERT ty EMPTY
  | Const _ ty => INSERT ty EMPTY
  | Comb t1 t2 => UNION (types_in t1) (types_in t2)
  | Abs v t => UNION (types_in v) (types_in t)

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
  | [], _ => False
  | _, [] => False
  | Tyapp c1 a1 :: xs, Tyapp c2 a2 :: ys => (c1 = c2 → arities_match a1 a2) ∧ arities_match xs ys
  | _ :: xs, _ :: ys => arities_match xs ys
termination_by l1 => sizeOf l1
decreasing_by
  all_goals simp_wf
  all_goals omega


/-! ## Theorems (stage 2) -/

universe u v w x

theorem Aux.type_ind {P : type → Prop} (hv : ∀ v, P (Tyvar v))
    (ha : ∀ n args, (∀ a, a ∈ args → P a) → P (Tyapp n args)) : ∀ ty, P ty
  | Tyvar v => hv v
  | Tyapp n args => ha n args (fun a _ => Aux.type_ind hv ha a)
termination_by ty => sizeOf ty
decreasing_by
  have := List.sizeOf_lt_of_mem (by assumption : a ∈ args)
  simp only [type.Tyapp.sizeOf_spec]
  omega

theorem Aux.mem_tyvars_Tyapp (x n : mlstring) (tys : List type) :
    x ∈ tyvars (Tyapp n tys) ↔ ∃ a, a ∈ tys ∧ x ∈ tyvars a := by
  rw [tyvars, MEM_FOLDR_LIST_UNION]
  simp

theorem Aux.has_type_Comb {s t : term} {ty : type} (h : has_type (Comb s t) ty) :
    ∃ dty, has_type s (Fun dty ty) ∧ has_type t dty := by
  cases h with
  | Comb h1 h2 => exact ⟨_, h1, h2⟩

theorem Aux.has_type_Abs {v t : term} {ty : type} (h : has_type (Abs v t) ty) :
    ∃ n dty rty, v = Var n dty ∧ ty = Fun dty rty ∧ has_type t rty := by
  cases h with
  | Abs h => exact ⟨_, _, _, rfl, rfl, h⟩

theorem Aux.RTC_tail {α : Type u} {R : α → α → Prop} {a c : α} (h : RTC R a c) :
    a = c ∨ ∃ b, RTC R a b ∧ R b c := by
  induction h with
  | refl x => exact Or.inl rfl
  | step x y z hxy _ ih =>
    right
    rcases ih with rfl | ⟨b, h1, h2⟩
    · exact ⟨x, RTC.refl x, hxy⟩
    · exact ⟨b, RTC.step x y b hxy h1, h2⟩

/- HOL4:
Theorem ALOOKUP_MAP_dest_var:
   ∀ls f x ty.
      EVERY (λs. ∃x ty. s = Var x ty) (MAP FST ls) ⇒
      ALOOKUP (MAP (dest_var ## f) ls) (x,ty) =
      OPTION_MAP f (ALOOKUP ls (Var x ty))
-/
theorem ALOOKUP_MAP_dest_var {α : Type u} {β : Type v} :
    ∀ (ls : List (term × α)) (f : α → β) (x : mlstring) (ty : type),
      EVERY (fun s => ∃ x ty, s = Var x ty) (ls.map Prod.fst) →
      ALOOKUP (ls.map (PAIR_MAP dest_var f)) (x, ty) =
      Option.map f (ALOOKUP ls (Var x ty)) := by
  intro ls f x ty
  induction ls with
  | nil => intro _; rfl
  | cons p t ih =>
    obtain ⟨s, a⟩ := p
    rintro ⟨⟨x', ty', hs⟩, h⟩
    have hs : s = Var x' ty' := hs
    subst hs
    have ih' := ih h
    simp only [List.map_cons, PAIR_MAP, dest_var_def, ALOOKUP, ih', Prod.mk.injEq,
      term.Var.injEq]
    by_cases hc : x' = x ∧ ty' = ty <;> simp [hc]

/- HOL4:
Theorem TYPE_SUBST_NIL[simp]:
   ∀ty. TYPE_SUBST [] ty = ty
-/
theorem TYPE_SUBST_NIL : ∀ ty : type, TYPE_SUBST [] ty = ty := by
  apply Aux.type_ind
  · intro v; simp [TYPE_SUBST, REV_ASSOCD]
  · intro n args ih
    rw [TYPE_SUBST, (MAP_EQ_ID (TYPE_SUBST []) args).mpr ih]

/- HOL4:
Theorem TYPE_SUBST_Bool:
   ∀tyin. TYPE_SUBST tyin Bool = Bool
-/
theorem TYPE_SUBST_Bool : ∀ tyin : List (type × type), TYPE_SUBST tyin BoolTy = BoolTy := by
  intro tyin
  simp [TYPE_SUBST]

/- HOL4:
Theorem is_instance_refl[simp]:
   ∀ty. is_instance ty ty
-/
theorem is_instance_refl : ∀ ty : type, is_instance ty ty := by
  intro ty
  exact ⟨[], (TYPE_SUBST_NIL ty).symm⟩

/- HOL4:
Theorem swap_ff:
   ∀f g. (λ(x,y). (y,x)) o (f ## g) = (g ## f) o (λ(x,y). (y,x))
-/
theorem swap_ff {α : Type u} {β : Type v} {γ : Type w} {δ : Type x} :
    ∀ (f : α → β) (g : γ → δ),
      (fun (p : β × δ) => match p with | (x, y) => (y, x)) ∘ PAIR_MAP f g =
      PAIR_MAP g f ∘ (fun (p : α × γ) => match p with | (x, y) => (y, x)) := by
  intro f g
  rfl

/- HOL4:
Theorem ff_def:
   ∀f g. (f ## g) = λ(x,y). (f x, g y)
-/
theorem ff_def {α : Type u} {β : Type v} {γ : Type w} {δ : Type x} :
    ∀ (f : α → β) (g : γ → δ),
      PAIR_MAP f g = (fun (p : α × γ) => match p with | (x, y) => (f x, g y)) := by
  intro f g
  rfl

/- HOL4:
Theorem TYPE_SUBST_compose:
   ∀tyin1 ty tyin2.
    TYPE_SUBST tyin2 (TYPE_SUBST tyin1 ty) =
    TYPE_SUBST ((MAP (TYPE_SUBST tyin2 ## I) tyin1) ++ tyin2) ty
-/
theorem TYPE_SUBST_compose :
    ∀ (tyin1 : List (type × type)) (ty : type) (tyin2 : List (type × type)),
      TYPE_SUBST tyin2 (TYPE_SUBST tyin1 ty) =
      TYPE_SUBST ((tyin1.map (PAIR_MAP (TYPE_SUBST tyin2) I)) ++ tyin2) ty := by
  intro tyin1 ty tyin2
  induction ty using Aux.type_ind with
  | hv v =>
    simp only [TYPE_SUBST]
    induction tyin1 with
    | nil => simp [REV_ASSOCD, TYPE_SUBST]
    | cons p t ih =>
      by_cases h : p.2 = Tyvar v
      · simp [REV_ASSOCD, h]
      · simp [REV_ASSOCD, h, ih]
  | ha n args ih =>
    simp only [TYPE_SUBST, List.map_map]
    congr 1
    exact List.map_congr_left ih

/- HOL4:
Theorem TYPE_SUBST_tyvars:
   ∀ty tyin tyin'.
    (TYPE_SUBST tyin ty = TYPE_SUBST tyin' ty) ⇔
    ∀x. MEM x (tyvars ty) ⇒
        REV_ASSOCD (Tyvar x) tyin' (Tyvar x) =
        REV_ASSOCD (Tyvar x) tyin  (Tyvar x)
-/
theorem TYPE_SUBST_tyvars :
    ∀ (ty : type) (tyin tyin' : List (type × type)),
      (TYPE_SUBST tyin ty = TYPE_SUBST tyin' ty) ↔
      ∀ x, x ∈ tyvars ty →
        REV_ASSOCD (Tyvar x) tyin' (Tyvar x) =
        REV_ASSOCD (Tyvar x) tyin (Tyvar x) := by
  intro ty tyin tyin'
  constructor
  · intro h x hx
    have := Aux.TYPE_SUBST_tyvars_imp tyin tyin' ty h x hx
    simp only [TYPE_SUBST] at this
    exact this.symm
  · induction ty using Aux.type_ind with
    | hv v =>
      intro h
      simp only [TYPE_SUBST]
      exact (h v (by simp [tyvars])).symm
    | ha n args ih =>
      intro h
      simp only [TYPE_SUBST]
      congr 1
      apply List.map_congr_left
      intro a ha
      exact ih a ha (fun x hx => h x ((Aux.mem_tyvars_Tyapp x n args).mpr ⟨a, ha, hx⟩))

/- HOL4:
Theorem WELLTYPED_LEMMA:
   ∀tm ty. tm has_type ty ⇒ (typeof tm = ty)
-/
theorem WELLTYPED_LEMMA : ∀ (tm : term) (ty : type), has_type tm ty → typeof tm = ty := by
  intro tm ty h
  induction h with
  | Var => rfl
  | Const => rfl
  | Comb _ _ ih _ => simp only [typeof, ih]; rfl
  | Abs _ ih => simp only [typeof, ih]

/- HOL4:
Theorem WELLTYPED:
   ∀tm. welltyped tm ⇔ tm has_type (typeof tm)
-/
theorem WELLTYPED : ∀ tm : term, welltyped tm ↔ has_type tm (typeof tm) := by
  intro tm
  constructor
  · rintro ⟨ty, h⟩
    rw [WELLTYPED_LEMMA tm ty h]
    exact h
  · exact fun h => ⟨_, h⟩

/- HOL4:
Theorem WELLTYPED_CLAUSES[simp]:
  (!n ty. welltyped(Var n ty)) /\
   (!n ty. welltyped(Const n ty)) /\
   (!s t. welltyped (Comb s t) <=>
            welltyped s /\ welltyped t /\
            ?rty. typeof s = Fun (typeof t) rty) /\
   (!v t. welltyped (Abs v t) = ∃n ty. v = Var n ty ∧ welltyped t)
-/
theorem WELLTYPED_CLAUSES :
    (∀ (n : mlstring) (ty : type), welltyped (Var n ty)) ∧
    (∀ (n : mlstring) (ty : type), welltyped (Const n ty)) ∧
    (∀ (s t : term), welltyped (Comb s t) ↔
        welltyped s ∧ welltyped t ∧
        ∃ rty, typeof s = Fun (typeof t) rty) ∧
    (∀ (v t : term), welltyped (Abs v t) ↔ ∃ n ty, v = Var n ty ∧ welltyped t) := by
  refine ⟨fun n ty => ⟨ty, has_type.Var⟩, fun n ty => ⟨ty, has_type.Const⟩, ?_, ?_⟩
  · intro s t
    constructor
    · rintro ⟨ty, h⟩
      obtain ⟨dty, h1, h2⟩ := Aux.has_type_Comb h
      refine ⟨⟨_, h1⟩, ⟨_, h2⟩, ty, ?_⟩
      rw [WELLTYPED_LEMMA _ _ h1, WELLTYPED_LEMMA _ _ h2]
    · rintro ⟨h1, h2, rty, h3⟩
      rw [WELLTYPED] at h1 h2
      rw [h3] at h1
      exact ⟨rty, has_type.Comb h1 h2⟩
  · intro v t
    constructor
    · rintro ⟨ty, h⟩
      obtain ⟨n, dty, rty, rfl, _, h2⟩ := Aux.has_type_Abs h
      exact ⟨n, dty, rfl, _, h2⟩
    · rintro ⟨n, ty, rfl, rty, h⟩
      exact ⟨_, has_type.Abs h⟩

theorem Aux.welltyped_Comb {s t : term} (h : welltyped (Comb s t)) :
    welltyped s ∧ welltyped t ∧ ∃ rty, typeof s = Fun (typeof t) rty :=
  (WELLTYPED_CLAUSES.2.2.1 s t).mp h

theorem Aux.welltyped_Abs {v t : term} (h : welltyped (Abs v t)) :
    ∃ n ty, v = Var n ty ∧ welltyped t :=
  (WELLTYPED_CLAUSES.2.2.2 v t).mp h

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
   (Lean name RACONV_thm: `RACONV` is already the inductive relation) -/
theorem RACONV_thm (env : List (term × term)) (x1 : mlstring) (ty1 : type) (x2 : mlstring)
    (ty2 : type) (l1 r1 l2 r2 v1 t1 v2 t2 : term) :
    (RACONV env (Var x1 ty1, Var x2 ty2) ↔
        ALPHAVARS env (Var x1 ty1, Var x2 ty2)) ∧
    (RACONV env (Var x1 ty1, Const x2 ty2) ↔ False) ∧
    (RACONV env (Var x1 ty1, Comb l2 r2) ↔ False) ∧
    (RACONV env (Var x1 ty1, Abs v2 t2) ↔ False) ∧
    (RACONV env (Const x1 ty1, Var x2 ty2) ↔ False) ∧
    (RACONV env (Const x1 ty1, Const x2 ty2) ↔ x1 = x2 ∧ ty1 = ty2) ∧
    (RACONV env (Const x1 ty1, Comb l2 r2) ↔ False) ∧
    (RACONV env (Const x1 ty1, Abs v2 t2) ↔ False) ∧
    (RACONV env (Comb l1 r1, Var x2 ty2) ↔ False) ∧
    (RACONV env (Comb l1 r1, Const x2 ty2) ↔ False) ∧
    (RACONV env (Comb l1 r1, Comb l2 r2) ↔
        RACONV env (l1, l2) ∧ RACONV env (r1, r2)) ∧
    (RACONV env (Comb l1 r1, Abs v2 t2) ↔ False) ∧
    (RACONV env (Abs v1 t1, Var x2 ty2) ↔ False) ∧
    (RACONV env (Abs v1 t1, Const x2 ty2) ↔ False) ∧
    (RACONV env (Abs v1 t1, Comb l2 r2) ↔ False) ∧
    (RACONV env (Abs v1 t1, Abs v2 t2) ↔
        typeof v1 = typeof v2 ∧
        RACONV ((v1, v2) :: env) (t1, t2)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> constructor <;>
    intro h
  all_goals first
    | exact h.elim
    | (cases h; done)
    | (cases h; assumption)
    | (cases h; exact ⟨rfl, rfl⟩)
    | (cases h; constructor <;> assumption)
    | exact RACONV.Var h
    | (obtain ⟨rfl, rfl⟩ := h; exact RACONV.Const)
    | exact RACONV.Comb h.1 h.2
    | exact RACONV.Abs h.1 h.2

/- HOL4:
Theorem RACONV_REFL:
   ∀t env. EVERY (UNCURRY $=) env ⇒ RACONV env (t,t)
-/
theorem RACONV_REFL :
    ∀ (t : term) (env : List (term × term)),
      EVERY (UNCURRY (fun a b => a = b)) env → RACONV env (t, t) := by
  intro t
  induction t with
  | Var x ty => intro env h; exact RACONV.Var (ALPHAVARS_REFL env _ h)
  | Const x ty => intro env h; exact RACONV.Const
  | Comb s t ihs iht => intro env h; exact RACONV.Comb (ihs env h) (iht env h)
  | Abs v t _ iht => intro env h; exact RACONV.Abs rfl (iht _ ⟨rfl, h⟩)

/- HOL4:
Theorem ACONV_REFL[simp]:
   ∀t. ACONV t t
-/
theorem ACONV_REFL : ∀ t : term, ACONV t t := by
  intro t
  exact RACONV_REFL t [] trivial

theorem Aux.ALPHAVARS_TRANS {α : Type u} (a b c : α) : ∀ (env : List (α × α)) (vs : List α),
    vs.length = env.length → ALPHAVARS env (a, b) → ALPHAVARS (ZIP (env.map Prod.snd, vs)) (b, c) →
    ALPHAVARS (ZIP (env.map Prod.fst, vs)) (a, c)
  | [], vs, _, h1, h2 => by
    simp only [List.map_nil, ZIP, ALPHAVARS] at h1 h2 ⊢
    rw [h1, h2]
  | (x, y) :: env, [], h, _, _ => by simp at h
  | (x, y) :: env, v :: vs, h, h1, h2 => by
    have ih := Aux.ALPHAVARS_TRANS a b c env vs (by simpa using h)
    simp only [List.map_cons, ZIP, ALPHAVARS, Prod.mk.injEq] at h1 h2 ⊢
    grind

theorem Aux.ALPHAVARS_SYM {α : Type u} (a b : α) : ∀ (env : List (α × α)),
    ALPHAVARS env (a, b) →
    ALPHAVARS (env.map (fun p => match p with | (x, y) => (y, x))) (b, a)
  | [], h => by
    simp only [ALPHAVARS, List.map_nil] at h ⊢
    exact h.symm
  | (x, y) :: env, h => by
    have ih := Aux.ALPHAVARS_SYM a b env
    simp only [List.map_cons, ALPHAVARS, Prod.mk.injEq] at h ⊢
    grind

/- HOL4:
Theorem RACONV_TRANS:
   ∀env tp. RACONV env tp ⇒ ∀vs t. LENGTH vs = LENGTH env ∧ RACONV (ZIP(MAP SND env,vs)) (SND tp,t) ⇒ RACONV (ZIP(MAP FST env,vs)) (FST tp, t)
-/
theorem RACONV_TRANS :
    ∀ (env : List (term × term)) (tp : term × term), RACONV env tp →
      ∀ (vs : List term) (t : term),
        vs.length = env.length ∧ RACONV (ZIP (env.map Prod.snd, vs)) (tp.2, t) →
        RACONV (ZIP (env.map Prod.fst, vs)) (tp.1, t) := by
  intro env tp h
  induction h with
  | Var ha =>
    rintro vs t ⟨hl, h⟩
    cases h with
    | Var hb => exact RACONV.Var (Aux.ALPHAVARS_TRANS _ _ _ _ vs hl ha hb)
  | Const =>
    rintro vs t ⟨hl, h⟩
    cases h with
    | Const => exact RACONV.Const
  | Comb _ _ ih1 ih2 =>
    rintro vs t ⟨hl, h⟩
    cases h with
    | Comb h1 h2 => exact RACONV.Comb (ih1 vs _ ⟨hl, h1⟩) (ih2 vs _ ⟨hl, h2⟩)
  | Abs hty _ ih =>
    rintro vs t ⟨hl, h⟩
    cases h with
    | @Abs _ _ v3 _ t3 hty' h' =>
      have hi := ih (v3 :: vs) t3 ⟨by simp [hl], by simpa [ZIP] using h'⟩
      exact RACONV.Abs (hty.trans hty') (by simpa [ZIP] using hi)

/- HOL4:
Theorem ACONV_TRANS:
   ∀t1 t2 t3. ACONV t1 t2 ∧ ACONV t2 t3 ⇒ ACONV t1 t3
-/
theorem ACONV_TRANS : ∀ (t1 t2 t3 : term), ACONV t1 t2 ∧ ACONV t2 t3 → ACONV t1 t3 := by
  rintro t1 t2 t3 ⟨h1, h2⟩
  have h := RACONV_TRANS [] (t1, t2) h1 [] t3 ⟨rfl, by simpa [ZIP] using h2⟩
  simpa [ZIP] using h

/- HOL4:
Theorem RACONV_SYM:
   ∀env tp. RACONV env tp ⇒ RACONV (MAP (λ(x,y). (y,x)) env) (SND tp,FST tp)
-/
theorem RACONV_SYM :
    ∀ (env : List (term × term)) (tp : term × term), RACONV env tp →
      RACONV (env.map (fun p => match p with | (x, y) => (y, x))) (tp.2, tp.1) := by
  intro env tp h
  induction h with
  | Var ha => exact RACONV.Var (Aux.ALPHAVARS_SYM _ _ _ ha)
  | Const => exact RACONV.Const
  | Comb _ _ ih1 ih2 => exact RACONV.Comb ih1 ih2
  | Abs hty _ ih => exact RACONV.Abs hty.symm ih

/- HOL4:
Theorem ACONV_SYM:
   ∀t1 t2. ACONV t1 t2 ⇒ ACONV t2 t1
-/
theorem ACONV_SYM : ∀ (t1 t2 : term), ACONV t1 t2 → ACONV t2 t1 := by
  intro t1 t2 h
  exact RACONV_SYM [] (t1, t2) h

/- HOL4:
Theorem ALPHAVARS_TYPE:
   ∀env s t. ALPHAVARS env (s,t) ∧
              EVERY (λ(x,y). welltyped x ∧ welltyped y
                             ∧ (typeof x = typeof y)) env ∧
              welltyped s ∧ welltyped t
              ⇒ typeof s = typeof t
-/
theorem ALPHAVARS_TYPE :
    ∀ (env : List (term × term)) (s t : term),
      ALPHAVARS env (s, t) ∧
      EVERY (fun p => match p with
        | (x, y) => welltyped x ∧ welltyped y ∧ typeof x = typeof y) env ∧
      welltyped s ∧ welltyped t →
      typeof s = typeof t := by
  rintro env s t ⟨h1, h2, _, _⟩
  rcases ALPHAVARS_MEM env (s, t) h1 with h | h
  · exact (Aux.EVERY_iff.mp h2 _ h).2.2
  · exact congrArg typeof h

/- HOL4:
Theorem RACONV_TYPE:
   ∀env p. RACONV env p
            ⇒ EVERY (λ(x,y). welltyped x ∧ welltyped y
                             ∧ (typeof x = typeof y)) env ∧
              welltyped (FST p) ∧ welltyped (SND p)
              ⇒ typeof (FST p) = typeof (SND p)
-/
theorem RACONV_TYPE :
    ∀ (env : List (term × term)) (p : term × term), RACONV env p →
      EVERY (fun q => match q with
        | (x, y) => welltyped x ∧ welltyped y ∧ typeof x = typeof y) env ∧
      welltyped p.1 ∧ welltyped p.2 →
      typeof p.1 = typeof p.2 := by
  intro env p h
  induction h with
  | Var ha => rintro ⟨h1, h2, h3⟩; exact ALPHAVARS_TYPE _ _ _ ⟨ha, h1, h2, h3⟩
  | Const => rintro _; rfl
  | Comb _ _ ih1 _ =>
    rintro ⟨h1, h2, h3⟩
    have e := ih1 ⟨h1, (Aux.welltyped_Comb h2).1, (Aux.welltyped_Comb h3).1⟩
    exact congrArg codomain e
  | Abs hty _ ih =>
    rintro ⟨h1, h2, h3⟩
    obtain ⟨n1, ty1, rfl, w1⟩ := Aux.welltyped_Abs h2
    obtain ⟨n2, ty2, rfl, w2⟩ := Aux.welltyped_Abs h3
    have e := ih ⟨⟨⟨⟨_, has_type.Var⟩, ⟨_, has_type.Var⟩, hty⟩, h1⟩, w1, w2⟩
    simp only [typeof] at hty e ⊢
    rw [hty, e]

/- HOL4:
Theorem ACONV_TYPE:
   ∀s t. ACONV s t ⇒ welltyped s ∧ welltyped t ⇒ (typeof s = typeof t)
-/
theorem ACONV_TYPE :
    ∀ (s t : term), ACONV s t → welltyped s ∧ welltyped t → typeof s = typeof t := by
  intro s t h ⟨h1, h2⟩
  exact RACONV_TYPE [] (s, t) h ⟨trivial, h1, h2⟩

/- HOL4:
Theorem subtype_Tyvar[simp] =
  ``ty subtype (Tyvar x)``
  [HOL4 proof text removed]
   (resulting theorem: ⊢ ty subtype Tyvar x ⇔ ty = Tyvar x,
    with ty and x free) -/
theorem subtype_Tyvar (ty : type) (x : mlstring) : subtype ty (Tyvar x) ↔ ty = Tyvar x := by
  constructor
  · intro h
    rcases Aux.RTC_tail h with h | ⟨b, _, h⟩
    · exact h
    · cases h
  · rintro rfl; exact RTC.refl _

/- HOL4:
Theorem subterm_Var[simp] =
  ``tm subterm (Var x ty)``
  [HOL4 proof text removed]
   (resulting theorem: ⊢ tm subterm Var x ty ⇔ tm = Var x ty,
    with tm, x and ty free) -/
theorem subterm_Var (tm : term) (x : mlstring) (ty : type) :
    subterm tm (Var x ty) ↔ tm = Var x ty := by
  constructor
  · intro h
    rcases Aux.RTC_tail h with h | ⟨b, _, h⟩
    · exact h
    · cases h
  · rintro rfl; exact RTC.refl _

/- HOL4:
Theorem subterm_Const[simp] =
  ``tm subterm (Const x ty)``
  [HOL4 proof text removed]
   (resulting theorem: ⊢ tm subterm Const x ty ⇔ tm = Const x ty,
    with tm, x and ty free) -/
theorem subterm_Const (tm : term) (x : mlstring) (ty : type) :
    subterm tm (Const x ty) ↔ tm = Const x ty := by
  constructor
  · intro h
    rcases Aux.RTC_tail h with h | ⟨b, _, h⟩
    · exact h
    · cases h
  · rintro rfl; exact RTC.refl _

theorem Aux.LLEX_mono {α : Type u} {R S : α → α → Prop} (h : ∀ a b, R a b → S a b) :
    ∀ l1 l2, LLEX R l1 l2 → LLEX S l1 l2
  | [], _, h' => by simpa [LLEX] using h'
  | _ :: _, [], h' => by simp [LLEX] at h'
  | a :: t1, b :: t2, h' => by
    have ih := Aux.LLEX_mono h t1 t2
    have hab := h a b
    simp only [LLEX] at h' ⊢
    grind

theorem Aux.LLEX_cons {α : Type u} (R : α → α → Prop) (a b : α) (t1 t2 : List α) :
    LLEX R (a :: t1) (b :: t2) ↔ R a b ∨ (a = b ∧ LLEX R t1 t2) := by
  simp only [LLEX]
  grind

theorem Aux.type_lt_rules :
    (∀ x1 x2, mlstring_lt x1 x2 → type_lt (Tyvar x1) (Tyvar x2)) ∧
    (∀ x1 x2 args2, type_lt (Tyvar x1) (Tyapp x2 args2)) ∧
    (∀ x1 args1 x2 args2, LEX mlstring_lt (LLEX type_lt) (x1, args1) (x2, args2) →
      type_lt (Tyapp x1 args1) (Tyapp x2 args2)) := by
  refine ⟨fun x1 x2 h R hR => hR.1 x1 x2 h, fun x1 x2 a R hR => hR.2.1 x1 x2 a, ?_⟩
  intro x1 a1 x2 a2 h R hR
  refine hR.2.2 x1 a1 x2 a2 ?_
  rcases h with h | ⟨h1, h2⟩
  · exact Or.inl h
  · exact Or.inr ⟨h1, Aux.LLEX_mono (fun a b hab => hab R hR) _ _ h2⟩

def Aux.type_lt_inv (R : type → type → Prop) : type → type → Prop
  | Tyvar x1, Tyvar x2 => mlstring_lt x1 x2
  | Tyvar _, Tyapp _ _ => True
  | Tyapp _ _, Tyvar _ => False
  | Tyapp x1 a1, Tyapp x2 a2 => LEX mlstring_lt (LLEX R) (x1, a1) (x2, a2)

theorem Aux.type_lt_inv_of {a b : type} (h : type_lt a b) : Aux.type_lt_inv type_lt a b := by
  have hl : ∀ a b, Aux.type_lt_inv type_lt a b → type_lt a b := by
    intro a b h
    cases a <;> cases b
    · exact Aux.type_lt_rules.1 _ _ h
    · exact Aux.type_lt_rules.2.1 _ _ _
    · exact h.elim
    · exact Aux.type_lt_rules.2.2 _ _ _ _ h
  refine h (Aux.type_lt_inv type_lt) ⟨fun _ _ h => h, fun _ _ _ => trivial, ?_⟩
  intro x1 a1 x2 a2 h
  rcases h with h | ⟨h1, h2⟩
  · exact Or.inl h
  · exact Or.inr ⟨h1, Aux.LLEX_mono hl _ _ h2⟩

/- HOL4:
Theorem type_lt_thm = Q.prove(
  `(type_lt (Tyvar x1) (Tyvar x2) ⇔ mlstring_lt x1 x2) ∧
    (type_lt (Tyvar _) (Tyapp _ _) ⇔ T) ∧
    (type_lt (Tyapp _ _) (Tyvar _) ⇔ F) ∧
    (type_lt (Tyapp x1 args1) (Tyapp x2 args2) ⇔
       (mlstring_lt LEX LLEX type_lt)
         (x1,args1) (x2,args2))`,
  [HOL4 proof text removed]
   (each conjunct is universally closed separately; each `_` is a fresh variable) -/
theorem type_lt_thm :
    (∀ (x1 x2 : mlstring), type_lt (Tyvar x1) (Tyvar x2) ↔ mlstring_lt x1 x2) ∧
    (∀ (a : mlstring) (b : mlstring) (c : List type), type_lt (Tyvar a) (Tyapp b c) ↔ True) ∧
    (∀ (a : mlstring) (b : List type) (c : mlstring), type_lt (Tyapp a b) (Tyvar c) ↔ False) ∧
    (∀ (x1 : mlstring) (args1 : List type) (x2 : mlstring) (args2 : List type),
      type_lt (Tyapp x1 args1) (Tyapp x2 args2) ↔
        LEX mlstring_lt (LLEX type_lt) (x1, args1) (x2, args2)) := by
  refine ⟨fun x1 x2 => ⟨fun h => Aux.type_lt_inv_of h, Aux.type_lt_rules.1 _ _⟩,
    fun a b c => ⟨fun _ => trivial, fun _ => Aux.type_lt_rules.2.1 _ _ _⟩,
    fun a b c => ⟨fun h => Aux.type_lt_inv_of h, False.elim⟩,
    fun x1 a1 x2 a2 => ⟨fun h => Aux.type_lt_inv_of h, Aux.type_lt_rules.2.2 _ _ _ _⟩⟩

theorem Aux.LEX_mono {α : Type u} {R S : α → α → Prop} (h : ∀ a b, R a b → S a b) (p q : α × α) :
    LEX R R p q → LEX S S p q := by
  rintro (h' | ⟨h1, h2⟩)
  · exact Or.inl (h _ _ h')
  · exact Or.inr ⟨h1, h _ _ h2⟩

def Aux.term_lt_inv (R : term → term → Prop) : term → term → Prop
  | Var x1 ty1, Var x2 ty2 => LEX mlstring_lt type_lt (x1, ty1) (x2, ty2)
  | Var _ _, Const _ _ => True
  | Var _ _, Comb _ _ => True
  | Var _ _, Abs _ _ => True
  | Const _ _, Var _ _ => False
  | Const x1 ty1, Const x2 ty2 => LEX mlstring_lt type_lt (x1, ty1) (x2, ty2)
  | Const _ _, Comb _ _ => True
  | Const _ _, Abs _ _ => True
  | Comb _ _, Var _ _ => False
  | Comb _ _, Const _ _ => False
  | Comb s1 s2, Comb t1 t2 => LEX R R (s1, s2) (t1, t2)
  | Comb _ _, Abs _ _ => True
  | Abs _ _, Var _ _ => False
  | Abs _ _, Const _ _ => False
  | Abs _ _, Comb _ _ => False
  | Abs s1 s2, Abs t1 t2 => LEX R R (s1, s2) (t1, t2)

theorem Aux.term_lt_of_inv {a b : term} (h : Aux.term_lt_inv term_lt a b) : term_lt a b := by
  intro R hR
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := id hR
  cases a <;> cases b <;> first
    | exact h.elim
    | exact h1 _ _ _ _ h
    | exact h2 _ _ _ _
    | exact h3 _ _ _ _
    | exact h4 _ _ _ _
    | exact h5 _ _ _ _ h
    | exact h6 _ _ _ _
    | exact h7 _ _ _ _
    | exact h8 _ _ _ _ (Aux.LEX_mono (fun a b hab => hab R hR) _ _ h)
    | exact h9 _ _ _ _
    | exact h10 _ _ _ _ (Aux.LEX_mono (fun a b hab => hab R hR) _ _ h)

theorem Aux.term_lt_inv_of {a b : term} (h : term_lt a b) : Aux.term_lt_inv term_lt a b := by
  refine h (Aux.term_lt_inv term_lt) ⟨fun _ _ _ _ h => h, fun _ _ _ _ => trivial,
    fun _ _ _ _ => trivial, fun _ _ _ _ => trivial, fun _ _ _ _ h => h,
    fun _ _ _ _ => trivial, fun _ _ _ _ => trivial, ?_, fun _ _ _ _ => trivial, ?_⟩
  · intro s1 s2 t1 t2 h
    exact Aux.LEX_mono (fun _ _ => Aux.term_lt_of_inv) _ _ h
  · intro s1 s2 t1 t2 h
    exact Aux.LEX_mono (fun _ _ => Aux.term_lt_of_inv) _ _ h

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
  [HOL4 proof text removed]
   (each conjunct is universally closed separately; each `_` is a fresh variable) -/
theorem term_lt_thm :
    (∀ (x1 : mlstring) (ty1 : type) (x2 : mlstring) (ty2 : type),
      term_lt (Var x1 ty1) (Var x2 ty2) ↔
        LEX mlstring_lt type_lt (x1, ty1) (x2, ty2)) ∧
    (∀ (a : mlstring) (b : type) (c : mlstring) (d : type),
      term_lt (Var a b) (Const c d) ↔ True) ∧
    (∀ (a : mlstring) (b : type) (c d : term), term_lt (Var a b) (Comb c d) ↔ True) ∧
    (∀ (a : mlstring) (b : type) (c d : term), term_lt (Var a b) (Abs c d) ↔ True) ∧
    (∀ (a : mlstring) (b : type) (c : mlstring) (d : type),
      term_lt (Const a b) (Var c d) ↔ False) ∧
    (∀ (x1 : mlstring) (ty1 : type) (x2 : mlstring) (ty2 : type),
      term_lt (Const x1 ty1) (Const x2 ty2) ↔
        LEX mlstring_lt type_lt (x1, ty1) (x2, ty2)) ∧
    (∀ (a : mlstring) (b : type) (c d : term), term_lt (Const a b) (Comb c d) ↔ True) ∧
    (∀ (a : mlstring) (b : type) (c d : term), term_lt (Const a b) (Abs c d) ↔ True) ∧
    (∀ (a b : term) (c : mlstring) (d : type), term_lt (Comb a b) (Var c d) ↔ False) ∧
    (∀ (a b : term) (c : mlstring) (d : type), term_lt (Comb a b) (Const c d) ↔ False) ∧
    (∀ (s1 s2 t1 t2 : term),
      term_lt (Comb s1 s2) (Comb t1 t2) ↔ LEX term_lt term_lt (s1, s2) (t1, t2)) ∧
    (∀ (a b c d : term), term_lt (Comb a b) (Abs c d) ↔ True) ∧
    (∀ (a b : term) (c : mlstring) (d : type), term_lt (Abs a b) (Var c d) ↔ False) ∧
    (∀ (a b : term) (c : mlstring) (d : type), term_lt (Abs a b) (Const c d) ↔ False) ∧
    (∀ (a b c d : term), term_lt (Abs a b) (Comb c d) ↔ False) ∧
    (∀ (s1 s2 t1 t2 : term),
      term_lt (Abs s1 s2) (Abs t1 t2) ↔ LEX term_lt term_lt (s1, s2) (t1, t2)) := by
  have key : ∀ a b, term_lt a b ↔ Aux.term_lt_inv term_lt a b :=
    fun a b => ⟨Aux.term_lt_inv_of, Aux.term_lt_of_inv⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (intro a b c d; exact key _ _)

theorem Aux.TO_refl {α : Type u} (R : α → α → Prop) (x : α) :
    TO_of_LinearOrder R x x = EQUAL := by
  simp [TO_of_LinearOrder]

theorem Aux.TotOrd_TO {α : Type u} {R : α → α → Prop} (h : StrongLinearOrder R) :
    TotOrd (TO_of_LinearOrder R) := by
  obtain ⟨⟨hi, ht⟩, htr⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · intro x y
    unfold TO_of_LinearOrder
    grind
  · intro x y
    have h1 := htr x y
    have h2 := ht x y x
    have h3 := hi x
    unfold TO_of_LinearOrder
    grind
  · intro x y z
    have h1 := ht x y z
    have h2 := hi x
    have h3 := ht x y x
    unfold TO_of_LinearOrder
    grind

/- HOL4:
Theorem type_cmp_refl[simp]:
   type_cmp t t = EQUAL
-/
theorem type_cmp_refl (t : type) : type_cmp t t = EQUAL := by
  exact Aux.TO_refl _ t

/- HOL4:
Theorem term_cmp_refl[simp]:
   term_cmp t t = EQUAL
-/
theorem term_cmp_refl (t : term) : term_cmp t t = EQUAL := by
  exact Aux.TO_refl _ t

theorem Aux.LLEX_irrefl {α : Type u} {R : α → α → Prop} :
    ∀ l : List α, (∀ a, a ∈ l → ¬ R a a) → ¬ LLEX R l l
  | [], _ => by simp [LLEX]
  | a :: t, h => by
    rw [Aux.LLEX_cons]
    rintro (h' | ⟨_, h'⟩)
    · exact h a List.mem_cons_self h'
    · exact Aux.LLEX_irrefl t (fun b hb => h b (List.mem_cons_of_mem _ hb)) h'

theorem Aux.LLEX_trans {α : Type u} {R : α → α → Prop} :
    ∀ l1 l2 l3 : List α, (∀ a, a ∈ l1 → ∀ b c, R a b → R b c → R a c) →
      LLEX R l1 l2 → LLEX R l2 l3 → LLEX R l1 l3
  | [], [], _, _, h1, _ => by simp [LLEX] at h1
  | [], _ :: _, [], _, _, h2 => by simp [LLEX] at h2
  | [], _ :: _, _ :: _, _, _, _ => by simp [LLEX]
  | _ :: _, [], _, _, h1, _ => by simp [LLEX] at h1
  | _ :: _, _ :: _, [], _, _, h2 => by simp [LLEX] at h2
  | a :: t1, b :: t2, c :: t3, h, h1, h2 => by
    have ih := Aux.LLEX_trans t1 t2 t3 (fun b hb => h b (List.mem_cons_of_mem _ hb))
    have ha := h a List.mem_cons_self b c
    rw [Aux.LLEX_cons] at h1 h2 ⊢
    grind

theorem Aux.LLEX_tri {α : Type u} {R : α → α → Prop} :
    ∀ l1 l2 : List α, (∀ a, a ∈ l1 → ∀ b, R a b ∨ R b a ∨ a = b) →
      LLEX R l1 l2 ∨ LLEX R l2 l1 ∨ l1 = l2
  | [], [], _ => by simp
  | [], _ :: _, _ => by simp [LLEX]
  | _ :: _, [], _ => by simp [LLEX]
  | a :: t1, b :: t2, h => by
    have ih := Aux.LLEX_tri t1 t2 (fun b hb => h b (List.mem_cons_of_mem _ hb))
    have ha := h a List.mem_cons_self b
    rw [Aux.LLEX_cons, Aux.LLEX_cons]
    grind

theorem Aux.type_lt_irrefl : ∀ t, ¬ type_lt t t := by
  apply Aux.type_ind
  · intro v
    rw [type_lt_thm.1]
    exact StrongLinearOrder_mlstring_lt.1.1 v
  · intro n args ih
    rw [type_lt_thm.2.2.2]
    rintro (h | ⟨_, h⟩)
    · exact StrongLinearOrder_mlstring_lt.1.1 n h
    · exact Aux.LLEX_irrefl args ih h

theorem Aux.type_lt_trans : ∀ a b c, type_lt a b → type_lt b c → type_lt a c := by
  have ht := StrongLinearOrder_mlstring_lt.1.2
  intro a
  induction a using Aux.type_ind with
  | hv v =>
    intro b c h1 h2
    cases b with
    | Tyvar v2 =>
      cases c with
      | Tyvar v3 =>
        rw [type_lt_thm.1] at h1 h2 ⊢
        exact ht _ _ _ ⟨h1, h2⟩
      | Tyapp => exact (type_lt_thm.2.1 _ _ _).mpr trivial
    | Tyapp n2 a2 =>
      cases c with
      | Tyvar v3 => exact ((type_lt_thm.2.2.1 _ _ _).mp h2).elim
      | Tyapp => exact (type_lt_thm.2.1 _ _ _).mpr trivial
  | ha n args ih =>
    intro b c h1 h2
    cases b with
    | Tyvar v2 => exact ((type_lt_thm.2.2.1 _ _ _).mp h1).elim
    | Tyapp n2 a2 =>
      cases c with
      | Tyvar v3 => exact ((type_lt_thm.2.2.1 _ _ _).mp h2).elim
      | Tyapp n3 a3 =>
        rw [type_lt_thm.2.2.2] at h1 h2 ⊢
        have hl := Aux.LLEX_trans (R := type_lt) args a2 a3 ih
        have hn := ht n n2 n3
        simp only [LEX] at h1 h2 ⊢
        grind

theorem Aux.type_lt_tri : ∀ a b, type_lt a b ∨ type_lt b a ∨ a = b := by
  have ht := StrongLinearOrder_mlstring_lt.2
  intro a
  induction a using Aux.type_ind with
  | hv v =>
    intro b
    cases b with
    | Tyvar v2 =>
      rw [type_lt_thm.1, type_lt_thm.1]
      have := ht v v2
      grind
    | Tyapp => exact Or.inl ((type_lt_thm.2.1 _ _ _).mpr trivial)
  | ha n args ih =>
    intro b
    cases b with
    | Tyvar v2 => exact Or.inr (Or.inl ((type_lt_thm.2.1 _ _ _).mpr trivial))
    | Tyapp n2 a2 =>
      rw [type_lt_thm.2.2.2, type_lt_thm.2.2.2]
      have hl := Aux.LLEX_tri (R := type_lt) args a2 ih
      have hn := ht n n2
      simp only [LEX]
      grind

theorem Aux.LEX_irrefl {α : Type u} {β : Type v} {R : α → α → Prop} {S : β → β → Prop}
    (hR : ∀ a, ¬ R a a) (hS : ∀ a, ¬ S a a) (p : α × β) : ¬ LEX R S p p := by
  rintro (h | ⟨_, h⟩)
  · exact hR _ h
  · exact hS _ h

/- HOL4:
Theorem StrongLinearOrder_type_lt:
   StrongLinearOrder type_lt
-/
theorem StrongLinearOrder_type_lt : StrongLinearOrder type_lt := by
  exact ⟨⟨Aux.type_lt_irrefl, fun a b c h => Aux.type_lt_trans a b c h.1 h.2⟩, Aux.type_lt_tri⟩

/- HOL4:
Theorem TotOrd_type_cmp:
   TotOrd type_cmp
-/
theorem TotOrd_type_cmp : TotOrd type_cmp := by
  exact Aux.TotOrd_TO StrongLinearOrder_type_lt

theorem Aux.term_lt_iff (a b : term) : term_lt a b ↔ Aux.term_lt_inv term_lt a b :=
  ⟨Aux.term_lt_inv_of, Aux.term_lt_of_inv⟩

theorem Aux.term_lt_irrefl : ∀ t, ¬ term_lt t t := by
  have hm := StrongLinearOrder_mlstring_lt.1.1
  intro t
  induction t with
  | Var x ty => rw [term_lt_thm.1]; exact Aux.LEX_irrefl hm Aux.type_lt_irrefl _
  | Const x ty =>
    rw [term_lt_thm.2.2.2.2.2.1]; exact Aux.LEX_irrefl hm Aux.type_lt_irrefl _
  | Comb s t ihs iht =>
    rw [Aux.term_lt_iff]
    rintro (h | ⟨_, h⟩)
    · exact ihs h
    · exact iht h
  | Abs s t ihs iht =>
    rw [Aux.term_lt_iff]
    rintro (h | ⟨_, h⟩)
    · exact ihs h
    · exact iht h

theorem Aux.LEX_trans {α : Type u} {β : Type v} {R : α → α → Prop} {S : β → β → Prop}
    {a1 a2 a3 : α} {b1 b2 b3 : β} (hR : R a1 a2 → R a2 a3 → R a1 a3)
    (hS : S b1 b2 → S b2 b3 → S b1 b3)
    (h1 : LEX R S (a1, b1) (a2, b2)) (h2 : LEX R S (a2, b2) (a3, b3)) :
    LEX R S (a1, b1) (a3, b3) := by
  simp only [LEX] at *
  grind

theorem Aux.LEX_tri {α : Type u} {β : Type v} {R : α → α → Prop} {S : β → β → Prop}
    {a1 a2 : α} {b1 b2 : β} (hR : R a1 a2 ∨ R a2 a1 ∨ a1 = a2)
    (hS : S b1 b2 ∨ S b2 b1 ∨ b1 = b2) :
    LEX R S (a1, b1) (a2, b2) ∨ LEX R S (a2, b2) (a1, b1) ∨ (a1 = a2 ∧ b1 = b2) := by
  simp only [LEX]
  grind

theorem Aux.term_lt_trans : ∀ a b c, term_lt a b → term_lt b c → term_lt a c := by
  have hm := StrongLinearOrder_mlstring_lt.1.2
  intro a
  induction a with
  | Var x ty =>
    intro b c h1 h2
    rw [Aux.term_lt_iff] at h1 h2 ⊢
    cases b <;> cases c <;> first
      | exact h1.elim
      | exact h2.elim
      | trivial
      | exact Aux.LEX_trans (fun h1 h2 => hm _ _ _ ⟨h1, h2⟩) (Aux.type_lt_trans _ _ _) h1 h2
  | Const x ty =>
    intro b c h1 h2
    rw [Aux.term_lt_iff] at h1 h2 ⊢
    cases b <;> cases c <;> first
      | exact h1.elim
      | exact h2.elim
      | trivial
      | exact Aux.LEX_trans (fun h1 h2 => hm _ _ _ ⟨h1, h2⟩) (Aux.type_lt_trans _ _ _) h1 h2
  | Comb s t ihs iht =>
    intro b c h1 h2
    rw [Aux.term_lt_iff] at h1 h2 ⊢
    cases b <;> cases c <;> first
      | exact h1.elim
      | exact h2.elim
      | trivial
      | exact Aux.LEX_trans (ihs _ _) (iht _ _) h1 h2
  | Abs s t ihs iht =>
    intro b c h1 h2
    rw [Aux.term_lt_iff] at h1 h2 ⊢
    cases b <;> cases c <;> first
      | exact h1.elim
      | exact h2.elim
      | trivial
      | exact Aux.LEX_trans (ihs _ _) (iht _ _) h1 h2

theorem Aux.term_lt_tri : ∀ a b, term_lt a b ∨ term_lt b a ∨ a = b := by
  have hm := StrongLinearOrder_mlstring_lt.2
  intro a
  induction a with
  | Var x ty =>
    intro b
    rw [Aux.term_lt_iff, Aux.term_lt_iff]
    cases b <;> first
      | exact Or.inl trivial
      | exact Or.inr (Or.inl trivial)
      | (rw [term.Var.injEq]; exact Aux.LEX_tri (hm _ _) (Aux.type_lt_tri _ _))
  | Const x ty =>
    intro b
    rw [Aux.term_lt_iff, Aux.term_lt_iff]
    cases b <;> first
      | exact Or.inl trivial
      | exact Or.inr (Or.inl trivial)
      | (rw [term.Const.injEq]; exact Aux.LEX_tri (hm _ _) (Aux.type_lt_tri _ _))
  | Comb s t ihs iht =>
    intro b
    rw [Aux.term_lt_iff, Aux.term_lt_iff]
    cases b <;> first
      | exact Or.inl trivial
      | exact Or.inr (Or.inl trivial)
      | (rw [term.Comb.injEq]; exact Aux.LEX_tri (ihs _) (iht _))
  | Abs s t ihs iht =>
    intro b
    rw [Aux.term_lt_iff, Aux.term_lt_iff]
    cases b <;> first
      | exact Or.inl trivial
      | exact Or.inr (Or.inl trivial)
      | (rw [term.Abs.injEq]; exact Aux.LEX_tri (ihs _) (iht _))

/- HOL4:
Theorem StrongLinearOrder_term_lt:
   StrongLinearOrder term_lt
-/
theorem StrongLinearOrder_term_lt : StrongLinearOrder term_lt := by
  exact ⟨⟨Aux.term_lt_irrefl, fun a b c h => Aux.term_lt_trans a b c h.1 h.2⟩, Aux.term_lt_tri⟩

/- HOL4:
Theorem TotOrd_term_cmp:
   TotOrd term_cmp
-/
theorem TotOrd_term_cmp : TotOrd term_cmp := by
  exact Aux.TotOrd_TO StrongLinearOrder_term_lt

/- HOL4:
Theorem ALPHAVARS_eq_ordav:
   ∀env t1 t2. ALPHAVARS env (t1,t2) ⇔ ordav env t1 t2 = EQUAL
-/
theorem ALPHAVARS_eq_ordav :
    ∀ (env : List (term × term)) (t1 t2 : term),
      ALPHAVARS env (t1, t2) ↔ ordav env t1 t2 = EQUAL := by
  intro env t1 t2
  induction env with
  | nil =>
    simp only [ALPHAVARS, ordav]
    exact (TotOrd_term_cmp.1 t1 t2).symm
  | cons p env ih =>
    obtain ⟨a, b⟩ := p
    simp only [ALPHAVARS, ordav, Prod.mk.injEq]
    by_cases h1 : t1 = a
    · by_cases h2 : t2 = b <;> simp [h1, h2]
    · by_cases h2 : t2 = b
      · simp [h1, h2]
      · have h1' : ¬ a = t1 := fun e => h1 e.symm
        have h2' : ¬ b = t2 := fun e => h2 e.symm
        simp [h1, h2, h1', h2', ih]

theorem Aux.ordav_refl (t : term) : ∀ env : List (term × term),
    EVERY (UNCURRY (fun a b => a = b)) env → ordav env t t = EQUAL := by
  intro env h
  rw [← ALPHAVARS_eq_ordav]
  exact ALPHAVARS_REFL env t h

theorem Aux.orda_refl (t : term) : ∀ env : List (term × term),
    EVERY (UNCURRY (fun a b => a = b)) env → orda env t t = EQUAL := by
  induction t with
  | Var x ty => intro env h; rw [orda]; simp [Aux.ordav_refl _ env h]
  | Const x ty => intro env h; rw [orda]; simp [term_cmp_refl]
  | Comb s t ihs iht => intro env h; rw [orda]; simp [ihs env h, iht env h]
  | Abs v t _ iht =>
    intro env h
    rw [orda]
    simp [type_cmp_refl, iht ((v, v) :: env) ⟨rfl, h⟩]

theorem Aux.orda_Var (env : List (term × term)) (x1 x2 : mlstring) (ty1 ty2 : type) :
    orda env (Var x1 ty1) (Var x2 ty2) = ordav env (Var x1 ty1) (Var x2 ty2) := by
  rw [orda]
  split
  · rename_i h
    rw [h.1, h.2]
    exact (term_cmp_refl _).symm
  · rfl

theorem Aux.orda_Const (env : List (term × term)) (x1 x2 : mlstring) (ty1 ty2 : type) :
    orda env (Const x1 ty1) (Const x2 ty2) = term_cmp (Const x1 ty1) (Const x2 ty2) := by
  rw [orda]
  split
  · rename_i h
    rw [h.1]
    exact (term_cmp_refl _).symm
  · rfl

theorem Aux.orda_Comb (env : List (term × term)) (s1 s2 t1 t2 : term) :
    orda env (Comb s1 t1) (Comb s2 t2) =
      if orda env s1 s2 ≠ EQUAL then orda env s1 s2 else orda env t1 t2 := by
  rw [orda]
  split
  · rename_i h
    obtain ⟨h1, rfl⟩ := h
    cases h1
    simp [Aux.orda_refl _ [] trivial]
  · rfl

theorem Aux.orda_Abs (env : List (term × term)) (v1 v2 t1 t2 : term) :
    orda env (Abs v1 t1) (Abs v2 t2) =
      if type_cmp (typeof v1) (typeof v2) ≠ EQUAL then type_cmp (typeof v1) (typeof v2)
      else orda ((v1, v2) :: env) t1 t2 := by
  rw [orda]
  split
  · rename_i h
    obtain ⟨h1, rfl⟩ := h
    cases h1
    simp [type_cmp_refl, Aux.orda_refl _ [(v1, v1)] ⟨rfl, trivial⟩]
  · rfl

def Aux.rank : term → Nat
  | Var _ _ => 0
  | Const _ _ => 1
  | Comb _ _ => 2
  | Abs _ _ => 3

theorem Aux.orda_rank_lt (env : List (term × term)) (t1 t2 : term)
    (h : Aux.rank t1 < Aux.rank t2) : orda env t1 t2 = LESS := by
  cases t1 <;> cases t2 <;> first
    | (simp [Aux.rank] at h; done)
    | (rw [orda] <;> simp)

theorem Aux.orda_rank_gt (env : List (term × term)) (t1 t2 : term)
    (h : Aux.rank t2 < Aux.rank t1) : orda env t1 t2 = GREATER := by
  cases t1 <;> cases t2 <;> first
    | (simp [Aux.rank] at h; done)
    | (rw [orda] <;> simp)

theorem Aux.orda_rank_ne (env : List (term × term)) (t1 t2 : term)
    (h : Aux.rank t1 ≠ Aux.rank t2) : orda env t1 t2 ≠ EQUAL := by
  rcases Nat.lt_or_gt_of_ne h with h | h
  · rw [Aux.orda_rank_lt env t1 t2 h]; simp
  · rw [Aux.orda_rank_gt env t1 t2 h]; simp

theorem Aux.RACONV_rank {env : List (term × term)} {t1 t2 : term} (h : RACONV env (t1, t2)) :
    Aux.rank t1 = Aux.rank t2 := by
  cases h <;> rfl

/- HOL4:
Theorem RACONV_eq_orda:
   ∀env t1 t2. RACONV env (t1,t2) ⇔ orda env t1 t2 = EQUAL
-/
theorem RACONV_eq_orda :
    ∀ (env : List (term × term)) (t1 t2 : term),
      RACONV env (t1, t2) ↔ orda env t1 t2 = EQUAL := by
  have cross : ∀ (env : List (term × term)) (t1 t2 : term), Aux.rank t1 ≠ Aux.rank t2 →
      (RACONV env (t1, t2) ↔ orda env t1 t2 = EQUAL) := fun env t1 t2 h =>
    ⟨fun hr => absurd (Aux.RACONV_rank hr) h, fun ho => absurd ho (Aux.orda_rank_ne env t1 t2 h)⟩
  intro env t1
  induction t1 generalizing env with
  | Var x ty =>
    intro t2
    cases t2 with
    | Var x2 ty2 =>
      rw [Aux.orda_Var, ← ALPHAVARS_eq_ordav]
      exact ⟨fun h => by cases h; assumption, RACONV.Var⟩
    | Const => exact cross _ _ _ (by simp [Aux.rank])
    | Comb => exact cross _ _ _ (by simp [Aux.rank])
    | Abs => exact cross _ _ _ (by simp [Aux.rank])
  | Const x ty =>
    intro t2
    cases t2 with
    | Var => exact cross _ _ _ (by simp [Aux.rank])
    | Const x2 ty2 =>
      rw [Aux.orda_Const]
      refine Iff.trans ?_ (TotOrd_term_cmp.1 _ _).symm
      exact ⟨fun h => by cases h; rfl, fun h => by cases h; exact RACONV.Const⟩
    | Comb => exact cross _ _ _ (by simp [Aux.rank])
    | Abs => exact cross _ _ _ (by simp [Aux.rank])
  | Comb s t ihs iht =>
    intro t2
    cases t2 with
    | Var => exact cross _ _ _ (by simp [Aux.rank])
    | Const => exact cross _ _ _ (by simp [Aux.rank])
    | Comb s2 t2 =>
      rw [Aux.orda_Comb]
      have h1 := ihs env s2
      have h2 := iht env t2
      constructor
      · intro h
        cases h with
        | Comb ha hb => simp [h1.mp ha, h2.mp hb]
      · intro h
        by_cases hc : orda env s s2 = EQUAL
        · rw [if_neg (by simp [hc])] at h
          exact RACONV.Comb (h1.mpr hc) (h2.mpr h)
        · rw [if_pos hc] at h
          exact absurd h hc
    | Abs => exact cross _ _ _ (by simp [Aux.rank])
  | Abs v t _ iht =>
    intro t2
    cases t2 with
    | Var => exact cross _ _ _ (by simp [Aux.rank])
    | Const => exact cross _ _ _ (by simp [Aux.rank])
    | Comb => exact cross _ _ _ (by simp [Aux.rank])
    | Abs v2 t2 =>
      rw [Aux.orda_Abs]
      have h2 := iht ((v, v2) :: env) t2
      have h1 := TotOrd_type_cmp.1 (typeof v) (typeof v2)
      constructor
      · intro h
        cases h with
        | Abs ha hb => simp [h1.mpr ha, h2.mp hb]
      · intro h
        by_cases hc : type_cmp (typeof v) (typeof v2) = EQUAL
        · rw [if_neg (by simp [hc])] at h
          exact RACONV.Abs (h1.mp hc) (h2.mpr h)
        · rw [if_pos hc] at h
          exact absurd h hc

/- HOL4:
Theorem ACONV_eq_orda:
   ∀t1 t2. ACONV t1 t2 = (orda [] t1 t2 = EQUAL)
-/
theorem ACONV_eq_orda : ∀ (t1 t2 : term), ACONV t1 t2 ↔ orda [] t1 t2 = EQUAL := by
  intro t1 t2
  exact RACONV_eq_orda [] t1 t2

theorem Aux.TotOrd_flip {α : Type u} {c : comp α} (h : TotOrd c) (x y : α) :
    flip_ord (c x y) = c y x := by
  obtain ⟨h1, h2, _⟩ := h
  cases hc : c x y with
  | LESS => exact ((h2 y x).mpr hc).symm
  | EQUAL =>
    have := (h1 x y).mp hc
    subst this
    exact hc.symm
  | GREATER => exact ((h2 x y).mp hc).symm

/- HOL4:
Theorem ordav_sym:
   ∀env v1 v2. flip_ord (ordav env v1 v2) = ordav (MAP (λ(x,y). (y,x)) env) v2 v1
-/
theorem ordav_sym :
    ∀ (env : List (term × term)) (v1 v2 : term),
      flip_ord (ordav env v1 v2) =
      ordav (env.map (fun p => match p with | (x, y) => (y, x))) v2 v1 := by
  intro env v1 v2
  induction env with
  | nil => exact Aux.TotOrd_flip TotOrd_term_cmp v1 v2
  | cons p env ih =>
    obtain ⟨a, b⟩ := p
    simp only [List.map_cons, ordav]
    rw [← ih]
    by_cases h1 : v1 = a <;> by_cases h2 : v2 = b <;> simp [h1, h2, invert_comparison]

/- HOL4:
Theorem orda_sym:
   ∀env t1 t2. flip_ord (orda env t1 t2) = orda (MAP (λ(x,y). (y,x)) env) t2 t1
-/
theorem orda_sym :
    ∀ (env : List (term × term)) (t1 t2 : term),
      flip_ord (orda env t1 t2) =
      orda (env.map (fun p => match p with | (x, y) => (y, x))) t2 t1 := by
  have cross : ∀ (e1 e2 : List (term × term)) (t1 t2 : term), Aux.rank t1 ≠ Aux.rank t2 →
      flip_ord (orda e1 t1 t2) = orda e2 t2 t1 := by
    intro e1 e2 t1 t2 h
    rcases Nat.lt_or_gt_of_ne h with h | h
    · rw [Aux.orda_rank_lt e1 t1 t2 h, Aux.orda_rank_gt e2 t2 t1 h]; rfl
    · rw [Aux.orda_rank_gt e1 t1 t2 h, Aux.orda_rank_lt e2 t2 t1 h]; rfl
  have lex : ∀ a a' b b' : ordering, flip_ord a = a' → flip_ord b = b' →
      flip_ord (if a ≠ EQUAL then a else b) = if a' ≠ EQUAL then a' else b' := by
    rintro a _ b _ rfl rfl
    cases a <;> simp [invert_comparison]
  intro env t1
  induction t1 generalizing env with
  | Var x ty =>
    intro t2
    cases t2 with
    | Var x2 ty2 => rw [Aux.orda_Var, Aux.orda_Var]; exact ordav_sym _ _ _
    | Const => exact cross _ _ _ _ (by simp [Aux.rank])
    | Comb => exact cross _ _ _ _ (by simp [Aux.rank])
    | Abs => exact cross _ _ _ _ (by simp [Aux.rank])
  | Const x ty =>
    intro t2
    cases t2 with
    | Var => exact cross _ _ _ _ (by simp [Aux.rank])
    | Const x2 ty2 =>
      rw [Aux.orda_Const, Aux.orda_Const]
      exact Aux.TotOrd_flip TotOrd_term_cmp _ _
    | Comb => exact cross _ _ _ _ (by simp [Aux.rank])
    | Abs => exact cross _ _ _ _ (by simp [Aux.rank])
  | Comb s t ihs iht =>
    intro t2
    cases t2 with
    | Var => exact cross _ _ _ _ (by simp [Aux.rank])
    | Const => exact cross _ _ _ _ (by simp [Aux.rank])
    | Comb s2 t2 =>
      rw [Aux.orda_Comb, Aux.orda_Comb]
      exact lex _ _ _ _ (ihs env s2) (iht env t2)
    | Abs => exact cross _ _ _ _ (by simp [Aux.rank])
  | Abs v t _ iht =>
    intro t2
    cases t2 with
    | Var => exact cross _ _ _ _ (by simp [Aux.rank])
    | Const => exact cross _ _ _ _ (by simp [Aux.rank])
    | Comb => exact cross _ _ _ _ (by simp [Aux.rank])
    | Abs v2 t2 =>
      rw [Aux.orda_Abs, Aux.orda_Abs]
      exact lex _ _ _ _ (Aux.TotOrd_flip TotOrd_type_cmp _ _) (iht ((v, v2) :: env) t2)

/-- the transitivity property of comparison results -/
def Aux.TT (a b c : ordering) : Prop :=
  (a = EQUAL → c = b) ∧ (b = EQUAL → c = a) ∧ (a = LESS → b = LESS → c = LESS)

theorem Aux.TT_TotOrd {α : Type u} {c : comp α} (h : TotOrd c) (x y z : α) :
    Aux.TT (c x y) (c y z) (c x z) := by
  obtain ⟨h1, _, h3⟩ := h
  refine ⟨fun e => ?_, fun e => ?_, fun e1 e2 => h3 x y z ⟨e1, e2⟩⟩
  · rw [(h1 x y).mp e]
  · rw [(h1 y z).mp e]

theorem Aux.TT_lex {a b c a' b' c' : ordering} (h : Aux.TT a b c) (h' : Aux.TT a' b' c') :
    Aux.TT (if a ≠ EQUAL then a else a') (if b ≠ EQUAL then b else b')
      (if c ≠ EQUAL then c else c') := by
  unfold Aux.TT at *
  cases a <;> cases b <;> cases c <;> simp_all

theorem Aux.TT_rank (e1 e2 e3 : List (term × term)) (t1 t2 t3 : term)
    (h : ¬ (Aux.rank t1 = Aux.rank t2 ∧ Aux.rank t2 = Aux.rank t3)) :
    Aux.TT (orda e1 t1 t2) (orda e2 t2 t3) (orda e3 t1 t3) := by
  have l1 := Aux.orda_rank_lt e1 t1 t2
  have l2 := Aux.orda_rank_lt e2 t2 t3
  have l3 := Aux.orda_rank_lt e3 t1 t3
  have g1 := Aux.orda_rank_gt e1 t1 t2
  have g2 := Aux.orda_rank_gt e2 t2 t3
  have g3 := Aux.orda_rank_gt e3 t1 t3
  unfold Aux.TT
  rcases Nat.lt_trichotomy (Aux.rank t1) (Aux.rank t2) with h1 | h1 | h1 <;>
    rcases Nat.lt_trichotomy (Aux.rank t2) (Aux.rank t3) with h2 | h2 | h2
  · simp [l1 h1, l2 h2, l3 (by omega)]
  · simp [l1 h1, l3 (by omega)]
  · simp [l1 h1, g2 h2]
  · simp [l2 h2, l3 (by omega)]
  · exact absurd ⟨h1, h2⟩ h
  · simp [g2 h2, g3 (by omega)]
  · simp [g1 h1, l2 h2]
  · simp [g1 h1, g3 (by omega)]
  · simp [g1 h1, g2 h2, g3 (by omega)]

theorem Aux.ordav_TT (x y z : term) : ∀ e : List (term × term × term),
    Aux.TT (ordav (e.map (fun p => (p.1, p.2.1))) x y) (ordav (e.map (fun p => (p.2.1, p.2.2))) y z)
      (ordav (e.map (fun p => (p.1, p.2.2))) x z)
  | [] => Aux.TT_TotOrd TotOrd_term_cmp x y z
  | (a, b, c) :: e => by
    have ih := Aux.ordav_TT x y z e
    simp only [List.map_cons, ordav]
    unfold Aux.TT at *
    by_cases h1 : x = a <;> by_cases h2 : y = b <;> by_cases h3 : z = c <;> simp_all

theorem Aux.orda_TT : ∀ (x y z : term) (e : List (term × term × term)),
    Aux.TT (orda (e.map (fun p => (p.1, p.2.1))) x y) (orda (e.map (fun p => (p.2.1, p.2.2))) y z)
      (orda (e.map (fun p => (p.1, p.2.2))) x z) := by
  intro x
  induction x with
  | Var x ty =>
    intro y z e
    cases y <;> cases z <;> first
      | (apply Aux.TT_rank; simp [Aux.rank]; done)
      | (simp only [Aux.orda_Var]; exact Aux.ordav_TT _ _ _ _)
  | Const x ty =>
    intro y z e
    cases y <;> cases z <;> first
      | (apply Aux.TT_rank; simp [Aux.rank]; done)
      | (simp only [Aux.orda_Const]; exact Aux.TT_TotOrd TotOrd_term_cmp _ _ _)
  | Comb s t ihs iht =>
    intro y z e
    cases y <;> cases z <;> first
      | (apply Aux.TT_rank; simp [Aux.rank]; done)
      | (simp only [Aux.orda_Comb]; exact Aux.TT_lex (ihs _ _ e) (iht _ _ e))
  | Abs v t _ iht =>
    intro y z e
    cases y <;> cases z <;> first
      | (apply Aux.TT_rank; simp [Aux.rank]; done)
      | (rename_i v2 t2 v3 t3
         simp only [Aux.orda_Abs]
         exact Aux.TT_lex (Aux.TT_TotOrd TotOrd_type_cmp _ _ _) (iht _ _ ((v, v2, v3) :: e)))

theorem Aux.orda_TT_nil (x y z : term) : Aux.TT (orda [] x y) (orda [] y z) (orda [] x z) :=
  Aux.orda_TT x y z []

theorem Aux.alpha_lt_of_GREATER {x y : term} (h : orda [] x y = GREATER) : alpha_lt y x := by
  have := orda_sym [] x y
  rw [h] at this
  exact this.symm

/- HOL4:
Theorem transitive_alpha_lt:
   transitive alpha_lt
-/
theorem transitive_alpha_lt : transitive alpha_lt := by
  rintro x y z ⟨h1, h2⟩
  exact (Aux.orda_TT_nil x y z).2.2 h1 h2

/- HOL4:
Theorem alpha_lt_not_refl[simp]:
   ∀x. ¬alpha_lt x x
-/
theorem alpha_lt_not_refl : ∀ x : term, ¬ alpha_lt x x := by
  intro x h
  unfold alpha_lt at h
  rw [Aux.orda_refl x [] trivial] at h
  simp at h

theorem Aux.alpha_lt_of_EQUAL {x y z : term} (h1 : orda [] x y = EQUAL) (h2 : alpha_lt y z) :
    alpha_lt x z := by
  unfold alpha_lt at *
  rw [(Aux.orda_TT_nil x y z).1 h1]
  exact h2

theorem Aux.VFREE_IN_ALPHAVARS {α : Type u} (a b v : α) : ∀ env : List (α × α),
    ALPHAVARS env (a, b) →
    ((a = v ∧ ¬ (∃ y, (v, y) ∈ env)) ↔ (b = v ∧ ¬ (∃ y, (y, v) ∈ env)))
  | [], h => by
    simp only [ALPHAVARS] at h
    simp [h]
  | (x, y) :: env, h => by
    have ih := Aux.VFREE_IN_ALPHAVARS a b v env
    simp only [ALPHAVARS, Prod.mk.injEq] at h
    simp only [List.mem_cons, Prod.mk.injEq]
    grind

/- HOL4:
Theorem VFREE_IN_RACONV:
   ∀env p. RACONV env p
            ⇒ ∀x ty. VFREE_IN (Var x ty) (FST p) ∧
                     ¬(∃y. MEM (Var x ty,y) env) ⇔
                     VFREE_IN (Var x ty) (SND p) ∧
                     ¬(∃y. MEM (y,Var x ty) env)
-/
theorem VFREE_IN_RACONV :
    ∀ (env : List (term × term)) (p : term × term), RACONV env p →
      ∀ (x : mlstring) (ty : type),
        (VFREE_IN (Var x ty) p.1 ∧ ¬ (∃ y, (Var x ty, y) ∈ env)) ↔
        (VFREE_IN (Var x ty) p.2 ∧ ¬ (∃ y, (y, Var x ty) ∈ env)) := by
  intro env p h
  induction h with
  | Var ha =>
    intro x ty
    exact Aux.VFREE_IN_ALPHAVARS _ _ _ _ ha
  | Const => intro x ty; simp [VFREE_IN]
  | Comb _ _ ih1 ih2 =>
    intro x ty
    have h1 := ih1 x ty
    have h2 := ih2 x ty
    simp only [VFREE_IN] at h1 h2 ⊢
    grind
  | Abs _ _ ih =>
    intro x ty
    have h1 := ih x ty
    simp only [VFREE_IN, List.mem_cons, Prod.mk.injEq] at h1 ⊢
    grind

/- HOL4:
Theorem VFREE_IN_ACONV:
   ∀s t x ty. ACONV s t ⇒ (VFREE_IN (Var x ty) s ⇔ VFREE_IN (Var x ty) t)
-/
theorem VFREE_IN_ACONV :
    ∀ (s t : term) (x : mlstring) (ty : type),
      ACONV s t → (VFREE_IN (Var x ty) s ↔ VFREE_IN (Var x ty) t) := by
  intro s t x ty h
  have := VFREE_IN_RACONV [] (s, t) h x ty
  simpa using this

/- HOL4:
Theorem hypset_ok_nil[simp]:
   hypset_ok []
-/
theorem hypset_ok_nil : hypset_ok [] := by
  exact trivial

/- HOL4:
Theorem hypset_ok_sing[simp]:
   ∀p. hypset_ok [p]
-/
theorem hypset_ok_sing : ∀ p : term, hypset_ok [p] := by
  intro p
  exact trivial

theorem Aux.SORTED_cons {α : Type u} {R : α → α → Prop} (ht : transitive R) :
    ∀ (h : α) (l : List α), SORTED R (h :: l) ↔ EVERY (R h) l ∧ SORTED R l
  | h, [] => by simp [SORTED, EVERY]
  | h, a :: l => by
    have ih := Aux.SORTED_cons ht a l
    simp only [SORTED, EVERY]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨⟨h1, ?_⟩, h2⟩
      rw [Aux.EVERY_iff]
      intro x hx
      exact ht _ _ _ ⟨h1, Aux.EVERY_iff.mp (ih.mp h2).1 x hx⟩
    · rintro ⟨⟨h1, _⟩, h2⟩
      exact ⟨h1, h2⟩

/- HOL4:
Theorem hypset_ok_cons:
   hypset_ok (h::hs) ⇔
    EVERY (alpha_lt h) hs ∧ hypset_ok hs
-/
theorem hypset_ok_cons (h : term) (hs : List term) :
    hypset_ok (h :: hs) ↔ EVERY (alpha_lt h) hs ∧ hypset_ok hs := by
  exact Aux.SORTED_cons transitive_alpha_lt h hs

/- HOL4:
Theorem term_union_idem[simp]:
   ∀ls. term_union ls ls = ls
-/
theorem term_union_idem : ∀ ls : List term, term_union ls ls = ls := by
  intro ls
  induction ls with
  | nil => simp [term_union]
  | cons a t ih =>
    rw [term_union]
    simp [Aux.orda_refl a [] trivial, ih]

/- HOL4:
Theorem term_union_thm:
   (∀l2. term_union [] l2 = l2) ∧
    (∀l1. term_union l1 [] = l1) ∧
    (∀h1 t1 h2 t2.
          term_union (h1::t1) (h2::t2) =
          case orda [] h1 h2 of
          | EQUAL =>   h1::term_union t1 t2
          | LESS =>    h1::term_union t1 (h2::t2)
          | GREATER => h2::term_union (h1::t1) t2)
-/
theorem term_union_thm :
    (∀ l2 : List term, term_union [] l2 = l2) ∧
    (∀ l1 : List term, term_union l1 [] = l1) ∧
    (∀ (h1 : term) (t1 : List term) (h2 : term) (t2 : List term),
      term_union (h1 :: t1) (h2 :: t2) =
      match orda [] h1 h2 with
      | EQUAL => h1 :: term_union t1 t2
      | LESS => h1 :: term_union t1 (h2 :: t2)
      | GREATER => h2 :: term_union (h1 :: t1) t2) := by
  refine ⟨fun l2 => by simp [term_union], fun l1 => by cases l1 <;> simp [term_union], ?_⟩
  intro h1 t1 h2 t2
  rw [term_union]
  cases orda [] h1 h2 <;> simp

/- HOL4:
Theorem MEM_term_union_imp:
   ∀l1 l2 x. MEM x (term_union l1 l2) ⇒ MEM x l1 ∨ MEM x l2
-/
theorem MEM_term_union_imp :
    ∀ (l1 l2 : List term) (x : term), x ∈ term_union l1 l2 → x ∈ l1 ∨ x ∈ l2 := by
  intro l1
  induction l1 with
  | nil => intro l2 x h; rw [term_union_thm.1] at h; exact Or.inr h
  | cons h1 t1 ih1 =>
    intro l2
    induction l2 with
    | nil => intro x h; rw [term_union_thm.2.1] at h; exact Or.inl h
    | cons h2 t2 ih2 =>
      intro x h
      rw [term_union_thm.2.2] at h
      have a1 := ih1 t2 x
      have a2 := ih1 (h2 :: t2) x
      have a3 := ih2 x
      simp only [List.mem_cons] at a2 a3 ⊢
      cases hc : orda [] h1 h2 <;> simp only [hc, List.mem_cons] at h <;> grind

/- HOL4:
Theorem hypset_ok_term_union[simp]:
   ∀l1 l2. hypset_ok l1 ∧ hypset_ok l2 ⇒
            hypset_ok (term_union l1 l2)
-/
theorem hypset_ok_term_union :
    ∀ (l1 l2 : List term), hypset_ok l1 ∧ hypset_ok l2 →
      hypset_ok (term_union l1 l2) := by
  intro l1
  induction l1 with
  | nil => rintro l2 ⟨_, h⟩; rw [term_union_thm.1]; exact h
  | cons h1 t1 ih1 =>
    intro l2
    induction l2 with
    | nil => rintro ⟨h, _⟩; rw [term_union_thm.2.1]; exact h
    | cons h2 t2 ih2 =>
      rintro ⟨ha, hb⟩
      have ha' := (hypset_ok_cons h1 t1).mp ha
      have hb' := (hypset_ok_cons h2 t2).mp hb
      have hae := Aux.EVERY_iff.mp ha'.1
      have hbe := Aux.EVERY_iff.mp hb'.1
      have ht := transitive_alpha_lt
      rw [term_union_thm.2.2]
      cases hc : orda [] h1 h2 with
      | EQUAL =>
        refine (hypset_ok_cons _ _).mpr ⟨Aux.EVERY_iff.mpr fun x hx => ?_, ih1 t2 ⟨ha'.2, hb'.2⟩⟩
        rcases MEM_term_union_imp _ _ _ hx with h | h
        · exact hae x h
        · exact Aux.alpha_lt_of_EQUAL hc (hbe x h)
      | LESS =>
        refine (hypset_ok_cons _ _).mpr
          ⟨Aux.EVERY_iff.mpr fun x hx => ?_, ih1 (h2 :: t2) ⟨ha'.2, hb⟩⟩
        rcases MEM_term_union_imp _ _ _ hx with h | h
        · exact hae x h
        · rcases List.mem_cons.mp h with h | h
          · rw [h]; exact hc
          · exact ht _ _ _ ⟨hc, hbe x h⟩
      | GREATER =>
        have hc' := Aux.alpha_lt_of_GREATER hc
        refine (hypset_ok_cons _ _).mpr ⟨Aux.EVERY_iff.mpr fun x hx => ?_, ih2 ⟨ha, hb'.2⟩⟩
        rcases MEM_term_union_imp _ _ _ hx with h | h
        · rcases List.mem_cons.mp h with h | h
          · rw [h]; exact hc'
          · exact ht _ _ _ ⟨hc', hae x h⟩
        · exact hbe x h

/- HOL4:
Theorem EVERY_term_union:
   EVERY P l1 ∧ EVERY P l2 ⇒ EVERY P (term_union l1 l2)
-/
theorem EVERY_term_union (P : term → Prop) (l1 l2 : List term) :
    EVERY P l1 ∧ EVERY P l2 → EVERY P (term_union l1 l2) := by
  rintro ⟨h1, h2⟩
  rw [Aux.EVERY_iff] at *
  intro x hx
  rcases MEM_term_union_imp _ _ _ hx with h | h
  · exact h1 x h
  · exact h2 x h

theorem Aux.MEM_term_union : ∀ (l1 l2 : List term) (t : term), (t ∈ l1 ∨ t ∈ l2) →
    ∃ y, y ∈ term_union l1 l2 ∧ ACONV t y := by
  intro l1
  induction l1 with
  | nil =>
    intro l2 t h
    rw [term_union_thm.1]
    exact ⟨t, by simpa using h, ACONV_REFL t⟩
  | cons h1 t1 ih1 =>
    intro l2
    induction l2 with
    | nil =>
      intro t h
      rw [term_union_thm.2.1]
      exact ⟨t, by simpa using h, ACONV_REFL t⟩
    | cons h2 t2 ih2 =>
      intro t h
      rw [term_union_thm.2.2]
      have mono : ∀ (a : term) (l : List term), (∃ y, y ∈ l ∧ ACONV t y) →
          ∃ y, y ∈ a :: l ∧ ACONV t y :=
        fun a l ⟨y, hy, ha⟩ => ⟨y, List.mem_cons_of_mem _ hy, ha⟩
      simp only [List.mem_cons] at h
      cases hc : orda [] h1 h2 with
      | EQUAL =>
        have hac := ACONV_SYM _ _ ((ACONV_eq_orda h1 h2).mpr hc)
        rcases h with (rfl | h) | (rfl | h)
        · exact ⟨t, List.mem_cons_self, ACONV_REFL t⟩
        · exact mono _ _ (ih1 t2 t (Or.inl h))
        · exact ⟨h1, List.mem_cons_self, hac⟩
        · exact mono _ _ (ih1 t2 t (Or.inr h))
      | LESS =>
        rcases h with (rfl | h) | h
        · exact ⟨t, List.mem_cons_self, ACONV_REFL t⟩
        · exact mono _ _ (ih1 _ t (Or.inl h))
        · exact mono _ _ (ih1 _ t (Or.inr (List.mem_cons.mpr h)))
      | GREATER =>
        rcases h with h | (rfl | h)
        · exact mono _ _ (ih2 t (Or.inl (List.mem_cons.mpr h)))
        · exact ⟨t, List.mem_cons_self, ACONV_REFL t⟩
        · exact mono _ _ (ih2 t (Or.inr h))

/- HOL4:
Theorem MEM_term_union:
   ∀h1 h2 t. hypset_ok h1 ∧ hypset_ok h2 ∧ (MEM t h1 ∨ MEM t h2) ⇒
      ∃y. MEM y (term_union h1 h2) ∧ ACONV t y
-/
theorem MEM_term_union :
    ∀ (h1 h2 : List term) (t : term), hypset_ok h1 ∧ hypset_ok h2 ∧ (t ∈ h1 ∨ t ∈ h2) →
      ∃ y, y ∈ term_union h1 h2 ∧ ACONV t y := by
  rintro h1 h2 t ⟨_, _, h⟩
  exact Aux.MEM_term_union h1 h2 t h

/- HOL4:
Theorem term_remove_nil[simp]:
   ∀a. term_remove a [] = []
-/
theorem term_remove_nil : ∀ a : term, term_remove a [] = [] := by
  intro a
  simp [term_remove]

theorem Aux.term_remove_cons (t s : term) (ss : List term) :
    term_remove t (s :: ss) =
      match orda [] t s with
      | GREATER => s :: term_remove t ss
      | EQUAL => ss
      | LESS => s :: ss := by
  rw [term_remove]
  cases orda [] t s <;> simp
  exact fun h => h.symm

/- HOL4:
Theorem MEM_term_remove_imp:
   ∀ls x t. MEM t (term_remove x ls) ⇒
      MEM t ls ∧ (hypset_ok ls ⇒ ¬ACONV x t)
-/
theorem MEM_term_remove_imp :
    ∀ (ls : List term) (x t : term), t ∈ term_remove x ls →
      t ∈ ls ∧ (hypset_ok ls → ¬ ACONV x t) := by
  intro ls x t
  have hne : ∀ {y z : term}, alpha_lt y z → ¬ ACONV y z := by
    intro y z h ha
    rw [ACONV_eq_orda, h] at ha
    simp at ha
  induction ls with
  | nil => intro h; simp [term_remove] at h
  | cons s ss ih =>
    intro h
    rw [Aux.term_remove_cons] at h
    cases hc : orda [] x s with
    | GREATER =>
      simp only [hc] at h
      rcases List.mem_cons.mp h with h | h
      · subst h
        refine ⟨List.mem_cons_self, fun _ ha => ?_⟩
        rw [ACONV_eq_orda, hc] at ha
        simp at ha
      · obtain ⟨h1, h2⟩ := ih h
        exact ⟨List.mem_cons_of_mem _ h1, fun hk => h2 ((hypset_ok_cons _ _).mp hk).2⟩
    | EQUAL =>
      simp only [hc] at h
      refine ⟨List.mem_cons_of_mem _ h, fun hk => ?_⟩
      exact hne (Aux.alpha_lt_of_EQUAL hc (Aux.EVERY_iff.mp ((hypset_ok_cons _ _).mp hk).1 t h))
    | LESS =>
      simp only [hc] at h
      refine ⟨h, fun hk => ?_⟩
      rcases List.mem_cons.mp h with h | h
      · rw [h]; exact hne hc
      · exact hne (transitive_alpha_lt _ _ _
          ⟨hc, Aux.EVERY_iff.mp ((hypset_ok_cons _ _).mp hk).1 t h⟩)

/- HOL4:
Theorem hypset_ok_term_remove[simp]:
   ∀ls. hypset_ok ls ⇒ ∀t. hypset_ok (term_remove t ls)
-/
theorem hypset_ok_term_remove :
    ∀ ls : List term, hypset_ok ls → ∀ t : term, hypset_ok (term_remove t ls) := by
  intro ls h t
  induction ls with
  | nil => rw [term_remove_nil]; exact h
  | cons s ss ih =>
    have h' := (hypset_ok_cons _ _).mp h
    rw [Aux.term_remove_cons]
    cases hc : orda [] t s with
    | GREATER =>
      refine (hypset_ok_cons _ _).mpr ⟨Aux.EVERY_iff.mpr fun x hx => ?_, ih h'.2⟩
      exact Aux.EVERY_iff.mp h'.1 x (MEM_term_remove_imp _ _ _ hx).1
    | EQUAL => exact h'.2
    | LESS => exact h

/- HOL4:
Theorem EVERY_term_remove:
   EVERY P ls ⇒ EVERY P (term_remove t ls)
-/
theorem EVERY_term_remove (P : term → Prop) (ls : List term) (t : term) :
    EVERY P ls → EVERY P (term_remove t ls) := by
  intro h
  rw [Aux.EVERY_iff] at *
  intro x hx
  exact h x (MEM_term_remove_imp _ _ _ hx).1

theorem Aux.MEM_term_remove (x t : term) (hn : ¬ ACONV x t) :
    ∀ ls : List term, t ∈ ls → t ∈ term_remove x ls := by
  intro ls
  induction ls with
  | nil => intro h; simp at h
  | cons s ss ih =>
    intro h
    rw [Aux.term_remove_cons]
    cases hc : orda [] x s with
    | GREATER =>
      rcases List.mem_cons.mp h with h | h
      · rw [h]; exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih h)
    | EQUAL =>
      rcases List.mem_cons.mp h with h | h
      · subst h; exact absurd ((ACONV_eq_orda _ _).mpr hc) hn
      · exact h
    | LESS => exact h

/- HOL4:
Theorem MEM_term_remove:
   ∀h x t. MEM t h ∧ ¬ACONV x t ∧ hypset_ok h
    ⇒ MEM t (term_remove x h)
-/
theorem MEM_term_remove :
    ∀ (h : List term) (x t : term), t ∈ h ∧ ¬ ACONV x t ∧ hypset_ok h →
      t ∈ term_remove x h := by
  rintro h x t ⟨h1, h2, _⟩
  exact Aux.MEM_term_remove x t h2 h h1

/- HOL4:
Theorem term_image_nil[simp]:
   term_image f [] = []
-/
theorem term_image_nil (f : term → term) : term_image f [] = [] := by
  simp [term_image]

theorem Aux.term_image_cons (f : term → term) (h : term) (t : List term) :
    term_image f (h :: t) =
      if f h = h ∧ term_image f t = t then h :: t else term_union [f h] (term_image f t) := by
  rw [term_image]

/- HOL4:
Theorem MEM_term_image_imp:
   ∀ls f t. MEM t (term_image f ls) ⇒ ∃x. MEM x ls ∧ t = f x
-/
theorem MEM_term_image_imp :
    ∀ (ls : List term) (f : term → term) (t : term), t ∈ term_image f ls →
      ∃ x, x ∈ ls ∧ t = f x := by
  intro ls f t
  induction ls with
  | nil => intro h; simp [term_image] at h
  | cons a l ih =>
    intro h
    rw [Aux.term_image_cons] at h
    have step : t ∈ term_image f l → ∃ x, x ∈ a :: l ∧ t = f x := by
      intro h
      obtain ⟨x, h1, h2⟩ := ih h
      exact ⟨x, List.mem_cons_of_mem _ h1, h2⟩
    split at h
    · rename_i hc
      rcases List.mem_cons.mp h with h | h
      · exact ⟨a, List.mem_cons_self, by rw [hc.1, h]⟩
      · exact step (by rw [hc.2]; exact h)
    · rcases MEM_term_union_imp _ _ _ h with h | h
      · exact ⟨a, List.mem_cons_self, by simpa using h⟩
      · exact step h

/- HOL4:
Theorem hypset_ok_term_image:
   ∀ls f. hypset_ok ls ⇒ hypset_ok (term_image f ls)
-/
theorem hypset_ok_term_image :
    ∀ (ls : List term) (f : term → term), hypset_ok ls → hypset_ok (term_image f ls) := by
  intro ls f
  induction ls with
  | nil => intro h; rw [term_image_nil]; exact h
  | cons a l ih =>
    intro h
    rw [Aux.term_image_cons]
    split
    · exact h
    · exact hypset_ok_term_union _ _
        ⟨hypset_ok_sing _, ih ((hypset_ok_cons _ _).mp h).2⟩

theorem Aux.MEM_term_image (f : term → term) (t : term) : ∀ ls : List term, t ∈ ls →
    ∃ y, y ∈ term_image f ls ∧ ACONV (f t) y := by
  intro ls
  induction ls with
  | nil => intro h; simp at h
  | cons a l ih =>
    intro h
    rw [Aux.term_image_cons]
    split
    · rename_i hc
      rcases List.mem_cons.mp h with h | h
      · exact ⟨a, List.mem_cons_self, by rw [h, hc.1]; exact ACONV_REFL a⟩
      · obtain ⟨y, h1, h2⟩ := ih h
        exact ⟨y, List.mem_cons_of_mem _ (by rw [← hc.2]; exact h1), h2⟩
    · rcases List.mem_cons.mp h with h | h
      · subst h
        exact Aux.MEM_term_union _ _ _ (Or.inl (by simp))
      · obtain ⟨y, h1, h2⟩ := ih h
        obtain ⟨z, h3, h4⟩ := Aux.MEM_term_union [f a] _ y (Or.inr h1)
        exact ⟨z, h3, ACONV_TRANS _ _ _ ⟨h2, h4⟩⟩

/- HOL4:
Theorem MEM_term_image:
   ∀ls f t. MEM t ls ∧ hypset_ok ls ⇒ ∃y. MEM y (term_image f ls) ∧ ACONV (f t) y
-/
theorem MEM_term_image :
    ∀ (ls : List term) (f : term → term) (t : term), t ∈ ls ∧ hypset_ok ls →
      ∃ y, y ∈ term_image f ls ∧ ACONV (f t) y := by
  rintro ls f t ⟨h, _⟩
  exact Aux.MEM_term_image f t ls h

/- HOL4:
Theorem VSUBST_HAS_TYPE:
   ∀tm ty ilist.
      tm has_type ty ∧
      (∀s s'. MEM (s',s) ilist ⇒ ∃x ty. (s = Var x ty) ∧ s' has_type ty)
      ⇒ (VSUBST ilist tm) has_type ty
-/
theorem VSUBST_HAS_TYPE :
    ∀ (tm : term) (ty : type) (ilist : List (term × term)),
      has_type tm ty ∧
      (∀ s s', (s', s) ∈ ilist → ∃ x ty, s = Var x ty ∧ has_type s' ty) →
      has_type (VSUBST ilist tm) ty := by
  intro tm
  induction tm with
  | Var x ty' =>
    rintro ty ilist ⟨h1, h2⟩
    cases h1
    simp only [VSUBST]
    rcases REV_ASSOCD_MEM ilist (Var x ty') (Var x ty') with h | h
    · obtain ⟨x', ty', e, h3⟩ := h2 _ _ h
      cases e
      exact h3
    · rw [h]; exact has_type.Var
  | Const x ty' =>
    rintro ty ilist ⟨h1, h2⟩
    exact h1
  | Comb s t ihs iht =>
    rintro ty ilist ⟨h1, h2⟩
    obtain ⟨dty, h3, h4⟩ := Aux.has_type_Comb h1
    exact has_type.Comb (ihs _ _ ⟨h3, h2⟩) (iht _ _ ⟨h4, h2⟩)
  | Abs v t _ iht =>
    rintro ty ilist ⟨h1, h2⟩
    obtain ⟨n, dty, rty, rfl, rfl, h3⟩ := Aux.has_type_Abs h1
    have h4 : ∀ s s', (s', s) ∈ FILTER (fun p : term × term => ¬ p.2 = Var n dty) ilist →
        ∃ x ty, s = Var x ty ∧ has_type s' ty := by
      intro s s' hm
      exact h2 s s' (Aux.mem_FILTER.mp hm).1
    simp only [VSUBST, dest_var_def]
    split
    · apply has_type.Abs
      refine iht _ _ ⟨h3, fun s s' hm => ?_⟩
      rcases List.mem_cons.mp hm with hm | hm
      · cases hm
        exact ⟨n, dty, rfl, has_type.Var⟩
      · exact h4 s s' hm
    · exact has_type.Abs (iht _ _ ⟨h3, h4⟩)

/- HOL4:
Theorem VSUBST_WELLTYPED:
   ∀tm ty ilist.
      welltyped tm ∧
      (∀s s'. MEM (s',s) ilist ⇒ ∃x ty. (s = Var x ty) ∧ s' has_type ty)
      ⇒ welltyped (VSUBST ilist tm)
-/
theorem VSUBST_WELLTYPED :
    ∀ (tm : term) (ty : type) (ilist : List (term × term)),
      welltyped tm ∧
      (∀ s s', (s', s) ∈ ilist → ∃ x ty, s = Var x ty ∧ has_type s' ty) →
      welltyped (VSUBST ilist tm) := by
  rintro tm _ ilist ⟨⟨ty, h⟩, h2⟩
  exact ⟨ty, VSUBST_HAS_TYPE tm ty ilist ⟨h, h2⟩⟩

end

end Candle
