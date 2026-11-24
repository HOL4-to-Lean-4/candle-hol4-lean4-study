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
  IN_INFINITE_NOT_FINITE
  |> Q.ISPECL[`UNIV:string set`,`s:string set`]
  |> REWRITE_RULE[INST_TYPE[alpha|->``:char``]INFINITE_LIST_UNIV,IN_UNIV]
  |> SIMP_RULE(srw_ss())[GSYM RIGHT_EXISTS_IMP_THM]
  |> Q.GEN`s`
  |> SIMP_RULE(srw_ss())[SKOLEM_THM])
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

/-! Auxiliary lemmas (namespace `Candle.Aux`). -/

theorem Aux.type_ind {P : type → Prop} (h1 : ∀ v, P (Tyvar v))
    (h2 : ∀ n tys, (∀ t, t ∈ tys → P t) → P (Tyapp n tys)) : ∀ ty, P ty
  | Tyvar v => h1 v
  | Tyapp n tys => h2 n tys (fun t ht => by
      have : sizeOf t < sizeOf (Tyapp n tys) := by
        have := List.sizeOf_lt_of_mem ht
        simp only [type.Tyapp.sizeOf_spec]; omega
      exact Aux.type_ind h1 h2 t)
termination_by ty => sizeOf ty

theorem Aux.mem_tyvars_Tyapp (x n : mlstring) (tys : List type) :
    x ∈ tyvars (Tyapp n tys) ↔ ∃ a, a ∈ tys ∧ x ∈ tyvars a := by
  rw [tyvars, MEM_FOLDR_LIST_UNION]
  simp

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
  intro ls f x ty h
  induction ls with
  | nil => rfl
  | cons p t ih =>
    obtain ⟨s, a⟩ := p
    obtain ⟨⟨x', ty', rfl⟩, h2⟩ := h
    simp only [List.map_cons, PAIR_MAP, ALOOKUP, dest_var_def, Prod.mk.injEq, term.Var.injEq]
    by_cases hc : x' = x ∧ ty' = ty
    · simp [hc]
    · simp only [hc, if_false]
      exact ih h2

/- HOL4:
Theorem TYPE_SUBST_NIL[simp]:
   ∀ty. TYPE_SUBST [] ty = ty
-/
theorem TYPE_SUBST_NIL : ∀ ty : type, TYPE_SUBST [] ty = ty := by
  intro ty
  induction ty using Aux.type_ind with
  | h1 v => simp only [TYPE_SUBST, REV_ASSOCD]
  | h2 n tys ih =>
    rw [TYPE_SUBST]
    congr 1
    rw [MAP_EQ_ID]
    exact ih

/- HOL4:
Theorem TYPE_SUBST_Bool:
   ∀tyin. TYPE_SUBST tyin Bool = Bool
-/
theorem TYPE_SUBST_Bool : ∀ tyin : List (type × type), TYPE_SUBST tyin BoolTy = BoolTy := by
  intro tyin
  rw [TYPE_SUBST]
  rfl

theorem Aux.TYPE_SUBST_Fun (i : List (type × type)) (a b : type) :
    TYPE_SUBST i (Fun a b) = Fun (TYPE_SUBST i a) (TYPE_SUBST i b) := by
  rw [TYPE_SUBST]
  rfl

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
  funext p
  rfl

/- HOL4:
Theorem ff_def:
   ∀f g. (f ## g) = λ(x,y). (f x, g y)
-/
theorem ff_def {α : Type u} {β : Type v} {γ : Type w} {δ : Type x} :
    ∀ (f : α → β) (g : γ → δ),
      PAIR_MAP f g = (fun (p : α × γ) => match p with | (x, y) => (f x, g y)) := by
  intro f g
  funext p
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
  | h1 v =>
    rw [TYPE_SUBST.eq_1 tyin1, TYPE_SUBST.eq_1 (_ ++ _)]
    induction tyin1 with
    | nil => simp only [REV_ASSOCD, List.map_nil, List.nil_append, TYPE_SUBST]
    | cons p t ih =>
      obtain ⟨a, b⟩ := p
      by_cases h : b = Tyvar v
      · simp [REV_ASSOCD, PAIR_MAP, h]
      · simp only [REV_ASSOCD, List.map_cons, List.cons_append, PAIR_MAP, I, h, if_false]
        exact ih
  | h2 n tys ih =>
    rw [TYPE_SUBST, TYPE_SUBST, TYPE_SUBST, List.map_map]
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
  induction ty using Aux.type_ind with
  | h1 v =>
    simp only [TYPE_SUBST, tyvars, List.mem_singleton, forall_eq]
    exact eq_comm
  | h2 n tys ih =>
    rw [TYPE_SUBST, TYPE_SUBST]
    simp only [type.Tyapp.injEq, true_and, List.map_inj_left, Aux.mem_tyvars_Tyapp]
    constructor
    · rintro h x ⟨a, ha, hx⟩
      exact (ih a ha).mp (h a ha) x hx
    · intro h a ha
      exact (ih a ha).mpr (fun x hx => h x ⟨a, ha, hx⟩)

/- HOL4:
Theorem WELLTYPED_LEMMA:
   ∀tm ty. tm has_type ty ⇒ (typeof tm = ty)
-/
theorem WELLTYPED_LEMMA : ∀ (tm : term) (ty : type), has_type tm ty → typeof tm = ty := by
  intro tm ty h
  induction h with
  | Var => rfl
  | Const => rfl
  | Comb _ _ ih1 _ => rw [typeof, ih1]; rfl
  | Abs _ ih => rw [typeof, ih]; rfl

/- HOL4:
Theorem WELLTYPED:
   ∀tm. welltyped tm ⇔ tm has_type (typeof tm)
-/
theorem WELLTYPED : ∀ tm : term, welltyped tm ↔ has_type tm (typeof tm) := by
  intro tm
  exact ⟨fun ⟨ty, h⟩ => by rw [WELLTYPED_LEMMA _ _ h]; exact h, fun h => ⟨_, h⟩⟩

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
  refine ⟨fun n ty => ⟨ty, has_type.Var⟩, fun n ty => ⟨ty, has_type.Const⟩, fun s t => ?_, fun v t => ?_⟩
  · constructor
    · rintro ⟨rty, h⟩
      cases h with
      | Comb h1 h2 =>
        exact ⟨⟨_, h1⟩, ⟨_, h2⟩, rty, by rw [WELLTYPED_LEMMA _ _ h1, WELLTYPED_LEMMA _ _ h2]⟩
    · rintro ⟨hs, ht, rty, e⟩
      have hs' := (WELLTYPED s).mp hs
      rw [e] at hs'
      exact ⟨rty, has_type.Comb hs' ((WELLTYPED t).mp ht)⟩
  · constructor
    · rintro ⟨ty, h⟩
      cases h with
      | Abs h => exact ⟨_, _, rfl, _, h⟩
    · rintro ⟨n, ty, rfl, rty, h⟩
      exact ⟨_, has_type.Abs h⟩

theorem Aux.welltyped_Comb {s t : term} : welltyped (Comb s t) ↔
    welltyped s ∧ welltyped t ∧ ∃ rty, typeof s = Fun (typeof t) rty := WELLTYPED_CLAUSES.2.2.1 s t

theorem Aux.welltyped_Abs {v t : term} : welltyped (Abs v t) ↔ ∃ n ty, v = Var n ty ∧ welltyped t :=
  WELLTYPED_CLAUSES.2.2.2 v t

theorem Aux.welltyped_Var {n : mlstring} {ty : type} : welltyped (Var n ty) := ⟨ty, has_type.Var⟩

theorem Aux.welltyped_Const {n : mlstring} {ty : type} : welltyped (Const n ty) := ⟨ty, has_type.Const⟩

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
  refine ⟨⟨?_, RACONV.Var⟩, ⟨?_, False.elim⟩, ⟨?_, False.elim⟩, ⟨?_, False.elim⟩, ⟨?_, False.elim⟩,
    ⟨?_, ?_⟩, ⟨?_, False.elim⟩, ⟨?_, False.elim⟩, ⟨?_, False.elim⟩, ⟨?_, False.elim⟩,
    ⟨?_, fun h => RACONV.Comb h.1 h.2⟩, ⟨?_, False.elim⟩, ⟨?_, False.elim⟩, ⟨?_, False.elim⟩,
    ⟨?_, False.elim⟩, ⟨?_, fun h => RACONV.Abs h.1 h.2⟩⟩
  case refine_7 => rintro ⟨rfl, rfl⟩; exact RACONV.Const
  all_goals (intro h; cases h)
  · assumption
  · exact ⟨rfl, rfl⟩
  · exact ⟨by assumption, by assumption⟩
  · exact ⟨by assumption, by assumption⟩

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
  | Comb a b iha ihb => intro env h; exact RACONV.Comb (iha env h) (ihb env h)
  | Abs v b _ ihb => intro env h; exact RACONV.Abs rfl (ihb ((v, v) :: env) ⟨rfl, h⟩)

/- HOL4:
Theorem ACONV_REFL[simp]:
   ∀t. ACONV t t
-/
theorem ACONV_REFL : ∀ t : term, ACONV t t := by
  intro t
  exact RACONV_REFL t [] trivial

theorem Aux.ALPHAVARS_trans {α : Type u} : ∀ (env : List (α × α)) (vs : List α) (s t u : α),
    vs.length = env.length → ALPHAVARS env (s, t) →
    ALPHAVARS (ZIP (env.map Prod.snd, vs)) (t, u) → ALPHAVARS (ZIP (env.map Prod.fst, vs)) (s, u)
  | [], _, s, t, u, _, h1, h2 => by
    simp only [List.map_nil, ZIP, ALPHAVARS] at h1 h2 ⊢
    exact h1.trans h2
  | _ :: _, [], _, _, _, hl, _, _ => by simp at hl
  | (a, b) :: env, c :: vs, s, t, u, hl, h1, h2 => by
    simp only [List.map_cons, ZIP, ALPHAVARS, Prod.mk.injEq] at h1 h2 ⊢
    have ih := Aux.ALPHAVARS_trans env vs s t u (by simpa using hl)
    rcases h1 with ⟨rfl, rfl⟩ | ⟨ha, hb, h1⟩
    · rcases h2 with ⟨_, rfl⟩ | ⟨h2, _⟩
      · exact Or.inl ⟨rfl, rfl⟩
      · exact absurd rfl h2
    · rcases h2 with ⟨rfl, _⟩ | ⟨_, hc, h2⟩
      · exact absurd rfl hb
      · exact Or.inr ⟨ha, hc, ih h1 h2⟩

theorem Aux.ALPHAVARS_sym {α : Type u} (env : List (α × α)) (s t : α) (h : ALPHAVARS env (s, t)) :
    ALPHAVARS (env.map (fun p => match p with | (x, y) => (y, x))) (t, s) := by
  induction env with
  | nil => exact Eq.symm h
  | cons p env ih =>
    obtain ⟨a, b⟩ := p
    simp only [List.map_cons, ALPHAVARS, Prod.mk.injEq] at h ⊢
    rcases h with ⟨rfl, rfl⟩ | ⟨ha, hb, h⟩
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr ⟨hb, ha, ih h⟩

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
    rintro vs t ⟨hl, h2⟩
    cases h2 with
    | Var hb => exact RACONV.Var (Aux.ALPHAVARS_trans _ vs _ _ _ hl ha hb)
  | Const =>
    rintro vs t ⟨hl, h2⟩
    cases h2 with
    | Const => exact RACONV.Const
  | Comb _ _ ih1 ih2 =>
    rintro vs t ⟨hl, h2⟩
    cases h2 with
    | Comb ha hb => exact RACONV.Comb (ih1 vs _ ⟨hl, ha⟩) (ih2 vs _ ⟨hl, hb⟩)
  | Abs e _ ih =>
    rintro vs t ⟨hl, h2⟩
    cases h2 with
    | @Abs _ _ v3 _ t3 e2 h2 =>
      refine RACONV.Abs (e.trans e2) ?_
      have := ih (v3 :: vs) t3 ⟨by simp [hl], by simpa [ZIP] using h2⟩
      simpa [ZIP] using this

/- HOL4:
Theorem ACONV_TRANS:
   ∀t1 t2 t3. ACONV t1 t2 ∧ ACONV t2 t3 ⇒ ACONV t1 t3
-/
theorem ACONV_TRANS : ∀ (t1 t2 t3 : term), ACONV t1 t2 ∧ ACONV t2 t3 → ACONV t1 t3 := by
  rintro t1 t2 t3 ⟨h1, h2⟩
  have e : ZIP (([] : List (term × term)).map Prod.snd, ([] : List term)) = [] := by simp [ZIP]
  have e2 : ZIP (([] : List (term × term)).map Prod.fst, ([] : List term)) = [] := by simp [ZIP]
  have h := RACONV_TRANS [] (t1, t2) h1 [] t3 ⟨rfl, by rw [e]; exact h2⟩
  rw [e2] at h
  exact h

/- HOL4:
Theorem RACONV_SYM:
   ∀env tp. RACONV env tp ⇒ RACONV (MAP (λ(x,y). (y,x)) env) (SND tp,FST tp)
-/
theorem RACONV_SYM :
    ∀ (env : List (term × term)) (tp : term × term), RACONV env tp →
      RACONV (env.map (fun p => match p with | (x, y) => (y, x))) (tp.2, tp.1) := by
  intro env tp h
  induction h with
  | Var ha => exact RACONV.Var (Aux.ALPHAVARS_sym _ _ _ ha)
  | Const => exact RACONV.Const
  | Comb _ _ ih1 ih2 => exact RACONV.Comb ih1 ih2
  | Abs e _ ih => exact RACONV.Abs e.symm ih

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
  rintro env s t ⟨h, he, _, _⟩
  rcases ALPHAVARS_MEM env (s, t) h with h | h
  · exact ((Aux.EVERY_iff _ _).mp he _ h).2.2
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
  | Var ha => rintro ⟨he, h1, h2⟩; exact ALPHAVARS_TYPE _ _ _ ⟨ha, he, h1, h2⟩
  | Const => intro _; rfl
  | Comb _ _ ih1 _ =>
    rintro ⟨he, h1, h2⟩
    exact congrArg codomain (ih1 ⟨he, (Aux.welltyped_Comb.mp h1).1, (Aux.welltyped_Comb.mp h2).1⟩)
  | Abs e _ ih =>
    rintro ⟨he, h1, h2⟩
    obtain ⟨n1, ty1, rfl, w1⟩ := Aux.welltyped_Abs.mp h1
    obtain ⟨n2, ty2, rfl, w2⟩ := Aux.welltyped_Abs.mp h2
    have := ih ⟨⟨⟨Aux.welltyped_Var, Aux.welltyped_Var, e⟩, he⟩, w1, w2⟩
    simp only [typeof] at this e ⊢
    rw [this, e]

/- HOL4:
Theorem ACONV_TYPE:
   ∀s t. ACONV s t ⇒ welltyped s ∧ welltyped t ⇒ (typeof s = typeof t)
-/
theorem ACONV_TYPE :
    ∀ (s t : term), ACONV s t → welltyped s ∧ welltyped t → typeof s = typeof t := by
  intro s t h hw
  exact RACONV_TYPE [] (s, t) h ⟨trivial, hw⟩

theorem Aux.RTC_cases2 {α : Type u} {R : α → α → Prop} {x z : α} (h : RTC R x z) :
    x = z ∨ ∃ y, RTC R x y ∧ R y z := by
  induction h with
  | refl x => exact Or.inl rfl
  | step x y z hxy _ ih =>
    rcases ih with rfl | ⟨w, hw, hwz⟩
    · exact Or.inr ⟨x, RTC.refl x, hxy⟩
    · exact Or.inr ⟨w, RTC.step x y w hxy hw, hwz⟩

/- HOL4:
Theorem subtype_Tyvar[simp] =
  ``ty subtype (Tyvar x)``
  |> SIMP_CONV(srw_ss()++boolSimps.DNF_ss)
      [Once relationTheory.RTC_CASES2,subtype1_cases]
   (resulting theorem: ⊢ ty subtype Tyvar x ⇔ ty = Tyvar x,
    with ty and x free) -/
theorem subtype_Tyvar (ty : type) (x : mlstring) : subtype ty (Tyvar x) ↔ ty = Tyvar x := by
  constructor
  · intro h
    rcases Aux.RTC_cases2 h with h | ⟨y, _, h⟩
    · exact h
    · cases h
  · rintro rfl; exact RTC.refl _

/- HOL4:
Theorem subterm_Var[simp] =
  ``tm subterm (Var x ty)``
  |> SIMP_CONV(srw_ss()++boolSimps.DNF_ss)
      [Once relationTheory.RTC_CASES2,subterm1_cases]
   (resulting theorem: ⊢ tm subterm Var x ty ⇔ tm = Var x ty,
    with tm, x and ty free) -/
theorem subterm_Var (tm : term) (x : mlstring) (ty : type) :
    subterm tm (Var x ty) ↔ tm = Var x ty := by
  constructor
  · intro h
    rcases Aux.RTC_cases2 h with h | ⟨y, _, h⟩
    · exact h
    · cases h
  · rintro rfl; exact RTC.refl _

/- HOL4:
Theorem subterm_Const[simp] =
  ``tm subterm (Const x ty)``
  |> SIMP_CONV(srw_ss()++boolSimps.DNF_ss)
      [Once relationTheory.RTC_CASES2,subterm1_cases]
   (resulting theorem: ⊢ tm subterm Const x ty ⇔ tm = Const x ty,
    with tm, x and ty free) -/
theorem subterm_Const (tm : term) (x : mlstring) (ty : type) :
    subterm tm (Const x ty) ↔ tm = Const x ty := by
  constructor
  · intro h
    rcases Aux.RTC_cases2 h with h | ⟨y, _, h⟩
    · exact h
    · cases h
  · rintro rfl; exact RTC.refl _

theorem Aux.LLEX_cons {α : Type u} (R : α → α → Prop) (a b : α) (s t : List α) :
    LLEX R (a :: s) (b :: t) ↔ R a b ∨ (a = b ∧ LLEX R s t) := by
  simp only [LLEX]
  by_cases h1 : R a b
  · simp [h1]
  · by_cases h2 : a = b
    · subst h2; simp [h1]
    · simp [h1, h2]

theorem Aux.LLEX_nil {α : Type u} (R : α → α → Prop) (l : List α) : LLEX R l [] ↔ False := by
  cases l <;> simp [LLEX]

theorem Aux.LLEX_mono {α : Type u} {R S : α → α → Prop} (h : ∀ x y, R x y → S x y) :
    ∀ l1 l2 : List α, LLEX R l1 l2 → LLEX S l1 l2
  | [], l2, h1 => by simpa [LLEX] using h1
  | a :: s, [], h1 => by simp [LLEX] at h1
  | a :: s, b :: t, h1 => by
    rw [Aux.LLEX_cons] at h1 ⊢
    rcases h1 with h1 | ⟨h1, h2⟩
    · exact Or.inl (h _ _ h1)
    · exact Or.inr ⟨h1, Aux.LLEX_mono h s t h2⟩

theorem Aux.LLEX_irrefl {α : Type u} {R : α → α → Prop} :
    ∀ l : List α, (∀ a, a ∈ l → ¬ R a a) → ¬ LLEX R l l
  | [], _ => by simp [LLEX]
  | a :: s, h => by
    rw [Aux.LLEX_cons]
    rintro (h1 | ⟨_, h1⟩)
    · exact h a List.mem_cons_self h1
    · exact Aux.LLEX_irrefl s (fun b hb => h b (List.mem_cons_of_mem _ hb)) h1

theorem Aux.LLEX_tri {α : Type u} {R : α → α → Prop} :
    ∀ l1 : List α, (∀ a, a ∈ l1 → ∀ b, R a b ∨ R b a ∨ a = b) →
      ∀ l2, LLEX R l1 l2 ∨ LLEX R l2 l1 ∨ l1 = l2
  | [], _, [] => Or.inr (Or.inr rfl)
  | [], _, _ :: _ => Or.inl (by simp [LLEX])
  | _ :: _, _, [] => Or.inr (Or.inl (by simp [LLEX]))
  | a :: s, h, b :: t => by
    rw [Aux.LLEX_cons, Aux.LLEX_cons]
    rcases h a List.mem_cons_self b with h1 | h1 | rfl
    · exact Or.inl (Or.inl h1)
    · exact Or.inr (Or.inl (Or.inl h1))
    · rcases Aux.LLEX_tri s (fun b hb => h b (List.mem_cons_of_mem _ hb)) t with h1 | h1 | rfl
      · exact Or.inl (Or.inr ⟨rfl, h1⟩)
      · exact Or.inr (Or.inl (Or.inr ⟨rfl, h1⟩))
      · exact Or.inr (Or.inr rfl)

theorem Aux.LLEX_trans {α : Type u} {R : α → α → Prop} :
    ∀ l1 : List α, (∀ a, a ∈ l1 → ∀ b c, R a b → R b c → R a c) →
      ∀ l2 l3, LLEX R l1 l2 → LLEX R l2 l3 → LLEX R l1 l3
  | _, _, l2, [], _, h2 => by rw [Aux.LLEX_nil] at h2; exact h2.elim
  | l1, _, [], _ :: _, h1, _ => by rw [Aux.LLEX_nil] at h1; exact h1.elim
  | [], _, _ :: _, _ :: _, _, _ => by simp [LLEX]
  | a :: s, h, b :: t, c :: u, h1, h2 => by
    rw [Aux.LLEX_cons] at h1 h2 ⊢
    have ih := Aux.LLEX_trans s (fun b hb => h b (List.mem_cons_of_mem _ hb)) t u
    rcases h1 with h1 | ⟨rfl, h1⟩
    · rcases h2 with h2 | ⟨rfl, h2⟩
      · exact Or.inl (h a List.mem_cons_self b c h1 h2)
      · exact Or.inl h1
    · rcases h2 with h2 | ⟨rfl, h2⟩
      · exact Or.inl h2
      · exact Or.inr ⟨rfl, ih h1 h2⟩

theorem Aux.mlstring_lt_irrefl (a : mlstring) : ¬ mlstring_lt a a :=
  StrongLinearOrder_mlstring_lt.1.1 a

theorem Aux.mlstring_lt_trans {a b c : mlstring} (h1 : mlstring_lt a b) (h2 : mlstring_lt b c) :
    mlstring_lt a c := StrongLinearOrder_mlstring_lt.1.2 a b c ⟨h1, h2⟩

theorem Aux.mlstring_lt_tri (a b : mlstring) : mlstring_lt a b ∨ mlstring_lt b a ∨ a = b :=
  StrongLinearOrder_mlstring_lt.2 a b

theorem Aux.type_lt_Tyvar_Tyvar {x1 x2 : mlstring} (h : mlstring_lt x1 x2) :
    type_lt (Tyvar x1) (Tyvar x2) := fun _ hR => hR.1 _ _ h

theorem Aux.type_lt_Tyvar_Tyapp (x1 x2 : mlstring) (args2 : List type) :
    type_lt (Tyvar x1) (Tyapp x2 args2) := fun _ hR => hR.2.1 _ _ _

theorem Aux.type_lt_Tyapp_Tyapp {x1 x2 : mlstring} {args1 args2 : List type}
    (h : LEX mlstring_lt (LLEX type_lt) (x1, args1) (x2, args2)) :
    type_lt (Tyapp x1 args1) (Tyapp x2 args2) := by
  intro R hR
  apply hR.2.2
  rcases h with h | ⟨h1, h2⟩
  · exact Or.inl h
  · exact Or.inr ⟨h1, Aux.LLEX_mono (fun x y hxy => hxy R hR) _ _ h2⟩

def Aux.type_lt_F : type → type → Prop
  | Tyvar x1, Tyvar x2 => mlstring_lt x1 x2
  | Tyvar _, Tyapp _ _ => True
  | Tyapp _ _, Tyvar _ => False
  | Tyapp x1 args1, Tyapp x2 args2 => LEX mlstring_lt (LLEX type_lt) (x1, args1) (x2, args2)

theorem Aux.type_lt_F_iff (a b : type) : type_lt a b ↔ Aux.type_lt_F a b := by
  have hF : ∀ a b, Aux.type_lt_F a b → type_lt a b := by
    intro a b h
    cases a with
    | Tyvar x =>
      cases b with
      | Tyvar y => exact Aux.type_lt_Tyvar_Tyvar h
      | Tyapp y l => exact Aux.type_lt_Tyvar_Tyapp _ _ _
    | Tyapp x l =>
      cases b with
      | Tyvar y => exact h.elim
      | Tyapp y m => exact Aux.type_lt_Tyapp_Tyapp h
  refine ⟨fun h => h Aux.type_lt_F ⟨fun _ _ h => h, fun _ _ _ => trivial, ?_⟩, hF a b⟩
  intro x1 args1 x2 args2 h
  rcases h with h | ⟨h1, h2⟩
  · exact Or.inl h
  · exact Or.inr ⟨h1, Aux.LLEX_mono hF _ _ h2⟩

/- HOL4:
Theorem type_lt_thm = Q.prove(
  `(type_lt (Tyvar x1) (Tyvar x2) ⇔ mlstring_lt x1 x2) ∧
    (type_lt (Tyvar _) (Tyapp _ _) ⇔ T) ∧
    (type_lt (Tyapp _ _) (Tyvar _) ⇔ F) ∧
    (type_lt (Tyapp x1 args1) (Tyapp x2 args2) ⇔
       (mlstring_lt LEX LLEX type_lt)
         (x1,args1) (x2,args2))`,
  rw[] >> rw[Once type_lt_cases])
  |> CONJUNCTS |> map GEN_ALL |> LIST_CONJ
   (each conjunct is universally closed separately; each `_` is a fresh variable) -/
theorem type_lt_thm :
    (∀ (x1 x2 : mlstring), type_lt (Tyvar x1) (Tyvar x2) ↔ mlstring_lt x1 x2) ∧
    (∀ (a : mlstring) (b : mlstring) (c : List type), type_lt (Tyvar a) (Tyapp b c) ↔ True) ∧
    (∀ (a : mlstring) (b : List type) (c : mlstring), type_lt (Tyapp a b) (Tyvar c) ↔ False) ∧
    (∀ (x1 : mlstring) (args1 : List type) (x2 : mlstring) (args2 : List type),
      type_lt (Tyapp x1 args1) (Tyapp x2 args2) ↔
        LEX mlstring_lt (LLEX type_lt) (x1, args1) (x2, args2)) := by
  refine ⟨fun _ _ => Aux.type_lt_F_iff _ _, fun _ _ _ => Aux.type_lt_F_iff _ _,
    fun _ _ _ => Aux.type_lt_F_iff _ _, fun _ _ _ _ => Aux.type_lt_F_iff _ _⟩

theorem Aux.LEX_mono {R1 R2 S1 S2 : term → term → Prop} (h1 : ∀ x y, R1 x y → S1 x y)
    (h2 : ∀ x y, R2 x y → S2 x y) (p q : term × term) (h : LEX R1 R2 p q) : LEX S1 S2 p q := by
  rcases h with h | ⟨h, h'⟩
  · exact Or.inl (h1 _ _ h)
  · exact Or.inr ⟨h, h2 _ _ h'⟩

def Aux.term_lt_F : term → term → Prop
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
  | Comb s1 s2, Comb t1 t2 => LEX term_lt term_lt (s1, s2) (t1, t2)
  | Comb _ _, Abs _ _ => True
  | Abs _ _, Var _ _ => False
  | Abs _ _, Const _ _ => False
  | Abs _ _, Comb _ _ => False
  | Abs s1 s2, Abs t1 t2 => LEX term_lt term_lt (s1, s2) (t1, t2)

theorem Aux.term_lt_F_iff (a b : term) : term_lt a b ↔ Aux.term_lt_F a b := by
  have hF : ∀ a b, Aux.term_lt_F a b → term_lt a b := by
    intro a b h
    cases a <;> cases b <;> first | exact h.elim | skip
    · exact fun R hR => hR.1 _ _ _ _ h
    · exact fun R hR => hR.2.1 _ _ _ _
    · exact fun R hR => hR.2.2.1 _ _ _ _
    · exact fun R hR => hR.2.2.2.1 _ _ _ _
    · exact fun R hR => hR.2.2.2.2.1 _ _ _ _ h
    · exact fun R hR => hR.2.2.2.2.2.1 _ _ _ _
    · exact fun R hR => hR.2.2.2.2.2.2.1 _ _ _ _
    · exact fun R hR => hR.2.2.2.2.2.2.2.1 _ _ _ _
        (Aux.LEX_mono (fun x y hxy => hxy R hR) (fun x y hxy => hxy R hR) _ _ h)
    · exact fun R hR => hR.2.2.2.2.2.2.2.2.1 _ _ _ _
    · exact fun R hR => hR.2.2.2.2.2.2.2.2.2 _ _ _ _
        (Aux.LEX_mono (fun x y hxy => hxy R hR) (fun x y hxy => hxy R hR) _ _ h)
  refine ⟨fun h => h Aux.term_lt_F ?_, hF a b⟩
  refine ⟨fun _ _ _ _ h => h, fun _ _ _ _ => trivial, fun _ _ _ _ => trivial,
    fun _ _ _ _ => trivial, fun _ _ _ _ h => h, fun _ _ _ _ => trivial, fun _ _ _ _ => trivial,
    fun _ _ _ _ h => Aux.LEX_mono hF hF _ _ h, fun _ _ _ _ => trivial,
    fun _ _ _ _ h => Aux.LEX_mono hF hF _ _ h⟩

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
  |> CONJUNCTS |> map GEN_ALL |> LIST_CONJ
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
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    exact fun _ _ _ _ => Aux.term_lt_F_iff _ _

theorem Aux.type_lt_irrefl (a : type) : ¬ type_lt a a := by
  induction a using Aux.type_ind with
  | h1 v => rw [type_lt_thm.1]; exact Aux.mlstring_lt_irrefl v
  | h2 n tys ih =>
    rw [type_lt_thm.2.2.2]
    rintro (h | ⟨_, h⟩)
    · exact Aux.mlstring_lt_irrefl n h
    · exact Aux.LLEX_irrefl tys ih h

theorem Aux.type_lt_tri (a : type) : ∀ b, type_lt a b ∨ type_lt b a ∨ a = b := by
  induction a using Aux.type_ind with
  | h1 v =>
    intro b
    cases b with
    | Tyvar w =>
      rw [type_lt_thm.1, type_lt_thm.1]
      rcases Aux.mlstring_lt_tri v w with h | h | rfl
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr rfl)
    | Tyapp m l => exact Or.inl (Aux.type_lt_Tyvar_Tyapp _ _ _)
  | h2 n tys ih =>
    intro b
    cases b with
    | Tyvar w => exact Or.inr (Or.inl (Aux.type_lt_Tyvar_Tyapp _ _ _))
    | Tyapp m l =>
      rw [type_lt_thm.2.2.2, type_lt_thm.2.2.2]
      rcases Aux.mlstring_lt_tri n m with h | h | rfl
      · exact Or.inl (Or.inl h)
      · exact Or.inr (Or.inl (Or.inl h))
      · rcases Aux.LLEX_tri tys ih l with h | h | rfl
        · exact Or.inl (Or.inr ⟨rfl, h⟩)
        · exact Or.inr (Or.inl (Or.inr ⟨rfl, h⟩))
        · exact Or.inr (Or.inr rfl)

theorem Aux.type_lt_trans (a : type) : ∀ b c, type_lt a b → type_lt b c → type_lt a c := by
  induction a using Aux.type_ind with
  | h1 v =>
    intro b c h1 h2
    cases c with
    | Tyapp m l => exact Aux.type_lt_Tyvar_Tyapp _ _ _
    | Tyvar w =>
      cases b with
      | Tyapp m l => rw [type_lt_thm.2.2.1] at h2; exact h2.elim
      | Tyvar u =>
        rw [type_lt_thm.1] at *
        exact Aux.mlstring_lt_trans h1 h2
  | h2 n tys ih =>
    intro b c h1 h2
    cases b with
    | Tyvar u => rw [type_lt_thm.2.2.1] at h1; exact h1.elim
    | Tyapp m l =>
      cases c with
      | Tyvar u => rw [type_lt_thm.2.2.1] at h2; exact h2.elim
      | Tyapp k r =>
        rw [type_lt_thm.2.2.2] at *
        rcases h1 with h1 | ⟨h1, h1'⟩
        · rcases h2 with h2 | ⟨h2, h2'⟩
          · exact Or.inl (Aux.mlstring_lt_trans h1 h2)
          · simp only at h2; subst h2; exact Or.inl h1
        · rcases h2 with h2 | ⟨h2, h2'⟩
          · simp only at h1; subst h1; exact Or.inl h2
          · simp only at h1 h2; subst h1; subst h2
            exact Or.inr ⟨rfl, Aux.LLEX_trans tys ih _ _ h1' h2'⟩

/- HOL4:
Theorem type_cmp_refl[simp]:
   type_cmp t t = EQUAL
-/
theorem type_cmp_refl (t : type) : type_cmp t t = EQUAL := by
  simp [type_cmp, TO_of_LinearOrder]

/- HOL4:
Theorem term_cmp_refl[simp]:
   term_cmp t t = EQUAL
-/
theorem term_cmp_refl (t : term) : term_cmp t t = EQUAL := by
  simp [term_cmp, TO_of_LinearOrder]

theorem Aux.TO_EQUAL {α : Type u} (R : α → α → Prop) (x y : α) :
    TO_of_LinearOrder R x y = EQUAL ↔ x = y := by
  unfold TO_of_LinearOrder
  by_cases h : x = y
  · simp [h]
  · by_cases h2 : R x y <;> simp [h, h2]

theorem Aux.TO_LESS {α : Type u} {R : α → α → Prop} (hR : StrongLinearOrder R) (x y : α) :
    TO_of_LinearOrder R x y = LESS ↔ R x y := by
  unfold TO_of_LinearOrder
  by_cases h : x = y
  · subst h; simp [hR.1.1 x]
  · by_cases h2 : R x y <;> simp [h, h2]

theorem Aux.TO_GREATER {α : Type u} {R : α → α → Prop} (hR : StrongLinearOrder R) (x y : α) :
    TO_of_LinearOrder R x y = GREATER ↔ R y x := by
  unfold TO_of_LinearOrder
  by_cases h : x = y
  · subst h; simp [hR.1.1 x]
  · by_cases h2 : R x y
    · simp only [h, h2, if_true, if_false]
      exact ⟨fun h => (by cases h), fun h3 => absurd (hR.1.2 _ _ _ ⟨h2, h3⟩) (hR.1.1 x)⟩
    · simp only [h, h2, if_false, true_iff]
      rcases hR.2 x y with h3 | h3 | h3
      · exact absurd h3 h2
      · exact h3
      · exact absurd h3 h

theorem Aux.TotOrd_TO {α : Type u} {R : α → α → Prop} (hR : StrongLinearOrder R) :
    TotOrd (TO_of_LinearOrder R) := by
  refine ⟨Aux.TO_EQUAL R, fun x y => ?_, fun x y z h => ?_⟩
  · rw [Aux.TO_GREATER hR, Aux.TO_LESS hR]
  · rw [Aux.TO_LESS hR] at *
    rw [Aux.TO_LESS hR] at h
    exact hR.1.2 x y z h

theorem Aux.TO_sym {α : Type u} {R : α → α → Prop} (hR : StrongLinearOrder R) (x y : α) :
    invert_comparison (TO_of_LinearOrder R x y) = TO_of_LinearOrder R y x := by
  cases h : TO_of_LinearOrder R x y with
  | LESS => rw [Aux.TO_LESS hR] at h; exact ((Aux.TO_GREATER hR y x).mpr h).symm
  | EQUAL => rw [Aux.TO_EQUAL] at h; exact ((Aux.TO_EQUAL R y x).mpr h.symm).symm
  | GREATER => rw [Aux.TO_GREATER hR] at h; exact ((Aux.TO_LESS hR y x).mpr h).symm

/-- Composition law of comparisons. -/
theorem Aux.TO_comp {α : Type u} {R : α → α → Prop} (hR : StrongLinearOrder R) (x y z : α)
    (h1 : TO_of_LinearOrder R x y ≠ GREATER) (h2 : TO_of_LinearOrder R y z ≠ GREATER) :
    TO_of_LinearOrder R x z =
      if TO_of_LinearOrder R x y = EQUAL then TO_of_LinearOrder R y z
      else TO_of_LinearOrder R x y := by
  by_cases e : x = y
  · subst e; rw [if_pos ((Aux.TO_EQUAL R x x).mpr rfl)]
  · rw [if_neg (fun h => e ((Aux.TO_EQUAL R x y).mp h))]
    have hl : TO_of_LinearOrder R x y = LESS := by
      cases h : TO_of_LinearOrder R x y with
      | LESS => rfl
      | EQUAL => exact absurd ((Aux.TO_EQUAL R x y).mp h) e
      | GREATER => exact absurd h h1
    rw [hl, Aux.TO_LESS hR]
    rw [Aux.TO_LESS hR] at hl
    cases h : TO_of_LinearOrder R y z with
    | LESS => rw [Aux.TO_LESS hR] at h; exact hR.1.2 _ _ _ ⟨hl, h⟩
    | EQUAL => rw [Aux.TO_EQUAL] at h; exact h ▸ hl
    | GREATER => exact absurd h h2

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

theorem Aux.LEX_irrefl {α : Type u} {β : Type v} {R : α → α → Prop} {S : β → β → Prop} {a : α}
    {b : β} (h1 : ¬ R a a) (h2 : ¬ S b b) : ¬ LEX R S (a, b) (a, b) := by
  rintro (h | ⟨_, h⟩)
  · exact h1 h
  · exact h2 h

theorem Aux.LEX_tri {α : Type u} {β : Type v} {R : α → α → Prop} {S : β → β → Prop} {a : α}
    {b : β} (h1 : ∀ c, R a c ∨ R c a ∨ a = c) (h2 : ∀ d, S b d ∨ S d b ∨ b = d) (c : α) (d : β) :
    LEX R S (a, b) (c, d) ∨ LEX R S (c, d) (a, b) ∨ (a = c ∧ b = d) := by
  rcases h1 c with h | h | rfl
  · exact Or.inl (Or.inl h)
  · exact Or.inr (Or.inl (Or.inl h))
  · rcases h2 d with h | h | rfl
    · exact Or.inl (Or.inr ⟨rfl, h⟩)
    · exact Or.inr (Or.inl (Or.inr ⟨rfl, h⟩))
    · exact Or.inr (Or.inr ⟨rfl, rfl⟩)

theorem Aux.LEX_trans {α : Type u} {β : Type v} {R : α → α → Prop} {S : β → β → Prop} {a c e : α}
    {b d f : β} (h1 : R a c → R c e → R a e) (h2 : S b d → S d f → S b f)
    (h : LEX R S (a, b) (c, d)) (h' : LEX R S (c, d) (e, f)) : LEX R S (a, b) (e, f) := by
  simp only [LEX] at *
  rcases h with h | ⟨rfl, h⟩
  · rcases h' with h' | ⟨rfl, h'⟩
    · exact Or.inl (h1 h h')
    · exact Or.inl h
  · rcases h' with h' | ⟨rfl, h'⟩
    · exact Or.inl h'
    · exact Or.inr ⟨rfl, h2 h h'⟩

theorem Aux.term_lt_irrefl (a : term) : ¬ term_lt a a := by
  rw [Aux.term_lt_F_iff]
  induction a with
  | Var x ty => exact Aux.LEX_irrefl (Aux.mlstring_lt_irrefl x) (Aux.type_lt_irrefl ty)
  | Const x ty => exact Aux.LEX_irrefl (Aux.mlstring_lt_irrefl x) (Aux.type_lt_irrefl ty)
  | Comb s t ihs iht => rw [← Aux.term_lt_F_iff] at ihs iht; exact Aux.LEX_irrefl ihs iht
  | Abs s t ihs iht => rw [← Aux.term_lt_F_iff] at ihs iht; exact Aux.LEX_irrefl ihs iht

theorem Aux.term_lt_tri (a : term) : ∀ b, term_lt a b ∨ term_lt b a ∨ a = b := by
  induction a with
  | Var x ty =>
    intro b
    cases b with
    | Var y uy =>
      simp only [term_lt_thm, term.Var.injEq]
      exact Aux.LEX_tri (Aux.mlstring_lt_tri x) (Aux.type_lt_tri ty) y uy
    | _ => simp [term_lt_thm]
  | Const x ty =>
    intro b
    cases b with
    | Const y uy =>
      simp only [term_lt_thm, term.Const.injEq]
      exact Aux.LEX_tri (Aux.mlstring_lt_tri x) (Aux.type_lt_tri ty) y uy
    | _ => simp [term_lt_thm]
  | Comb s t ihs iht =>
    intro b
    cases b with
    | Comb s' t' =>
      simp only [term_lt_thm, term.Comb.injEq]
      exact Aux.LEX_tri ihs iht s' t'
    | _ => simp [term_lt_thm]
  | Abs s t ihs iht =>
    intro b
    cases b with
    | Abs s' t' =>
      simp only [term_lt_thm, term.Abs.injEq]
      exact Aux.LEX_tri ihs iht s' t'
    | _ => simp [term_lt_thm]

theorem Aux.term_lt_trans (a : term) : ∀ b c, term_lt a b → term_lt b c → term_lt a c := by
  induction a with
  | Var x ty =>
    intro b c h1 h2
    cases b <;> cases c <;> simp only [term_lt_thm] at h1 h2 ⊢
    exact Aux.LEX_trans Aux.mlstring_lt_trans (Aux.type_lt_trans _ _ _) h1 h2
  | Const x ty =>
    intro b c h1 h2
    cases b <;> cases c <;> simp only [term_lt_thm] at h1 h2 ⊢
    exact Aux.LEX_trans Aux.mlstring_lt_trans (Aux.type_lt_trans _ _ _) h1 h2
  | Comb s t ihs iht =>
    intro b c h1 h2
    cases b <;> cases c <;> simp only [term_lt_thm] at h1 h2 ⊢
    exact Aux.LEX_trans (ihs _ _) (iht _ _) h1 h2
  | Abs s t ihs iht =>
    intro b c h1 h2
    cases b <;> cases c <;> simp only [term_lt_thm] at h1 h2 ⊢
    exact Aux.LEX_trans (ihs _ _) (iht _ _) h1 h2

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
  | nil => simp only [ALPHAVARS, ordav]; exact (TotOrd_term_cmp.1 t1 t2).symm
  | cons p env ih =>
    obtain ⟨a, b⟩ := p
    simp only [ALPHAVARS, ordav, Prod.mk.injEq]
    by_cases h1 : t1 = a
    · by_cases h2 : t2 = b
      · simp [h1, h2]
      · simp [h1, h2]
    · by_cases h2 : t2 = b
      · simp [h1, h2]
      · have h1' : a ≠ t1 := fun h => h1 h.symm
        have h2' : b ≠ t2 := fun h => h2 h.symm
        simp [h1, h2, h1', h2', ih]

theorem Aux.RACONV_Var_iff {env : List (term × term)} {x1 : mlstring} {ty1 : type} {x2 : mlstring}
    {ty2 : type} : RACONV env (Var x1 ty1, Var x2 ty2) ↔ ALPHAVARS env (Var x1 ty1, Var x2 ty2) :=
  ⟨fun h => by cases h; assumption, RACONV.Var⟩

theorem Aux.RACONV_Const_iff {env : List (term × term)} {x1 : mlstring} {ty1 : type} {x2 : mlstring}
    {ty2 : type} : RACONV env (Const x1 ty1, Const x2 ty2) ↔ Const x1 ty1 = Const x2 ty2 :=
  ⟨fun h => by cases h; rfl, fun h => by rw [h]; exact RACONV.Const⟩

theorem Aux.RACONV_Comb_iff {env : List (term × term)} {s1 t1 s2 t2 : term} :
    RACONV env (Comb s1 t1, Comb s2 t2) ↔ RACONV env (s1, s2) ∧ RACONV env (t1, t2) :=
  ⟨fun h => by cases h; exact ⟨by assumption, by assumption⟩, fun h => RACONV.Comb h.1 h.2⟩

theorem Aux.RACONV_Abs_iff {env : List (term × term)} {s1 t1 s2 t2 : term} :
    RACONV env (Abs s1 t1, Abs s2 t2) ↔
      typeof s1 = typeof s2 ∧ RACONV ((s1, s2) :: env) (t1, t2) :=
  ⟨fun h => by cases h; exact ⟨by assumption, by assumption⟩, fun h => RACONV.Abs h.1 h.2⟩

def Aux.rank : term → Nat
  | Var _ _ => 0
  | Const _ _ => 1
  | Comb _ _ => 2
  | Abs _ _ => 3

theorem Aux.orda_rank_lt (env : List (term × term)) (t1 t2 : term) (h : Aux.rank t1 < Aux.rank t2) :
    orda env t1 t2 = LESS := by
  have hne : ¬ (t1 = t2 ∧ env = []) := fun ⟨e, _⟩ => by rw [e] at h; exact Nat.lt_irrefl _ h
  rw [orda.eq_def, if_neg hne]
  cases t1 <;> cases t2 <;> first | rfl | (simp [Aux.rank] at h)

theorem Aux.orda_rank_gt (env : List (term × term)) (t1 t2 : term) (h : Aux.rank t2 < Aux.rank t1) :
    orda env t1 t2 = GREATER := by
  have hne : ¬ (t1 = t2 ∧ env = []) := fun ⟨e, _⟩ => by rw [e] at h; exact Nat.lt_irrefl _ h
  rw [orda.eq_def, if_neg hne]
  cases t1 <;> cases t2 <;> first | rfl | (simp [Aux.rank] at h)

theorem Aux.RACONV_rank {env : List (term × term)} {t1 t2 : term} (h : RACONV env (t1, t2)) :
    Aux.rank t1 = Aux.rank t2 := by
  cases h <;> rfl

theorem Aux.RACONV_eq_orda_rank {env : List (term × term)} {t1 t2 : term}
    (h : Aux.rank t1 ≠ Aux.rank t2) : RACONV env (t1, t2) ↔ orda env t1 t2 = EQUAL := by
  constructor
  · intro h'; exact absurd (Aux.RACONV_rank h') h
  · intro h'
    rcases Nat.lt_or_gt_of_ne h with hl | hl
    · rw [Aux.orda_rank_lt env t1 t2 hl] at h'; cases h'
    · rw [Aux.orda_rank_gt env t1 t2 hl] at h'; cases h'

theorem Aux.RACONV_diag_iff {t1 t2 : term} {env : List (term × term)} (h : t1 = t2 ∧ env = []) :
    RACONV env (t1, t2) ↔ EQUAL = EQUAL := by
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨fun _ => rfl, fun _ => RACONV_REFL _ _ trivial⟩

/- HOL4:
Theorem RACONV_eq_orda:
   ∀env t1 t2. RACONV env (t1,t2) ⇔ orda env t1 t2 = EQUAL
-/
theorem RACONV_eq_orda :
    ∀ (env : List (term × term)) (t1 t2 : term),
      RACONV env (t1, t2) ↔ orda env t1 t2 = EQUAL := by
  intro env t1
  induction t1 generalizing env with
  | Var x ty =>
    intro t2
    by_cases hr : Aux.rank (Var x ty) = Aux.rank t2
    · cases t2 with
      | Var y uy =>
        rw [orda]
        by_cases h : Var x ty = Var y uy ∧ env = []
        · rw [if_pos h]; exact Aux.RACONV_diag_iff h
        · rw [if_neg h, Aux.RACONV_Var_iff]
          exact ALPHAVARS_eq_ordav env _ _
      | _ => simp [Aux.rank] at hr
    · exact Aux.RACONV_eq_orda_rank hr
  | Const x ty =>
    intro t2
    by_cases hr : Aux.rank (Const x ty) = Aux.rank t2
    · cases t2 with
      | Const y uy =>
        rw [orda]
        by_cases h : Const x ty = Const y uy ∧ env = []
        · rw [if_pos h]; exact Aux.RACONV_diag_iff h
        · rw [if_neg h, Aux.RACONV_Const_iff]
          exact (TotOrd_term_cmp.1 _ _).symm
      | _ => simp [Aux.rank] at hr
    · exact Aux.RACONV_eq_orda_rank hr
  | Comb a b iha ihb =>
    intro t2
    by_cases hr : Aux.rank (Comb a b) = Aux.rank t2
    · cases t2 with
      | Comb c d =>
        rw [orda]
        by_cases h : Comb a b = Comb c d ∧ env = []
        · rw [if_pos h]; exact Aux.RACONV_diag_iff h
        · rw [if_neg h, Aux.RACONV_Comb_iff, iha, ihb]
          show _ ↔ (if orda env a c ≠ EQUAL then orda env a c else orda env b d) = EQUAL
          by_cases hc : orda env a c = EQUAL <;> simp [hc]
      | _ => simp [Aux.rank] at hr
    · exact Aux.RACONV_eq_orda_rank hr
  | Abs a b _ ihb =>
    intro t2
    by_cases hr : Aux.rank (Abs a b) = Aux.rank t2
    · cases t2 with
      | Abs c d =>
        rw [orda]
        by_cases h : Abs a b = Abs c d ∧ env = []
        · rw [if_pos h]; exact Aux.RACONV_diag_iff h
        · rw [if_neg h, Aux.RACONV_Abs_iff, ihb, ← TotOrd_type_cmp.1]
          show _ ↔ (if type_cmp (typeof a) (typeof c) ≠ EQUAL then type_cmp (typeof a) (typeof c)
            else orda ((a, c) :: env) b d) = EQUAL
          by_cases hc : type_cmp (typeof a) (typeof c) = EQUAL <;> simp [hc]
      | _ => simp [Aux.rank] at hr
    · exact Aux.RACONV_eq_orda_rank hr

/- HOL4:
Theorem ACONV_eq_orda:
   ∀t1 t2. ACONV t1 t2 = (orda [] t1 t2 = EQUAL)
-/
theorem ACONV_eq_orda : ∀ (t1 t2 : term), ACONV t1 t2 ↔ orda [] t1 t2 = EQUAL := by
  intro t1 t2
  exact RACONV_eq_orda [] t1 t2

theorem Aux.orda_Var (env : List (term × term)) (x y : mlstring) (a b : type) :
    orda env (Var x a) (Var y b) = ordav env (Var x a) (Var y b) := by
  rw [orda]
  by_cases h : Var x a = Var y b ∧ env = []
  · rw [if_pos h]
    obtain ⟨h1, rfl⟩ := h
    rw [h1]
    exact (term_cmp_refl _).symm
  · rw [if_neg h]

theorem Aux.orda_Const (env : List (term × term)) (x y : mlstring) (a b : type) :
    orda env (Const x a) (Const y b) = term_cmp (Const x a) (Const y b) := by
  rw [orda]
  by_cases h : Const x a = Const y b ∧ env = []
  · rw [if_pos h]
    obtain ⟨h1, rfl⟩ := h
    rw [h1]
    exact (term_cmp_refl _).symm
  · rw [if_neg h]

theorem Aux.orda_Comb (env : List (term × term)) (a b c d : term) :
    orda env (Comb a b) (Comb c d) =
      if orda env a c = EQUAL then orda env b d else orda env a c := by
  rw [orda]
  by_cases h : Comb a b = Comb c d ∧ env = []
  · rw [if_pos h]
    obtain ⟨h1, rfl⟩ := h
    obtain ⟨rfl, rfl⟩ := term.Comb.inj h1
    rw [if_pos ((ACONV_eq_orda a a).mp (ACONV_REFL a))]
    exact ((ACONV_eq_orda b b).mp (ACONV_REFL b)).symm
  · rw [if_neg h]
    show (if orda env a c ≠ EQUAL then orda env a c else orda env b d) = _
    by_cases hc : orda env a c = EQUAL <;> simp [hc]

theorem Aux.orda_Abs (env : List (term × term)) (a b c d : term) :
    orda env (Abs a b) (Abs c d) =
      if type_cmp (typeof a) (typeof c) = EQUAL then orda ((a, c) :: env) b d
      else type_cmp (typeof a) (typeof c) := by
  rw [orda]
  by_cases h : Abs a b = Abs c d ∧ env = []
  · rw [if_pos h]
    obtain ⟨h1, rfl⟩ := h
    obtain ⟨rfl, rfl⟩ := term.Abs.inj h1
    rw [if_pos (type_cmp_refl _)]
    exact ((RACONV_eq_orda [(a, a)] b b).mp (RACONV_REFL b _ ⟨rfl, trivial⟩)).symm
  · rw [if_neg h]
    show (if type_cmp (typeof a) (typeof c) ≠ EQUAL then type_cmp (typeof a) (typeof c)
            else orda ((a, c) :: env) b d) = _
    by_cases hc : type_cmp (typeof a) (typeof c) = EQUAL <;> simp [hc]

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
  | nil => exact Aux.TO_sym StrongLinearOrder_term_lt v1 v2
  | cons p env ih =>
    obtain ⟨a, b⟩ := p
    simp only [List.map_cons, ordav]
    by_cases h1 : v1 = a
    · by_cases h2 : v2 = b <;> simp [h1, h2, invert_comparison]
    · by_cases h2 : v2 = b
      · simp [h1, h2, invert_comparison]
      · simp only [h1, h2, if_false]
        exact ih

/- HOL4:
Theorem orda_sym:
   ∀env t1 t2. flip_ord (orda env t1 t2) = orda (MAP (λ(x,y). (y,x)) env) t2 t1
-/
theorem orda_sym :
    ∀ (env : List (term × term)) (t1 t2 : term),
      flip_ord (orda env t1 t2) =
      orda (env.map (fun p => match p with | (x, y) => (y, x))) t2 t1 := by
  intro env t1
  induction t1 generalizing env with
  | Var x ty =>
    intro t2
    cases t2 with
    | Var y uy => rw [Aux.orda_Var, Aux.orda_Var]; exact ordav_sym _ _ _
    | _ =>
      rw [Aux.orda_rank_lt _ _ _ (by simp [Aux.rank]), Aux.orda_rank_gt _ _ _ (by simp [Aux.rank])]
      rfl
  | Const x ty =>
    intro t2
    cases t2 with
    | Const y uy =>
      rw [Aux.orda_Const, Aux.orda_Const]; exact Aux.TO_sym StrongLinearOrder_term_lt _ _
    | Var y uy =>
      rw [Aux.orda_rank_gt _ _ _ (by simp [Aux.rank]), Aux.orda_rank_lt _ _ _ (by simp [Aux.rank])]
      rfl
    | _ =>
      rw [Aux.orda_rank_lt _ _ _ (by simp [Aux.rank]), Aux.orda_rank_gt _ _ _ (by simp [Aux.rank])]
      rfl
  | Comb a b iha ihb =>
    intro t2
    cases t2 with
    | Comb c d =>
      rw [Aux.orda_Comb, Aux.orda_Comb, ← iha, ← ihb]
      cases h : orda env a c <;> simp [invert_comparison]
    | Abs c d =>
      rw [Aux.orda_rank_lt _ _ _ (by simp [Aux.rank]), Aux.orda_rank_gt _ _ _ (by simp [Aux.rank])]
      rfl
    | _ =>
      rw [Aux.orda_rank_gt _ _ _ (by simp [Aux.rank]), Aux.orda_rank_lt _ _ _ (by simp [Aux.rank])]
      rfl
  | Abs a b _ ihb =>
    intro t2
    cases t2 with
    | Abs c d =>
      have ih := ihb ((a, c) :: env) d
      simp only [List.map_cons] at ih
      rw [Aux.orda_Abs, Aux.orda_Abs, ← ih]
      have hs : type_cmp (typeof c) (typeof a) = invert_comparison (type_cmp (typeof a) (typeof c)) :=
        (Aux.TO_sym StrongLinearOrder_type_lt _ _).symm
      rw [hs]
      cases h : type_cmp (typeof a) (typeof c) <;> simp [invert_comparison]
    | _ =>
      rw [Aux.orda_rank_gt _ _ _ (by simp [Aux.rank]), Aux.orda_rank_lt _ _ _ (by simp [Aux.rank])]
      rfl

theorem Aux.ordav_comp : ∀ (env1 env2 : List (term × term)) (t1 t2 t3 : term),
    env1.map Prod.snd = env2.map Prod.fst →
    ordav env1 t1 t2 ≠ GREATER → ordav env2 t2 t3 ≠ GREATER →
    ordav (ZIP (env1.map Prod.fst, env2.map Prod.snd)) t1 t3 =
      if ordav env1 t1 t2 = EQUAL then ordav env2 t2 t3 else ordav env1 t1 t2
  | [], [], t1, t2, t3, _, h1, h2 => by
    simp only [List.map_nil, ZIP, ordav] at h1 h2 ⊢
    exact Aux.TO_comp StrongLinearOrder_term_lt t1 t2 t3 h1 h2
  | [], _ :: _, _, _, _, he, _, _ => by simp at he
  | _ :: _, [], _, _, _, he, _, _ => by simp at he
  | (a, b) :: env1, (b', c) :: env2, t1, t2, t3, he, h1, h2 => by
    simp only [List.map_cons, List.cons.injEq] at he
    obtain ⟨rfl, he⟩ := he
    have ih := Aux.ordav_comp env1 env2 t1 t2 t3 he
    simp only [List.map_cons, ZIP, ordav] at h1 h2 ⊢
    by_cases ha : t1 = a
    · by_cases hb : t2 = b
      · simp [ha, hb]
      · by_cases hc : t3 = c
        · simp [hb, hc] at h2
        · simp [ha, hb, hc]
    · by_cases hb : t2 = b
      · simp [ha, hb] at h1
      · by_cases hc : t3 = c
        · simp [hb, hc] at h2
        · simp only [ha, hb, hc, if_false] at h1 h2 ⊢
          exact ih h1 h2

theorem Aux.orda_comp_rank (t1 t2 t3 : term) (env1 env2 env3 : List (term × term))
    (hr : ¬ (Aux.rank t1 = Aux.rank t2 ∧ Aux.rank t2 = Aux.rank t3))
    (h1 : orda env1 t1 t2 ≠ GREATER) (h2 : orda env2 t2 t3 ≠ GREATER) :
    orda env3 t1 t3 =
      if orda env1 t1 t2 = EQUAL then orda env2 t2 t3 else orda env1 t1 t2 := by
  have g1 : Aux.rank t1 ≤ Aux.rank t2 := by
    apply Classical.byContradiction; intro h
    exact h1 (Aux.orda_rank_gt _ _ _ (by omega))
  have g2 : Aux.rank t2 ≤ Aux.rank t3 := by
    apply Classical.byContradiction; intro h
    exact h2 (Aux.orda_rank_gt _ _ _ (by omega))
  rw [Aux.orda_rank_lt env3 t1 t3 (by omega)]
  by_cases hl : Aux.rank t1 < Aux.rank t2
  · rw [Aux.orda_rank_lt env1 t1 t2 hl]; simp
  · rw [Aux.orda_rank_lt env2 t2 t3 (by omega)]
    cases h : orda env1 t1 t2 with
    | LESS => simp
    | EQUAL => simp
    | GREATER => exact absurd h h1

theorem Aux.orda_comp (t1 : term) : ∀ (t2 t3 : term) (env1 env2 : List (term × term)),
    env1.map Prod.snd = env2.map Prod.fst →
    orda env1 t1 t2 ≠ GREATER → orda env2 t2 t3 ≠ GREATER →
    orda (ZIP (env1.map Prod.fst, env2.map Prod.snd)) t1 t3 =
      if orda env1 t1 t2 = EQUAL then orda env2 t2 t3 else orda env1 t1 t2 := by
  induction t1 with
  | Var x ty =>
    intro t2 t3 env1 env2 he h1 h2
    by_cases hr : Aux.rank (Var x ty) = Aux.rank t2 ∧ Aux.rank t2 = Aux.rank t3
    · cases t2 <;> first | (simp [Aux.rank] at hr; done) | skip
      cases t3 <;> first | (simp [Aux.rank] at hr; done) | skip
      simp only [Aux.orda_Var] at h1 h2 ⊢
      exact Aux.ordav_comp env1 env2 _ _ _ he h1 h2
    · exact Aux.orda_comp_rank _ _ _ _ _ _ hr h1 h2
  | Const x ty =>
    intro t2 t3 env1 env2 he h1 h2
    by_cases hr : Aux.rank (Const x ty) = Aux.rank t2 ∧ Aux.rank t2 = Aux.rank t3
    · cases t2 <;> first | (simp [Aux.rank] at hr; done) | skip
      cases t3 <;> first | (simp [Aux.rank] at hr; done) | skip
      simp only [Aux.orda_Const] at h1 h2 ⊢
      exact Aux.TO_comp StrongLinearOrder_term_lt _ _ _ h1 h2
    · exact Aux.orda_comp_rank _ _ _ _ _ _ hr h1 h2
  | Comb a b iha ihb =>
    intro t2 t3 env1 env2 he h1 h2
    by_cases hr : Aux.rank (Comb a b) = Aux.rank t2 ∧ Aux.rank t2 = Aux.rank t3
    · cases t2 with
      | Comb c d =>
        cases t3 with
        | Comb e f =>
          simp only [Aux.orda_Comb] at h1 h2 ⊢
          have g1 : orda env1 a c ≠ GREATER := fun h => by simp [h] at h1
          have g2 : orda env2 c e ≠ GREATER := fun h => by simp [h] at h2
          rw [iha c e env1 env2 he g1 g2]
          cases k1 : orda env1 a c with
          | GREATER => exact absurd k1 g1
          | LESS => simp
          | EQUAL =>
            cases k2 : orda env2 c e with
            | GREATER => exact absurd k2 g2
            | LESS =>
              simp only [k1, if_true] at h1
              cases k3 : orda env1 b d with
              | GREATER => exact absurd k3 h1
              | LESS => simp
              | EQUAL => simp
            | EQUAL =>
              simp only [k1, k2, if_true] at h1 h2
              simp [ihb d f env1 env2 he h1 h2]
        | _ => simp [Aux.rank] at hr
      | _ => simp [Aux.rank] at hr
    · exact Aux.orda_comp_rank _ _ _ _ _ _ hr h1 h2
  | Abs a b _ ihb =>
    intro t2 t3 env1 env2 he h1 h2
    by_cases hr : Aux.rank (Abs a b) = Aux.rank t2 ∧ Aux.rank t2 = Aux.rank t3
    · cases t2 with
      | Abs c d =>
        cases t3 with
        | Abs e f =>
          simp only [Aux.orda_Abs] at h1 h2 ⊢
          have g1 : type_cmp (typeof a) (typeof c) ≠ GREATER := fun h => by simp [h] at h1
          have g2 : type_cmp (typeof c) (typeof e) ≠ GREATER := fun h => by simp [h] at h2
          have g3 : type_cmp (typeof a) (typeof e) =
              if type_cmp (typeof a) (typeof c) = EQUAL then type_cmp (typeof c) (typeof e)
              else type_cmp (typeof a) (typeof c) :=
            Aux.TO_comp StrongLinearOrder_type_lt _ _ _ g1 g2
          rw [g3]
          cases k1 : type_cmp (typeof a) (typeof c) with
          | GREATER => exact absurd k1 g1
          | LESS => simp
          | EQUAL =>
            cases k2 : type_cmp (typeof c) (typeof e) with
            | GREATER => exact absurd k2 g2
            | LESS =>
              simp only [k1, if_true] at h1
              cases k3 : orda ((a, c) :: env1) b d with
              | GREATER => exact absurd k3 h1
              | LESS => simp
              | EQUAL => simp
            | EQUAL =>
              simp only [k1, k2, if_true] at h1 h2
              have ih := ihb d f ((a, c) :: env1) ((c, e) :: env2) (by simp [he]) h1 h2
              simp only [List.map_cons, ZIP] at ih
              simp [ih]
        | _ => simp [Aux.rank] at hr
      | _ => simp [Aux.rank] at hr
    · exact Aux.orda_comp_rank _ _ _ _ _ _ hr h1 h2

theorem Aux.orda_nil_comp (x y z : term) (h1 : orda [] x y ≠ GREATER) (h2 : orda [] y z ≠ GREATER) :
    orda [] x z = if orda [] x y = EQUAL then orda [] y z else orda [] x y := by
  have h := Aux.orda_comp x y z [] [] rfl h1 h2
  simpa [ZIP] using h

theorem Aux.alpha_lt_trans {x y z : term} (h1 : alpha_lt x y) (h2 : alpha_lt y z) : alpha_lt x z := by
  unfold alpha_lt at *
  rw [Aux.orda_nil_comp x y z (by simp [h1]) (by simp [h2]), h1]
  simp

theorem Aux.ACONV_alpha_lt {x y z : term} (h1 : ACONV x y) (h2 : alpha_lt y z) : alpha_lt x z := by
  rw [ACONV_eq_orda] at h1
  unfold alpha_lt at *
  rw [Aux.orda_nil_comp x y z (by simp [h1]) (by simp [h2]), h1]
  simpa using h2

theorem Aux.alpha_lt_ACONV {x y z : term} (h1 : alpha_lt x y) (h2 : ACONV y z) : alpha_lt x z := by
  rw [ACONV_eq_orda] at h2
  unfold alpha_lt at *
  rw [Aux.orda_nil_comp x y z (by simp [h1]) (by simp [h2]), h1]
  simp

theorem Aux.orda_GREATER {x y : term} : orda [] x y = GREATER ↔ alpha_lt y x := by
  have h := orda_sym [] x y
  simp only [List.map_nil] at h
  unfold alpha_lt
  rw [← h]
  cases orda [] x y <;> simp [invert_comparison]

theorem Aux.alpha_lt_not_ACONV {x y : term} (h : alpha_lt x y) : ¬ ACONV x y := by
  rw [ACONV_eq_orda]
  unfold alpha_lt at h
  rw [h]
  intro h'; cases h'

/- HOL4:
Theorem transitive_alpha_lt:
   transitive alpha_lt
-/
theorem transitive_alpha_lt : transitive alpha_lt := by
  intro x y z h
  exact Aux.alpha_lt_trans h.1 h.2

/- HOL4:
Theorem alpha_lt_not_refl[simp]:
   ∀x. ¬alpha_lt x x
-/
theorem alpha_lt_not_refl : ∀ x : term, ¬ alpha_lt x x := by
  intro x h
  exact Aux.alpha_lt_not_ACONV h (ACONV_REFL x)

theorem Aux.ALPHAVARS_frees {α : Type u} (v : α) (env : List (α × α)) (s t : α)
    (h : ALPHAVARS env (s, t)) :
    (s = v ∧ ¬ (∃ y, (v, y) ∈ env)) ↔ (t = v ∧ ¬ (∃ y, (y, v) ∈ env)) := by
  induction env with
  | nil =>
    have h' : s = t := h
    simp [h']
  | cons p env ih =>
    obtain ⟨a, b⟩ := p
    simp only [ALPHAVARS, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | ⟨ha, hb, h⟩
    · constructor
      · rintro ⟨rfl, h2⟩; exact absurd ⟨t, List.mem_cons_self⟩ h2
      · rintro ⟨rfl, h2⟩; exact absurd ⟨s, List.mem_cons_self⟩ h2
    · have ih' := ih h
      simp only [List.mem_cons, Prod.mk.injEq]
      constructor
      · rintro ⟨e, h2⟩
        obtain ⟨e2, h3⟩ := ih'.mp ⟨e, fun ⟨y, hy⟩ => h2 ⟨y, Or.inr hy⟩⟩
        refine ⟨e2, ?_⟩
        rintro ⟨y, ⟨_, e3⟩ | hy⟩
        · exact hb (e3.symm.trans e2.symm)
        · exact h3 ⟨y, hy⟩
      · rintro ⟨e, h2⟩
        obtain ⟨e2, h3⟩ := ih'.mpr ⟨e, fun ⟨y, hy⟩ => h2 ⟨y, Or.inr hy⟩⟩
        refine ⟨e2, ?_⟩
        rintro ⟨y, ⟨e3, _⟩ | hy⟩
        · exact ha (e3.symm.trans e2.symm)
        · exact h3 ⟨y, hy⟩

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
  | Var ha => intro x ty; exact Aux.ALPHAVARS_frees (Var x ty) _ _ _ ha
  | Const => intro x ty; simp [VFREE_IN]
  | Comb _ _ ih1 ih2 =>
    intro x ty
    have h1 := ih1 x ty
    have h2 := ih2 x ty
    simp only [VFREE_IN]
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
  simpa using VFREE_IN_RACONV [] (s, t) h x ty

/- HOL4:
Theorem hypset_ok_nil[simp]:
   hypset_ok []
-/
theorem hypset_ok_nil : hypset_ok [] := by
  simp [hypset_ok, SORTED]

/- HOL4:
Theorem hypset_ok_sing[simp]:
   ∀p. hypset_ok [p]
-/
theorem hypset_ok_sing : ∀ p : term, hypset_ok [p] := by
  intro p
  simp [hypset_ok, SORTED]

theorem Aux.SORTED_cons {α : Type u} {R : α → α → Prop} (ht : transitive R) (l : List α) :
    ∀ h, SORTED R (h :: l) ↔ EVERY (R h) l ∧ SORTED R l := by
  induction l with
  | nil => intro h; simp [SORTED, EVERY]
  | cons b t ih =>
    intro h
    simp only [SORTED, EVERY]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨⟨h1, ?_⟩, h2⟩
      rw [Aux.EVERY_iff]
      intro x hx
      exact ht h b x ⟨h1, (Aux.EVERY_iff _ _).mp ((ih b).mp h2).1 x hx⟩
    · rintro ⟨⟨h1, _⟩, h2⟩
      exact ⟨h1, h2⟩

/- HOL4:
Theorem hypset_ok_cons:
   hypset_ok (h::hs) ⇔
    EVERY (alpha_lt h) hs ∧ hypset_ok hs
-/
theorem hypset_ok_cons (h : term) (hs : List term) :
    hypset_ok (h :: hs) ↔ EVERY (alpha_lt h) hs ∧ hypset_ok hs := by
  exact Aux.SORTED_cons transitive_alpha_lt hs h

/- HOL4:
Theorem term_union_idem[simp]:
   ∀ls. term_union ls ls = ls
-/
theorem term_union_idem : ∀ ls : List term, term_union ls ls = ls := by
  intro ls
  induction ls with
  | nil => rw [term_union]
  | cons a t ih =>
    rw [term_union]
    simp only [(ACONV_eq_orda a a).mp (ACONV_REFL a), if_true, ih]

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
  refine ⟨fun l2 => by rw [term_union], fun l1 => ?_, fun h1 t1 h2 t2 => ?_⟩
  · cases l1 with
    | nil => rw [term_union]
    | cons a t => rw [term_union]; simp
  · rw [term_union]
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
      intro x hx
      rw [term_union_thm.2.2] at hx
      split at hx
      · rcases List.mem_cons.mp hx with rfl | hx
        · simp
        · rcases ih1 _ _ hx with h | h <;> simp [h]
      · rcases List.mem_cons.mp hx with rfl | hx
        · simp
        · rcases ih1 _ _ hx with h | h
          · simp [h]
          · exact Or.inr h
      · rcases List.mem_cons.mp hx with rfl | hx
        · simp
        · rcases ih2 _ hx with h | h
          · exact Or.inl h
          · simp [h]

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
  | nil => intro l2 h; rw [term_union_thm.1]; exact h.2
  | cons h1 t1 ih1 =>
    intro l2
    induction l2 with
    | nil => intro h; rw [term_union_thm.2.1]; exact h.1
    | cons h2 t2 ih2 =>
      rintro ⟨k1, k2⟩
      have k1' := (hypset_ok_cons h1 t1).mp k1
      have k2' := (hypset_ok_cons h2 t2).mp k2
      rw [Aux.EVERY_iff] at k1' k2'
      rw [term_union_thm.2.2]
      split
      · next hc =>
        rw [← ACONV_eq_orda] at hc
        rw [hypset_ok_cons, Aux.EVERY_iff]
        refine ⟨fun x hx => ?_, ih1 _ ⟨k1'.2, k2'.2⟩⟩
        rcases MEM_term_union_imp _ _ _ hx with h | h
        · exact k1'.1 x h
        · exact Aux.ACONV_alpha_lt hc (k2'.1 x h)
      · next hc =>
        have hc' : alpha_lt h1 h2 := hc
        rw [hypset_ok_cons, Aux.EVERY_iff]
        refine ⟨fun x hx => ?_, ih1 _ ⟨k1'.2, k2⟩⟩
        rcases MEM_term_union_imp _ _ _ hx with h | h
        · exact k1'.1 x h
        · rcases List.mem_cons.mp h with rfl | h
          · exact hc'
          · exact Aux.alpha_lt_trans hc' (k2'.1 x h)
      · next hc =>
        have hc' : alpha_lt h2 h1 := Aux.orda_GREATER.mp hc
        rw [hypset_ok_cons, Aux.EVERY_iff]
        refine ⟨fun x hx => ?_, ih2 ⟨k1, k2'.2⟩⟩
        rcases MEM_term_union_imp _ _ _ hx with h | h
        · rcases List.mem_cons.mp h with rfl | h
          · exact hc'
          · exact Aux.alpha_lt_trans hc' (k1'.1 x h)
        · exact k2'.1 x h

/- HOL4:
Theorem EVERY_term_union:
   EVERY P l1 ∧ EVERY P l2 ⇒ EVERY P (term_union l1 l2)
-/
theorem EVERY_term_union (P : term → Prop) (l1 l2 : List term) :
    EVERY P l1 ∧ EVERY P l2 → EVERY P (term_union l1 l2) := by
  simp only [Aux.EVERY_iff]
  rintro ⟨h1, h2⟩ x hx
  rcases MEM_term_union_imp _ _ _ hx with h | h
  · exact h1 x h
  · exact h2 x h

/- HOL4:
Theorem MEM_term_union:
   ∀h1 h2 t. hypset_ok h1 ∧ hypset_ok h2 ∧ (MEM t h1 ∨ MEM t h2) ⇒
      ∃y. MEM y (term_union h1 h2) ∧ ACONV t y
-/
theorem MEM_term_union :
    ∀ (h1 h2 : List term) (t : term), hypset_ok h1 ∧ hypset_ok h2 ∧ (t ∈ h1 ∨ t ∈ h2) →
      ∃ y, y ∈ term_union h1 h2 ∧ ACONV t y := by
  intro l1
  induction l1 with
  | nil =>
    rintro l2 t ⟨_, _, h⟩
    rw [term_union_thm.1]
    simp only [List.not_mem_nil, false_or] at h
    exact ⟨t, h, ACONV_REFL t⟩
  | cons h1 t1 ih1 =>
    intro l2
    induction l2 with
    | nil =>
      rintro t ⟨_, _, h⟩
      rw [term_union_thm.2.1]
      simp only [List.not_mem_nil, or_false] at h
      exact ⟨t, h, ACONV_REFL t⟩
    | cons h2 t2 ih2 =>
      rintro t ⟨k1, k2, h⟩
      have k1' := ((hypset_ok_cons h1 t1).mp k1).2
      have k2' := ((hypset_ok_cons h2 t2).mp k2).2
      rw [term_union_thm.2.2]
      split
      · next hc =>
        rw [← ACONV_eq_orda] at hc
        simp only [List.mem_cons] at h
        rcases h with (rfl | h) | (rfl | h)
        · exact ⟨t, List.mem_cons_self, ACONV_REFL t⟩
        · obtain ⟨y, hy, ha⟩ := ih1 t2 t ⟨k1', k2', Or.inl h⟩
          exact ⟨y, List.mem_cons_of_mem _ hy, ha⟩
        · exact ⟨h1, List.mem_cons_self, ACONV_SYM _ _ hc⟩
        · obtain ⟨y, hy, ha⟩ := ih1 t2 t ⟨k1', k2', Or.inr h⟩
          exact ⟨y, List.mem_cons_of_mem _ hy, ha⟩
      · rcases h with h | h
        · rcases List.mem_cons.mp h with rfl | h
          · exact ⟨t, List.mem_cons_self, ACONV_REFL t⟩
          · obtain ⟨y, hy, ha⟩ := ih1 (h2 :: t2) t ⟨k1', k2, Or.inl h⟩
            exact ⟨y, List.mem_cons_of_mem _ hy, ha⟩
        · obtain ⟨y, hy, ha⟩ := ih1 (h2 :: t2) t ⟨k1', k2, Or.inr h⟩
          exact ⟨y, List.mem_cons_of_mem _ hy, ha⟩
      · rcases h with h | h
        · obtain ⟨y, hy, ha⟩ := ih2 t ⟨k1, k2', Or.inl h⟩
          exact ⟨y, List.mem_cons_of_mem _ hy, ha⟩
        · rcases List.mem_cons.mp h with rfl | h
          · exact ⟨t, List.mem_cons_self, ACONV_REFL t⟩
          · obtain ⟨y, hy, ha⟩ := ih2 t ⟨k1, k2', Or.inr h⟩
            exact ⟨y, List.mem_cons_of_mem _ hy, ha⟩

/- HOL4:
Theorem term_remove_nil[simp]:
   ∀a. term_remove a [] = []
-/
theorem term_remove_nil : ∀ a : term, term_remove a [] = [] := by
  intro a
  simp only [term_remove]

theorem Aux.term_remove_cons (t s : term) (ss : List term) :
    term_remove t (s :: ss) =
      match orda [] t s with
      | GREATER => s :: term_remove t ss
      | EQUAL => ss
      | LESS => s :: ss := by
  simp only [term_remove]
  cases orda [] t s with
  | LESS => simp
  | EQUAL => simp
  | GREATER =>
    by_cases h : term_remove t ss = ss <;> simp [h]

/- HOL4:
Theorem MEM_term_remove_imp:
   ∀ls x t. MEM t (term_remove x ls) ⇒
      MEM t ls ∧ (hypset_ok ls ⇒ ¬ACONV x t)
-/
theorem MEM_term_remove_imp :
    ∀ (ls : List term) (x t : term), t ∈ term_remove x ls →
      t ∈ ls ∧ (hypset_ok ls → ¬ ACONV x t) := by
  intro ls x t
  induction ls with
  | nil => intro h; rw [term_remove_nil] at h; simp at h
  | cons s ss ih =>
    intro h
    rw [Aux.term_remove_cons] at h
    split at h
    · next hc =>
      rcases List.mem_cons.mp h with rfl | h
      · refine ⟨List.mem_cons_self, fun _ ha => ?_⟩
        rw [ACONV_eq_orda, hc] at ha
        cases ha
      · exact ⟨List.mem_cons_of_mem _ (ih h).1,
          fun hh => (ih h).2 ((hypset_ok_cons s ss).mp hh).2⟩
    · next hc =>
      rw [← ACONV_eq_orda] at hc
      refine ⟨List.mem_cons_of_mem _ h, fun hh ha => ?_⟩
      have h1 := (Aux.EVERY_iff _ _).mp ((hypset_ok_cons s ss).mp hh).1 t h
      exact Aux.alpha_lt_not_ACONV h1 (ACONV_TRANS _ _ _ ⟨ACONV_SYM _ _ hc, ha⟩)
    · next hc =>
      refine ⟨h, fun hh ha => ?_⟩
      have hc' : alpha_lt x s := hc
      rcases List.mem_cons.mp h with rfl | h
      · exact Aux.alpha_lt_not_ACONV hc' ha
      · have h1 := (Aux.EVERY_iff _ _).mp ((hypset_ok_cons s ss).mp hh).1 t h
        exact Aux.alpha_lt_not_ACONV (Aux.alpha_lt_trans hc' h1) ha

/- HOL4:
Theorem hypset_ok_term_remove[simp]:
   ∀ls. hypset_ok ls ⇒ ∀t. hypset_ok (term_remove t ls)
-/
theorem hypset_ok_term_remove :
    ∀ ls : List term, hypset_ok ls → ∀ t : term, hypset_ok (term_remove t ls) := by
  intro ls
  induction ls with
  | nil => intro h t; rw [term_remove_nil]; exact h
  | cons s ss ih =>
    intro h t
    have h' := (hypset_ok_cons s ss).mp h
    rw [Aux.EVERY_iff] at h'
    rw [Aux.term_remove_cons]
    split
    · rw [hypset_ok_cons, Aux.EVERY_iff]
      exact ⟨fun x hx => h'.1 x (MEM_term_remove_imp _ _ _ hx).1, ih h'.2 t⟩
    · exact h'.2
    · exact h

/- HOL4:
Theorem EVERY_term_remove:
   EVERY P ls ⇒ EVERY P (term_remove t ls)
-/
theorem EVERY_term_remove (P : term → Prop) (ls : List term) (t : term) :
    EVERY P ls → EVERY P (term_remove t ls) := by
  simp only [Aux.EVERY_iff]
  intro h x hx
  exact h x (MEM_term_remove_imp _ _ _ hx).1

/- HOL4:
Theorem MEM_term_remove:
   ∀h x t. MEM t h ∧ ¬ACONV x t ∧ hypset_ok h
    ⇒ MEM t (term_remove x h)
-/
theorem MEM_term_remove :
    ∀ (h : List term) (x t : term), t ∈ h ∧ ¬ ACONV x t ∧ hypset_ok h →
      t ∈ term_remove x h := by
  intro ls x t
  induction ls with
  | nil => rintro ⟨h, _⟩; simp at h
  | cons s ss ih =>
    rintro ⟨hm, hn, hh⟩
    rw [Aux.term_remove_cons]
    split
    · rcases List.mem_cons.mp hm with rfl | hm
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih ⟨hm, hn, ((hypset_ok_cons s ss).mp hh).2⟩)
    · next hc =>
      rw [← ACONV_eq_orda] at hc
      rcases List.mem_cons.mp hm with rfl | hm
      · exact absurd hc hn
      · exact hm
    · exact hm

/- HOL4:
Theorem term_image_nil[simp]:
   term_image f [] = []
-/
theorem term_image_nil (f : term → term) : term_image f [] = [] := by
  simp only [term_image]

theorem Aux.term_image_cons (f : term → term) (h : term) (t : List term) :
    term_image f (h :: t) =
      if f h = h ∧ term_image f t = t then h :: t else term_union [f h] (term_image f t) := by
  simp only [term_image]

/- HOL4:
Theorem MEM_term_image_imp:
   ∀ls f t. MEM t (term_image f ls) ⇒ ∃x. MEM x ls ∧ t = f x
-/
theorem MEM_term_image_imp :
    ∀ (ls : List term) (f : term → term) (t : term), t ∈ term_image f ls →
      ∃ x, x ∈ ls ∧ t = f x := by
  intro ls f t
  induction ls with
  | nil => intro h; rw [term_image_nil] at h; simp at h
  | cons a l ih =>
    intro h
    rw [Aux.term_image_cons] at h
    split at h
    · next hc =>
      rcases List.mem_cons.mp h with rfl | h
      · exact ⟨t, List.mem_cons_self, hc.1.symm⟩
      · obtain ⟨x, hx, e⟩ := ih (by rw [hc.2]; exact h)
        exact ⟨x, List.mem_cons_of_mem _ hx, e⟩
    · rcases MEM_term_union_imp _ _ _ h with h | h
      · exact ⟨a, List.mem_cons_self, List.mem_singleton.mp h⟩
      · obtain ⟨x, hx, e⟩ := ih h
        exact ⟨x, List.mem_cons_of_mem _ hx, e⟩

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
    · exact hypset_ok_term_union _ _ ⟨hypset_ok_sing _, ih ((hypset_ok_cons a l).mp h).2⟩

/- HOL4:
Theorem MEM_term_image:
   ∀ls f t. MEM t ls ∧ hypset_ok ls ⇒ ∃y. MEM y (term_image f ls) ∧ ACONV (f t) y
-/
theorem MEM_term_image :
    ∀ (ls : List term) (f : term → term) (t : term), t ∈ ls ∧ hypset_ok ls →
      ∃ y, y ∈ term_image f ls ∧ ACONV (f t) y := by
  intro ls f t
  induction ls with
  | nil => rintro ⟨h, _⟩; simp at h
  | cons a l ih =>
    rintro ⟨hm, hh⟩
    have hh' := ((hypset_ok_cons a l).mp hh).2
    rw [Aux.term_image_cons]
    split
    · next hc =>
      rcases List.mem_cons.mp hm with rfl | hm
      · exact ⟨t, List.mem_cons_self, by rw [hc.1]; exact ACONV_REFL t⟩
      · obtain ⟨y, hy, ha⟩ := ih ⟨hm, hh'⟩
        rw [hc.2] at hy
        exact ⟨y, List.mem_cons_of_mem _ hy, ha⟩
    · have hi := hypset_ok_term_image l f hh'
      rcases List.mem_cons.mp hm with rfl | hm
      · exact MEM_term_union _ _ _ ⟨hypset_ok_sing _, hi, Or.inl List.mem_cons_self⟩
      · obtain ⟨y, hy, ha⟩ := ih ⟨hm, hh'⟩
        obtain ⟨z, hz, hb⟩ := MEM_term_union [f a] (term_image f l) y ⟨hypset_ok_sing _, hi, Or.inr hy⟩
        exact ⟨z, hz, ACONV_TRANS _ _ _ ⟨ha, hb⟩⟩

theorem Aux.has_type_unique {t : term} {a b : type} (h1 : has_type t a) (h2 : has_type t b) : a = b :=
  (WELLTYPED_LEMMA _ _ h1).symm.trans (WELLTYPED_LEMMA _ _ h2)

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
    rintro ty ilist ⟨ht, hi⟩
    cases ht
    simp only [VSUBST]
    rcases REV_ASSOCD_MEM ilist (Var x ty') (Var x ty') with h | h
    · obtain ⟨x', ty'', e, h'⟩ := hi _ _ h
      obtain ⟨rfl, rfl⟩ := term.Var.inj e
      exact h'
    · rw [h]; exact has_type.Var
  | Const x ty' =>
    rintro ty ilist ⟨ht, hi⟩
    simp only [VSUBST]
    exact ht
  | Comb a b iha ihb =>
    rintro ty ilist ⟨ht, hi⟩
    simp only [VSUBST]
    cases ht with
    | Comb h1 h2 => exact has_type.Comb (iha _ _ ⟨h1, hi⟩) (ihb _ _ ⟨h2, hi⟩)
  | Abs v b _ ihb =>
    rintro ty ilist ⟨ht, hi⟩
    cases ht with
    | @Abs n dty rty _ h =>
      have hf : ∀ s s', (s', s) ∈ FILTER (fun p => ¬ (p.2 = Var n dty)) ilist →
          ∃ x ty, s = Var x ty ∧ has_type s' ty :=
        fun s s' hm => hi s s' (Aux.mem_FILTER_imp _ _ _ hm)
      simp only [VSUBST, dest_var_def]
      split
      · refine has_type.Abs (ihb _ _ ⟨h, fun s s' hm => ?_⟩)
        rcases List.mem_cons.mp hm with hm | hm
        · cases hm; exact ⟨n, dty, rfl, has_type.Var⟩
        · exact hf s s' hm
      · exact has_type.Abs (ihb _ _ ⟨h, hf⟩)

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
  rintro tm _ ilist ⟨⟨ty, h⟩, hi⟩
  exact ⟨ty, VSUBST_HAS_TYPE tm ty ilist ⟨h, hi⟩⟩

end

end Candle
