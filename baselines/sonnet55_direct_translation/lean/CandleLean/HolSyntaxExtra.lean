import CandleLean.HolSyntax
/-
  Translation of the definitions of `candle/standard/syntax/holSyntaxExtraScript.sml`.
  Namespace `Candle.HolSyntaxExtra`.
-/
namespace Candle.HolSyntaxExtra

open HOL Candle.Misc Candle.Mlstring Candle.HolSyntaxLib Candle.HolSyntax
universe u v

open Classical

noncomputable section

/- HOL4: Inductive subtype1:
  MEM a args ⇒ subtype1 a (Tyapp name args)
End -/
inductive subtype1 : type → type → Prop where
  | mk (a : type) (name : mlstring) (args : List type) : MEM a args → subtype1 a (.Tyapp name args)

/- HOL4: Overload subtype =``RTC subtype1``   (infix `ty1 subtype ty2`) -/
def subtype : type → type → Prop := RTC subtype1

/- HOL4: Inductive subterm1:
  subterm1 t1 (Comb t1 t2) ∧
  subterm1 t2 (Comb t1 t2) ∧
  subterm1 tm (Abs v tm) ∧
  subterm1 v (Abs v tm)
End -/
inductive subterm1 : term → term → Prop where
  | comb_l (t1 t2 : term) : subterm1 t1 (.Comb t1 t2)
  | comb_r (t1 t2 : term) : subterm1 t2 (.Comb t1 t2)
  | abs_body (tm v : term) : subterm1 tm (.Abs v tm)
  | abs_var (tm v : term) : subterm1 v (.Abs v tm)

/- HOL4: Overload subterm =``RTC subterm1``   (infix `t1 subterm t2`) -/
def subterm : term → term → Prop := RTC subterm1

/- HOL4: Datatype:
  dbterm =
    dbVar mlstring type
  | dbBound num
  | dbConst mlstring type
  | dbComb dbterm dbterm
  | dbAbs type dbterm
End
   (the Lean type is named `DbTerm`, since the constant `dbterm` (below) shares the name `dbterm`) -/
inductive DbTerm where
  | dbVar : mlstring → type → DbTerm
  | dbBound : Nat → DbTerm
  | dbConst : mlstring → type → DbTerm
  | dbComb : DbTerm → DbTerm → DbTerm
  | dbAbs : type → DbTerm → DbTerm

export DbTerm (dbVar dbBound dbConst dbComb dbAbs)

/- HOL4: Definition bind_def[simp]:
  (bind v n (dbVar x ty) = if v = (x,ty) then dbBound n else dbVar x ty) ∧
  bind v n (dbBound m) = dbBound m ∧
  bind v n (dbConst x ty) = dbConst x ty ∧
  bind v n (dbComb t1 t2) = dbComb (bind v n t1) (bind v n t2) ∧
  bind v n (dbAbs ty tm) = dbAbs ty (bind v (n+1) tm)
End -/
def bind (v : mlstring × type) : Nat → DbTerm → DbTerm
  | n, .dbVar x ty => if v = (x, ty) then .dbBound n else .dbVar x ty
  | _, .dbBound m => .dbBound m
  | _, .dbConst x ty => .dbConst x ty
  | n, .dbComb t1 t2 => .dbComb (bind v n t1) (bind v n t2)
  | n, .dbAbs ty tm => .dbAbs ty (bind v (n + 1) tm)

/- HOL4: Definition db_def[simp]:
  db (Var x ty) = dbVar x ty ∧
  db (Const x ty) = dbConst x ty ∧
  db (Comb t1 t2) = dbComb (db t1) (db t2) ∧
  db (Abs v tm) = dbAbs (typeof v) (bind (dest_var v) 0 (db tm))
End -/
def db : term → DbTerm
  | .Var x ty => .dbVar x ty
  | .Const x ty => .dbConst x ty
  | .Comb t1 t2 => .dbComb (db t1) (db t2)
  | .Abs v tm => .dbAbs (typeof v) (bind (dest_var v) 0 (db tm))

/- HOL4: Definition dbVSUBST_def[simp]:
  dbVSUBST ilist (dbVar x ty) = REV_ASSOCD (dbVar x ty) ilist (dbVar x ty) ∧
  dbVSUBST ilist (dbBound m) = dbBound m ∧
  dbVSUBST ilist (dbConst x ty) = dbConst x ty ∧
  dbVSUBST ilist (dbComb t1 t2) = dbComb (dbVSUBST ilist t1) (dbVSUBST ilist t2) ∧
  dbVSUBST ilist (dbAbs ty t) = dbAbs ty (dbVSUBST ilist t)
End -/
def dbVSUBST (ilist : List (DbTerm × DbTerm)) : DbTerm → DbTerm
  | .dbVar x ty => REV_ASSOCD (.dbVar x ty) ilist (.dbVar x ty)
  | .dbBound m => .dbBound m
  | .dbConst x ty => .dbConst x ty
  | .dbComb t1 t2 => .dbComb (dbVSUBST ilist t1) (dbVSUBST ilist t2)
  | .dbAbs ty t => .dbAbs ty (dbVSUBST ilist t)

/- HOL4: Definition dbVFREE_IN_def[simp]:
  (dbVFREE_IN v (dbVar x ty) ⇔ dbVar x ty = v) ∧
  (dbVFREE_IN v (dbBound n) ⇔ F) ∧
  (dbVFREE_IN v (dbConst x ty) ⇔ dbConst x ty = v) ∧
  (dbVFREE_IN v (dbComb t1 t2) ⇔ (dbVFREE_IN v t1 ∨ dbVFREE_IN v t2)) ∧
  (dbVFREE_IN v (dbAbs ty t) ⇔ dbVFREE_IN v t)
End -/
def dbVFREE_IN (v : DbTerm) : DbTerm → Prop
  | .dbVar x ty => .dbVar x ty = v
  | .dbBound _ => False
  | .dbConst x ty => .dbConst x ty = v
  | .dbComb t1 t2 => dbVFREE_IN v t1 ∨ dbVFREE_IN v t2
  | .dbAbs _ t => dbVFREE_IN v t

/- HOL4: Definition dbINST_def[simp]:
  dbINST tyin (dbVar x ty) = dbVar x (TYPE_SUBST tyin ty) ∧
  dbINST tyin (dbBound n) = dbBound n ∧
  dbINST tyin (dbConst x ty) = dbConst x (TYPE_SUBST tyin ty) ∧
  dbINST tyin (dbComb t1 t2) = dbComb (dbINST tyin t1) (dbINST tyin t2) ∧
  dbINST tyin (dbAbs ty t) = dbAbs (TYPE_SUBST tyin ty) (dbINST tyin t)
End -/
def dbINST (tyin : List (type × type)) : DbTerm → DbTerm
  | .dbVar x ty => .dbVar x (TYPE_SUBST tyin ty)
  | .dbBound n => .dbBound n
  | .dbConst x ty => .dbConst x (TYPE_SUBST tyin ty)
  | .dbComb t1 t2 => .dbComb (dbINST tyin t1) (dbINST tyin t2)
  | .dbAbs ty t => .dbAbs (TYPE_SUBST tyin ty) (dbINST tyin t)

/- HOL4: Definition dbterm_def[simp]:
  (dbterm env (Var s ty) =
     case find_index (s,ty) env 0 of SOME n => dbBound n | NONE => dbVar s ty) ∧
  (dbterm env (Const s ty) = dbConst s ty) ∧
  (dbterm env (Comb t1 t2) = dbComb (dbterm env t1) (dbterm env t2)) ∧
  (dbterm env (Abs v t) = dbAbs (typeof v) (dbterm ((dest_var v)::env) t))
End -/
def dbterm (env : List (mlstring × type)) : term → DbTerm
  | .Var s ty =>
    match find_index (s, ty) env 0 with
    | some n => .dbBound n
    | none => .dbVar s ty
  | .Const s ty => .dbConst s ty
  | .Comb t1 t2 => .dbComb (dbterm env t1) (dbterm env t2)
  | .Abs v t => .dbAbs (typeof v) (dbterm (dest_var v :: env) t)

/- HOL4: Definition bind_list_aux_def[simp]:
  bind_list_aux n [] tm = tm ∧
  bind_list_aux n (v::vs) tm = bind_list_aux (n+1) vs (bind v n tm)
End -/
def bind_list_aux : Nat → List (mlstring × type) → DbTerm → DbTerm
  | _, [], tm => tm
  | n, v :: vs, tm => bind_list_aux (n + 1) vs (bind v n tm)

/- HOL4: Definition bv_names_def[simp]:
  bv_names (Var _ _) = [] ∧
  bv_names (Const _ _) = [] ∧
  bv_names (Comb s t) = bv_names s ++ bv_names t ∧
  bv_names (Abs v t) = (FST(dest_var v))::bv_names t
End -/
def bv_names : term → List mlstring
  | .Var _ _ => []
  | .Const _ _ => []
  | .Comb s t => bv_names s ++ bv_names t
  | .Abs v t => (FST (dest_var v)) :: bv_names t

/- HOL4: Definition simple_subst_def[simp]:
  (simple_subst ilist (Var x ty) = REV_ASSOCD (Var x ty) ilist (Var x ty)) ∧
  (simple_subst ilist (Const x ty) = Const x ty) ∧
  (simple_subst ilist (Comb t1 t2) = Comb (simple_subst ilist t1) (simple_subst ilist t2)) ∧
  (simple_subst ilist (Abs v tm) =
    Abs v (simple_subst (FILTER (λ(s',s). (s ≠ v)) ilist) tm))
End -/
def simple_subst : List (term × term) → term → term
  | ilist, .Var x ty => REV_ASSOCD (.Var x ty) ilist (.Var x ty)
  | _, .Const x ty => .Const x ty
  | ilist, .Comb t1 t2 => .Comb (simple_subst ilist t1) (simple_subst ilist t2)
  | ilist, .Abs v tm => .Abs v (simple_subst (FILTER (fun p => p.2 ≠ v) ilist) tm)

/- HOL4: Definition simple_inst_def[simp]:
  simple_inst tyin (Var x ty) = Var x (TYPE_SUBST tyin ty) ∧
  simple_inst tyin (Const x ty) = Const x (TYPE_SUBST tyin ty) ∧
  simple_inst tyin (Comb s t) = Comb (simple_inst tyin s) (simple_inst tyin t) ∧
  simple_inst tyin (Abs v t) = Abs (simple_inst tyin v) (simple_inst tyin t)
End -/
def simple_inst (tyin : List (type × type)) : term → term
  | .Var x ty => .Var x (TYPE_SUBST tyin ty)
  | .Const x ty => .Const x (TYPE_SUBST tyin ty)
  | .Comb s t => .Comb (simple_inst tyin s) (simple_inst tyin t)
  | .Abs v t => .Abs (simple_inst tyin v) (simple_inst tyin t)

/- HOL4: Definition rename_bvars_def:
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
def rename_bvars : List mlstring → List (mlstring × (mlstring × type)) → term →
    List mlstring × term
  | names, env, .Var s ty => (names, .Var (REV_ASSOCD (s, ty) env s) ty)
  | names, _, .Const s ty => (names, .Const s ty)
  | names, env, .Comb t1 t2 =>
    let r1 := rename_bvars names env t1
    let r2 := rename_bvars r1.1 env t2
    (r2.1, .Comb r1.2 r2.2)
  | [], env, .Abs v tm =>
    let r := rename_bvars [] env tm
    (r.1, .Abs v r.2)
  | s' :: names, env, .Abs v tm =>
    let r := rename_bvars names ((s', dest_var v) :: env) tm
    (r.1, .Abs (.Var s' (typeof v)) r.2)

/- HOL4: val fresh_def = new_specification("fresh_def",["fresh"], ...)
   i.e. a function `fresh : string set -> string` with `∀s. FINITE s ⇒ fresh s ∉ s`
   (it exists because `string` is infinite).  Defined by Hilbert choice. -/
def fresh (s : Set string) : string := ε (fun x => x ∉ s)

/- HOL4: val fresh_term_def = new_specification("fresh_term_def",["fresh_term"],
  Q.prove(`∃f. ∀s tm. FINITE s ⇒
                     welltyped tm ⇒
                     welltyped (f s tm) ∧
                     ACONV tm (f s tm) ∧
                     ALL_DISTINCT (bv_names (f s tm)) ∧
                     DISJOINT (set (bv_names (f s tm))) s`, ...))
   `fresh_term : mlstring set -> term -> term`.  Defined by Hilbert choice from the specification. -/
def fresh_term (s : Set mlstring) (tm : term) : term :=
  ε (fun r => FINITE s → welltyped tm →
      welltyped r ∧ ACONV tm r ∧ ALL_DISTINCT (bv_names r) ∧
      DISJOINT (LIST_TO_SET (bv_names r)) s)

/- HOL4: Definition vfree_in_def:
  vfree_in v tm =
    case tm of
      Abs bv bod => v <> bv /\ vfree_in v bod
    | Comb s t => vfree_in v s \/ vfree_in v t
    | _ => (tm = v)
End -/
def vfree_in (v : term) : term → Prop
  | .Abs bv bod => v ≠ bv ∧ vfree_in v bod
  | .Comb s t => vfree_in v s ∨ vfree_in v t
  | tm => tm = v

/-- Helper for the termination of `variant`: an upper bound on `strlen x + 1` for the names of
    free variables of a term. -/
def variant_fvlen : term → Nat
  | .Var x _ => strlen x + 1
  | .Const _ _ => 0
  | .Comb s t => MAX (variant_fvlen s) (variant_fvlen t)
  | .Abs _ t => variant_fvlen t

/-- Helper for the termination of `variant`: the bound for a list of terms. -/
def variant_bound : List term → Nat
  | [] => 0
  | a :: l => MAX (variant_fvlen a) (variant_bound l)

theorem variant_fvlen_spec (a : term) (x : mlstring) (ty : type) :
    vfree_in (.Var x ty) a → strlen x + 1 ≤ variant_fvlen a := by
  induction a with
  | Var y ty' =>
    intro h; simp only [vfree_in, term.Var.injEq] at h; obtain ⟨rfl, _⟩ := h
    simp [variant_fvlen]
  | Const y ty' => intro h; simp [vfree_in] at h
  | Comb s t ihs iht =>
    intro h
    simp only [vfree_in] at h
    simp only [variant_fvlen, MAX]
    rcases h with h | h
    · have := ihs h; split <;> omega
    · have := iht h; split <;> omega
  | Abs v t ihs iht =>
    intro h; simp only [vfree_in] at h; exact iht h.2

theorem variant_bound_spec (avoid : List term) (x : mlstring) (ty : type) :
    EXISTS (vfree_in (.Var x ty)) avoid → strlen x + 1 ≤ variant_bound avoid := by
  induction avoid with
  | nil => simp [EXISTS]
  | cons a l ih =>
    intro h
    simp only [EXISTS] at h
    simp only [variant_bound, MAX]
    rcases h with h | h
    · have := variant_fvlen_spec a x ty h; split <;> omega
    · have := ih h; split <;> omega

theorem strlen_strcat_prime_helper (s : mlstring) : strlen (strcat s (ml "'")) = strlen s + 1 := by
  cases s with
  | implode l =>
    simp [strcat, concat, strlen, ml, hstr, FLAT, MAP, LENGTH]
    rfl

/- HOL4: Definition variant_def:
  variant avoid v =
    if EXISTS (vfree_in v) avoid then
    case v of
       Var s ty => variant avoid (Var(s ^ «'») ty)
    | _ => v else v
Termination
  WF_REL_TAC `measure (\(avoid,v).
     let n = SUM_SET (BIGUNION (set (MAP (λa. {strlen x + 1 | ∃ty. VFREE_IN (Var x ty) a}) avoid))) in
       n - (case v of Var x ty => strlen x | _ => 0))` >> ...
End
   (a different, equally valid, termination measure is used here.) -/
def variant (avoid : List term) (v : term) : term :=
  if h : EXISTS (vfree_in v) avoid then
    match v, h with
    | .Var s ty, h => variant avoid (.Var (strcat s (ml "'")) ty)
    | v, _ => v
  else v
termination_by (variant_bound avoid - (match v with | .Var x _ => strlen x | _ => 0))
decreasing_by
  all_goals simp_wf
  have := variant_bound_spec avoid s ty h
  rw [strlen_strcat_prime_helper]
  omega

/- HOL4: Definition subtract_def:
  subtract l1 l2 = FILTER (\t. ~(MEM t l2)) l1
End -/
def subtract {α : Type u} (l1 l2 : List α) : List α := FILTER (fun t => ¬ MEM t l2) l1

/- HOL4: Definition insert_def:
  insert x l = if MEM x l then l else x::l
End -/
def insert {α : Type u} (x : α) (l : List α) : List α := if MEM x l then l else x :: l

/- HOL4: Definition itlist_def:
  itlist f l b =
    case l of
      [] => b
    | (h::t) => f h (itlist f t b)
End -/
def itlist {α : Type u} {β : Type v} (f : α → β → β) : List α → β → β
  | [], b => b
  | h :: t, b => f h (itlist f t b)

/- HOL4: Definition union_def:
  union l1 l2 = itlist insert l1 l2
End -/
def union {α : Type u} (l1 l2 : List α) : List α := itlist insert l1 l2

/- HOL4: Definition frees_def:
  frees tm =
    case tm of
      Var _ _ => [tm]
    | Const _ _ => []
    | Abs bv bod => subtract (frees bod) [bv]
    | Comb s t => union (frees s) (frees t)
End -/
def frees : term → List term
  | .Var x ty => [.Var x ty]
  | .Const _ _ => []
  | .Abs bv bod => subtract (frees bod) [bv]
  | .Comb s t => union (frees s) (frees t)

/- HOL4: Overload ConstDef = ``λx t. ConstSpec [(x,t)] (Var x (typeof t) === t)`` -/
def ConstDef (x : mlstring) (t : term) : update := .ConstSpec [(x, t)] (Var x (typeof t) === t)

/- HOL4: Definition types_in_def[simp]:
  types_in (Var x ty) = {ty} ∧
  types_in (Const c ty) = {ty} ∧
  types_in (Comb t1 t2) = types_in t1 ∪ types_in t2 ∧
  types_in (Abs v t) = types_in v ∪ types_in t
End -/
def types_in : term → Set type
  | .Var _ ty => {ty}
  | .Const _ ty => {ty}
  | .Comb t1 t2 => types_in t1 ∪ types_in t2
  | .Abs v t => types_in v ∪ types_in t

/- HOL4: Definition arities_match_def:
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
  | .Tyapp c1 a1 :: xs, .Tyapp c2 a2 :: ys => (c1 = c2 → arities_match a1 a2) ∧ arities_match xs ys
  | _ :: xs, _ :: ys => arities_match xs ys
termination_by xs => sizeOf xs
decreasing_by all_goals (simp_wf; omega)

/- ===== Stage 2: theorem statements ===== -/

/- HOL4: Theorem ALOOKUP_MAP_dest_var:
   ∀ls f x ty.
      EVERY (λs. ∃x ty. s = Var x ty) (MAP FST ls) ⇒
      ALOOKUP (MAP (dest_var ## f) ls) (x,ty) =
      OPTION_MAP f (ALOOKUP ls (Var x ty)) -/
theorem ALOOKUP_MAP_dest_var {α β : Type u} (ls : List (term × α)) (f : α → β) (x : mlstring) (ty : type) :
    EVERY (fun s => ∃ x ty, s = Var x ty) (MAP FST ls) →
    ALOOKUP (MAP (dest_var ## f) ls) (x, ty) =
    OPTION_MAP f (ALOOKUP ls (Var x ty)) := by sorry

/- HOL4: Theorem TYPE_SUBST_NIL[simp]:
   ∀ty. TYPE_SUBST [] ty = ty -/
theorem TYPE_SUBST_NIL (ty : type) : TYPE_SUBST [] ty = ty := by sorry

/- HOL4: Theorem TYPE_SUBST_Bool:
   ∀tyin. TYPE_SUBST tyin Bool = Bool -/
theorem TYPE_SUBST_Bool (tyin : List (type × type)) : TYPE_SUBST tyin BoolTy = BoolTy := by sorry

/- HOL4: Theorem is_instance_refl[simp]:
   ∀ty. is_instance ty ty -/
theorem is_instance_refl (ty : type) : is_instance ty ty := by sorry

/- HOL4: Theorem swap_ff:
   ∀f g. (λ(x,y). (y,x)) o (f ## g) = (g ## f) o (λ(x,y). (y,x)) -/
theorem swap_ff {α β γ δ : Type u} (f : α → β) (g : γ → δ) :
    (fun p : β × δ => (p.2, p.1)) ∘ (f ## g) = (g ## f) ∘ (fun p : α × γ => (p.2, p.1)) := by sorry

/- HOL4: Theorem ff_def:
   ∀f g. (f ## g) = λ(x,y). (f x, g y) -/
theorem ff_def {α β γ δ : Type u} (f : α → β) (g : γ → δ) :
    (f ## g) = fun p : α × γ => (f p.1, g p.2) := by sorry

/- HOL4: Theorem TYPE_SUBST_compose:
   ∀tyin1 ty tyin2.
    TYPE_SUBST tyin2 (TYPE_SUBST tyin1 ty) =
    TYPE_SUBST ((MAP (TYPE_SUBST tyin2 ## I) tyin1) ++ tyin2) ty -/
theorem TYPE_SUBST_compose (tyin1 : List (type × type)) (ty : type) (tyin2 : List (type × type)) :
    TYPE_SUBST tyin2 (TYPE_SUBST tyin1 ty) =
    TYPE_SUBST ((MAP (TYPE_SUBST tyin2 ## I) tyin1) ++ tyin2) ty := by sorry

/- HOL4: Theorem TYPE_SUBST_tyvars:
   ∀ty tyin tyin'.
    (TYPE_SUBST tyin ty = TYPE_SUBST tyin' ty) ⇔
    ∀x. MEM x (tyvars ty) ⇒
        REV_ASSOCD (Tyvar x) tyin' (Tyvar x) =
        REV_ASSOCD (Tyvar x) tyin  (Tyvar x) -/
theorem TYPE_SUBST_tyvars (ty : type) (tyin tyin' : List (type × type)) :
    (TYPE_SUBST tyin ty = TYPE_SUBST tyin' ty) ↔
    ∀ x : mlstring, MEM x (tyvars ty) →
        REV_ASSOCD (Tyvar x) tyin' (Tyvar x) =
        REV_ASSOCD (Tyvar x) tyin (Tyvar x) := by sorry

/- HOL4: Theorem WELLTYPED_LEMMA:
   ∀tm ty. tm has_type ty ⇒ (typeof tm = ty) -/
theorem WELLTYPED_LEMMA (tm : term) (ty : type) : has_type tm ty → typeof tm = ty := by sorry

/- HOL4: Theorem WELLTYPED:
   ∀tm. welltyped tm ⇔ tm has_type (typeof tm) -/
theorem WELLTYPED (tm : term) : welltyped tm ↔ has_type tm (typeof tm) := by sorry

/- HOL4: Theorem WELLTYPED_CLAUSES[simp]:
  (!n ty. welltyped(Var n ty)) /\
   (!n ty. welltyped(Const n ty)) /\
   (!s t. welltyped (Comb s t) <=>
            welltyped s /\ welltyped t /\
            ?rty. typeof s = Fun (typeof t) rty) /\
   (!v t. welltyped (Abs v t) = ∃n ty. v = Var n ty ∧ welltyped t) -/
theorem WELLTYPED_CLAUSES :
    (∀ (n : mlstring) (ty : type), welltyped (Var n ty)) ∧
    (∀ (n : mlstring) (ty : type), welltyped (Const n ty)) ∧
    (∀ s t : term, welltyped (Comb s t) ↔
            welltyped s ∧ welltyped t ∧
            ∃ rty, typeof s = Fun (typeof t) rty) ∧
    (∀ v t : term, welltyped (Abs v t) = ∃ (n : mlstring) (ty : type), v = Var n ty ∧ welltyped t) := by sorry

/- HOL4: Theorem RACONV:
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
   (free variables are universally quantified) -/
theorem RACONV (env : List (term × term)) (x1 x2 : mlstring) (ty1 ty2 : type)
    (l1 r1 l2 r2 v1 t1 v2 t2 : term) :
    (HolSyntax.RACONV env (Var x1 ty1, Var x2 ty2) ↔
        ALPHAVARS env (Var x1 ty1, Var x2 ty2)) ∧
    (HolSyntax.RACONV env (Var x1 ty1, Const x2 ty2) ↔ False) ∧
    (HolSyntax.RACONV env (Var x1 ty1, Comb l2 r2) ↔ False) ∧
    (HolSyntax.RACONV env (Var x1 ty1, Abs v2 t2) ↔ False) ∧
    (HolSyntax.RACONV env (Const x1 ty1, Var x2 ty2) ↔ False) ∧
    (HolSyntax.RACONV env (Const x1 ty1, Const x2 ty2) ↔ (x1 = x2) ∧ (ty1 = ty2)) ∧
    (HolSyntax.RACONV env (Const x1 ty1, Comb l2 r2) ↔ False) ∧
    (HolSyntax.RACONV env (Const x1 ty1, Abs v2 t2) ↔ False) ∧
    (HolSyntax.RACONV env (Comb l1 r1, Var x2 ty2) ↔ False) ∧
    (HolSyntax.RACONV env (Comb l1 r1, Const x2 ty2) ↔ False) ∧
    (HolSyntax.RACONV env (Comb l1 r1, Comb l2 r2) ↔
        HolSyntax.RACONV env (l1, l2) ∧ HolSyntax.RACONV env (r1, r2)) ∧
    (HolSyntax.RACONV env (Comb l1 r1, Abs v2 t2) ↔ False) ∧
    (HolSyntax.RACONV env (Abs v1 t1, Var x2 ty2) ↔ False) ∧
    (HolSyntax.RACONV env (Abs v1 t1, Const x2 ty2) ↔ False) ∧
    (HolSyntax.RACONV env (Abs v1 t1, Comb l2 r2) ↔ False) ∧
    (HolSyntax.RACONV env (Abs v1 t1, Abs v2 t2) ↔
          typeof v1 = typeof v2 ∧
          HolSyntax.RACONV ((v1, v2) :: env) (t1, t2)) := by sorry

/- HOL4: Theorem RACONV_REFL:
   ∀t env. EVERY (UNCURRY $=) env ⇒ RACONV env (t,t) -/
theorem RACONV_REFL (t : term) (env : List (term × term)) :
    EVERY (UNCURRY (fun a b : term => a = b)) env → HolSyntax.RACONV env (t, t) := by sorry

/- HOL4: Theorem ACONV_REFL[simp]:
   ∀t. ACONV t t -/
theorem ACONV_REFL (t : term) : ACONV t t := by sorry

/- HOL4: Theorem RACONV_TRANS:
   ∀env tp. RACONV env tp ⇒ ∀vs t. LENGTH vs = LENGTH env ∧ RACONV (ZIP(MAP SND env,vs)) (SND tp,t) ⇒ RACONV (ZIP(MAP FST env,vs)) (FST tp, t) -/
theorem RACONV_TRANS (env : List (term × term)) (tp : term × term) :
    HolSyntax.RACONV env tp →
    ∀ (vs : List term) (t : term),
      LENGTH vs = LENGTH env ∧ HolSyntax.RACONV (ZIP (MAP SND env, vs)) (SND tp, t) →
      HolSyntax.RACONV (ZIP (MAP FST env, vs)) (FST tp, t) := by sorry

/- HOL4: Theorem ACONV_TRANS:
   ∀t1 t2 t3. ACONV t1 t2 ∧ ACONV t2 t3 ⇒ ACONV t1 t3 -/
theorem ACONV_TRANS (t1 t2 t3 : term) : ACONV t1 t2 ∧ ACONV t2 t3 → ACONV t1 t3 := by sorry

/- HOL4: Theorem RACONV_SYM:
   ∀env tp. RACONV env tp ⇒ RACONV (MAP (λ(x,y). (y,x)) env) (SND tp,FST tp) -/
theorem RACONV_SYM (env : List (term × term)) (tp : term × term) :
    HolSyntax.RACONV env tp →
    HolSyntax.RACONV (MAP (fun p : term × term => (p.2, p.1)) env) (SND tp, FST tp) := by sorry

/- HOL4: Theorem ACONV_SYM:
   ∀t1 t2. ACONV t1 t2 ⇒ ACONV t2 t1 -/
theorem ACONV_SYM (t1 t2 : term) : ACONV t1 t2 → ACONV t2 t1 := by sorry

/- HOL4: Theorem ALPHAVARS_TYPE:
   ∀env s t. ALPHAVARS env (s,t) ∧
              EVERY (λ(x,y). welltyped x ∧ welltyped y
                             ∧ (typeof x = typeof y)) env ∧
              welltyped s ∧ welltyped t
              ⇒ typeof s = typeof t -/
theorem ALPHAVARS_TYPE (env : List (term × term)) (s t : term) :
    ALPHAVARS env (s, t) ∧
    EVERY (fun p : term × term => welltyped p.1 ∧ welltyped p.2 ∧ (typeof p.1 = typeof p.2)) env ∧
    welltyped s ∧ welltyped t →
    typeof s = typeof t := by sorry

/- HOL4: Theorem RACONV_TYPE:
   ∀env p. RACONV env p
            ⇒ EVERY (λ(x,y). welltyped x ∧ welltyped y
                             ∧ (typeof x = typeof y)) env ∧
              welltyped (FST p) ∧ welltyped (SND p)
              ⇒ typeof (FST p) = typeof (SND p) -/
theorem RACONV_TYPE (env : List (term × term)) (p : term × term) :
    HolSyntax.RACONV env p →
    EVERY (fun q : term × term => welltyped q.1 ∧ welltyped q.2 ∧ (typeof q.1 = typeof q.2)) env ∧
    welltyped (FST p) ∧ welltyped (SND p) →
    typeof (FST p) = typeof (SND p) := by sorry

/- HOL4: Theorem ACONV_TYPE:
   ∀s t. ACONV s t ⇒ welltyped s ∧ welltyped t ⇒ (typeof s = typeof t) -/
theorem ACONV_TYPE (s t : term) : ACONV s t → welltyped s ∧ welltyped t → typeof s = typeof t := by sorry

/- HOL4: Theorem subtype_Tyvar[simp] =
  ``ty subtype (Tyvar x)``
  |> SIMP_CONV(srw_ss()++boolSimps.DNF_ss)
      [Once relationTheory.RTC_CASES2,subtype1_cases]
   (resulting theorem: ty subtype (Tyvar x) ⇔ (ty = Tyvar x)) -/
theorem subtype_Tyvar (ty : type) (x : mlstring) : subtype ty (Tyvar x) ↔ ty = Tyvar x := by sorry

/- HOL4: Theorem subterm_Var[simp] =
  ``tm subterm (Var x ty)``
  |> SIMP_CONV(srw_ss()++boolSimps.DNF_ss)
      [Once relationTheory.RTC_CASES2,subterm1_cases]
   (resulting theorem: tm subterm (Var x ty) ⇔ (tm = Var x ty)) -/
theorem subterm_Var (tm : term) (x : mlstring) (ty : type) : subterm tm (Var x ty) ↔ tm = Var x ty := by sorry

/- HOL4: Theorem subterm_Const[simp] =
  ``tm subterm (Const x ty)``
  |> SIMP_CONV(srw_ss()++boolSimps.DNF_ss)
      [Once relationTheory.RTC_CASES2,subterm1_cases]
   (resulting theorem: tm subterm (Const x ty) ⇔ (tm = Const x ty)) -/
theorem subterm_Const (tm : term) (x : mlstring) (ty : type) : subterm tm (Const x ty) ↔ tm = Const x ty := by sorry

/- HOL4: Theorem type_lt_thm = Q.prove(
  `(type_lt (Tyvar x1) (Tyvar x2) ⇔ mlstring_lt x1 x2) ∧
    (type_lt (Tyvar _) (Tyapp _ _) ⇔ T) ∧
    (type_lt (Tyapp _ _) (Tyvar _) ⇔ F) ∧
    (type_lt (Tyapp x1 args1) (Tyapp x2 args2) ⇔
       (mlstring_lt LEX LLEX type_lt)
         (x1,args1) (x2,args2))`, ...)
  |> CONJUNCTS |> map GEN_ALL |> LIST_CONJ
   (each conjunct is separately universally quantified; `_` are distinct fresh variables) -/
theorem type_lt_thm :
    (∀ x1 x2 : mlstring, type_lt (Tyvar x1) (Tyvar x2) ↔ mlstring_lt x1 x2) ∧
    (∀ (a : mlstring) (b : mlstring) (c : List type), type_lt (Tyvar a) (Tyapp b c) ↔ True) ∧
    (∀ (a : mlstring) (b : List type) (c : mlstring), type_lt (Tyapp a b) (Tyvar c) ↔ False) ∧
    (∀ (x1 : mlstring) (args1 : List type) (x2 : mlstring) (args2 : List type),
      type_lt (Tyapp x1 args1) (Tyapp x2 args2) ↔
       (LEX mlstring_lt (LLEX type_lt)) (x1, args1) (x2, args2)) := by sorry

/- HOL4: Theorem term_lt_thm = Q.prove(`
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
    (term_lt LEX term_lt) (s1,s2) (t1,t2))`, ...)
  |> CONJUNCTS |> map GEN_ALL |> LIST_CONJ
   (each conjunct is separately universally quantified; `_` are distinct fresh variables) -/
theorem term_lt_thm :
    (∀ (x1 : mlstring) (ty1 : type) (x2 : mlstring) (ty2 : type),
      term_lt (Var x1 ty1) (Var x2 ty2) ↔ (LEX mlstring_lt type_lt) (x1, ty1) (x2, ty2)) ∧
    (∀ (a : mlstring) (b : type) (c : mlstring) (d : type), term_lt (Var a b) (Const c d) ↔ True) ∧
    (∀ (a : mlstring) (b : type) (c d : term), term_lt (Var a b) (Comb c d) ↔ True) ∧
    (∀ (a : mlstring) (b : type) (c d : term), term_lt (Var a b) (Abs c d) ↔ True) ∧
    (∀ (a : mlstring) (b : type) (c : mlstring) (d : type), term_lt (Const a b) (Var c d) ↔ False) ∧
    (∀ (x1 : mlstring) (ty1 : type) (x2 : mlstring) (ty2 : type),
      term_lt (Const x1 ty1) (Const x2 ty2) ↔ (LEX mlstring_lt type_lt) (x1, ty1) (x2, ty2)) ∧
    (∀ (a : mlstring) (b : type) (c d : term), term_lt (Const a b) (Comb c d) ↔ True) ∧
    (∀ (a : mlstring) (b : type) (c d : term), term_lt (Const a b) (Abs c d) ↔ True) ∧
    (∀ (a b : term) (c : mlstring) (d : type), term_lt (Comb a b) (Var c d) ↔ False) ∧
    (∀ (a b : term) (c : mlstring) (d : type), term_lt (Comb a b) (Const c d) ↔ False) ∧
    (∀ (s1 s2 t1 t2 : term),
      term_lt (Comb s1 s2) (Comb t1 t2) ↔ (LEX term_lt term_lt) (s1, s2) (t1, t2)) ∧
    (∀ (a b c d : term), term_lt (Comb a b) (Abs c d) ↔ True) ∧
    (∀ (a b : term) (c : mlstring) (d : type), term_lt (Abs a b) (Var c d) ↔ False) ∧
    (∀ (a b : term) (c : mlstring) (d : type), term_lt (Abs a b) (Const c d) ↔ False) ∧
    (∀ (a b c d : term), term_lt (Abs a b) (Comb c d) ↔ False) ∧
    (∀ (s1 s2 t1 t2 : term),
      term_lt (Abs s1 s2) (Abs t1 t2) ↔ (LEX term_lt term_lt) (s1, s2) (t1, t2)) := by sorry

/- HOL4: Theorem type_cmp_refl[simp]:
   type_cmp t t = EQUAL
   (free variable t is universally quantified) -/
theorem type_cmp_refl (t : type) : type_cmp t t = EQUAL := by sorry

/- HOL4: Theorem term_cmp_refl[simp]:
   term_cmp t t = EQUAL
   (free variable t is universally quantified) -/
theorem term_cmp_refl (t : term) : term_cmp t t = EQUAL := by sorry

/- HOL4: Theorem StrongLinearOrder_type_lt:
   StrongLinearOrder type_lt -/
theorem StrongLinearOrder_type_lt : StrongLinearOrder type_lt := by sorry

/- HOL4: Theorem TotOrd_type_cmp:
   TotOrd type_cmp -/
theorem TotOrd_type_cmp : TotOrd type_cmp := by sorry

/- HOL4: Theorem StrongLinearOrder_term_lt:
   StrongLinearOrder term_lt -/
theorem StrongLinearOrder_term_lt : StrongLinearOrder term_lt := by sorry

/- HOL4: Theorem TotOrd_term_cmp:
   TotOrd term_cmp -/
theorem TotOrd_term_cmp : TotOrd term_cmp := by sorry

/- HOL4: Theorem ALPHAVARS_eq_ordav:
   ∀env t1 t2. ALPHAVARS env (t1,t2) ⇔ ordav env t1 t2 = EQUAL -/
theorem ALPHAVARS_eq_ordav (env : List (term × term)) (t1 t2 : term) :
    ALPHAVARS env (t1, t2) ↔ ordav env t1 t2 = EQUAL := by sorry

/- HOL4: Theorem RACONV_eq_orda:
   ∀env t1 t2. RACONV env (t1,t2) ⇔ orda env t1 t2 = EQUAL -/
theorem RACONV_eq_orda (env : List (term × term)) (t1 t2 : term) :
    HolSyntax.RACONV env (t1, t2) ↔ orda env t1 t2 = EQUAL := by sorry

/- HOL4: Theorem ACONV_eq_orda:
   ∀t1 t2. ACONV t1 t2 = (orda [] t1 t2 = EQUAL) -/
theorem ACONV_eq_orda (t1 t2 : term) : ACONV t1 t2 = (orda [] t1 t2 = EQUAL) := by sorry

/- HOL4: Theorem ordav_sym:
   ∀env v1 v2. flip_ord (ordav env v1 v2) = ordav (MAP (λ(x,y). (y,x)) env) v2 v1 -/
theorem ordav_sym (env : List (term × term)) (v1 v2 : term) :
    flip_ord (ordav env v1 v2) = ordav (MAP (fun p : term × term => (p.2, p.1)) env) v2 v1 := by sorry

/- HOL4: Theorem orda_sym:
   ∀env t1 t2. flip_ord (orda env t1 t2) = orda (MAP (λ(x,y). (y,x)) env) t2 t1 -/
theorem orda_sym (env : List (term × term)) (t1 t2 : term) :
    flip_ord (orda env t1 t2) = orda (MAP (fun p : term × term => (p.2, p.1)) env) t2 t1 := by sorry

/- HOL4: Theorem transitive_alpha_lt:
   transitive alpha_lt -/
theorem transitive_alpha_lt : transitive alpha_lt := by sorry

/- HOL4: Theorem alpha_lt_not_refl[simp]:
   ∀x. ¬alpha_lt x x -/
theorem alpha_lt_not_refl (x : term) : ¬alpha_lt x x := by sorry

/- HOL4: Theorem VFREE_IN_RACONV:
   ∀env p. RACONV env p
            ⇒ ∀x ty. VFREE_IN (Var x ty) (FST p) ∧
                     ¬(∃y. MEM (Var x ty,y) env) ⇔
                     VFREE_IN (Var x ty) (SND p) ∧
                     ¬(∃y. MEM (y,Var x ty) env) -/
theorem VFREE_IN_RACONV (env : List (term × term)) (p : term × term) :
    HolSyntax.RACONV env p →
    ∀ (x : mlstring) (ty : type),
      (VFREE_IN (Var x ty) (FST p) ∧ ¬(∃ y : term, MEM (Var x ty, y) env)) ↔
      (VFREE_IN (Var x ty) (SND p) ∧ ¬(∃ y : term, MEM (y, Var x ty) env)) := by sorry

/- HOL4: Theorem VFREE_IN_ACONV:
   ∀s t x ty. ACONV s t ⇒ (VFREE_IN (Var x ty) s ⇔ VFREE_IN (Var x ty) t) -/
theorem VFREE_IN_ACONV (s t : term) (x : mlstring) (ty : type) :
    ACONV s t → (VFREE_IN (Var x ty) s ↔ VFREE_IN (Var x ty) t) := by sorry

/- HOL4: Theorem hypset_ok_nil[simp]:
   hypset_ok [] -/
theorem hypset_ok_nil : hypset_ok ([] : List term) := by sorry

/- HOL4: Theorem hypset_ok_sing[simp]:
   ∀p. hypset_ok [p] -/
theorem hypset_ok_sing (p : term) : hypset_ok [p] := by sorry

/- HOL4: Theorem hypset_ok_cons:
   hypset_ok (h::hs) ⇔
    EVERY (alpha_lt h) hs ∧ hypset_ok hs
   (free variables h, hs are universally quantified) -/
theorem hypset_ok_cons (h : term) (hs : List term) :
    hypset_ok (h :: hs) ↔ EVERY (alpha_lt h) hs ∧ hypset_ok hs := by sorry

/- HOL4: Theorem term_union_idem[simp]:
   ∀ls. term_union ls ls = ls -/
theorem term_union_idem (ls : List term) : term_union ls ls = ls := by sorry

/- HOL4: Theorem term_union_thm:
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
          | .eq => h1 :: term_union t1 t2
          | .lt => h1 :: term_union t1 (h2 :: t2)
          | .gt => h2 :: term_union (h1 :: t1) t2) := by sorry

/- HOL4: Theorem MEM_term_union_imp:
   ∀l1 l2 x. MEM x (term_union l1 l2) ⇒ MEM x l1 ∨ MEM x l2 -/
theorem MEM_term_union_imp (l1 l2 : List term) (x : term) :
    MEM x (term_union l1 l2) → MEM x l1 ∨ MEM x l2 := by sorry

/- HOL4: Theorem hypset_ok_term_union[simp]:
   ∀l1 l2. hypset_ok l1 ∧ hypset_ok l2 ⇒
            hypset_ok (term_union l1 l2) -/
theorem hypset_ok_term_union (l1 l2 : List term) :
    hypset_ok l1 ∧ hypset_ok l2 → hypset_ok (term_union l1 l2) := by sorry

/- HOL4: Theorem EVERY_term_union:
   EVERY P l1 ∧ EVERY P l2 ⇒ EVERY P (term_union l1 l2)
   (free variables P, l1, l2 are universally quantified) -/
theorem EVERY_term_union (P : term → Prop) (l1 l2 : List term) :
    EVERY P l1 ∧ EVERY P l2 → EVERY P (term_union l1 l2) := by sorry

/- HOL4: Theorem MEM_term_union:
   ∀h1 h2 t. hypset_ok h1 ∧ hypset_ok h2 ∧ (MEM t h1 ∨ MEM t h2) ⇒
      ∃y. MEM y (term_union h1 h2) ∧ ACONV t y -/
theorem MEM_term_union (h1 h2 : List term) (t : term) :
    hypset_ok h1 ∧ hypset_ok h2 ∧ (MEM t h1 ∨ MEM t h2) →
    ∃ y : term, MEM y (term_union h1 h2) ∧ ACONV t y := by sorry

/- HOL4: Theorem term_remove_nil[simp]:
   ∀a. term_remove a [] = [] -/
theorem term_remove_nil (a : term) : term_remove a [] = [] := by sorry

/- HOL4: Theorem MEM_term_remove_imp:
   ∀ls x t. MEM t (term_remove x ls) ⇒
      MEM t ls ∧ (hypset_ok ls ⇒ ¬ACONV x t) -/
theorem MEM_term_remove_imp (ls : List term) (x t : term) :
    MEM t (term_remove x ls) → MEM t ls ∧ (hypset_ok ls → ¬ACONV x t) := by sorry

/- HOL4: Theorem hypset_ok_term_remove[simp]:
   ∀ls. hypset_ok ls ⇒ ∀t. hypset_ok (term_remove t ls) -/
theorem hypset_ok_term_remove (ls : List term) :
    hypset_ok ls → ∀ t : term, hypset_ok (term_remove t ls) := by sorry

/- HOL4: Theorem EVERY_term_remove:
   EVERY P ls ⇒ EVERY P (term_remove t ls)
   (free variables P, ls, t are universally quantified) -/
theorem EVERY_term_remove (P : term → Prop) (ls : List term) (t : term) :
    EVERY P ls → EVERY P (term_remove t ls) := by sorry

/- HOL4: Theorem MEM_term_remove:
   ∀h x t. MEM t h ∧ ¬ACONV x t ∧ hypset_ok h
    ⇒ MEM t (term_remove x h) -/
theorem MEM_term_remove (h : List term) (x t : term) :
    MEM t h ∧ ¬ACONV x t ∧ hypset_ok h → MEM t (term_remove x h) := by sorry

/- HOL4: Theorem term_image_nil[simp]:
   term_image f [] = []
   (free variable f is universally quantified) -/
theorem term_image_nil (f : term → term) : term_image f [] = [] := by sorry

/- HOL4: Theorem MEM_term_image_imp:
   ∀ls f t. MEM t (term_image f ls) ⇒ ∃x. MEM x ls ∧ t = f x -/
theorem MEM_term_image_imp (ls : List term) (f : term → term) (t : term) :
    MEM t (term_image f ls) → ∃ x : term, MEM x ls ∧ t = f x := by sorry

/- HOL4: Theorem hypset_ok_term_image:
   ∀ls f. hypset_ok ls ⇒ hypset_ok (term_image f ls) -/
theorem hypset_ok_term_image (ls : List term) (f : term → term) :
    hypset_ok ls → hypset_ok (term_image f ls) := by sorry

/- HOL4: Theorem MEM_term_image:
   ∀ls f t. MEM t ls ∧ hypset_ok ls ⇒ ∃y. MEM y (term_image f ls) ∧ ACONV (f t) y -/
theorem MEM_term_image (ls : List term) (f : term → term) (t : term) :
    MEM t ls ∧ hypset_ok ls → ∃ y : term, MEM y (term_image f ls) ∧ ACONV (f t) y := by sorry

/- HOL4: Theorem VSUBST_HAS_TYPE:
   ∀tm ty ilist.
      tm has_type ty ∧
      (∀s s'. MEM (s',s) ilist ⇒ ∃x ty. (s = Var x ty) ∧ s' has_type ty)
      ⇒ (VSUBST ilist tm) has_type ty -/
theorem VSUBST_HAS_TYPE (tm : term) (ty : type) (ilist : List (term × term)) :
    has_type tm ty ∧
    (∀ s s' : term, MEM (s', s) ilist → ∃ (x : mlstring) (ty : type), (s = Var x ty) ∧ has_type s' ty) →
    has_type (VSUBST ilist tm) ty := by sorry

/- HOL4: Theorem VSUBST_WELLTYPED:
   ∀tm ty ilist.
      welltyped tm ∧
      (∀s s'. MEM (s',s) ilist ⇒ ∃x ty. (s = Var x ty) ∧ s' has_type ty)
      ⇒ welltyped (VSUBST ilist tm) -/
theorem VSUBST_WELLTYPED (tm : term) (ty : type) (ilist : List (term × term)) :
    welltyped tm ∧
    (∀ s s' : term, MEM (s', s) ilist → ∃ (x : mlstring) (ty : type), (s = Var x ty) ∧ has_type s' ty) →
    welltyped (VSUBST ilist tm) := by sorry

end

end Candle.HolSyntaxExtra
