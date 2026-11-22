/-
  HOL4 theory `holSyntaxExtra` (candle/standard/syntax/holSyntaxExtraScript.sml):
  target theorems, second part (split from `HolSyntaxExtra.lean` for parallel translation).
-/
import CandleLean.HolSyntaxExtra

namespace Candle

noncomputable section
open Classical

/- HOL4:
Theorem VFREE_IN_VSUBST:
   ∀tm u uty ilist.
      welltyped tm ⇒
      (VFREE_IN (Var u uty) (VSUBST ilist tm) ⇔
       ∃y ty. VFREE_IN (Var y ty) tm ∧
              VFREE_IN (Var u uty) (REV_ASSOCD (Var y ty) ilist (Var y ty))) -/
theorem VFREE_IN_VSUBST :
    ∀ (tm : term) (u : mlstring) (uty : type) (ilist : List (term × term)),
      welltyped tm →
      (VFREE_IN (Var u uty) (VSUBST ilist tm) ↔
       ∃ (y : mlstring) (ty : type), VFREE_IN (Var y ty) tm ∧
              VFREE_IN (Var u uty) (REV_ASSOCD (Var y ty) ilist (Var y ty))) := by
  sorry

/- HOL4:
Theorem VSUBST_NIL[simp]:
   ∀tm. VSUBST [] tm = tm -/
theorem VSUBST_NIL :
    ∀ (tm : term), VSUBST [] tm = tm := by
  sorry

/- HOL4:
Theorem INST_CORE_HAS_TYPE:
   ∀n tm env tyin.
      welltyped tm ∧ (sizeof tm = n) ∧
      (∀s s'. MEM (s,s') env ⇒
              ∃x ty. (s = Var x ty) ∧
                     (s' = Var x (TYPE_SUBST tyin ty)))
      ⇒ (∃x ty. (INST_CORE env tyin tm = Clash(Var x (TYPE_SUBST tyin ty))) ∧
                VFREE_IN (Var x ty) tm ∧
                REV_ASSOCD (Var x (TYPE_SUBST tyin ty))
                  env (Var x ty) ≠ Var x ty)
      ∨ (∀x ty. VFREE_IN (Var x ty) tm
                ⇒ REV_ASSOCD (Var x (TYPE_SUBST tyin ty))
                    env (Var x ty) = Var x ty) ∧
        (∃tm'. INST_CORE env tyin tm = Result tm' ∧
               tm' has_type (TYPE_SUBST tyin (typeof tm)) ∧
               (∀u uty. VFREE_IN (Var u uty) tm' ⇔
                        ∃oty. VFREE_IN (Var u oty) tm ∧
                              uty = TYPE_SUBST tyin oty)) -/
theorem INST_CORE_HAS_TYPE :
    ∀ (n : Nat) (tm : term) (env : List (term × term)) (tyin : List (type × type)),
      welltyped tm ∧ (sizeof tm = n) ∧
      (∀ (s s' : term), MEM (s, s') env →
              ∃ (x : mlstring) (ty : type), (s = Var x ty) ∧
                     (s' = Var x (TYPE_SUBST tyin ty)))
      → (∃ (x : mlstring) (ty : type),
                (INST_CORE env tyin tm = Clash (Var x (TYPE_SUBST tyin ty))) ∧
                VFREE_IN (Var x ty) tm ∧
                REV_ASSOCD (Var x (TYPE_SUBST tyin ty))
                  env (Var x ty) ≠ Var x ty)
      ∨ ((∀ (x : mlstring) (ty : type), VFREE_IN (Var x ty) tm
                → REV_ASSOCD (Var x (TYPE_SUBST tyin ty))
                    env (Var x ty) = Var x ty) ∧
        (∃ (tm' : term), INST_CORE env tyin tm = Result tm' ∧
               has_type tm' (TYPE_SUBST tyin (typeof tm)) ∧
               (∀ (u : mlstring) (uty : type), VFREE_IN (Var u uty) tm' ↔
                        ∃ (oty : type), VFREE_IN (Var u oty) tm ∧
                              uty = TYPE_SUBST tyin oty))) := by
  sorry

/- HOL4:
Theorem INST_CORE_NIL_IS_RESULT:
   ∀tyin tm. welltyped tm ⇒ IS_RESULT (INST_CORE [] tyin tm) -/
theorem INST_CORE_NIL_IS_RESULT :
    ∀ (tyin : List (type × type)) (tm : term),
      welltyped tm → IS_RESULT (INST_CORE [] tyin tm) := by
  sorry

/- HOL4:
Theorem INST_HAS_TYPE:
   ∀tm ty tyin ty'. tm has_type ty ∧ ty' = TYPE_SUBST tyin ty ⇒ INST tyin tm has_type ty' -/
theorem INST_HAS_TYPE :
    ∀ (tm : term) (ty : type) (tyin : List (type × type)) (ty' : type),
      has_type tm ty ∧ ty' = TYPE_SUBST tyin ty → has_type (INST tyin tm) ty' := by
  sorry

/- HOL4:
Theorem INST_WELLTYPED:
   ∀tm tyin.  welltyped tm ⇒ welltyped (INST tyin tm) -/
theorem INST_WELLTYPED :
    ∀ (tm : term) (tyin : List (type × type)), welltyped tm → welltyped (INST tyin tm) := by
  sorry

/- HOL4:
Theorem tyvars_ALL_DISTINCT[simp]:
   ∀ty. ALL_DISTINCT (tyvars ty) -/
theorem tyvars_ALL_DISTINCT :
    ∀ (ty : type), ALL_DISTINCT (tyvars ty) := by
  sorry

/- HOL4:
Theorem tvars_ALL_DISTINCT[simp]:
   ∀tm. ALL_DISTINCT (tvars tm) -/
theorem tvars_ALL_DISTINCT :
    ∀ (tm : term), ALL_DISTINCT (tvars tm) := by
  sorry

/- HOL4:
Theorem EQUATION_HAS_TYPE_BOOL:
   ∀s t. (s === t) has_type Bool
          ⇔ welltyped s ∧ welltyped t ∧ (typeof s = typeof t) -/
theorem EQUATION_HAS_TYPE_BOOL :
    ∀ (s t : term), has_type (s === t) Bool'
          ↔ welltyped s ∧ welltyped t ∧ (typeof s = typeof t) := by
  sorry

/- HOL4:
Theorem type_ok_TYPE_SUBST:
   ∀s tyin ty.
      type_ok s ty ∧
      EVERY (type_ok s) (MAP FST tyin)
    ⇒ type_ok s (TYPE_SUBST tyin ty) -/
theorem type_ok_TYPE_SUBST :
    ∀ (s : tysig) (tyin : List (type × type)) (ty : type),
      type_ok s ty ∧
      EVERY (type_ok s) (MAP FST tyin)
    → type_ok s (TYPE_SUBST tyin ty) := by
  sorry

/- HOL4:
Theorem type_ok_TYPE_SUBST_imp:
   ∀s tyin ty. type_ok s (TYPE_SUBST tyin ty) ⇒
                ∀x. MEM x (tyvars ty) ⇒ type_ok s (TYPE_SUBST tyin (Tyvar x)) -/
theorem type_ok_TYPE_SUBST_imp :
    ∀ (s : tysig) (tyin : List (type × type)) (ty : type),
      type_ok s (TYPE_SUBST tyin ty) →
        ∀ (x : mlstring), MEM x (tyvars ty) → type_ok s (TYPE_SUBST tyin (Tyvar x)) := by
  sorry

/- HOL4:
Theorem term_ok_welltyped:
   ∀sig t. term_ok sig t ⇒ welltyped t -/
theorem term_ok_welltyped :
    ∀ (sig : Candle.sig) (t : term), term_ok sig t → welltyped t := by
  sorry

/- HOL4:
Theorem term_ok_type_ok:
   ∀sig t. is_std_sig sig ∧ term_ok sig t
          ⇒ type_ok (FST sig) (typeof t) -/
theorem term_ok_type_ok :
    ∀ (sig : Candle.sig) (t : term), is_std_sig sig ∧ term_ok sig t
          → type_ok (FST sig) (typeof t) := by
  sorry

/- HOL4:
Theorem term_ok_equation:
   is_std_sig sig ⇒
      (term_ok sig (s === t) ⇔
        term_ok sig s ∧ term_ok sig t ∧
        typeof t = typeof s) -/
theorem term_ok_equation (sig : Candle.sig) (s t : term) :
    is_std_sig sig →
      (term_ok sig (s === t) ↔
        term_ok sig s ∧ term_ok sig t ∧
        typeof t = typeof s) := by
  sorry

/- HOL4:
Theorem term_ok_VSUBST:
   ∀sig tm ilist.
    term_ok sig tm ∧
    (∀s s'. MEM (s',s) ilist ⇒ ∃x ty. s = Var x ty ∧ s' has_type ty ∧ term_ok sig s')
    ⇒
    term_ok sig (VSUBST ilist tm) -/
theorem term_ok_VSUBST :
    ∀ (sig : Candle.sig) (tm : term) (ilist : List (term × term)),
      term_ok sig tm ∧
      (∀ (s s' : term), MEM (s', s) ilist →
        ∃ (x : mlstring) (ty : type), s = Var x ty ∧ has_type s' ty ∧ term_ok sig s')
      →
      term_ok sig (VSUBST ilist tm) := by
  sorry

/- HOL4:
Theorem term_ok_INST_CORE:
   ∀sig env tyin tm.
      term_ok sig tm ∧
      EVERY (type_ok (FST sig)) (MAP FST tyin) ∧
      (∀s s'. MEM (s,s') env ⇒ ∃x ty. s = Var x ty ∧ s' = Var x (TYPE_SUBST tyin ty)) ∧
      IS_RESULT (INST_CORE env tyin tm)
      ⇒
      term_ok sig (RESULT (INST_CORE env tyin tm)) -/
theorem term_ok_INST_CORE :
    ∀ (sig : Candle.sig) (env : List (term × term)) (tyin : List (type × type)) (tm : term),
      term_ok sig tm ∧
      EVERY (type_ok (FST sig)) (MAP FST tyin) ∧
      (∀ (s s' : term), MEM (s, s') env →
        ∃ (x : mlstring) (ty : type), s = Var x ty ∧ s' = Var x (TYPE_SUBST tyin ty)) ∧
      IS_RESULT (INST_CORE env tyin tm)
      →
      term_ok sig (RESULT (INST_CORE env tyin tm)) := by
  sorry

/- HOL4:
Theorem term_ok_INST:
   ∀sig tyin tm.
    term_ok sig tm ∧
    EVERY (type_ok (FST sig)) (MAP FST tyin) ⇒
    term_ok sig (INST tyin tm) -/
theorem term_ok_INST :
    ∀ (sig : Candle.sig) (tyin : List (type × type)) (tm : term),
      term_ok sig tm ∧
      EVERY (type_ok (FST sig)) (MAP FST tyin) →
      term_ok sig (INST tyin tm) := by
  sorry

/- HOL4:
Theorem term_ok_raconv:
   ∀env tp. RACONV env tp ⇒
      ∀sig.
      EVERY (λ(s,s'). welltyped s ∧ welltyped s' ∧ typeof s = typeof s' ∧ type_ok (FST sig) (typeof s)) env ⇒
      term_ok sig (FST tp) ∧ welltyped (SND tp) ⇒ term_ok sig (SND tp) -/
theorem term_ok_raconv :
    ∀ (env : List (term × term)) (tp : term × term), RACONV env tp →
      ∀ (sig : Candle.sig),
      EVERY (fun ((s, s') : term × term) =>
        welltyped s ∧ welltyped s' ∧ typeof s = typeof s' ∧ type_ok (FST sig) (typeof s)) env →
      term_ok sig (FST tp) ∧ welltyped (SND tp) → term_ok sig (SND tp) := by
  sorry

/- HOL4:
Theorem term_ok_aconv:
   ∀sig t1 t2. ACONV t1 t2 ∧ term_ok sig t1 ∧ welltyped t2 ⇒ term_ok sig t2 -/
theorem term_ok_aconv :
    ∀ (sig : Candle.sig) (t1 t2 : term),
      ACONV t1 t2 ∧ term_ok sig t1 ∧ welltyped t2 → term_ok sig t2 := by
  sorry

/- HOL4:
Theorem bind_not_free:
   ∀t n v. ¬dbVFREE_IN (UNCURRY dbVar v) t ⇒ bind v n t = t -/
theorem bind_not_free :
    ∀ (t : dbterm_ty) (n : Nat) (v : mlstring × type),
      ¬ dbVFREE_IN (UNCURRY dbVar v) t → bind v n t = t := by
  sorry

/- HOL4:
Theorem bind_dbVSUBST:
   ∀tm v n ls.
    (UNCURRY dbVar v) ∉ set (MAP SND ls) ∧
    (∀k. dbVFREE_IN k tm ∧ MEM k (MAP SND ls) ⇒
        ¬dbVFREE_IN (UNCURRY dbVar v) (REV_ASSOCD k ls k))
    ⇒
    bind v n (dbVSUBST ls tm) = dbVSUBST ls (bind v n tm) -/
theorem bind_dbVSUBST :
    ∀ (tm : dbterm_ty) (v : mlstring × type) (n : Nat) (ls : List (dbterm_ty × dbterm_ty)),
      (UNCURRY dbVar v) ∉ set (MAP SND ls) ∧
      (∀ (k : dbterm_ty), dbVFREE_IN k tm ∧ MEM k (MAP SND ls) →
          ¬ dbVFREE_IN (UNCURRY dbVar v) (REV_ASSOCD k ls k))
      →
      bind v n (dbVSUBST ls tm) = dbVSUBST ls (bind v n tm) := by
  sorry

/- HOL4:
Theorem bind_dbVSUBST_cons:
   ∀tm z x n ls.
    ¬dbVFREE_IN (UNCURRY dbVar z) (dbVSUBST ls (bind x n tm))
    ⇒
    bind z n (dbVSUBST ((UNCURRY dbVar z,UNCURRY dbVar x)::ls) tm) = dbVSUBST ls (bind x n tm) -/
theorem bind_dbVSUBST_cons :
    ∀ (tm : dbterm_ty) (z x : mlstring × type) (n : Nat) (ls : List (dbterm_ty × dbterm_ty)),
      ¬ dbVFREE_IN (UNCURRY dbVar z) (dbVSUBST ls (bind x n tm))
      →
      bind z n (dbVSUBST ((UNCURRY dbVar z, UNCURRY dbVar x) :: ls) tm) =
        dbVSUBST ls (bind x n tm) := by
  sorry

/- HOL4:
Theorem dbVSUBST_frees:
   ∀tm ls ls'.
    (∀k. dbVFREE_IN k tm ⇒ REV_ASSOCD k ls k = REV_ASSOCD k ls' k)
     ⇒
      dbVSUBST ls tm = dbVSUBST ls' tm -/
theorem dbVSUBST_frees :
    ∀ (tm : dbterm_ty) (ls ls' : List (dbterm_ty × dbterm_ty)),
      (∀ (k : dbterm_ty), dbVFREE_IN k tm → REV_ASSOCD k ls k = REV_ASSOCD k ls' k)
      →
        dbVSUBST ls tm = dbVSUBST ls' tm := by
  sorry

/- HOL4:
Theorem dbVFREE_IN_bind:
   ∀tm x v n b. dbVFREE_IN x (bind v n tm) ⇔ (x ≠ UNCURRY dbVar v) ∧ dbVFREE_IN x tm -/
theorem dbVFREE_IN_bind {α : Type} [Nonempty α] :
    ∀ (tm : dbterm_ty) (x : dbterm_ty) (v : mlstring × type) (n : Nat) (b : α),
      dbVFREE_IN x (bind v n tm) ↔ (x ≠ UNCURRY dbVar v) ∧ dbVFREE_IN x tm := by
  sorry

/- HOL4:
Theorem dbVFREE_IN_VFREE_IN:
   ∀tm x. welltyped tm ⇒ (dbVFREE_IN (db x) (db tm) ⇔ VFREE_IN x tm) -/
theorem dbVFREE_IN_VFREE_IN :
    ∀ (tm x : term), welltyped tm → (dbVFREE_IN (db x) (db tm) ↔ VFREE_IN x tm) := by
  sorry

/- HOL4:
Theorem MAP_db_FILTER_neq:
   ∀ls z ty. MAP (λ(x,y). (db x, db y)) (FILTER (λ(x,y). y ≠ Var z ty) ls) = FILTER (λ(x,y). y ≠ dbVar z ty) (MAP (λ(x,y). (db x, db y)) ls) -/
theorem MAP_db_FILTER_neq :
    ∀ (ls : List (term × term)) (z : mlstring) (ty : type),
      MAP (fun ((x, y) : term × term) => (db x, db y))
          (FILTER (fun ((x, y) : term × term) => y ≠ Var z ty) ls) =
        FILTER (fun ((x, y) : dbterm_ty × dbterm_ty) => y ≠ dbVar z ty)
          (MAP (fun ((x, y) : term × term) => (db x, db y)) ls) := by
  sorry

/- HOL4:
Theorem REV_ASSOCD_MAP_db:
   ∀ls k ky.
    (∀k v. MEM (v,k) ls ⇒ ∃x ty. k = Var x ty)
    ⇒
    REV_ASSOCD (dbVar k ky) (MAP (λ(x,y). (db x, db y)) ls) (dbVar k ky) = db (REV_ASSOCD (Var k ky) ls (Var k ky)) -/
theorem REV_ASSOCD_MAP_db :
    ∀ (ls : List (term × term)) (k : mlstring) (ky : type),
      (∀ (k v : term), MEM (v, k) ls → ∃ (x : mlstring) (ty : type), k = Var x ty)
      →
      REV_ASSOCD (dbVar k ky) (MAP (fun ((x, y) : term × term) => (db x, db y)) ls) (dbVar k ky) =
        db (REV_ASSOCD (Var k ky) ls (Var k ky)) := by
  sorry

/- HOL4:
Theorem dbVFREE_IN_dbVSUBST:
   ∀tm u uty ilist.
      dbVFREE_IN (dbVar u uty) (dbVSUBST ilist tm) ⇔
      ∃y ty. dbVFREE_IN (dbVar y ty) tm ∧
             dbVFREE_IN (dbVar u uty)
               (REV_ASSOCD (dbVar y ty) ilist (dbVar y ty)) -/
theorem dbVFREE_IN_dbVSUBST :
    ∀ (tm : dbterm_ty) (u : mlstring) (uty : type) (ilist : List (dbterm_ty × dbterm_ty)),
      dbVFREE_IN (dbVar u uty) (dbVSUBST ilist tm) ↔
      ∃ (y : mlstring) (ty : type), dbVFREE_IN (dbVar y ty) tm ∧
             dbVFREE_IN (dbVar u uty)
               (REV_ASSOCD (dbVar y ty) ilist (dbVar y ty)) := by
  sorry

/- HOL4:
Theorem VSUBST_dbVSUBST:
   ∀tm ilist.
    welltyped tm ∧
    (∀k v. MEM (v,k) ilist ⇒ welltyped v ∧ ∃x ty. k = Var x ty)
    ⇒
    db (VSUBST ilist tm) = dbVSUBST (MAP (λ(x,y). (db x, db y)) ilist) (db tm) -/
theorem VSUBST_dbVSUBST :
    ∀ (tm : term) (ilist : List (term × term)),
      welltyped tm ∧
      (∀ (k v : term), MEM (v, k) ilist →
        welltyped v ∧ ∃ (x : mlstring) (ty : type), k = Var x ty)
      →
      db (VSUBST ilist tm) =
        dbVSUBST (MAP (fun ((x, y) : term × term) => (db x, db y)) ilist) (db tm) := by
  sorry

/- HOL4:
Theorem dbINST_bind:
   ∀tm v n ls.
      (∀ty. dbVFREE_IN (dbVar (FST v) ty) tm ∧ (TYPE_SUBST ls ty = TYPE_SUBST ls (SND v)) ⇒ ty = SND v)
      ⇒ dbINST ls (bind v n tm) = bind (FST v,TYPE_SUBST ls (SND v)) n (dbINST ls tm) -/
theorem dbINST_bind :
    ∀ (tm : dbterm_ty) (v : mlstring × type) (n : Nat) (ls : List (type × type)),
      (∀ (ty : type), dbVFREE_IN (dbVar (FST v) ty) tm ∧
          (TYPE_SUBST ls ty = TYPE_SUBST ls (SND v)) → ty = SND v)
      → dbINST ls (bind v n tm) = bind (FST v, TYPE_SUBST ls (SND v)) n (dbINST ls tm) := by
  sorry

/- HOL4:
Theorem dbVSUBST_nil[simp]:
   ∀tm. dbVSUBST [] tm = tm -/
theorem dbVSUBST_nil :
    ∀ (tm : dbterm_ty), dbVSUBST [] tm = tm := by
  sorry

/- HOL4:
Theorem INST_CORE_dbINST:
   ∀tm tyin env tmi.
      welltyped tm ∧ (∀s s'. MEM (s,s') env ⇒ ∃x ty. s = Var x ty ∧ s' = Var x (TYPE_SUBST tyin ty)) ∧
      INST_CORE env tyin tm = Result tmi ⇒
        db tmi = dbINST tyin (db tm) -/
theorem INST_CORE_dbINST :
    ∀ (tm : term) (tyin : List (type × type)) (env : List (term × term)) (tmi : term),
      welltyped tm ∧
      (∀ (s s' : term), MEM (s, s') env →
        ∃ (x : mlstring) (ty : type), s = Var x ty ∧ s' = Var x (TYPE_SUBST tyin ty)) ∧
      INST_CORE env tyin tm = Result tmi →
        db tmi = dbINST tyin (db tm) := by
  sorry

/- HOL4:
Theorem INST_dbINST:
   ∀tm tyin.
      welltyped tm ⇒
      db (INST tyin tm) = dbINST tyin (db tm) -/
theorem INST_dbINST :
    ∀ (tm : term) (tyin : List (type × type)),
      welltyped tm →
      db (INST tyin tm) = dbINST tyin (db tm) := by
  sorry

/- HOL4:
Theorem bind_list_aux_clauses:
   (∀env m. bind_list_aux m env (dbBound n) = dbBound n) ∧
    (∀env m. bind_list_aux m env (dbConst x ty) = dbConst x ty) ∧
    (∀env m t1 t2. bind_list_aux m env (dbComb t1 t2) = dbComb (bind_list_aux m env t1) (bind_list_aux m env t2)) ∧
    (∀env m ty tm. bind_list_aux m env (dbAbs ty tm) = dbAbs ty (bind_list_aux (m+1) env tm)) -/
theorem bind_list_aux_clauses (n : Nat) (x : mlstring) (ty : type) :
    (∀ (env : List (mlstring × type)) (m : Nat),
      bind_list_aux m env (dbBound n) = dbBound n) ∧
    (∀ (env : List (mlstring × type)) (m : Nat),
      bind_list_aux m env (dbConst x ty) = dbConst x ty) ∧
    (∀ (env : List (mlstring × type)) (m : Nat) (t1 t2 : dbterm_ty),
      bind_list_aux m env (dbComb t1 t2) =
        dbComb (bind_list_aux m env t1) (bind_list_aux m env t2)) ∧
    (∀ (env : List (mlstring × type)) (m : Nat) (ty : type) (tm : dbterm_ty),
      bind_list_aux m env (dbAbs ty tm) = dbAbs ty (bind_list_aux (m + 1) env tm)) := by
  sorry

/- HOL4:
Theorem dbterm_bind:
   ∀tm env. dbterm env tm = bind_list_aux 0 env (db tm) -/
theorem dbterm_bind :
    ∀ (tm : term) (env : List (mlstring × type)),
      dbterm env tm = bind_list_aux 0 env (db tm) := by
  sorry

/- HOL4:
Theorem dbterm_db:
   ∀tm. dbterm [] tm = db tm -/
theorem dbterm_db :
    ∀ (tm : term), dbterm [] tm = db tm := by
  sorry

/- HOL4:
Theorem dbterm_RACONV:
   ∀t1 env1 t2 env2. welltyped t1 ∧ welltyped t2 ∧ dbterm env1 t1 = dbterm env2 t2 ∧ LENGTH env1 = LENGTH env2 ⇒
      RACONV (ZIP(MAP (UNCURRY Var) env1,MAP (UNCURRY Var) env2)) (t1,t2) -/
theorem dbterm_RACONV :
    ∀ (t1 : term) (env1 : List (mlstring × type)) (t2 : term) (env2 : List (mlstring × type)),
      welltyped t1 ∧ welltyped t2 ∧ dbterm env1 t1 = dbterm env2 t2 ∧
      LENGTH env1 = LENGTH env2 →
      RACONV (ZIP (MAP (UNCURRY Var) env1, MAP (UNCURRY Var) env2)) (t1, t2) := by
  sorry

/- HOL4:
Theorem RACONV_dbterm:
   ∀env tp. RACONV env tp ⇒
    welltyped (FST tp) ∧ welltyped (SND tp) ∧
    (∀vp. MEM vp env ⇒ (∃x ty. (FST vp = Var x ty)) ∧ (∃x ty. (SND vp = Var x ty)))
     ⇒ dbterm (MAP (dest_var o FST) env) (FST tp) = dbterm (MAP (dest_var o SND) env) (SND tp) -/
theorem RACONV_dbterm :
    ∀ (env : List (term × term)) (tp : term × term), RACONV env tp →
      welltyped (FST tp) ∧ welltyped (SND tp) ∧
      (∀ (vp : term × term), MEM vp env →
        (∃ (x : mlstring) (ty : type), (FST vp = Var x ty)) ∧
        (∃ (x : mlstring) (ty : type), (SND vp = Var x ty)))
      → dbterm (MAP (dest_var ∘ FST) env) (FST tp) = dbterm (MAP (dest_var ∘ SND) env) (SND tp) := by
  sorry

/- HOL4:
Theorem dbterm_ACONV:
   ∀t1 t2. welltyped t1 ∧ welltyped t2 ⇒ (ACONV t1 t2 ⇔ dbterm [] t1 = dbterm [] t2) -/
theorem dbterm_ACONV :
    ∀ (t1 t2 : term), welltyped t1 ∧ welltyped t2 →
      (ACONV t1 t2 ↔ dbterm [] t1 = dbterm [] t2) := by
  sorry

/- HOL4:
Theorem ACONV_db:
   ∀t1 t2. welltyped t1 ∧ welltyped t2 ⇒ (ACONV t1 t2 ⇔ db t1 = db t2) -/
theorem ACONV_db :
    ∀ (t1 t2 : term), welltyped t1 ∧ welltyped t2 → (ACONV t1 t2 ↔ db t1 = db t2) := by
  sorry

/- HOL4:
Theorem ACONV_VSUBST:
   ∀t1 t2 ilist.
    welltyped t1 ∧ welltyped t2 ∧
    (∀k v. MEM (v,k) ilist ⇒ ∃x ty. k = Var x ty ∧ v has_type ty) ∧
    ACONV t1 t2 ⇒
    ACONV (VSUBST ilist t1) (VSUBST ilist t2) -/
theorem ACONV_VSUBST :
    ∀ (t1 t2 : term) (ilist : List (term × term)),
      welltyped t1 ∧ welltyped t2 ∧
      (∀ (k v : term), MEM (v, k) ilist →
        ∃ (x : mlstring) (ty : type), k = Var x ty ∧ has_type v ty) ∧
      ACONV t1 t2 →
      ACONV (VSUBST ilist t1) (VSUBST ilist t2) := by
  sorry

/- HOL4:
Theorem ACONV_INST:
   ∀t1 t2 tyin. welltyped t1 ∧ welltyped t2 ∧ ACONV t1 t2 ⇒ ACONV (INST tyin t1) (INST tyin t2) -/
theorem ACONV_INST :
    ∀ (t1 t2 : term) (tyin : List (type × type)),
      welltyped t1 ∧ welltyped t2 ∧ ACONV t1 t2 → ACONV (INST tyin t1) (INST tyin t2) := by
  sorry

/- HOL4:
Theorem VSUBST_simple_subst:
   ∀tm ilist. DISJOINT (set (bv_names tm)) {y | ∃ty u. VFREE_IN (Var y ty) u ∧ MEM u (MAP FST ilist)} ∧
               (∀s s'. MEM (s',s) ilist ⇒ ∃x ty. s = Var x ty) ∧
               welltyped tm
               ⇒ VSUBST ilist tm = simple_subst ilist tm -/
theorem VSUBST_simple_subst :
    ∀ (tm : term) (ilist : List (term × term)),
      DISJOINT (set (bv_names tm))
        {y : mlstring | ∃ (ty : type) (u : term),
          VFREE_IN (Var y ty) u ∧ MEM u (MAP FST ilist)} ∧
      (∀ (s s' : term), MEM (s', s) ilist → ∃ (x : mlstring) (ty : type), s = Var x ty) ∧
      welltyped tm
      → VSUBST ilist tm = simple_subst ilist tm := by
  sorry

/- HOL4:
Theorem INST_CORE_simple_inst:
   ∀env tyin tm.
      ALL_DISTINCT (bv_names tm ++ (MAP (FST o dest_var o SND) env)) ∧
      DISJOINT (set(bv_names tm)) {x | ∃ty. VFREE_IN (Var x ty) tm} ∧
      (∀s s'. MEM (s,s') env ⇒ ∃x ty. s = Var x ty ∧ s' = Var x (TYPE_SUBST tyin ty)) ∧
      (∀x ty ty'. VFREE_IN (Var x ty) tm ∧ MEM (Var x ty') (MAP FST env) ⇒ ty' = ty) ∧
      welltyped tm
      ⇒ INST_CORE env tyin tm = Result (simple_inst tyin tm) -/
theorem INST_CORE_simple_inst :
    ∀ (env : List (term × term)) (tyin : List (type × type)) (tm : term),
      ALL_DISTINCT (bv_names tm ++ (MAP (FST ∘ dest_var ∘ SND) env)) ∧
      DISJOINT (set (bv_names tm)) {x : mlstring | ∃ (ty : type), VFREE_IN (Var x ty) tm} ∧
      (∀ (s s' : term), MEM (s, s') env →
        ∃ (x : mlstring) (ty : type), s = Var x ty ∧ s' = Var x (TYPE_SUBST tyin ty)) ∧
      (∀ (x : mlstring) (ty ty' : type),
        VFREE_IN (Var x ty) tm ∧ MEM (Var x ty') (MAP FST env) → ty' = ty) ∧
      welltyped tm
      → INST_CORE env tyin tm = Result (simple_inst tyin tm) := by
  sorry

/- HOL4:
Theorem INST_simple_inst:
   ∀tyin tm.
      ALL_DISTINCT (bv_names tm) ∧
      DISJOINT (set (bv_names tm)) {x | ∃ty. VFREE_IN (Var x ty) tm} ∧
      welltyped tm
      ⇒
      INST tyin tm = simple_inst tyin tm -/
theorem INST_simple_inst :
    ∀ (tyin : List (type × type)) (tm : term),
      ALL_DISTINCT (bv_names tm) ∧
      DISJOINT (set (bv_names tm)) {x : mlstring | ∃ (ty : type), VFREE_IN (Var x ty) tm} ∧
      welltyped tm
      →
      INST tyin tm = simple_inst tyin tm := by
  sorry

/- HOL4:
Theorem simple_subst_has_type:
   ∀tm ty.
      tm has_type ty ⇒
      ∀subst.
        EVERY (λ(s',s). s' has_type typeof s) subst ⇒
        simple_subst subst tm has_type ty -/
theorem simple_subst_has_type :
    ∀ (tm : term) (ty : type),
      has_type tm ty →
      ∀ (subst : List (term × term)),
        EVERY (fun ((s', s) : term × term) => has_type s' (typeof s)) subst →
        has_type (simple_subst subst tm) ty := by
  sorry

/- HOL4:
Theorem simple_inst_has_type:
   ∀tm tyin. welltyped tm ⇒ simple_inst tyin tm has_type (TYPE_SUBST tyin (typeof tm)) -/
theorem simple_inst_has_type :
    ∀ (tm : term) (tyin : List (type × type)),
      welltyped tm → has_type (simple_inst tyin tm) (TYPE_SUBST tyin (typeof tm)) := by
  sorry

/- HOL4:
Theorem FST_rename_bvars:
   ∀names env tm. LENGTH (bv_names tm) ≤ LENGTH names ⇒ (FST (rename_bvars names env tm) = DROP (LENGTH (bv_names tm)) names) -/
theorem FST_rename_bvars :
    ∀ (names : List mlstring) (env : List (mlstring × (mlstring × type))) (tm : term),
      LENGTH (bv_names tm) ≤ LENGTH names →
      (FST (rename_bvars names env tm) = DROP (LENGTH (bv_names tm)) names) := by
  sorry

/- HOL4:
Theorem rename_bvars_RACONV:
   ∀names env tm.
    LENGTH (bv_names tm) ≤ LENGTH names ∧
    DISJOINT (set (MAP FST env ++ names)) (set (MAP (FST o SND) env ++ bv_names tm)) ∧
    DISJOINT (set (MAP FST env ++ names)) {x | ∃ty. VFREE_IN (Var x ty) tm} ∧
    ALL_DISTINCT (MAP FST env ++ names) ∧
    welltyped tm
    ⇒ RACONV (MAP (λ(s',(s,ty)). (Var s ty, Var s' ty)) env) (tm, SND (rename_bvars names env tm)) -/
theorem rename_bvars_RACONV :
    ∀ (names : List mlstring) (env : List (mlstring × (mlstring × type))) (tm : term),
      LENGTH (bv_names tm) ≤ LENGTH names ∧
      DISJOINT (set (MAP FST env ++ names)) (set (MAP (FST ∘ SND) env ++ bv_names tm)) ∧
      DISJOINT (set (MAP FST env ++ names))
        {x : mlstring | ∃ (ty : type), VFREE_IN (Var x ty) tm} ∧
      ALL_DISTINCT (MAP FST env ++ names) ∧
      welltyped tm
      → RACONV
          (MAP (fun ((s', (s, ty)) : mlstring × (mlstring × type)) => (Var s ty, Var s' ty)) env)
          (tm, SND (rename_bvars names env tm)) := by
  sorry

/- HOL4:
Theorem rename_bvars_ACONV:
   ∀names tm.
    LENGTH (bv_names tm) ≤ LENGTH names ∧ ALL_DISTINCT names ∧
    DISJOINT (set names) {x | MEM x (bv_names tm) ∨ ∃ty. VFREE_IN (Var x ty) tm} ∧
    welltyped tm
    ⇒
    ACONV tm (SND (rename_bvars names [] tm)) -/
theorem rename_bvars_ACONV :
    ∀ (names : List mlstring) (tm : term),
      LENGTH (bv_names tm) ≤ LENGTH names ∧ ALL_DISTINCT names ∧
      DISJOINT (set names)
        {x : mlstring | MEM x (bv_names tm) ∨ ∃ (ty : type), VFREE_IN (Var x ty) tm} ∧
      welltyped tm
      →
      ACONV tm (SND (rename_bvars names [] tm)) := by
  sorry

/- HOL4:
Theorem rename_bvars_has_type:
   ∀names env tm ty. tm has_type ty ⇒ SND (rename_bvars names env tm) has_type ty -/
theorem rename_bvars_has_type :
    ∀ (names : List mlstring) (env : List (mlstring × (mlstring × type))) (tm : term)
      (ty : type),
      has_type tm ty → has_type (SND (rename_bvars names env tm)) ty := by
  sorry

/- HOL4:
Theorem rename_bvars_welltyped:
   ∀names env tm. welltyped tm ⇒ welltyped (SND (rename_bvars names env tm)) -/
theorem rename_bvars_welltyped :
    ∀ (names : List mlstring) (env : List (mlstring × (mlstring × type))) (tm : term),
      welltyped tm → welltyped (SND (rename_bvars names env tm)) := by
  sorry

/- HOL4:
Theorem fresh_union:
   FINITE s ∧ FINITE t ⇒ fresh (s ∪ t) ∉ s ∧ fresh (s ∪ t) ∉ t -/
theorem fresh_union (s t : Set string) :
    FINITE s ∧ FINITE t → fresh (s ∪ t) ∉ s ∧ fresh (s ∪ t) ∉ t := by
  sorry

/- HOL4:
Theorem fresh_names_exist:
   ∀s n. FINITE (s:string set) ⇒ ∃names. LENGTH names = n ∧ ALL_DISTINCT names ∧ DISJOINT (set names) s -/
theorem fresh_names_exist :
    ∀ (s : Set string) (n : Nat), FINITE (s : Set string) →
      ∃ (names : List string),
        LENGTH names = n ∧ ALL_DISTINCT names ∧ DISJOINT (set names) s := by
  sorry

/- HOL4:
Theorem bv_names_rename_bvars:
   ∀names env tm.
    LENGTH (bv_names tm) ≤ LENGTH names ⇒
    bv_names (SND (rename_bvars names env tm)) = TAKE (LENGTH (bv_names tm)) names -/
theorem bv_names_rename_bvars :
    ∀ (names : List mlstring) (env : List (mlstring × (mlstring × type))) (tm : term),
      LENGTH (bv_names tm) ≤ LENGTH names →
      bv_names (SND (rename_bvars names env tm)) = TAKE (LENGTH (bv_names tm)) names := by
  sorry

/- HOL4:
Theorem FINITE_VFREE_IN[simp]:
   ∀tm. FINITE {x | ∃ty. VFREE_IN (Var x ty) tm} -/
theorem FINITE_VFREE_IN :
    ∀ (tm : term), FINITE {x : mlstring | ∃ (ty : type), VFREE_IN (Var x ty) tm} := by
  sorry

/- HOL4:
Theorem FINITE_VFREE_IN_2[simp]:
   ∀tm. FINITE {(x,ty) | VFREE_IN (Var x ty) tm} -/
theorem FINITE_VFREE_IN_2 :
    ∀ (tm : term),
      FINITE {p : mlstring × type | ∃ (x : mlstring) (ty : type),
        p = (x, ty) ∧ VFREE_IN (Var x ty) tm} := by
  sorry

/- HOL4:
Theorem FINITE_VFREE_IN_list[simp]:
   ∀ls. FINITE {x | ∃ty u. VFREE_IN (Var x ty) u ∧ MEM u ls} -/
theorem FINITE_VFREE_IN_list :
    ∀ (ls : List term),
      FINITE {x : mlstring | ∃ (ty : type) (u : term), VFREE_IN (Var x ty) u ∧ MEM u ls} := by
  sorry

/- HOL4:
Theorem FINITE_MEM_Var[simp]:
   ∀ls. FINITE {(x,ty) | MEM (Var x ty) ls} -/
theorem FINITE_MEM_Var :
    ∀ (ls : List term),
      FINITE {p : mlstring × type | ∃ (x : mlstring) (ty : type),
        p = (x, ty) ∧ MEM (Var x ty) ls} := by
  sorry

/- HOL4:
Theorem theory_ok_sig:
   ∀thy. theory_ok thy ⇒ is_std_sig (sigof thy) -/
theorem theory_ok_sig :
    ∀ (thy : Candle.thy), theory_ok thy → is_std_sig (sigof thy) := by
  sorry

/- HOL4:
Theorem arities_match_nil[simp]:
   (arities_match [] ls = (ls = [])) ∧
    (arities_match ls [] = (ls = [])) -/
theorem arities_match_nil (ls : List type) :
    (arities_match [] ls ↔ (ls = [])) ∧
    (arities_match ls [] ↔ (ls = [])) := by
  sorry

/- HOL4:
Theorem arities_match_Tyvar[simp]:
   arities_match (Tyvar v::ps) (ty::obs) = arities_match ps obs -/
theorem arities_match_Tyvar (v : mlstring) (ps : List type) (ty : type) (obs : List type) :
    arities_match (Tyvar v :: ps) (ty :: obs) ↔ arities_match ps obs := by
  sorry

end

end Candle
