import CmlTS.TypeSoundInvariants
import CmlTS.Proofs.ListAux

/-! Auxiliary induction principles for types and the typing relations. -/

namespace CmlTS

open scoped Classical

theorem Aux.typ_ind {P : typ → Prop} (tvar : ∀ tv, P (Tvar tv)) (tvar_db : ∀ n, P (Tvar_db n))
    (tapp : ∀ ts ti, (∀ t, t ∈ ts → P t) → P (Tapp ts ti)) : ∀ t, P t := by
  have key : ∀ n t, sizeOf t ≤ n → P t := by
    intro n
    induction n with
    | zero =>
      intro t h
      cases t <;> simp at h
    | succ n ih =>
      intro t h
      cases t with
      | Tvar tv => exact tvar tv
      | Tvar_db n => exact tvar_db n
      | Tapp ts ti =>
        refine tapp ts ti (fun t ht => ih t ?_)
        have := List.sizeOf_lt_of_mem ht
        simp only [typ.Tapp.sizeOf_spec] at h
        omega
  exact fun t => key _ t (Nat.le_refl _)

theorem Aux.ast_ind {P : ast_t → Prop} (tvar : ∀ tv, P (Atvar tv))
    (tfun : ∀ t1 t2, P t1 → P t2 → P (Atfun t1 t2))
    (ttup : ∀ ts, (∀ t, t ∈ ts → P t) → P (Attup ts))
    (tapp : ∀ ts ti, (∀ t, t ∈ ts → P t) → P (Atapp ts ti)) : ∀ t, P t := by
  have key : ∀ n t, sizeOf t ≤ n → P t := by
    intro n
    induction n with
    | zero =>
      intro t h
      cases t <;> simp at h
    | succ n ih =>
      intro t h
      cases t with
      | Atvar tv => exact tvar tv
      | Atfun t1 t2 =>
        simp only [ast_t.Atfun.sizeOf_spec] at h
        exact tfun t1 t2 (ih _ (by omega)) (ih _ (by omega))
      | Attup ts =>
        refine ttup ts (fun t ht => ih t ?_)
        have := List.sizeOf_lt_of_mem ht
        simp only [ast_t.Attup.sizeOf_spec] at h
        omega
      | Atapp ts ti =>
        refine tapp ts ti (fun t ht => ih t ?_)
        have := List.sizeOf_lt_of_mem ht
        simp only [ast_t.Atapp.sizeOf_spec] at h
        omega
  exact fun t => key _ t (Nat.le_refl _)

/-- Rule induction for `type_p`/`type_ps`. -/
theorem Aux.type_p_ind
    {P : Nat → type_env → pat → typ → List (varN × typ) → Prop}
    {Q : Nat → type_env → List pat → List typ → List (varN × typ) → Prop}
    (any : ∀ tvs tenv t, check_freevars tvs [] t → P tvs tenv Pany t [])
    (var : ∀ tvs tenv n t, check_freevars tvs [] t → P tvs tenv (Pvar n) t [(n, t)])
    (intLit : ∀ tvs tenv n, P tvs tenv (Plit (lit.IntLit n)) Tint [])
    (char : ∀ tvs tenv c, P tvs tenv (Plit (lit.Char c)) Tchar [])
    (strLit : ∀ tvs tenv s, P tvs tenv (Plit (lit.StrLit s)) Tstring [])
    (word8 : ∀ tvs tenv w, P tvs tenv (Plit (lit.Word8 w)) Tword8 [])
    (word64 : ∀ tvs tenv w, P tvs tenv (Plit (lit.Word64 w)) Tword64 [])
    (con : ∀ tvs tenv cn ps ts tvs' tn ts' bindings,
      EVERY (check_freevars tvs []) ts' → ts'.length = tvs'.length →
      type_ps tvs tenv ps (ts.map (type_subst (alist_to_fmap (tvs'.zip ts')))) bindings →
      nsLookup tenv.c cn = some (tvs', ts, tn) →
      Q tvs tenv ps (ts.map (type_subst (alist_to_fmap (tvs'.zip ts')))) bindings →
      P tvs tenv (Pcon (some cn) ps) (Tapp ts' tn) bindings)
    (tup : ∀ tvs tenv ps ts bindings, type_ps tvs tenv ps ts bindings →
      Q tvs tenv ps ts bindings → P tvs tenv (Pcon none ps) (Ttup ts) bindings)
    (ref : ∀ tvs tenv p t bindings, type_p tvs tenv p t bindings → P tvs tenv p t bindings →
      P tvs tenv (Pref p) (Tref t) bindings)
    (pas : ∀ tvs tenv p v t bindings, type_p tvs tenv p t bindings → P tvs tenv p t bindings →
      P tvs tenv (Pas p v) t (bindings ++ [(v, t)]))
    (tannot : ∀ tvs tenv p t bindings, check_freevars_ast [] t → check_type_names tenv.t t →
      type_p tvs tenv p (type_name_subst tenv.t t) bindings →
      P tvs tenv p (type_name_subst tenv.t t) bindings →
      P tvs tenv (Ptannot p t) (type_name_subst tenv.t t) bindings)
    (nil : ∀ tvs tenv, Q tvs tenv [] [] [])
    (cons : ∀ tvs tenv p ps t ts bindings bindings',
      type_p tvs tenv p t bindings → type_ps tvs tenv ps ts bindings' →
      P tvs tenv p t bindings → Q tvs tenv ps ts bindings' →
      Q tvs tenv (p :: ps) (t :: ts) (bindings' ++ bindings)) :
    (∀ tvs tenv p t b, type_p tvs tenv p t b → P tvs tenv p t b) ∧
    (∀ tvs tenv ps ts b, type_ps tvs tenv ps ts b → Q tvs tenv ps ts b) := by
  constructor
  · intro tvs tenv p t b h
    exact type_p.rec (motive_1 := fun p t b _ => P tvs tenv p t b)
      (motive_2 := fun ps ts b _ => Q tvs tenv ps ts b)
      (any tvs tenv) (var tvs tenv) (intLit tvs tenv) (char tvs tenv) (strLit tvs tenv)
      (word8 tvs tenv) (word64 tvs tenv) (con tvs tenv) (tup tvs tenv) (ref tvs tenv)
      (pas tvs tenv) (tannot tvs tenv) (nil tvs tenv) (cons tvs tenv) h
  · intro tvs tenv p t b h
    exact type_ps.rec (motive_1 := fun p t b _ => P tvs tenv p t b)
      (motive_2 := fun ps ts b _ => Q tvs tenv ps ts b)
      (any tvs tenv) (var tvs tenv) (intLit tvs tenv) (char tvs tenv) (strLit tvs tenv)
      (word8 tvs tenv) (word64 tvs tenv) (con tvs tenv) (tup tvs tenv) (ref tvs tenv)
      (pas tvs tenv) (tannot tvs tenv) (nil tvs tenv) (cons tvs tenv) h

/-- Rule induction for `type_e`/`type_es`/`type_funs`. -/
theorem Aux.type_e_ind
    {P : type_env → tenv_val_exp → exp → typ → Prop}
    {Q : type_env → tenv_val_exp → List exp → List typ → Prop}
    {R : type_env → tenv_val_exp → List (varN × varN × exp) → List (varN × typ) → Prop}
    (intLit : ∀ tenv tenvE n, P tenv tenvE (exp.Lit (lit.IntLit n)) Tint)
    (char : ∀ tenv tenvE c, P tenv tenvE (exp.Lit (lit.Char c)) Tchar)
    (strLit : ∀ tenv tenvE s, P tenv tenvE (exp.Lit (lit.StrLit s)) Tstring)
    (word8 : ∀ tenv tenvE w, P tenv tenvE (exp.Lit (lit.Word8 w)) Tword8)
    (word64 : ∀ tenv tenvE w, P tenv tenvE (exp.Lit (lit.Word64 w)) Tword64)
    (float64 : ∀ tenv tenvE w, P tenv tenvE (exp.Lit (lit.Float64 w)) Tdouble)
    (raise : ∀ tenv tenvE e t, check_freevars (num_tvs tenvE) [] t → type_e tenv tenvE e Texn →
      P tenv tenvE e Texn → P tenv tenvE (exp.Raise e) t)
    (handle : ∀ tenv tenvE e pes t (bs : pat × exp → List (varN × typ)),
      type_e tenv tenvE e t → ¬ pes = [] →
      (∀ pe, pe ∈ pes → ALL_DISTINCT (pat_bindings pe.1 [])) →
      (∀ pe, pe ∈ pes → type_p (num_tvs tenvE) tenv pe.1 Texn (bs pe)) →
      (∀ pe, pe ∈ pes → type_e tenv (bind_var_list 0 (bs pe) tenvE) pe.2 t) →
      P tenv tenvE e t →
      (∀ pe, pe ∈ pes → P tenv (bind_var_list 0 (bs pe) tenvE) pe.2 t) →
      P tenv tenvE (exp.Handle e pes) t)
    (con : ∀ tenv tenvE cn es tvs tn ts' ts,
      EVERY (check_freevars (num_tvs tenvE) []) ts' → tvs.length = ts'.length →
      type_es tenv tenvE es (ts.map (type_subst (alist_to_fmap (tvs.zip ts')))) →
      nsLookup tenv.c cn = some (tvs, ts, tn) →
      Q tenv tenvE es (ts.map (type_subst (alist_to_fmap (tvs.zip ts')))) →
      P tenv tenvE (exp.Con (some cn) es) (Tapp ts' tn))
    (tup : ∀ tenv tenvE es ts, type_es tenv tenvE es ts → Q tenv tenvE es ts →
      P tenv tenvE (exp.Con none es) (Ttup ts))
    (var : ∀ tenv tenvE n t targs tvs, tvs = targs.length →
      EVERY (check_freevars (num_tvs tenvE) []) targs →
      lookup_var n tenvE tenv = some (tvs, t) →
      P tenv tenvE (exp.Var n) (deBruijn_subst 0 targs t))
    (fn : ∀ tenv tenvE n e t1 t2, check_freevars (num_tvs tenvE) [] t1 →
      type_e tenv (Bind_name n 0 t1 tenvE) e t2 → P tenv (Bind_name n 0 t1 tenvE) e t2 →
      P tenv tenvE (exp.Fun n e) (Tfn t1 t2))
    (app : ∀ tenv tenvE o es ts t, type_es tenv tenvE es ts → type_op o ts t →
      check_freevars (num_tvs tenvE) [] t → Q tenv tenvE es ts →
      P tenv tenvE (exp.App o es) t)
    (log : ∀ tenv tenvE l e1 e2, type_e tenv tenvE e1 Tbool → type_e tenv tenvE e2 Tbool →
      P tenv tenvE e1 Tbool → P tenv tenvE e2 Tbool → P tenv tenvE (exp.Log l e1 e2) Tbool)
    (if' : ∀ tenv tenvE e1 e2 e3 t, type_e tenv tenvE e1 Tbool → type_e tenv tenvE e2 t →
      type_e tenv tenvE e3 t → P tenv tenvE e1 Tbool → P tenv tenvE e2 t → P tenv tenvE e3 t →
      P tenv tenvE (exp.If e1 e2 e3) t)
    (mat : ∀ tenv tenvE e pes t1 t2 (bs : pat × exp → List (varN × typ)),
      type_e tenv tenvE e t1 → ¬ pes = [] →
      (∀ pe, pe ∈ pes → ALL_DISTINCT (pat_bindings pe.1 [])) →
      (∀ pe, pe ∈ pes → type_p (num_tvs tenvE) tenv pe.1 t1 (bs pe)) →
      (∀ pe, pe ∈ pes → type_e tenv (bind_var_list 0 (bs pe) tenvE) pe.2 t2) →
      P tenv tenvE e t1 →
      (∀ pe, pe ∈ pes → P tenv (bind_var_list 0 (bs pe) tenvE) pe.2 t2) →
      P tenv tenvE (exp.Mat e pes) t2)
    (let' : ∀ tenv tenvE n e1 e2 t1 t2, type_e tenv tenvE e1 t1 →
      type_e tenv (opt_bind_name n 0 t1 tenvE) e2 t2 → P tenv tenvE e1 t1 →
      P tenv (opt_bind_name n 0 t1 tenvE) e2 t2 → P tenv tenvE (exp.Let n e1 e2) t2)
    (letrec : ∀ tenv tenvE funs e t bindings,
      type_funs tenv (bind_var_list 0 bindings tenvE) funs bindings →
      type_e tenv (bind_var_list 0 bindings tenvE) e t →
      R tenv (bind_var_list 0 bindings tenvE) funs bindings →
      P tenv (bind_var_list 0 bindings tenvE) e t → P tenv tenvE (exp.Letrec funs e) t)
    (tannot : ∀ tenv tenvE e t, check_freevars_ast [] t → check_type_names tenv.t t →
      type_e tenv tenvE e (type_name_subst tenv.t t) →
      P tenv tenvE e (type_name_subst tenv.t t) →
      P tenv tenvE (exp.Tannot e t) (type_name_subst tenv.t t))
    (lannot : ∀ tenv tenvE e l t, type_e tenv tenvE e t → P tenv tenvE e t →
      P tenv tenvE (exp.Lannot e l) t)
    (nil : ∀ tenv tenvE, Q tenv tenvE [] [])
    (cons : ∀ tenv tenvE e es t ts, type_e tenv tenvE e t → type_es tenv tenvE es ts →
      P tenv tenvE e t → Q tenv tenvE es ts → Q tenv tenvE (e :: es) (t :: ts))
    (fnil : ∀ tenv tenvE, R tenv tenvE [] [])
    (fcons : ∀ tenv tenvE fn n e funs bindings t1 t2,
      check_freevars (num_tvs tenvE) [] (Tfn t1 t2) →
      type_e tenv (Bind_name n 0 t1 tenvE) e t2 → type_funs tenv tenvE funs bindings →
      ALOOKUP bindings fn = none → P tenv (Bind_name n 0 t1 tenvE) e t2 →
      R tenv tenvE funs bindings →
      R tenv tenvE ((fn, n, e) :: funs) ((fn, Tfn t1 t2) :: bindings)) :
    (∀ tenv tenvE e t, type_e tenv tenvE e t → P tenv tenvE e t) ∧
    (∀ tenv tenvE es ts, type_es tenv tenvE es ts → Q tenv tenvE es ts) ∧
    (∀ tenv tenvE funs bs, type_funs tenv tenvE funs bs → R tenv tenvE funs bs) := by
  refine ⟨?_, ?_, ?_⟩
  · intro tenv tenvE e t h
    exact type_e.rec (motive_1 := fun tenvE e t _ => P tenv tenvE e t)
      (motive_2 := fun tenvE es ts _ => Q tenv tenvE es ts)
      (motive_3 := fun tenvE funs bs _ => R tenv tenvE funs bs)
      (intLit tenv) (char tenv) (strLit tenv) (word8 tenv) (word64 tenv) (float64 tenv)
      (raise tenv) (handle tenv) (con tenv) (tup tenv) (var tenv) (fn tenv) (app tenv)
      (log tenv) (if' tenv) (mat tenv) (let' tenv) (letrec tenv) (tannot tenv) (lannot tenv)
      (nil tenv) (cons tenv) (fnil tenv) (fcons tenv) h
  · intro tenv tenvE e t h
    exact type_es.rec (motive_1 := fun tenvE e t _ => P tenv tenvE e t)
      (motive_2 := fun tenvE es ts _ => Q tenv tenvE es ts)
      (motive_3 := fun tenvE funs bs _ => R tenv tenvE funs bs)
      (intLit tenv) (char tenv) (strLit tenv) (word8 tenv) (word64 tenv) (float64 tenv)
      (raise tenv) (handle tenv) (con tenv) (tup tenv) (var tenv) (fn tenv) (app tenv)
      (log tenv) (if' tenv) (mat tenv) (let' tenv) (letrec tenv) (tannot tenv) (lannot tenv)
      (nil tenv) (cons tenv) (fnil tenv) (fcons tenv) h
  · intro tenv tenvE e t h
    exact type_funs.rec (motive_1 := fun tenvE e t _ => P tenv tenvE e t)
      (motive_2 := fun tenvE es ts _ => Q tenv tenvE es ts)
      (motive_3 := fun tenvE funs bs _ => R tenv tenvE funs bs)
      (intLit tenv) (char tenv) (strLit tenv) (word8 tenv) (word64 tenv) (float64 tenv)
      (raise tenv) (handle tenv) (con tenv) (tup tenv) (var tenv) (fn tenv) (app tenv)
      (log tenv) (if' tenv) (mat tenv) (let' tenv) (letrec tenv) (tannot tenv) (lannot tenv)
      (nil tenv) (cons tenv) (fnil tenv) (fcons tenv) h

/-! ### lookups in a zip -/

theorem Aux.ALOOKUP_zip_mem {α β : Type} {l1 : List α} {l2 : List β} {k : α} {x : β}
    (h : ALOOKUP (l1.zip l2) k = some x) : k ∈ l1 ∧ x ∈ l2 := by
  have := Aux.ALOOKUP_mem h
  exact List.of_mem_zip this

theorem Aux.ALOOKUP_zip_some {α β : Type} {l1 : List α} {l2 : List β} {k : α}
    (hl : l1.length = l2.length) (h : k ∈ l1) : ∃ x, ALOOKUP (l1.zip l2) k = some x := by
  apply Aux.mem_ALOOKUP_some
  rw [List.map_fst_zip (by omega)]
  exact h

theorem Aux.ALOOKUP_zip_map {α β γ : Type} (f : β → γ) (l1 : List α) (l2 : List β) (k : α) :
    ALOOKUP (l1.zip (l2.map f)) k = (ALOOKUP (l1.zip l2) k).map f := by
  induction l1 generalizing l2 with
  | nil => simp [ALOOKUP]
  | cons a t ih =>
    cases l2 with
    | nil => simp [ALOOKUP]
    | cons b t2 =>
      simp only [List.map_cons, List.zip_cons_cons, ALOOKUP, ih]
      split <;> simp

end CmlTS
