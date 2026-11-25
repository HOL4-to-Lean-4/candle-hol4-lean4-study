import CmlTS.Ast
import CmlTS.TypeSystem
import CmlTS.SemanticPrimitives
import CmlTS.FpSem
import CmlTS.Evaluate
import CmlTS.NamespaceProps
import CmlTS.SemanticPrimitivesProps
import CmlTS.EvaluateProps
import CmlTS.Weakening
import CmlTS.TypeSysProps
import CmlTS.TypeSoundInvariants
import CmlTS.SemanticsMin

/-
HOL4 theory `typeSound` (typeSoundScript.sml).
-/

namespace CmlTS

noncomputable section

open scoped Classical

/- HOL4:
Definition store_type_extension_def:
  store_type_extension tenvS1 tenvS2 =
  ?tenvS'. (tenvS2 = FUNION tenvS' tenvS1) ∧
           (!l. (FLOOKUP tenvS' l = NONE) ∨ (FLOOKUP tenvS1 l = NONE))
End -/
def store_type_extension {α β : Type} (tenvS1 tenvS2 : fmap α β) : Prop :=
  ∃ tenvS', tenvS2 = FUNION tenvS' tenvS1 ∧
    ∀ l, FLOOKUP tenvS' l = none ∨ FLOOKUP tenvS1 l = none

/- HOL4:
Theorem fst_triple[local]:
  (\ (x,y,z). x) = FST -/
theorem fst_triple {α β γ : Type} :
    (fun ((x, _, _) : α × β × γ) => x) = Prod.fst := rfl

/- HOL4:
Theorem sing_list[local]:
  !l. LENGTH l = 1 ⇔ ?x. l = [x] -/
theorem sing_list {α : Type} :
    ∀ l : List α, l.length = 1 ↔ ∃ x, l = [x] := by
  intro l
  match l with
  | [] => simp
  | [x] => simp
  | x :: y :: l => simp

/- HOL4:
Theorem EVERY_LIST_REL[local]:
  EVERY (\x. f x y) l = LIST_REL (\x y. f x y) l (REPLICATE (LENGTH l) y) -/
theorem EVERY_LIST_REL {α β : Type} (f : α → β → Prop) (y : β) (l : List α) :
    EVERY (fun x => f x y) l ↔
      LIST_REL (fun x y => f x y) l (List.replicate l.length y) := by
  induction l with
  | nil => exact Iff.rfl
  | cons a t ih =>
    simp only [EVERY, List.length_cons, List.replicate_succ, LIST_REL, ih]

/- HOL4:
Theorem v_unchanged[simp]:
  !tenv x. tenv with v := tenv.v = tenv -/
theorem v_unchanged {α : Type} :
    ∀ (tenv : type_env) (_x : α), { tenv with v := tenv.v } = tenv := fun _ _ => rfl

/- HOL4:
Theorem check_dup_ctors_thm:
  check_dup_ctors (tvs,tn,condefs) = ALL_DISTINCT (MAP FST condefs) -/
theorem check_dup_ctors_thm (tvs : List tvarN) (tn : mlstring)
    (condefs : List (mlstring × List ast_t)) :
    check_dup_ctors (tvs, tn, condefs) ↔ ALL_DISTINCT (condefs.map Prod.fst) := by
  have h : (condefs.foldr (fun (n, _) x2 => if True then n :: x2 else x2) ([] : List mlstring)) =
      condefs.map Prod.fst := by
    induction condefs with
    | nil => rfl
    | cons a t ih =>
      rw [List.foldr_cons, ih]
      simp
  unfold check_dup_ctors
  dsimp only
  rw [h]

theorem Aux.type_v_inv {tvs : Nat} {ctMap : ctMap_ty} {tenvS : tenv_store} {v : value} {t : typ}
    (h : type_v tvs ctMap tenvS v t) :
    (∃ n, v = Litv (lit.IntLit n) ∧ t = Tapp [] Tint_num) ∨
    (∃ n, v = Litv (lit.Char n) ∧ t = Tapp [] Tchar_num) ∨
    (∃ n, v = Litv (lit.StrLit n) ∧ t = Tapp [] Tstring_num) ∨
    (∃ n, v = Litv (lit.Word8 n) ∧ t = Tapp [] Tword8_num) ∨
    (∃ n, v = Litv (lit.Word64 n) ∧ t = Tapp [] Tword64_num) ∨
    (∃ n, v = Litv (lit.Float64 n) ∧ t = Tapp [] Tdouble_num) ∨
    (∃ stamp vs tvs' ts' ts ti, v = Conv (some stamp) vs ∧ t = Tapp ts' ti ∧
      FLOOKUP ctMap stamp = some (tvs', ts, ti) ∧ tvs'.length = ts'.length ∧
      EVERY (check_freevars tvs []) ts' ∧
      LIST_REL (type_v tvs ctMap tenvS) vs
        (ts.map (type_subst (alist_to_fmap (tvs'.zip ts'))))) ∨
    (∃ vs ts, v = Conv none vs ∧ t = Tapp ts Ttup_num ∧
      LIST_REL (type_v tvs ctMap tenvS) vs ts) ∨
    (∃ env n e t1 t2, v = Closure env n e ∧ t = Tapp [t1, t2] Tfn_num) ∨
    (∃ env funs n t1 t2, v = Recclosure env funs n ∧ t = Tapp [t1, t2] Tfn_num) ∨
    (∃ n t1, v = Loc true n ∧ t = Tapp [t1] Tref_num ∧ FLOOKUP tenvS n = some (Ref_t t1)) ∨
    (∃ n, v = Loc true n ∧ t = Tapp [] Tword8array_num ∧ FLOOKUP tenvS n = some W8array_t) ∨
    (∃ n t1, v = Loc true n ∧ t = Tapp [t1] Tarray_num ∧ FLOOKUP tenvS n = some (Varray_t t1)) ∨
    (∃ vs t1, v = Vectorv vs ∧ t = Tapp [t1] Tvector_num ∧
      EVERY (fun v => type_v tvs ctMap tenvS v t1) vs) := by
  cases h with
  | intLit _ _ _ n => exact Or.inl ⟨_, rfl, rfl⟩
  | char _ _ _ n => exact Or.inr (Or.inl ⟨_, rfl, rfl⟩)
  | strLit _ _ _ n => exact Or.inr (Or.inr (Or.inl ⟨_, rfl, rfl⟩))
  | word8 _ _ _ n => exact Or.inr (Or.inr (Or.inr (Or.inl ⟨_, rfl, rfl⟩)))
  | word64 _ _ _ n => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, rfl, rfl⟩))))
  | float64 _ _ _ n => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, rfl, rfl⟩)))))
  | conv _ _ _ vs tvs' stamp ts' ts ti h1 h2 h3 h4 h5 =>
    refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨stamp, vs, tvs', ts', ts, ti, rfl, rfl, h5, h2, h1, ?_⟩))))))
    rw [← Aux.FUPDATE_LIST_reverse]
    exact LIST_REL_iff_aux.mpr ⟨h3, h4⟩
  | tup _ _ _ vs ts h1 h2 =>
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨vs, ts, rfl, rfl, LIST_REL_iff_aux.mpr ⟨h1, h2⟩⟩)))))))
  | closure _ _ _ env tenv tenvE n e t1 t2 =>
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨env, n, e, t1, t2, rfl, rfl⟩))))))))
  | recclosure _ _ _ env funs n t tenv tenvE bindings h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 =>
    obtain ⟨t1, t2, rfl, -⟩ := type_funs_Tfn _ _ _ _ () _ _ ⟨h7, h8⟩
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨env, funs, n, t1, t2, rfl, rfl⟩)))))))))
  | ref _ _ _ n t h1 h2 =>
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨n, t, rfl, rfl, h2⟩))))))))))
  | w8array _ _ _ n h1 =>
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl ⟨n, rfl, rfl, h1⟩)))))))))))
  | varray _ _ _ n t h1 h2 =>
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inl ⟨n, t, rfl, rfl, h2⟩))))))))))))
  | vector _ _ _ vs t h1 h2 =>
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inr ⟨vs, t, rfl, rfl, EVERY_iff_forall.mpr h2⟩))))))))))))

/-- The type numbers of values that are not constructor applications. -/
def Aux.isPrim (ti : Nat) : Prop :=
  ti = Tint_num ∨ ti = Tchar_num ∨ ti = Tstring_num ∨ ti = Tword8_num ∨ ti = Tword64_num ∨
  ti = Tdouble_num ∨ ti = Ttup_num ∨ ti = Tfn_num ∨ ti = Tref_num ∨ ti = Tword8array_num ∨
  ti = Tarray_num ∨ ti = Tvector_num

theorem Aux.no_conv {ctMap : ctMap_ty} {stamp : CmlTS.stamp} {tvs : List tvarN} {ts : List typ}
    {ti : type_ident} (hok : ctMap_ok ctMap) (h : FLOOKUP ctMap stamp = some (tvs, ts, ti))
    (hp : Aux.isPrim ti) : False := by
  cases stamp with
  | ExnStamp n =>
    have := (hok.2.1 _ _ _ _ h).2
    subst this
    simp [Aux.isPrim, Tint_num, Tchar_num, Tstring_num, Tword8_num, Tword64_num, Tdouble_num,
      Ttup_num, Tfn_num, Tref_num, Tword8array_num, Tarray_num, Tvector_num, Texn_num] at hp
  | TypeStamp cn n =>
    have := hok.2.2.1 _ _ _ _ _ h
    apply this
    unfold Aux.isPrim at hp
    simp only [prim_type_nums, List.mem_cons]
    rcases hp with h | h | h | h | h | h | h | h | h | h | h | h <;> simp [h]

theorem Aux.canon {tvs : Nat} {ctMap : ctMap_ty} {tenvS : tenv_store} {v : value}
    {ts0 : List typ} {ti0 : type_ident}
    (h : type_v tvs ctMap tenvS v (Tapp ts0 ti0)) (hok : ctMap_ok ctMap) (hp : Aux.isPrim ti0) :
    (ti0 = Tint_num ∧ ∃ n, v = Litv (lit.IntLit n)) ∨
    (ti0 = Tchar_num ∧ ∃ n, v = Litv (lit.Char n)) ∨
    (ti0 = Tstring_num ∧ ∃ n, v = Litv (lit.StrLit n)) ∨
    (ti0 = Tword8_num ∧ ∃ n, v = Litv (lit.Word8 n)) ∨
    (ti0 = Tword64_num ∧ ∃ n, v = Litv (lit.Word64 n)) ∨
    (ti0 = Tdouble_num ∧ ∃ n, v = Litv (lit.Float64 n)) ∨
    (ti0 = Ttup_num ∧ ∃ vs, v = Conv none vs ∧ LIST_REL (type_v tvs ctMap tenvS) vs ts0) ∨
    (ti0 = Tfn_num ∧ ((∃ env n e, v = Closure env n e) ∨ ∃ env funs n, v = Recclosure env funs n)) ∨
    (ti0 = Tref_num ∧ ∃ n t1, v = Loc true n ∧ ts0 = [t1] ∧ FLOOKUP tenvS n = some (Ref_t t1)) ∨
    (ti0 = Tword8array_num ∧ ∃ n, v = Loc true n ∧ FLOOKUP tenvS n = some W8array_t) ∨
    (ti0 = Tarray_num ∧ ∃ n t1, v = Loc true n ∧ ts0 = [t1] ∧
      FLOOKUP tenvS n = some (Varray_t t1)) ∨
    (ti0 = Tvector_num ∧ ∃ vs t1, v = Vectorv vs ∧ ts0 = [t1] ∧
      EVERY (fun v => type_v tvs ctMap tenvS v t1) vs) := by
  rcases Aux.type_v_inv h with ⟨n, rfl, ht⟩ | ⟨n, rfl, ht⟩ | ⟨n, rfl, ht⟩ | ⟨n, rfl, ht⟩ |
    ⟨n, rfl, ht⟩ | ⟨n, rfl, ht⟩ | ⟨stamp, vs, tvs', ts', ts, ti, rfl, ht, hl, -⟩ |
    ⟨vs, ts, rfl, ht, hr⟩ | ⟨env, n, e, t1, t2, rfl, ht⟩ | ⟨env, funs, n, t1, t2, rfl, ht⟩ |
    ⟨n, t1, rfl, ht, hl⟩ | ⟨n, rfl, ht, hl⟩ | ⟨n, t1, rfl, ht, hl⟩ | ⟨vs, t1, rfl, ht, hl⟩
  all_goals (rw [typ.Tapp.injEq] at ht; obtain ⟨rfl, rfl⟩ := ht)
  · exact Or.inl ⟨rfl, _, rfl⟩
  · exact Or.inr (Or.inl ⟨rfl, _, rfl⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨rfl, _, rfl⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, _, rfl⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, _, rfl⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, _, rfl⟩)))))
  · exact (Aux.no_conv hok hl hp).elim
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, _, rfl, hr⟩))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨rfl, Or.inl ⟨_, _, _, rfl⟩⟩)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨rfl, Or.inr ⟨_, _, _, rfl⟩⟩)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨rfl, _, _, rfl, rfl, hl⟩))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨rfl, _, rfl, hl⟩)))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨rfl, _, _, rfl, rfl, hl⟩))))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      ⟨rfl, _, _, rfl, rfl, hl⟩))))))))))

theorem Aux.store_lookup_eq {α : Type} (l : Nat) (st : List (store_v α)) :
    store_lookup l st = st[l]? := by
  unfold store_lookup
  split
  · rename_i h; rw [Aux.EL_getElem? _ _ h]
  · rename_i h; rw [List.getElem?_eq_none (by omega)]

theorem Aux.LUPDATE_eq {α : Type} (x : α) : ∀ (l : List α) (n : Nat),
    LUPDATE x n l = l.set n x := by
  intro l
  induction l with
  | nil => intro n; rfl
  | cons a t ih =>
    intro n
    cases n with
    | zero => rfl
    | succ n => simp [LUPDATE, ih]

theorem Aux.type_s_lookup {ctMap : ctMap_ty} {envS : List (store_v value)} {tenvS : tenv_store}
    {l : Nat} {st : store_t} (h : type_s ctMap envS tenvS) (hl : FLOOKUP tenvS l = some st) :
    ∃ sv, store_lookup l envS = some sv ∧ type_sv ctMap tenvS sv st := by
  obtain ⟨sv, hsv⟩ := (h l).1.mp ⟨st, hl⟩
  exact ⟨sv, hsv, (h l).2 _ _ ⟨hl, hsv⟩⟩

/- HOL4:
Theorem prim_canonical_values_thm:
  (type_v tvs ctMap tenvS v Tint ∧ ctMap_ok ctMap ⇒ (∃n. v = Litv (IntLit n))) ∧
  (type_v tvs ctMap tenvS v Tchar ∧ ctMap_ok ctMap ⇒ (∃c. v = Litv (Char c))) ∧
  (type_v tvs ctMap tenvS v Tstring ∧ ctMap_ok ctMap ⇒ (∃s. v = Litv (StrLit s))) ∧
  (type_v tvs ctMap tenvS v Tword8 ∧ ctMap_ok ctMap ⇒ (∃n. v = Litv (Word8 n))) ∧
  (type_v tvs ctMap tenvS v Tword64 ∧ ctMap_ok ctMap ⇒ (∃n. v = Litv (Word64 n))) /\
  (type_v tvs ctMap tenvS v Tdouble /\ ctMap_ok ctMap ==> ∃n. v = Litv (Float64 n)) ∧
  (type_v tvs ctMap tenvS v (Ttup ts) ∧ ctMap_ok ctMap ⇒
   (∃vs. v = Conv NONE vs ∧ LENGTH ts = LENGTH vs)) ∧
  (type_v tvs ctMap tenvS v (Tfn t1 t2) ∧ ctMap_ok ctMap ⇒
   (∃env n e. v = Closure env n e) ∨
   (∃env funs n. v = Recclosure env funs n)) ∧
  (type_v tvs ctMap tenvS v (Tref t1) ∧ ctMap_ok ctMap ∧ type_s ctMap envS tenvS ⇒
   (∃n v2. v = Loc T n ∧ store_lookup n envS = SOME (Refv v2) ∧
           type_v 0 ctMap tenvS v2 t1)) ∧
  (type_v tvs ctMap tenvS v Tword8array ∧ ctMap_ok ctMap ∧ type_s ctMap envS tenvS ⇒
   (∃n ws. v = Loc T n ∧ store_lookup n envS = SOME (W8array ws) ∧
           FLOOKUP tenvS n = SOME W8array_t)) ∧
  (type_v tvs ctMap tenvS v (Tarray t) ∧ ctMap_ok ctMap ∧ type_s ctMap envS tenvS ⇒
   (∃n vs. v = Loc T n ∧ store_lookup n envS = SOME (Varray vs) ∧
           EVERY (\v. type_v 0 ctMap tenvS v t) vs ∧
           FLOOKUP tenvS n = SOME (Varray_t t))) ∧
  (type_v tvs ctMap tenvS v (Tvector t) ∧ ctMap_ok ctMap ⇒
   (?vs. v = Vectorv vs ∧ EVERY (\v. type_v tvs ctMap tenvS v t) vs)) -/
theorem prim_canonical_values_thm (tvs : Nat) (ctMap : ctMap_ty) (tenvS : tenv_store)
    (v : value) (ts : List typ) (t1 t2 : typ) (envS : List (store_v value)) (t : typ) :
    (type_v tvs ctMap tenvS v Tint ∧ ctMap_ok ctMap → (∃ n, v = Litv (lit.IntLit n))) ∧
    (type_v tvs ctMap tenvS v Tchar ∧ ctMap_ok ctMap → (∃ c, v = Litv (lit.Char c))) ∧
    (type_v tvs ctMap tenvS v Tstring ∧ ctMap_ok ctMap → (∃ s, v = Litv (lit.StrLit s))) ∧
    (type_v tvs ctMap tenvS v Tword8 ∧ ctMap_ok ctMap → (∃ n, v = Litv (lit.Word8 n))) ∧
    (type_v tvs ctMap tenvS v Tword64 ∧ ctMap_ok ctMap → (∃ n, v = Litv (lit.Word64 n))) ∧
    (type_v tvs ctMap tenvS v Tdouble ∧ ctMap_ok ctMap → ∃ n, v = Litv (lit.Float64 n)) ∧
    (type_v tvs ctMap tenvS v (Ttup ts) ∧ ctMap_ok ctMap →
      (∃ vs, v = Conv none vs ∧ ts.length = vs.length)) ∧
    (type_v tvs ctMap tenvS v (Tfn t1 t2) ∧ ctMap_ok ctMap →
      (∃ env n e, v = Closure env n e) ∨
      (∃ env funs n, v = Recclosure env funs n)) ∧
    (type_v tvs ctMap tenvS v (Tref t1) ∧ ctMap_ok ctMap ∧ type_s ctMap envS tenvS →
      (∃ n v2, v = Loc true n ∧ store_lookup n envS = some (Refv v2) ∧
        type_v 0 ctMap tenvS v2 t1)) ∧
    (type_v tvs ctMap tenvS v Tword8array ∧ ctMap_ok ctMap ∧ type_s ctMap envS tenvS →
      (∃ n ws, v = Loc true n ∧ store_lookup n envS = some (W8array ws) ∧
        FLOOKUP tenvS n = some W8array_t)) ∧
    (type_v tvs ctMap tenvS v (Tarray t) ∧ ctMap_ok ctMap ∧ type_s ctMap envS tenvS →
      (∃ n vs, v = Loc true n ∧ store_lookup n envS = some (Varray vs) ∧
        EVERY (fun v => type_v 0 ctMap tenvS v t) vs ∧
        FLOOKUP tenvS n = some (Varray_t t))) ∧
    (type_v tvs ctMap tenvS v (Tvector t) ∧ ctMap_ok ctMap →
      (∃ vs, v = Vectorv vs ∧ EVERY (fun v => type_v tvs ctMap tenvS v t) vs)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro ⟨h, hok⟩
    have := Aux.canon h hok (by simp [Aux.isPrim])
    simp [Tint_num, Tchar_num, Tstring_num, Tword8_num, Tword64_num, Tdouble_num,
      Ttup_num, Tfn_num, Tref_num, Tword8array_num, Tarray_num, Tvector_num] at this
    exact this
  · rintro ⟨h, hok⟩
    have := Aux.canon h hok (by simp [Aux.isPrim])
    simp [Tint_num, Tchar_num, Tstring_num, Tword8_num, Tword64_num, Tdouble_num,
      Ttup_num, Tfn_num, Tref_num, Tword8array_num, Tarray_num, Tvector_num] at this
    exact this
  · rintro ⟨h, hok⟩
    have := Aux.canon h hok (by simp [Aux.isPrim])
    simp [Tint_num, Tchar_num, Tstring_num, Tword8_num, Tword64_num, Tdouble_num,
      Ttup_num, Tfn_num, Tref_num, Tword8array_num, Tarray_num, Tvector_num] at this
    exact this
  · rintro ⟨h, hok⟩
    have := Aux.canon h hok (by simp [Aux.isPrim])
    simp [Tint_num, Tchar_num, Tstring_num, Tword8_num, Tword64_num, Tdouble_num,
      Ttup_num, Tfn_num, Tref_num, Tword8array_num, Tarray_num, Tvector_num] at this
    exact this
  · rintro ⟨h, hok⟩
    have := Aux.canon h hok (by simp [Aux.isPrim])
    simp [Tint_num, Tchar_num, Tstring_num, Tword8_num, Tword64_num, Tdouble_num,
      Ttup_num, Tfn_num, Tref_num, Tword8array_num, Tarray_num, Tvector_num] at this
    exact this
  · rintro ⟨h, hok⟩
    have := Aux.canon h hok (by simp [Aux.isPrim])
    simp [Tint_num, Tchar_num, Tstring_num, Tword8_num, Tword64_num, Tdouble_num,
      Ttup_num, Tfn_num, Tref_num, Tword8array_num, Tarray_num, Tvector_num] at this
    exact this
  · rintro ⟨h, hok⟩
    have := Aux.canon h hok (by simp [Aux.isPrim])
    simp [Tint_num, Tchar_num, Tstring_num, Tword8_num, Tword64_num, Tdouble_num,
      Ttup_num, Tfn_num, Tref_num, Tword8array_num, Tarray_num, Tvector_num] at this
    obtain ⟨vs, rfl, hr⟩ := this
    exact ⟨vs, rfl, (Aux.LIST_REL_length hr).symm⟩
  · rintro ⟨h, hok⟩
    have := Aux.canon h hok (by simp [Aux.isPrim])
    simp [Tint_num, Tchar_num, Tstring_num, Tword8_num, Tword64_num, Tdouble_num,
      Ttup_num, Tfn_num, Tref_num, Tword8array_num, Tarray_num, Tvector_num] at this
    exact this
  · rintro ⟨h, hok, hs⟩
    have := Aux.canon h hok (by simp [Aux.isPrim])
    simp [Tint_num, Tchar_num, Tstring_num, Tword8_num, Tword64_num, Tdouble_num,
      Ttup_num, Tfn_num, Tref_num, Tword8array_num, Tarray_num, Tvector_num] at this
    obtain ⟨n, rfl, hl⟩ := this
    obtain ⟨sv, h1, h2⟩ := Aux.type_s_lookup hs hl
    cases sv <;> simp only [type_sv] at h2
    exact ⟨n, _, rfl, h1, h2⟩
  · rintro ⟨h, hok, hs⟩
    have := Aux.canon h hok (by simp [Aux.isPrim])
    simp [Tint_num, Tchar_num, Tstring_num, Tword8_num, Tword64_num, Tdouble_num,
      Ttup_num, Tfn_num, Tref_num, Tword8array_num, Tarray_num, Tvector_num] at this
    obtain ⟨n, rfl, hl⟩ := this
    obtain ⟨sv, h1, h2⟩ := Aux.type_s_lookup hs hl
    cases sv <;> simp only [type_sv] at h2
    exact ⟨n, _, rfl, h1, hl⟩
  · rintro ⟨h, hok, hs⟩
    have := Aux.canon h hok (by simp [Aux.isPrim])
    simp [Tint_num, Tchar_num, Tstring_num, Tword8_num, Tword64_num, Tdouble_num,
      Ttup_num, Tfn_num, Tref_num, Tword8array_num, Tarray_num, Tvector_num] at this
    obtain ⟨n, rfl, hl⟩ := this
    obtain ⟨sv, h1, h2⟩ := Aux.type_s_lookup hs hl
    cases sv <;> simp only [type_sv] at h2
    exact ⟨n, _, rfl, h1, h2, hl⟩
  · rintro ⟨h, hok⟩
    have := Aux.canon h hok (by simp [Aux.isPrim])
    simp [Tint_num, Tchar_num, Tstring_num, Tword8_num, Tword64_num, Tdouble_num,
      Ttup_num, Tfn_num, Tref_num, Tword8array_num, Tarray_num, Tvector_num] at this
    exact this

theorem Aux.type_subst_single (t : typ) :
    type_subst (alist_to_fmap ([ml!"'a"].zip [t])) (Tvar ml!"'a") = t := by
  simp [type_subst, Aux.FLOOKUP_alist_to_fmap, ALOOKUP]

theorem Aux.list_cases {tvs : Nat} {ctMap : ctMap_ty} {tenvS : tenv_store} {v : value} {t : typ}
    (h : type_v tvs ctMap tenvS v (Tlist t)) (hok : ctMap_ok ctMap)
    (hl : ctMap_has_lists ctMap) :
    v = Conv (some (TypeStamp ml!"[]" list_type_num)) [] ∨
    ∃ v1 v2, v = Conv (some (TypeStamp ml!"::" list_type_num)) [v1, v2] ∧
      type_v tvs ctMap tenvS v1 t ∧ type_v tvs ctMap tenvS v2 (Tlist t) := by
  obtain ⟨l1, l2, l3⟩ := hl
  rcases Aux.type_v_inv h with ⟨n, rfl, ht⟩ | ⟨n, rfl, ht⟩ | ⟨n, rfl, ht⟩ | ⟨n, rfl, ht⟩ |
    ⟨n, rfl, ht⟩ | ⟨n, rfl, ht⟩ | ⟨stamp, vs, tvs', ts', ts, ti, rfl, ht, hl, hlen, -, hr⟩ |
    ⟨vs, ts, rfl, ht, hr⟩ | ⟨env, n, e, t1, t2, rfl, ht⟩ | ⟨env, funs, n, t1, t2, rfl, ht⟩ |
    ⟨n, t1, rfl, ht, hl⟩ | ⟨n, rfl, ht, hl⟩ | ⟨n, t1, rfl, ht, hl⟩ | ⟨vs, t1, rfl, ht, hl⟩
  case inr.inr.inr.inr.inr.inr.inl =>
    simp only [Tlist, typ.Tapp.injEq] at ht
    obtain ⟨rfl, rfl⟩ := ht
    have hst := hok.2.2.2 _ _ _ _ _ _ _ ⟨hl, l1⟩
    cases stamp with
    | ExnStamp n => exact hst.elim
    | TypeStamp cn n =>
      have hn : n = list_type_num := hst
      subst hn
      by_cases h1 : cn = ml!"[]"
      · subst h1
        rw [l1] at hl
        cases hl
        cases vs with
        | nil => exact Or.inl rfl
        | cons _ _ => exact hr.elim
      · by_cases h2 : cn = ml!"::"
        · subst h2
          rw [l2] at hl
          cases hl
          obtain ⟨v1, vs1, rfl, ha, hr⟩ := Aux.LIST_REL_cons_right.mp hr
          obtain ⟨v2, vs2, rfl, hb, hr⟩ := Aux.LIST_REL_cons_right.mp hr
          rw [List.map_nil, Aux.LIST_REL_nil_right] at hr
          subst hr
          refine Or.inr ⟨v1, v2, rfl, ?_, ?_⟩
          · rwa [Aux.type_subst_single] at ha
          · simp only [Tlist, type_subst, List.map_cons, List.map_nil] at hb
            have e := Aux.type_subst_single t
            simp only [type_subst] at e
            rw [e] at hb
            exact hb
        · rw [l3 cn ⟨h2, h1⟩] at hl
          cases hl
  all_goals
    simp [Tlist, Tlist_num, Tint_num, Tchar_num, Tstring_num, Tword8_num, Tword64_num,
      Tdouble_num, Ttup_num, Tfn_num, Tref_num, Tword8array_num, Tarray_num, Tvector_num] at ht

/- HOL4:
Theorem has_lists_v_to_list[local]:
  !ctMap tvs tenvS t3.
    ctMap_ok ctMap ∧
    ctMap_has_lists ctMap ∧
    type_v tvs ctMap tenvS v (Tlist t3)
    ⇒
    ?vs. v_to_list v = SOME vs ∧
         EVERY (\v. type_v tvs ctMap tenvS v t3) vs ∧
         (t3 = Tchar ⇒ ?vs. v_to_char_list v = SOME vs) ∧
         (t3 = Tstring ⇒ ∃str. vs_to_string vs = SOME str) -/
theorem has_lists_v_to_list (v : value) :
    ∀ (ctMap : ctMap_ty) (tvs : Nat) (tenvS : tenv_store) (t3 : typ),
      ctMap_ok ctMap ∧
      ctMap_has_lists ctMap ∧
      type_v tvs ctMap tenvS v (Tlist t3)
      →
      ∃ vs, v_to_list v = some vs ∧
        EVERY (fun v => type_v tvs ctMap tenvS v t3) vs ∧
        (t3 = Tchar → ∃ vs, v_to_char_list v = some vs) ∧
        (t3 = Tstring → ∃ str, vs_to_string vs = some str) := by
  rintro ctMap tvs tenvS t3 ⟨hok, hl, h⟩
  have key : ∀ n (v : value), sizeOf v ≤ n → type_v tvs ctMap tenvS v (Tlist t3) →
      ∃ vs, v_to_list v = some vs ∧
        EVERY (fun v => type_v tvs ctMap tenvS v t3) vs ∧
        (t3 = Tchar → ∃ vs, v_to_char_list v = some vs) ∧
        (t3 = Tstring → ∃ str, vs_to_string vs = some str) := by
    intro n
    induction n with
    | zero =>
      intro v hs
      cases v <;> simp at hs
    | succ n ih =>
      intro v hs h
      rcases Aux.list_cases h hok hl with rfl | ⟨v1, v2, rfl, h1, h2⟩
      · refine ⟨[], ?_, trivial, fun _ => ⟨[], ?_⟩, fun _ => ⟨_, rfl⟩⟩
        · simp [v_to_list]
        · simp [v_to_char_list]
      · obtain ⟨vs, a1, a2, a3, a4⟩ := ih v2 (by simp at hs; omega) h2
        refine ⟨v1 :: vs, ?_, ⟨h1, a2⟩, ?_, ?_⟩
        · simp [v_to_list, a1]
        · rintro rfl
          obtain ⟨c, rfl⟩ := (prim_canonical_values_thm tvs ctMap tenvS v1 [] Tint Tint []
            Tint).2.1 ⟨h1, hok⟩
          obtain ⟨cs, hcs⟩ := a3 rfl
          exact ⟨c :: cs, by simp [v_to_char_list, hcs]⟩
        · rintro rfl
          obtain ⟨c, rfl⟩ := (prim_canonical_values_thm tvs ctMap tenvS v1 [] Tint Tint []
            Tint).2.2.1 ⟨h1, hok⟩
          obtain ⟨cs, hcs⟩ := a4 rfl
          exact ⟨strcat c cs, by simp [vs_to_string, hcs]⟩
  exact key _ v (Nat.le_refl _) h

theorem Aux.bool_cases {tvs : Nat} {ctMap : ctMap_ty} {tenvS : tenv_store} {v : value}
    (h : type_v tvs ctMap tenvS v Tbool) (hok : ctMap_ok ctMap)
    (hb : ctMap_has_bools ctMap) : ∃ b, v = Boolv b := by
  obtain ⟨l1, l2, l3⟩ := hb
  rcases Aux.type_v_inv h with ⟨n, rfl, ht⟩ | ⟨n, rfl, ht⟩ | ⟨n, rfl, ht⟩ | ⟨n, rfl, ht⟩ |
    ⟨n, rfl, ht⟩ | ⟨n, rfl, ht⟩ | ⟨stamp, vs, tvs', ts', ts, ti, rfl, ht, hl, hlen, -, hr⟩ |
    ⟨vs, ts, rfl, ht, hr⟩ | ⟨env, n, e, t1, t2, rfl, ht⟩ | ⟨env, funs, n, t1, t2, rfl, ht⟩ |
    ⟨n, t1, rfl, ht, hl⟩ | ⟨n, rfl, ht, hl⟩ | ⟨n, t1, rfl, ht, hl⟩ | ⟨vs, t1, rfl, ht, hl⟩
  case inr.inr.inr.inr.inr.inr.inl =>
    simp only [Tbool, typ.Tapp.injEq] at ht
    obtain ⟨rfl, rfl⟩ := ht
    have hst := hok.2.2.2 _ _ _ _ _ _ _ ⟨hl, l1⟩
    cases stamp with
    | ExnStamp n => exact hst.elim
    | TypeStamp cn n =>
      have hn : n = bool_type_num := hst
      subst hn
      by_cases h1 : cn = ml!"True"
      · subst h1
        rw [l1] at hl
        cases hl
        cases vs with
        | nil => exact ⟨true, rfl⟩
        | cons _ _ => exact hr.elim
      · by_cases h2 : cn = ml!"False"
        · subst h2
          rw [l2] at hl
          cases hl
          cases vs with
          | nil => exact ⟨false, by simp [Boolv]⟩
          | cons _ _ => exact hr.elim
        · rw [l3 cn ⟨h1, h2⟩] at hl
          cases hl
  all_goals
    simp [Tbool, Tbool_num, Tint_num, Tchar_num, Tstring_num, Tword8_num, Tword64_num,
      Tdouble_num, Ttup_num, Tfn_num, Tref_num, Tword8array_num, Tarray_num, Tvector_num] at ht

theorem Aux.ctor_cases {tvs : Nat} {ctMap : ctMap_ty} {tenvS : tenv_store} {v : value}
    {ts : List typ} {ti : type_ident} {stamp : CmlTS.stamp} {tvs' : List tvarN} {ts' : List typ}
    (h : type_v tvs ctMap tenvS v (Tapp ts ti)) (hok : ctMap_ok ctMap)
    (hs : FLOOKUP ctMap stamp = some (tvs', ts', ti)) :
    ∃ s2 vs tvs2 ts2, v = Conv (some s2) vs ∧ same_type stamp s2 ∧
      FLOOKUP ctMap s2 = some (tvs2, ts2, ti) ∧ tvs2.length = ts.length ∧
      LIST_REL (type_v tvs ctMap tenvS) vs
        (ts2.map (type_subst (alist_to_fmap (tvs2.zip ts)))) := by
  have hp : ¬ Aux.isPrim ti := fun hp => Aux.no_conv hok hs hp
  rcases Aux.type_v_inv h with ⟨n, rfl, ht⟩ | ⟨n, rfl, ht⟩ | ⟨n, rfl, ht⟩ | ⟨n, rfl, ht⟩ |
    ⟨n, rfl, ht⟩ | ⟨n, rfl, ht⟩ | ⟨stamp2, vs, tvs2, ts0, ts2, ti, rfl, ht, hl, hlen, -, hr⟩ |
    ⟨vs, ts, rfl, ht, hr⟩ | ⟨env, n, e, t1, t2, rfl, ht⟩ | ⟨env, funs, n, t1, t2, rfl, ht⟩ |
    ⟨n, t1, rfl, ht, hl⟩ | ⟨n, rfl, ht, hl⟩ | ⟨n, t1, rfl, ht, hl⟩ | ⟨vs, t1, rfl, ht, hl⟩
  case inr.inr.inr.inr.inr.inr.inl =>
    simp only [typ.Tapp.injEq] at ht
    obtain ⟨rfl, rfl⟩ := ht
    exact ⟨stamp2, vs, tvs2, ts2, rfl, hok.2.2.2 _ _ _ _ _ _ _ ⟨hs, hl⟩, hl, hlen, hr⟩
  all_goals
    simp only [typ.Tapp.injEq] at ht
    exact (hp (by simp [Aux.isPrim, ht.2])).elim

/- HOL4:
Theorem ctor_canonical_values_thm:
  (type_v tvs ctMap tenvS v Tbool ∧ ctMap_ok ctMap ∧ ctMap_has_bools ctMap ⇒
   (∃b. v = Boolv b)) /\
  (type_v tvs ctMap tenvS v (Tlist t) ∧ ctMap_ok ctMap ∧ ctMap_has_lists ctMap ⇒
   ?vs.
     v_to_list v = SOME vs ∧
     EVERY (\v. type_v tvs ctMap tenvS v t) vs ∧
     (t = Tchar ⇒ ?vs. v_to_char_list v = SOME vs) ∧
     (t = Tstring ⇒ ∃str. vs_to_string vs = SOME str)) ∧
  (type_v tvs ctMap tenvS v (Tapp ts ti) ∧
   ctMap_ok ctMap ∧
   FLOOKUP ctMap stamp = SOME (tvs',ts',ti) ⇒
   (?cn n vs. same_type stamp (TypeStamp cn n) ∧ v = Conv (SOME (TypeStamp cn n)) vs) ∨
   (?n vs. same_type stamp (ExnStamp n) ∧ v = Conv (SOME (ExnStamp n)) vs)) -/
theorem ctor_canonical_values_thm (tvs : Nat) (ctMap : ctMap_ty) (tenvS : tenv_store)
    (v : value) (t : typ) (ts : List typ) (ti : type_ident) (stamp : CmlTS.stamp)
    (tvs' : List tvarN) (ts' : List typ) :
    (type_v tvs ctMap tenvS v Tbool ∧ ctMap_ok ctMap ∧ ctMap_has_bools ctMap →
      (∃ b, v = Boolv b)) ∧
    (type_v tvs ctMap tenvS v (Tlist t) ∧ ctMap_ok ctMap ∧ ctMap_has_lists ctMap →
      ∃ vs,
        v_to_list v = some vs ∧
        EVERY (fun v => type_v tvs ctMap tenvS v t) vs ∧
        (t = Tchar → ∃ vs, v_to_char_list v = some vs) ∧
        (t = Tstring → ∃ str, vs_to_string vs = some str)) ∧
    (type_v tvs ctMap tenvS v (Tapp ts ti) ∧
      ctMap_ok ctMap ∧
      FLOOKUP ctMap stamp = some (tvs', ts', ti) →
      (∃ cn n vs, same_type stamp (TypeStamp cn n) ∧ v = Conv (some (TypeStamp cn n)) vs) ∨
      (∃ n vs, same_type stamp (ExnStamp n) ∧ v = Conv (some (ExnStamp n)) vs)) := by
  refine ⟨fun ⟨h, hok, hb⟩ => Aux.bool_cases h hok hb,
    fun ⟨h, hok, hl⟩ => has_lists_v_to_list v ctMap tvs tenvS t ⟨hok, hl, h⟩, ?_⟩
  rintro ⟨h, hok, hs⟩
  obtain ⟨s2, vs, tvs2, ts2, rfl, hst, -⟩ := Aux.ctor_cases h hok hs
  cases s2 with
  | TypeStamp cn n => exact Or.inl ⟨cn, n, vs, hst, rfl⟩
  | ExnStamp n => exact Or.inr ⟨n, vs, hst, rfl⟩

/- HOL4:
Theorem same_type_refl[local]:
  !t. same_type t t -/
theorem same_type_refl : ∀ t : stamp, same_type t t := by
  intro t
  cases t <;> simp [same_type]

/- HOL4:
Theorem eq_same_type[local]:
  (!v1 v2 tvs ctMap cns tenvS t.
     ctMap_ok ctMap ∧
     type_v tvs ctMap tenvS v1 t ∧
     type_v tvs ctMap tenvS v2 t
     ⇒
     do_eq v1 v2 ≠ Eq_type_error) ∧
  (!vs1 vs2 tvs ctMap cns tenvS ts.
     ctMap_ok ctMap ∧
     LIST_REL (type_v tvs ctMap tenvS) vs1 ts ∧
     LIST_REL (type_v tvs ctMap tenvS) vs2 ts
     ⇒
     do_eq_list vs1 vs2 ≠ Eq_type_error) -/
theorem eq_same_type {α β : Type} :
    (∀ (v1 v2 : value) (tvs : Nat) (ctMap : ctMap_ty) (_cns : α) (tenvS : tenv_store) (t : typ),
      ctMap_ok ctMap ∧
      type_v tvs ctMap tenvS v1 t ∧
      type_v tvs ctMap tenvS v2 t
      →
      do_eq v1 v2 ≠ Eq_type_error) ∧
    (∀ (vs1 vs2 : List value) (tvs : Nat) (ctMap : ctMap_ty) (_cns : β) (tenvS : tenv_store)
        (ts : List typ),
      ctMap_ok ctMap ∧
      LIST_REL (type_v tvs ctMap tenvS) vs1 ts ∧
      LIST_REL (type_v tvs ctMap tenvS) vs2 ts
      →
      do_eq_list vs1 vs2 ≠ Eq_type_error) := by
  have key : ∀ n,
      (∀ (v1 v2 : value) (tvs : Nat) (ctMap : ctMap_ty) (tenvS : tenv_store) (t : typ),
        sizeOf v1 ≤ n → ctMap_ok ctMap → type_v tvs ctMap tenvS v1 t →
        type_v tvs ctMap tenvS v2 t → do_eq v1 v2 ≠ Eq_type_error) ∧
      (∀ (vs1 vs2 : List value) (tvs : Nat) (ctMap : ctMap_ty) (tenvS : tenv_store)
          (ts : List typ), sizeOf vs1 ≤ n → ctMap_ok ctMap →
        LIST_REL (type_v tvs ctMap tenvS) vs1 ts → LIST_REL (type_v tvs ctMap tenvS) vs2 ts →
        do_eq_list vs1 vs2 ≠ Eq_type_error) := by
    intro n
    induction n with
    | zero =>
      refine ⟨fun v1 v2 tvs ctMap tenvS t hs => ?_, fun vs1 vs2 tvs ctMap tenvS ts hs => ?_⟩
      · cases v1 <;> simp at hs
      · cases vs1 <;> simp at hs
    | succ n ih =>
      obtain ⟨ih1, ih2⟩ := ih
      refine ⟨fun v1 v2 tvs ctMap tenvS t hs hok h1 h2 => ?_,
        fun vs1 vs2 tvs ctMap tenvS ts hs hok h1 h2 => ?_⟩
      · rcases Aux.type_v_inv h1 with ⟨n1, rfl, rfl⟩ | ⟨n1, rfl, rfl⟩ | ⟨n1, rfl, rfl⟩ |
          ⟨n1, rfl, rfl⟩ | ⟨n1, rfl, rfl⟩ | ⟨n1, rfl, rfl⟩ |
          ⟨stamp, vs1, tvs', ts', ts, ti, rfl, rfl, hl, hlen, -, hr⟩ |
          ⟨vs1, ts, rfl, rfl, hr⟩ | ⟨env, f, e, t1, t2, rfl, rfl⟩ |
          ⟨env, funs, f, t1, t2, rfl, rfl⟩ |
          ⟨n1, t1, rfl, rfl, hl⟩ | ⟨n1, rfl, rfl, hl⟩ | ⟨n1, t1, rfl, rfl, hl⟩ |
          ⟨vs1, t1, rfl, rfl, hl⟩
        case inr.inr.inr.inr.inr.inr.inl =>
          obtain ⟨s2, vs2, tvs2, ts2, rfl, hst, hl2, -, hr2⟩ := Aux.ctor_cases h2 hok hl
          rw [do_eq]
          split
          · rename_i hc
            obtain ⟨hc1, hc2⟩ := hc
            cases hc1
            rw [hl] at hl2
            cases hl2
            exact ih2 _ _ _ _ _ _ (by simp at hs; omega) hok hr hr2
          · have hst' : ctor_same_type (some stamp) (some s2) := hst
            rw [if_pos hst']
            simp
        all_goals
          have hc := Aux.canon h2 hok (by simp [Aux.isPrim])
          simp [Tint_num, Tchar_num, Tstring_num, Tword8_num, Tword64_num, Tdouble_num,
            Ttup_num, Tfn_num, Tref_num, Tword8array_num, Tarray_num, Tvector_num] at hc
        · obtain ⟨n2, rfl⟩ := hc; simp [do_eq, lit_same_type]
        · obtain ⟨n2, rfl⟩ := hc; simp [do_eq, lit_same_type]
        · obtain ⟨n2, rfl⟩ := hc; simp [do_eq, lit_same_type]
        · obtain ⟨n2, rfl⟩ := hc; simp [do_eq, lit_same_type]
        · obtain ⟨n2, rfl⟩ := hc; simp [do_eq, lit_same_type]
        · obtain ⟨n2, rfl⟩ := hc; simp [do_eq, lit_same_type]
        · obtain ⟨vs2, rfl, hr2⟩ := hc
          rw [do_eq, if_pos ⟨rfl, by rw [Aux.LIST_REL_length hr, Aux.LIST_REL_length hr2]⟩]
          exact ih2 _ _ _ _ _ _ (by simp at hs; omega) hok hr hr2
        · rcases hc with ⟨env2, f2, e2, rfl⟩ | ⟨env2, f2, e2, rfl⟩ <;> simp [do_eq]
        · rcases hc with ⟨env2, f2, e2, rfl⟩ | ⟨env2, f2, e2, rfl⟩ <;> simp [do_eq]
        · obtain ⟨n2, rfl, -⟩ := hc; simp [do_eq]
        · obtain ⟨n2, rfl, -⟩ := hc; simp [do_eq]
        · obtain ⟨n2, rfl, -⟩ := hc; simp [do_eq]
        · obtain ⟨vs2, rfl, hr2⟩ := hc
          rw [do_eq]
          split
          · rename_i hlen
            rw [EVERY_LIST_REL (fun x y => type_v tvs ctMap tenvS x y) t1 vs1] at hl
            rw [EVERY_LIST_REL (fun x y => type_v tvs ctMap tenvS x y) t1 vs2, ← hlen] at hr2
            exact ih2 _ _ _ _ _ _ (by simp at hs; omega) hok hl hr2
          · simp
      · cases vs1 with
        | nil =>
          rw [Aux.LIST_REL_nil_left] at h1
          subst h1
          rw [Aux.LIST_REL_nil_right] at h2
          subst h2
          simp [do_eq_list]
        | cons a vs1 =>
          obtain ⟨t, ts, rfl, ha, h1⟩ := Aux.LIST_REL_cons_left.mp h1
          obtain ⟨b, vs2, rfl, hb, h2⟩ := Aux.LIST_REL_cons_right.mp h2
          have e1 := ih1 a b tvs ctMap tenvS t (by simp at hs; omega) hok ha hb
          have e2 := ih2 vs1 vs2 tvs ctMap tenvS ts (by simp at hs; omega) hok h1 h2
          rw [do_eq_list]
          cases hq : do_eq a b with
          | Eq_type_error => exact absurd hq e1
          | Eq_val r =>
            dsimp only
            split
            · simp
            · exact e2
  exact ⟨fun v1 v2 tvs ctMap _ tenvS t ⟨a, b, c⟩ =>
      (key _).1 v1 v2 tvs ctMap tenvS t (Nat.le_refl _) a b c,
    fun vs1 vs2 tvs ctMap _ tenvS ts ⟨a, b, c⟩ =>
      (key _).2 vs1 vs2 tvs ctMap tenvS ts (Nat.le_refl _) a b c⟩

/- HOL4:
Theorem type_env_conv_thm[local]:
  ∀ctMap envC tenvC.
    nsAll2 (type_ctor ctMap) envC tenvC ⇒
    ∀cn tvs ts tn ti.
      (nsLookup tenvC cn = SOME (tvs,ts,ti) ⇒
       ?cn' stamp.
         nsLookup envC cn = SOME (LENGTH ts,stamp) ∧
         FLOOKUP ctMap stamp = SOME (tvs, ts, ti)) ∧
      (nsLookup tenvC cn = NONE ⇒ nsLookup envC cn = NONE)
(`tn` and `cn'` are unused and have polymorphic types; HOL4 types are nonempty, hence
`[Nonempty ε]` for the existentially quantified `cn'`) -/
theorem type_env_conv_thm {σ α β γ m n δ ε : Type} [Nonempty ε] :
    ∀ (ctMap : fmap σ (α × List β × γ)) (envC : Namespace m n (Nat × σ))
      (tenvC : Namespace m n (α × List β × γ)),
      nsAll2 (type_ctor ctMap) envC tenvC →
      ∀ (cn : ident m n) (tvs : α) (ts : List β) (_tn : δ) (ti : γ),
        (nsLookup tenvC cn = some (tvs, ts, ti) →
          ∃ (_cn' : ε) (stamp : σ),
            nsLookup envC cn = some (ts.length, stamp) ∧
            FLOOKUP ctMap stamp = some (tvs, ts, ti)) ∧
        (nsLookup tenvC cn = none → nsLookup envC cn = none) := by
  intro ctMap envC tenvC h cn tvs ts _ ti
  refine ⟨fun hl => ?_, (nsAll2_nsLookup_none _ _ _ _ h).mpr⟩
  obtain ⟨⟨n, stamp⟩, hv, h1, rfl⟩ := nsAll2_nsLookup2 _ _ _ _ _ ⟨hl, h⟩
  exact ⟨Classical.choice inferInstance, stamp, hv, h1⟩

/- HOL4:
Theorem type_funs_fst[local]:
  !tenv tenvE funs tenv'.
    type_funs tenv tenvE funs tenv'
    ⇒
    MAP FST funs = MAP FST tenv' -/
theorem type_funs_fst :
    ∀ (tenv : type_env) (tenvE : tenv_val_exp) (funs : List (varN × varN × exp))
      (tenv' : List (varN × typ)),
      type_funs tenv tenvE funs tenv'
      →
      funs.map Prod.fst = tenv'.map Prod.fst := fun _ _ _ _ h => Aux.type_funs_fst h

/- HOL4:
Theorem type_recfun_env_help[local]:
  ∀fn funs funs' ctMap tenv bindings tenvE env tenvS tvs bindings'.
    ALL_DISTINCT (MAP FST funs') ∧
    tenv_ok tenv ∧
    type_all_env ctMap tenvS env (tenv with v := add_tenvE tenvE tenv.v) ∧
    tenv_val_exp_ok tenvE ∧
    num_tvs tenvE = 0 ∧
    (!fn t. (ALOOKUP bindings fn = SOME t) ⇒ (ALOOKUP bindings' fn = SOME t)) ∧
    type_funs tenv (bind_var_list 0 bindings' (bind_tvar tvs tenvE)) funs' bindings' ∧
    type_funs tenv (bind_var_list 0 bindings' (bind_tvar tvs tenvE)) funs bindings
    ⇒
    LIST_REL (λ(x,y) (x',y'). x = x' ∧ (λ(tvs,t). type_v tvs ctMap tenvS y t) y')
             (MAP (λ(fn,n,e). (fn,Recclosure env funs' fn)) funs)
             (MAP (λ(x,t). (x,tvs,t)) bindings)
(the outer `fn` is unused and has a polymorphic type) -/
theorem type_recfun_env_help {α : Type} :
    ∀ (_fn : α) (funs funs' : List (varN × varN × exp)) (ctMap : ctMap_ty) (tenv : type_env)
      (bindings : List (varN × typ)) (tenvE : tenv_val_exp) (env : sem_env value)
      (tenvS : tenv_store) (tvs : Nat) (bindings' : List (varN × typ)),
      ALL_DISTINCT (funs'.map Prod.fst) ∧
      tenv_ok tenv ∧
      type_all_env ctMap tenvS env { tenv with v := add_tenvE tenvE tenv.v } ∧
      tenv_val_exp_ok tenvE ∧
      num_tvs tenvE = 0 ∧
      (∀ fn t, ALOOKUP bindings fn = some t → ALOOKUP bindings' fn = some t) ∧
      type_funs tenv (bind_var_list 0 bindings' (bind_tvar tvs tenvE)) funs' bindings' ∧
      type_funs tenv (bind_var_list 0 bindings' (bind_tvar tvs tenvE)) funs bindings
      →
      LIST_REL
        (fun ((x, y) : varN × value) ((x', y') : varN × Nat × typ) =>
          x = x' ∧ (fun ((tvs, t) : Nat × typ) => type_v tvs ctMap tenvS y t) y')
        (funs.map (fun (fn, _, _) => (fn, Recclosure env funs' fn)))
        (bindings.map (fun (x, t) => (x, tvs, t))) := by
  intro _ funs
  induction funs with
  | nil =>
    rintro funs' ctMap tenv bindings tenvE env tenvS tvs bindings' ⟨-, -, -, -, -, -, -, h⟩
    rw [Aux.type_funs_nil_inv h]
    trivial
  | cons f funs ih =>
    rintro funs' ctMap tenv bindings tenvE env tenvS tvs bindings'
      ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
    obtain ⟨fn, n, e⟩ := f
    obtain ⟨t1, t2, bs', rfl, a1, a2, a3, a4⟩ := Aux.type_funs_cons_inv h8
    have hfn : ALOOKUP bindings' fn = some (Tfn t1 t2) := h6 fn _ (by simp [ALOOKUP])
    refine ⟨⟨rfl, ?_⟩, ih funs' ctMap tenv bs' tenvE env tenvS tvs bindings'
      ⟨h1, h2, h3, h4, h5, fun g t hg => h6 g t ?_, h7, a3⟩⟩
    · refine type_v_recclosure_aux _ _ _ _ _ _ _ tenv tenvE bindings' h2 h4 h5 h3.1 h3.2 h7 hfn
        h1 ?_
      rw [Aux.type_funs_fst h7]
      exact List.mem_map.mpr ⟨_, Aux.ALOOKUP_mem hfn, rfl⟩
    · simp only [ALOOKUP]
      rw [if_neg]
      · exact hg
      · rintro rfl
        rw [a4] at hg
        cases hg

/- HOL4:
Theorem type_recfun_env[local]:
  ∀funs ctMap tenvS tvs tenv tenvE env bindings.
    tenv_ok tenv ∧
    type_all_env ctMap tenvS env (tenv with v := add_tenvE tenvE tenv.v) ∧
    tenv_val_exp_ok tenvE ∧
    num_tvs tenvE = 0 ∧
    type_funs tenv (bind_var_list 0 bindings (bind_tvar tvs tenvE)) funs bindings ∧
    ALL_DISTINCT (MAP FST funs)
    ⇒
    LIST_REL (λ(x,y) (x',y'). x = x' ∧ (λ(tvs,t). type_v tvs ctMap tenvS y t) y')
             (MAP (λ(fn,n,e). (fn,Recclosure env funs fn)) funs)
             (MAP (λ(x,t). (x,tvs,t)) bindings) -/
theorem type_recfun_env :
    ∀ (funs : List (varN × varN × exp)) (ctMap : ctMap_ty) (tenvS : tenv_store) (tvs : Nat)
      (tenv : type_env) (tenvE : tenv_val_exp) (env : sem_env value)
      (bindings : List (varN × typ)),
      tenv_ok tenv ∧
      type_all_env ctMap tenvS env { tenv with v := add_tenvE tenvE tenv.v } ∧
      tenv_val_exp_ok tenvE ∧
      num_tvs tenvE = 0 ∧
      type_funs tenv (bind_var_list 0 bindings (bind_tvar tvs tenvE)) funs bindings ∧
      ALL_DISTINCT (funs.map Prod.fst)
      →
      LIST_REL
        (fun ((x, y) : varN × value) ((x', y') : varN × Nat × typ) =>
          x = x' ∧ (fun ((tvs, t) : Nat × typ) => type_v tvs ctMap tenvS y t) y')
        (funs.map (fun (fn, _, _) => (fn, Recclosure env funs fn)))
        (bindings.map (fun (x, t) => (x, tvs, t))) :=
  fun funs ctMap tenvS tvs tenv tenvE env bindings ⟨h1, h2, h3, h4, h5, h6⟩ =>
    type_recfun_env_help () funs funs ctMap tenv bindings tenvE env tenvS tvs bindings
      ⟨h6, h1, h2, h3, h4, fun _ _ h => h, h5, h5⟩

/- HOL4:
val type_v_exn = SIMP_RULE (srw_ss()) [] (Q.prove (
  `!tvs cenv senv.
    ctMap_has_exns cenv ⇒
  type_v tvs cenv senv (Conv (SOME chr_stamp) []) Texn ∧
  type_v tvs cenv senv (Conv (SOME subscript_stamp) []) Texn ∧
  type_v tvs cenv senv (Conv (SOME bind_stamp) []) Texn ∧
  type_v tvs cenv senv (Conv (SOME div_stamp) []) Texn`, ...
(stated as in the `Q.prove`; `SIMP_RULE` gives a logically equivalent formula) -/
theorem type_v_exn :
    ∀ (tvs : Nat) (cenv : ctMap_ty) (senv : tenv_store),
      ctMap_has_exns cenv →
      type_v tvs cenv senv (Conv (some chr_stamp) []) Texn ∧
      type_v tvs cenv senv (Conv (some subscript_stamp) []) Texn ∧
      type_v tvs cenv senv (Conv (some bind_stamp) []) Texn ∧
      type_v tvs cenv senv (Conv (some div_stamp) []) Texn := by
  rintro tvs cenv senv ⟨h1, h2, h3, h4⟩
  have key : ∀ stamp, FLOOKUP cenv stamp = some ([], [], Texn_num) →
      type_v tvs cenv senv (Conv (some stamp) []) Texn :=
    fun stamp h => type_v_conv_aux _ _ _ _ [] stamp [] [] _ trivial rfl trivial h
  exact ⟨key _ h2, key _ h4, key _ h1, key _ h3⟩

theorem Aux.type_v_unit (tvs : Nat) (ctMap : ctMap_ty) (tenvS : tenv_store) :
    type_v tvs ctMap tenvS (Conv none []) (Ttup []) := type_v_tup_aux _ _ _ _ _ trivial

/- HOL4:
Theorem type_v_Boolv[local]:
  ctMap_has_bools ctMap ⇒ type_v tvs ctMap tenvS (Boolv b) Tbool -/
theorem type_v_Boolv (ctMap : ctMap_ty) (tvs : Nat) (tenvS : tenv_store) (b : Bool) :
    ctMap_has_bools ctMap → type_v tvs ctMap tenvS (Boolv b) Tbool := by
  rintro ⟨h1, h2, -⟩
  have key : ∀ stamp, FLOOKUP ctMap stamp = some ([], [], Tbool_num) →
      type_v tvs ctMap tenvS (Conv (some stamp) []) Tbool :=
    fun stamp h => type_v_conv_aux _ _ _ _ [] stamp [] [] _ trivial rfl trivial h
  cases b
  · simp only [Boolv, Bool.false_eq_true, if_false]; exact key _ h2
  · simp only [Boolv, if_true]; exact key _ h1

/- HOL4:
Theorem remove_lambda_prod[local]:
  (\ (x,y). P x y) = (\xy. P (FST xy) (SND xy)) -/
theorem remove_lambda_prod {α β γ : Type} (P : α → β → γ) :
    (fun ((x, y) : α × β) => P x y) = (fun xy => P xy.1 xy.2) := rfl

theorem Aux.add_tenvE_empty {m : Type} (tenvV : Namespace m varN (Nat × typ)) :
    add_tenvE tenv_val_exp.Empty tenvV = tenvV := rfl

/-- Extending a typed environment by a list of typed recursive functions. -/
theorem Aux.type_rec_env {funs : List (varN × varN × exp)} {ctMap : ctMap_ty}
    {tenvS : tenv_store} {tvs : Nat} {tenv : type_env} {tenvE : tenv_val_exp}
    {env : sem_env value} {bindings : List (varN × typ)} {envV : env_val} {tenvV : tenv_val}
    (h1 : tenv_ok tenv)
    (h2 : type_all_env ctMap tenvS env { tenv with v := add_tenvE tenvE tenv.v })
    (h3 : tenv_val_exp_ok tenvE) (h4 : num_tvs tenvE = 0)
    (h5 : type_funs tenv (bind_var_list 0 bindings (bind_tvar tvs tenvE)) funs bindings)
    (h7 : nsAll2 (fun _ v (p : Nat × typ) => type_v p.1 ctMap tenvS v p.2) envV tenvV) :
    nsAll2 (fun _ v (p : Nat × typ) => type_v p.1 ctMap tenvS v p.2)
      (build_rec_env funs env envV)
      (nsBindList (bindings.map (fun (x, t) => (x, (tvs, t)))) tenvV) := by
  rw [build_rec_env_merge funs () env envV, nsAppend_to_nsBindList]
  refine nsAll2_nsBindList _ _ _ _ _ ⟨?_, h7⟩
  have hd : ALL_DISTINCT (funs.map Prod.fst) := type_funs_distinct _ _ _ _ h5
  refine Aux.LIST_REL_mono ?_
    (type_recfun_env funs ctMap tenvS tvs tenv tenvE env bindings ⟨h1, h2, h3, h4, h5, hd⟩)
  rintro ⟨x, y⟩ ⟨x', k, t⟩ - - h
  exact h

/- HOL4:
Theorem opapp_type_sound:
  !ctMap tenvS vs ts t.
    ctMap_ok ctMap ∧
    type_op Opapp ts t ∧
    LIST_REL (type_v 0 ctMap tenvS) vs ts
    ⇒
    ?env e tenv tenvE.
      tenv_ok tenv ∧
      tenv_val_exp_ok tenvE ∧
      num_tvs tenvE = 0 ∧
      type_all_env ctMap tenvS env (tenv with v := add_tenvE tenvE tenv.v) ∧
      type_e tenv tenvE e t ∧
      do_opapp vs = SOME (env,e) -/
theorem opapp_type_sound :
    ∀ (ctMap : ctMap_ty) (tenvS : tenv_store) (vs : List value) (ts : List typ) (t : typ),
      ctMap_ok ctMap ∧
      type_op Opapp ts t ∧
      LIST_REL (type_v 0 ctMap tenvS) vs ts
      →
      ∃ (env : sem_env value) (e : exp) (tenv : type_env) (tenvE : tenv_val_exp),
        tenv_ok tenv ∧
        tenv_val_exp_ok tenvE ∧
        num_tvs tenvE = 0 ∧
        type_all_env ctMap tenvS env { tenv with v := add_tenvE tenvE tenv.v } ∧
        type_e tenv tenvE e t ∧
        do_opapp vs = some (env, e) := by
  rintro ctMap tenvS vs ts t ⟨hok, ho, hr⟩
  rw [type_op_cases] at ho
  simp only [reduceCtorEq, false_and, exists_false, or_false, true_and] at ho
  obtain ⟨t1, t2, rfl, rfl⟩ := ho
  obtain ⟨f, vs1, rfl, hf, hr⟩ := Aux.LIST_REL_cons_right.mp hr
  obtain ⟨x, vs2, rfl, hx, hr⟩ := Aux.LIST_REL_cons_right.mp hr
  rw [Aux.LIST_REL_nil_right] at hr
  subst hr
  have hx0 : check_freevars 0 [] t2 := type_v_freevars _ _ _ _ _ hx
  rcases (prim_canonical_values_thm 0 ctMap tenvS f [] t2 t [] t).2.2.2.2.2.2.2.1 ⟨hf, hok⟩ with
    ⟨env, n, e, rfl⟩ | ⟨env, funs, n, rfl⟩
  · obtain ⟨tenv, tenvE, t1', t2', ht, a1, a2, a3, a4, a5, a6, a7⟩ :=
      type_v_closure_inv_aux _ _ _ _ _ _ _ hf
    simp only [Tfn, typ.Tapp.injEq, List.cons.injEq, and_true] at ht
    obtain ⟨rfl, rfl⟩ := ht
    rw [bind_tvar0] at a7
    refine ⟨{ env with v := nsBind n x env.v }, e, tenv, Bind_name n 0 t2 tenvE, a1, ⟨?_, a2⟩, a3,
      ⟨a4, nsAll2_nsBind _ _ _ _ _ _ ⟨hx, a5⟩⟩, a7, rfl⟩
    rw [a3]; exact hx0
  · obtain ⟨tenv, tenvE, bindings, a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ :=
      type_v_recclosure_inv_aux _ _ _ _ _ _ _ hf
    obtain ⟨y, e, hfr⟩ := type_funs_find_recfun n () funs bindings () _ _ _ ⟨a7, a6⟩
    obtain ⟨he, -⟩ := type_recfun_lookup n funs y e _ _ _ () _ _ ⟨hfr, a6, a7⟩
    have hok2 := tenv_val_exp_ok_bvl_funs _ _ _ _ () _ ⟨a6, (Aux.ok_bind_tvar 0 tenvE).mpr a2⟩
    have hrec := Aux.type_rec_env (envV := env.v) (tenvV := add_tenvE tenvE tenv.v) a1 ⟨a4, a5⟩
      a2 a3 a6 (nsAll2_mono (fun i v p h => h) a5)
    rw [bind_tvar0] at he hok2
    refine ⟨{ env with v := nsBind y x (build_rec_env funs env env.v) }, e, tenv,
      Bind_name y 0 t2 (bind_var_list 0 bindings tenvE), a1, ⟨?_, hok2⟩, ?_, ⟨a4, ?_⟩, he, ?_⟩
    · rw [num_tvs_bind_var_list, a3]; exact hx0
    · simp only [num_tvs, num_tvs_bind_var_list, a3]
    · simp only [add_tenvE, add_tenvE_bvl]
      exact nsAll2_nsBind _ _ _ _ _ _ ⟨hx, nsAll2_mono (fun i v p h => h) hrec⟩
    · have hd : ALL_DISTINCT (funs.map (fun (f, _, _) => f)) := a8
      simp only [do_opapp]
      rw [if_pos hd, hfr]

/- HOL4:
Theorem store_type_extension_weakS:
  !tenvS1 tenvS2.
    store_type_extension tenvS1 tenvS2 ⇒ weakS tenvS2 tenvS1 -/
theorem store_type_extension_weakS {α β : Type} :
    ∀ tenvS1 tenvS2 : fmap α β,
      store_type_extension tenvS1 tenvS2 → weakS tenvS2 tenvS1 := by
  rintro s1 s2 ⟨s', rfl, h⟩
  rw [Aux.weakS_iff]
  intro x y hx
  rw [Aux.FLOOKUP_FUNION]
  rcases h x with h | h
  · rw [h]; exact hx
  · rw [h] at hx; cases hx

/- HOL4:
Theorem store_type_extension_refl:
  !tenvS. store_type_extension tenvS tenvS -/
theorem store_type_extension_refl {α β : Type} :
    ∀ tenvS : fmap α β, store_type_extension tenvS tenvS := by
  intro s
  refine ⟨FEMPTY, ?_, fun l => Or.inl rfl⟩
  apply Aux.fmap_ext
  intro x
  rw [Aux.FLOOKUP_FUNION, Aux.FLOOKUP_FEMPTY]

/- HOL4:
Theorem store_type_extension_trans:
  !s1 s2 s3.
    store_type_extension s1 s2 ∧ store_type_extension s2 s3 ⇒
    store_type_extension s1 s3 -/
theorem store_type_extension_trans {α β : Type} :
    ∀ s1 s2 s3 : fmap α β,
      store_type_extension s1 s2 ∧ store_type_extension s2 s3 →
      store_type_extension s1 s3 := by
  rintro s1 s2 s3 ⟨⟨a, rfl, ha⟩, ⟨b, rfl, hb⟩⟩
  refine ⟨FUNION b a, ?_, fun l => ?_⟩
  · apply Aux.fmap_ext
    intro x
    rw [Aux.FLOOKUP_FUNION, Aux.FLOOKUP_FUNION, Aux.FLOOKUP_FUNION, Aux.FLOOKUP_FUNION]
    cases FLOOKUP b x <;> rfl
  · have h1 := ha l
    have h2 := hb l
    rw [Aux.FLOOKUP_FUNION] at h2 ⊢
    rcases h1 with h1 | h1
    · rw [h1] at h2 ⊢
      rcases h2 with h2 | h2
      · rw [h2]; exact Or.inl rfl
      · exact Or.inr h2
    · exact Or.inr h1

/- HOL4:
Theorem store_assign_type_sound:
  !ctMap tenvS store sv st l.
    type_s ctMap store tenvS ∧
    FLOOKUP tenvS l = SOME st ∧
    type_sv ctMap tenvS sv st
    ⇒
    ?store'.
      store_assign l sv store = SOME store' ∧
      type_s ctMap store' tenvS -/
theorem store_assign_type_sound :
    ∀ (ctMap : ctMap_ty) (tenvS : tenv_store) (store : List (store_v value))
      (sv : store_v value) (st : store_t) (l : Nat),
      type_s ctMap store tenvS ∧
      FLOOKUP tenvS l = some st ∧
      type_sv ctMap tenvS sv st
      →
      ∃ store',
        store_assign l sv store = some store' ∧
        type_s ctMap store' tenvS := by
  rintro ctMap tenvS store sv st l ⟨hs, hl, ht⟩
  obtain ⟨sv0, h0, ht0⟩ := Aux.type_s_lookup hs hl
  have hlt : l < store.length := by
    rw [Aux.store_lookup_eq] at h0
    exact (List.getElem?_eq_some_iff.mp h0).1
  have hEL : EL l store = sv0 := by
    rw [Aux.store_lookup_eq, Aux.EL_getElem? _ _ hlt] at h0
    exact Option.some.inj h0
  have hsame : store_v_same_type sv0 sv := by
    cases st <;> cases sv0 <;> simp only [type_sv] at ht0 <;> cases sv <;>
      simp only [type_sv] at ht <;> simp [store_v_same_type]
  refine ⟨LUPDATE sv l store, by unfold store_assign; rw [if_pos ⟨hlt, by rw [hEL]; exact hsame⟩],
    fun k => ?_⟩
  rw [Aux.LUPDATE_eq, Aux.store_lookup_eq, List.getElem?_set]
  by_cases hk : l = k
  · subst hk
    rw [if_pos rfl, if_pos hlt]
    refine ⟨⟨fun _ => ⟨sv, rfl⟩, fun _ => ⟨st, hl⟩⟩, ?_⟩
    rintro st' sv' ⟨h1, h2⟩
    cases h2
    rw [hl] at h1
    cases h1
    exact ht
  · rw [if_neg hk, ← Aux.store_lookup_eq]
    exact hs k

/- HOL4:
Theorem store_alloc_type_sound:
  !ctMap tenvS store sv st.
    ctMap_ok ctMap ∧
    type_s ctMap store tenvS ∧
    type_sv ctMap tenvS sv st
    ⇒
    ?store' tenvS' n.
      store_type_extension tenvS tenvS' ∧
      store_alloc sv store = (store', n) ∧
      type_s ctMap store' tenvS' ∧
      FLOOKUP tenvS' n = SOME st -/
theorem store_alloc_type_sound :
    ∀ (ctMap : ctMap_ty) (tenvS : tenv_store) (store : List (store_v value))
      (sv : store_v value) (st : store_t),
      ctMap_ok ctMap ∧
      type_s ctMap store tenvS ∧
      type_sv ctMap tenvS sv st
      →
      ∃ (store' : List (store_v value)) (tenvS' : tenv_store) (n : Nat),
        store_type_extension tenvS tenvS' ∧
        store_alloc sv store = (store', n) ∧
        type_s ctMap store' tenvS' ∧
        FLOOKUP tenvS' n = some st := by
  rintro ctMap tenvS store sv st ⟨hok, hs, ht⟩
  have hnone : FLOOKUP tenvS store.length = none := by
    cases h : FLOOKUP tenvS store.length with
    | none => rfl
    | some st' =>
      obtain ⟨sv', h1⟩ := (hs store.length).1.mp ⟨st', h⟩
      rw [Aux.store_lookup_eq, List.getElem?_eq_none (Nat.le_refl _)] at h1
      cases h1
  have hl : ∀ k, FLOOKUP (FUNION (FUPDATE FEMPTY (store.length, st)) tenvS) k =
      if k = store.length then some st else FLOOKUP tenvS k := by
    intro k
    rw [Aux.FLOOKUP_FUNION, Aux.FLOOKUP_FUPDATE]
    by_cases hk : k = store.length
    · rw [if_pos hk, if_pos hk]
    · rw [if_neg hk, if_neg hk]; rfl
  have hext : store_type_extension tenvS (FUNION (FUPDATE FEMPTY (store.length, st)) tenvS) := by
    refine ⟨_, rfl, fun k => ?_⟩
    rw [Aux.FLOOKUP_FUPDATE]
    by_cases hk : k = store.length
    · subst hk; exact Or.inr hnone
    · rw [if_neg hk]; exact Or.inl rfl
  have hw := store_type_extension_weakS _ _ hext
  refine ⟨_, _, _, hext, rfl, fun k => ?_, by rw [hl, if_pos rfl]⟩
  rw [hl, Aux.store_lookup_eq]
  by_cases hk : k = store.length
  · subst hk
    rw [if_pos rfl, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
    refine ⟨⟨fun _ => ⟨sv, rfl⟩, fun _ => ⟨st, rfl⟩⟩, ?_⟩
    rintro st' sv' ⟨h1, h2⟩
    cases h1
    cases h2
    exact type_sv_weakening _ _ _ _ _ _ ⟨ht, weakCT_refl _, hw⟩
  · rw [if_neg hk]
    by_cases hk2 : k < store.length
    · rw [List.getElem?_append_left hk2, ← Aux.store_lookup_eq]
      refine ⟨(hs k).1, fun st' sv' h => ?_⟩
      exact type_sv_weakening _ _ _ _ _ _ ⟨(hs k).2 st' sv' h, weakCT_refl _, hw⟩
    · have e1 : (store ++ [sv])[k]? = none := List.getElem?_eq_none (by simp; omega)
      have e2 : store_lookup k store = none := by
        rw [Aux.store_lookup_eq]; exact List.getElem?_eq_none (by omega)
      rw [e1, ← e2]
      exact ⟨(hs k).1, fun st' sv' h =>
        type_sv_weakening _ _ _ _ _ _ ⟨(hs k).2 st' sv' h, weakCT_refl _, hw⟩⟩

theorem Aux.v_to_list_eq : ∀ (n : Nat) (x : value) (xs : List value), sizeOf x ≤ n →
    v_to_list x = some xs → list_to_v xs = x := by
  intro n
  induction n with
  | zero => intro x xs hs; cases x <;> simp at hs
  | succ n ih =>
    intro x xs hs h
    rw [v_to_list.eq_def] at h
    split at h
    · split at h
      · rename_i hst
        cases h
        rw [hst]
        rfl
      · cases h
    · split at h
      · rename_i hst
        split at h
        · cases h
        · rename_i ys hys
          cases h
          have := ih _ _ (by simp at hs; omega) hys
          rw [hst]
          simp only [list_to_v, this]
      · cases h
    · cases h

theorem Aux.type_v_nil {tvs : Nat} {ctMap : ctMap_ty} {tenvS : tenv_store} {t : typ}
    (hl : ctMap_has_lists ctMap) (hc : check_freevars tvs [] t) :
    type_v tvs ctMap tenvS (Conv (some (TypeStamp ml!"[]" list_type_num)) []) (Tlist t) :=
  type_v_conv_aux _ _ _ _ [ml!"'a"] _ [t] [] _ ⟨hc, trivial⟩ rfl trivial hl.1

theorem Aux.type_v_cons {tvs : Nat} {ctMap : ctMap_ty} {tenvS : tenv_store} {t : typ}
    {v1 v2 : value} (hl : ctMap_has_lists ctMap) (h1 : type_v tvs ctMap tenvS v1 t)
    (h2 : type_v tvs ctMap tenvS v2 (Tlist t)) :
    type_v tvs ctMap tenvS (Conv (some (TypeStamp ml!"::" list_type_num)) [v1, v2])
      (Tlist t) := by
  refine type_v_conv_aux _ _ _ _ [ml!"'a"] _ [t] _ _
    ⟨type_v_freevars _ _ _ _ _ h1, trivial⟩ rfl ?_ hl.2.1
  rw [Aux.FUPDATE_LIST_reverse]
  refine ⟨?_, ?_, trivial⟩
  · rw [Aux.type_subst_single]; exact h1
  · have e := Aux.type_subst_single t
    simp only [type_subst] at e
    simp only [Tlist, type_subst, List.map_cons, List.map_nil]
    rw [e]
    exact h2

theorem Aux.type_v_list {tvs : Nat} {ctMap : ctMap_ty} {tenvS : tenv_store} {t : typ}
    {vs : List value} (hl : ctMap_has_lists ctMap) (hc : check_freevars tvs [] t)
    (h : EVERY (fun v => type_v tvs ctMap tenvS v t) vs) :
    type_v tvs ctMap tenvS (list_to_v vs) (Tlist t) := by
  induction vs with
  | nil => exact Aux.type_v_nil hl hc
  | cons a vs ih => exact Aux.type_v_cons hl h.1 (ih h.2)

theorem Aux.list_to_v_inv {tvs : Nat} {ctMap : ctMap_ty} {tenvS : tenv_store} {t : typ}
    {vs : List value} (hl : ctMap_has_lists ctMap)
    (h : type_v tvs ctMap tenvS (list_to_v vs) (Tlist t)) :
    EVERY (fun v => type_v tvs ctMap tenvS v t) vs := by
  induction vs with
  | nil => trivial
  | cons a vs ih =>
    simp only [list_to_v] at h
    obtain ⟨tvs', ts', ts, ti, ht, h1, h2, h3, h4⟩ := type_v_conv_inv_aux _ _ _ _ _ _ h
    simp only [Tlist, typ.Tapp.injEq] at ht
    obtain ⟨rfl, rfl⟩ := ht
    rw [hl.2.1] at h4
    cases h4
    rw [Aux.FUPDATE_LIST_reverse] at h3
    obtain ⟨ha, hb, -⟩ := h3
    rw [Aux.type_subst_single] at ha
    refine ⟨ha, ih ?_⟩
    have e := Aux.type_subst_single t
    simp only [type_subst] at e
    simp only [Tlist, type_subst, List.map_cons, List.map_nil] at hb
    rw [e] at hb
    exact hb

/- HOL4:
Theorem type_v_list_to_v:
  !x xs t.
    type_v n ctMap tenvS x t /\
    v_to_list x = SOME xs ==>
    type_v n ctMap tenvS (list_to_v xs) t -/
theorem type_v_list_to_v (n : Nat) (ctMap : ctMap_ty) (tenvS : tenv_store) :
    ∀ (x : value) (xs : List value) (t : typ),
      type_v n ctMap tenvS x t ∧
      v_to_list x = some xs →
      type_v n ctMap tenvS (list_to_v xs) t := by
  rintro x xs t ⟨h1, h2⟩
  rw [Aux.v_to_list_eq _ x xs (Nat.le_refl _) h2]
  exact h1

/- HOL4:
Theorem type_v_list_to_v_APPEND:
  !xs ys t.
    ctMap_has_lists ctMap /\
    type_v 0 ctMap tenvS (list_to_v xs) (Tapp [t] Tlist_num) /\
    type_v 0 ctMap tenvS (list_to_v ys) (Tapp [t] Tlist_num)
    ==>
    type_v 0 ctMap tenvS (list_to_v (xs ++ ys)) (Tapp [t] Tlist_num) -/
theorem type_v_list_to_v_APPEND (ctMap : ctMap_ty) (tenvS : tenv_store) :
    ∀ (xs ys : List value) (t : typ),
      ctMap_has_lists ctMap ∧
      type_v 0 ctMap tenvS (list_to_v xs) (Tapp [t] Tlist_num) ∧
      type_v 0 ctMap tenvS (list_to_v ys) (Tapp [t] Tlist_num)
      →
      type_v 0 ctMap tenvS (list_to_v (xs ++ ys)) (Tapp [t] Tlist_num) := by
  rintro xs ys t ⟨hl, h1, h2⟩
  have hc : check_freevars 0 [] t := by
    have := type_v_freevars _ _ _ _ _ h1
    simp only [check_freevars, EVERY] at this
    exact this.1
  exact Aux.type_v_list hl hc
    (Aux.EVERY_append.mpr ⟨Aux.list_to_v_inv hl h1, Aux.list_to_v_inv hl h2⟩)

/- HOL4:
Theorem do_eq_Boolv:
  do_eq (Boolv b) (Boolv b') = Eq_val (b = b') -/
theorem do_eq_Boolv (b b' : Bool) :
    do_eq (Boolv b) (Boolv b') = Eq_val (decide (b = b')) := by
  cases b <;> cases b' <;> simp [Boolv, do_eq, do_eq_list, ctor_same_type, same_type]

/- HOL4:
Theorem prim_canonical_Boolv_thm:
  (type_v tvs ctMap tenvS v Tbool ∧ ctMap_ok ctMap ∧ ctMap_has_bools ctMap ⇒
  (∃b. v = Boolv b)) -/
theorem prim_canonical_Boolv_thm (tvs : Nat) (ctMap : ctMap_ty) (tenvS : tenv_store)
    (v : value) :
    type_v tvs ctMap tenvS v Tbool ∧ ctMap_ok ctMap ∧ ctMap_has_bools ctMap →
    (∃ b, v = Boolv b) := fun ⟨h1, h2, h3⟩ => Aux.bool_cases h1 h2 h3

/- HOL4:
Theorem prim_canonical_Boolv_cases[local]:
  type_v tvs ctMap tenvS v (Tapp [] Tbool_num) ∧
  ctMap_ok ctMap ∧
  ctMap_has_bools ctMap ⇒
  v = Boolv T ∨ v = Boolv F -/
theorem prim_canonical_Boolv_cases (tvs : Nat) (ctMap : ctMap_ty) (tenvS : tenv_store)
    (v : value) :
    type_v tvs ctMap tenvS v (Tapp [] Tbool_num) ∧
    ctMap_ok ctMap ∧
    ctMap_has_bools ctMap →
    v = Boolv true ∨ v = Boolv false := by
  rintro ⟨h1, h2, h3⟩
  obtain ⟨b, rfl⟩ := Aux.bool_cases h1 h2 h3
  cases b
  · exact Or.inr rfl
  · exact Or.inl rfl

theorem Aux.check_type_of {ctMap : ctMap_ty} {tenvS : tenv_store} {v : value} {ty : prim_type}
    (hok : ctMap_ok ctMap) (hb : ctMap_has_bools ctMap)
    (h : type_v 0 ctMap tenvS v (t_of ty)) : check_type ty v := by
  have pc := prim_canonical_values_thm 0 ctMap tenvS v [] Tint Tint [] Tint
  cases ty with
  | BoolT =>
    rcases prim_canonical_Boolv_cases 0 ctMap tenvS v ⟨h, hok, hb⟩ with h | h
    · exact Or.inl h
    · exact Or.inr h
  | IntT => exact pc.1 ⟨h, hok⟩
  | CharT => exact pc.2.1 ⟨h, hok⟩
  | StrT => exact pc.2.2.1 ⟨h, hok⟩
  | WordT sz =>
    cases sz with
    | W8 => exact pc.2.2.2.1 ⟨h, hok⟩
    | W64 => exact pc.2.2.2.2.1 ⟨h, hok⟩
  | Float64T => exact pc.2.2.2.2.2.1 ⟨h, hok⟩

theorem Aux.type_of_check {ctMap : ctMap_ty} {tenvS : tenv_store} {v : value} {ty : prim_type}
    (hb : ctMap_has_bools ctMap) (h : check_type ty v) : type_v 0 ctMap tenvS v (t_of ty) := by
  cases ty with
  | BoolT => rcases h with rfl | rfl <;> exact type_v_Boolv _ _ _ _ hb
  | IntT => obtain ⟨n, rfl⟩ := h; exact type_v.intLit _ _ _ _
  | CharT => obtain ⟨n, rfl⟩ := h; exact type_v.char _ _ _ _
  | StrT => obtain ⟨n, rfl⟩ := h; exact type_v.strLit _ _ _ _
  | WordT sz =>
    cases sz with
    | W8 => obtain ⟨n, rfl⟩ := h; exact type_v.word8 _ _ _ _
    | W64 => obtain ⟨n, rfl⟩ := h; exact type_v.word64 _ _ _ _
  | Float64T => obtain ⟨n, rfl⟩ := h; exact type_v.float64 _ _ _ _

theorem Aux.len1 {α : Type} {l : List α} (h : l.length = 1) : ∃ x, l = [x] := (sing_list l).mp h

theorem Aux.len2 {α : Type} {l : List α} (h : l.length = 2) : ∃ x y, l = [x, y] := by
  match l, h with
  | [x, y], _ => exact ⟨x, y, rfl⟩

theorem Aux.len3 {α : Type} {l : List α} (h : l.length = 3) : ∃ x y z, l = [x, y, z] := by
  match l, h with
  | [x, y, z], _ => exact ⟨x, y, z, rfl⟩

theorem Aux.do_arith_ok {a : arith} {ty : prim_type} {vs : List value}
    (h : supported_arith a ty = some vs.length) :
    (∃ v, do_arith a ty vs = some (Sum.inr v) ∧ check_type ty v) ∨
      do_arith a ty vs = some (Sum.inl div_exn_v) := by
  have hbool : ∀ b, check_type BoolT (Boolv b) := by
    intro b; cases b
    · exact Or.inr rfl
    · exact Or.inl rfl
  cases ty with
  | BoolT =>
    cases a <;> simp [supported_arith] at h
    obtain ⟨x, rfl⟩ := Aux.len1 h.symm
    exact Or.inl ⟨_, rfl, hbool _⟩
  | IntT =>
    cases a <;> simp [supported_arith] at h
    all_goals obtain ⟨x, y, rfl⟩ := Aux.len2 h.symm
    · exact Or.inl ⟨_, rfl, _, rfl⟩
    · exact Or.inl ⟨_, rfl, _, rfl⟩
    · exact Or.inl ⟨_, rfl, _, rfl⟩
    · by_cases h0 : the_Litv_IntLit y = 0
      · exact Or.inr (by simp [do_arith, h0])
      · exact Or.inl ⟨Litv (lit.IntLit (int_div (the_Litv_IntLit x) (the_Litv_IntLit y))),
          by simp only [do_arith, List.map_cons, List.map_nil, if_neg h0], _, rfl⟩
    · by_cases h0 : the_Litv_IntLit y = 0
      · exact Or.inr (by simp [do_arith, h0])
      · exact Or.inl ⟨Litv (lit.IntLit (int_mod (the_Litv_IntLit x) (the_Litv_IntLit y))),
          by simp only [do_arith, List.map_cons, List.map_nil, if_neg h0], _, rfl⟩
  | CharT => simp [supported_arith] at h
  | StrT => simp [supported_arith] at h
  | WordT sz =>
    cases sz <;> cases a <;> simp [supported_arith] at h
    all_goals obtain ⟨x, y, rfl⟩ := Aux.len2 h.symm
    all_goals exact Or.inl ⟨_, rfl, _, rfl⟩
  | Float64T =>
    cases a <;> simp [supported_arith] at h
    all_goals first
      | (obtain ⟨x, rfl⟩ := Aux.len1 h.symm; exact Or.inl ⟨_, rfl, _, rfl⟩)
      | (obtain ⟨x, y, rfl⟩ := Aux.len2 h.symm; exact Or.inl ⟨_, rfl, _, rfl⟩)
      | (obtain ⟨x, y, z, rfl⟩ := Aux.len3 h.symm; exact Or.inl ⟨_, rfl, _, rfl⟩)

theorem Aux.do_conv_ok {ty1 ty2 : prim_type} {v : value} (h : supported_conversion ty1 ty2) :
    (∃ v', do_conversion v ty1 ty2 = some (Sum.inr v') ∧ check_type ty2 v') ∨
      do_conversion v ty1 ty2 = some (Sum.inl chr_exn_v) := by
  unfold supported_conversion at h
  split at h
  case h_6 =>
    by_cases hi : the_Litv_IntLit v < 0 ∨ the_Litv_IntLit v > 255
    · exact Or.inr (by simp only [do_conversion, if_pos hi])
    · exact Or.inl ⟨_, by simp only [do_conversion, if_neg hi]; rfl, _, rfl⟩
  all_goals first
    | exact Or.inl ⟨_, rfl, _, rfl⟩
    | exact h.elim

theorem Aux.do_test_ok {ctMap : ctMap_ty} {tenvS : tenv_store} {v1 v2 : value} {tst : test}
    {ty : prim_type} (hok : ctMap_ok ctMap) (hb : ctMap_has_bools ctMap)
    (h : supported_test tst ty) (h1 : type_v 0 ctMap tenvS v1 (t_of ty))
    (h2 : type_v 0 ctMap tenvS v2 (t_of ty)) : ∃ b, do_test tst ty v1 v2 = Eq_val b := by
  have c1 := Aux.check_type_of hok hb h1
  have c2 := Aux.check_type_of hok hb h2
  cases tst with
  | Equal =>
    simp only [do_test, if_pos (And.intro c1 c2)]
    split
    · exact ⟨_, rfl⟩
    · have := (eq_same_type (α := Unit) (β := Unit)).1 v1 v2 0 ctMap () tenvS _ ⟨hok, h1, h2⟩
      cases hq : do_eq v1 v2 with
      | Eq_val b => exact ⟨b, rfl⟩
      | Eq_type_error => exact absurd hq this
  | Compare o =>
    simp only [supported_test, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl <;>
    · obtain ⟨x, rfl⟩ := c1
      obtain ⟨y, rfl⟩ := c2
      exact ⟨_, rfl⟩
  | AltCompare o => exact h.elim

theorem Aux.canon_ref {tvs : Nat} {ctMap : ctMap_ty} {tenvS : tenv_store} {v : value} {t : typ}
    (h : type_v tvs ctMap tenvS v (Tref t)) (hok : ctMap_ok ctMap) :
    ∃ n, v = Loc true n ∧ FLOOKUP tenvS n = some (Ref_t t) := by
  have := Aux.canon h hok (by simp [Aux.isPrim])
  simp [Tint_num, Tchar_num, Tstring_num, Tword8_num, Tword64_num, Tdouble_num,
    Ttup_num, Tfn_num, Tref_num, Tword8array_num, Tarray_num, Tvector_num] at this
  exact this

theorem Aux.LR1 {α β : Type} {R : α → β → Prop} {ws : List α} {t : β}
    (h : LIST_REL R ws [t]) : ∃ w, ws = [w] ∧ R w t := by
  obtain ⟨w, ws', rfl, h1, h⟩ := Aux.LIST_REL_cons_right.mp h
  rw [Aux.LIST_REL_nil_right] at h
  subst h
  exact ⟨w, rfl, h1⟩

theorem Aux.LR2 {α β : Type} {R : α → β → Prop} {ws : List α} {t1 t2 : β}
    (h : LIST_REL R ws [t1, t2]) : ∃ w1 w2, ws = [w1, w2] ∧ R w1 t1 ∧ R w2 t2 := by
  obtain ⟨w, ws', rfl, h1, h⟩ := Aux.LIST_REL_cons_right.mp h
  obtain ⟨w2, rfl, h2⟩ := Aux.LR1 h
  exact ⟨w, w2, rfl, h1, h2⟩

theorem Aux.LR3 {α β : Type} {R : α → β → Prop} {ws : List α} {t1 t2 t3 : β}
    (h : LIST_REL R ws [t1, t2, t3]) :
    ∃ w1 w2 w3, ws = [w1, w2, w3] ∧ R w1 t1 ∧ R w2 t2 ∧ R w3 t3 := by
  obtain ⟨w, ws', rfl, h1, h⟩ := Aux.LIST_REL_cons_right.mp h
  obtain ⟨w2, w3, rfl, h2, h3⟩ := Aux.LR2 h
  exact ⟨w, w2, w3, rfl, h1, h2, h3⟩

theorem Aux.LR5 {α β : Type} {R : α → β → Prop} {ws : List α} {t1 t2 t3 t4 t5 : β}
    (h : LIST_REL R ws [t1, t2, t3, t4, t5]) :
    ∃ w1 w2 w3 w4 w5, ws = [w1, w2, w3, w4, w5] ∧ R w1 t1 ∧ R w2 t2 ∧ R w3 t3 ∧ R w4 t4 ∧
      R w5 t5 := by
  obtain ⟨w, ws', rfl, h1, h⟩ := Aux.LIST_REL_cons_right.mp h
  obtain ⟨w2, ws', rfl, h2, h⟩ := Aux.LIST_REL_cons_right.mp h
  obtain ⟨w3, w4, w5, rfl, h3, h4, h5⟩ := Aux.LR3 h
  exact ⟨w, w2, w3, w4, w5, rfl, h1, h2, h3, h4, h5⟩

/- HOL4:
Theorem op_type_sound:
 !ctMap tenvS vs op ts t store (ffi : 'ffi ffi_state).
   good_ctMap ctMap ∧
   op ≠ Opapp ∧
   type_s ctMap store tenvS ∧
   type_op op ts t ∧
   check_freevars 0 [] t ∧
   LIST_REL (type_v 0 ctMap tenvS) vs (REVERSE ts)
 ⇒
 ?tenvS' store' ffi' r.
   store_type_extension tenvS tenvS' ∧
   type_s ctMap store' tenvS' ∧
   do_app (store,ffi) op (REVERSE vs) = SOME ((store', ffi'), r) ∧
   case r of
   | Rval v => type_v 0 ctMap tenvS' v t
   | Rerr (Rraise v) => type_v 0 ctMap tenvS' v Texn
   | Rerr (Rabort(Rffi_error _)) => T
   | Rerr (Rabort _) => F -/
theorem op_type_sound {ffi_ty : Type} :
    ∀ (ctMap : ctMap_ty) (tenvS : tenv_store) (vs : List value) (op : CmlTS.op)
      (ts : List typ) (t : typ) (store : List (store_v value)) (ffi : ffi_state ffi_ty),
      good_ctMap ctMap ∧
      op ≠ Opapp ∧
      type_s ctMap store tenvS ∧
      type_op op ts t ∧
      check_freevars 0 [] t ∧
      LIST_REL (type_v 0 ctMap tenvS) vs ts.reverse
      →
      ∃ (tenvS' : tenv_store) (store' : List (store_v value)) (ffi' : ffi_state ffi_ty)
        (r : result value value),
        store_type_extension tenvS tenvS' ∧
        type_s ctMap store' tenvS' ∧
        do_app (store, ffi) op vs.reverse = some ((store', ffi'), r) ∧
        (match r with
          | Rval v => type_v 0 ctMap tenvS' v t
          | Rerr (Rraise v) => type_v 0 ctMap tenvS' v Texn
          | Rerr (Rabort (Rffi_error _)) => True
          | Rerr (Rabort _) => False) := by
  rintro ctMap tenvS vs op ts t store ffi ⟨⟨hok, hb, hex, hlist⟩, hne, hs, ho, hc, hr⟩
  have hr' : LIST_REL (type_v 0 ctMap tenvS) vs.reverse ts := Aux.LIST_REL_reverse_iff.mpr hr
  generalize vs.reverse = ws at hr' ⊢
  obtain ⟨xchr, xsub, xbind, xdiv⟩ := type_v_exn 0 ctMap tenvS hex
  have xsub : type_v 0 ctMap tenvS sub_exn_v Texn := xsub
  have xchr : type_v 0 ctMap tenvS chr_exn_v Texn := xchr
  have xdiv : type_v 0 ctMap tenvS div_exn_v Texn := xdiv
  have rf := store_type_extension_refl tenvS
  have unit := Aux.type_v_unit 0 ctMap tenvS
  have cInt : ∀ v, type_v 0 ctMap tenvS v Tint → ∃ n, v = Litv (lit.IntLit n) := fun v h =>
    (prim_canonical_values_thm 0 ctMap tenvS v [] Tint Tint [] Tint).1 ⟨h, hok⟩
  have cChar : ∀ v, type_v 0 ctMap tenvS v Tchar → ∃ n, v = Litv (lit.Char n) := fun v h =>
    (prim_canonical_values_thm 0 ctMap tenvS v [] Tint Tint [] Tint).2.1 ⟨h, hok⟩
  have cStr : ∀ v, type_v 0 ctMap tenvS v Tstring → ∃ n, v = Litv (lit.StrLit n) := fun v h =>
    (prim_canonical_values_thm 0 ctMap tenvS v [] Tint Tint [] Tint).2.2.1 ⟨h, hok⟩
  have cW8 : ∀ v, type_v 0 ctMap tenvS v Tword8 → ∃ n, v = Litv (lit.Word8 n) := fun v h =>
    (prim_canonical_values_thm 0 ctMap tenvS v [] Tint Tint [] Tint).2.2.2.1 ⟨h, hok⟩
  have cW64 : ∀ v, type_v 0 ctMap tenvS v Tword64 → ∃ n, v = Litv (lit.Word64 n) := fun v h =>
    (prim_canonical_values_thm 0 ctMap tenvS v [] Tint Tint [] Tint).2.2.2.2.1 ⟨h, hok⟩
  have cArr8 : ∀ v, type_v 0 ctMap tenvS v Tword8array → ∃ n ws, v = Loc true n ∧
      store_lookup n store = some (W8array ws) ∧ FLOOKUP tenvS n = some W8array_t := fun v h =>
    (prim_canonical_values_thm 0 ctMap tenvS v [] Tint Tint store Tint).2.2.2.2.2.2.2.2.2.1
      ⟨h, hok, hs⟩
  have cArr : ∀ v t, type_v 0 ctMap tenvS v (Tarray t) → ∃ n vs, v = Loc true n ∧
      store_lookup n store = some (Varray vs) ∧ EVERY (fun v => type_v 0 ctMap tenvS v t) vs ∧
      FLOOKUP tenvS n = some (Varray_t t) := fun v t h =>
    (prim_canonical_values_thm 0 ctMap tenvS v [] Tint Tint store t).2.2.2.2.2.2.2.2.2.2.1
      ⟨h, hok, hs⟩
  have cVec : ∀ v t, type_v 0 ctMap tenvS v (Tvector t) → ∃ vs, v = Vectorv vs ∧
      EVERY (fun v => type_v 0 ctMap tenvS v t) vs := fun v t h =>
    (prim_canonical_values_thm 0 ctMap tenvS v [] Tint Tint store t).2.2.2.2.2.2.2.2.2.2.2
      ⟨h, hok⟩
  have cList : ∀ v t, type_v 0 ctMap tenvS v (Tlist t) → ∃ vs, v_to_list v = some vs ∧
      EVERY (fun v => type_v 0 ctMap tenvS v t) vs ∧
      (t = Tchar → ∃ vs, v_to_char_list v = some vs) ∧
      (t = Tstring → ∃ str, vs_to_string vs = some str) := fun v t h =>
    has_lists_v_to_list v ctMap 0 tenvS t ⟨hok, hlist, h⟩
  have assign8 : ∀ n ws', FLOOKUP tenvS n = some W8array_t →
      ∃ store', store_assign n (W8array ws') store = some store' ∧ type_s ctMap store' tenvS :=
    fun n ws' h => store_assign_type_sound _ _ _ _ W8array_t _ ⟨hs, h, trivial⟩
  rw [type_op_cases] at ho
  rcases ho with ⟨t1, t2, rfl, rfl, rfl⟩ | ⟨sh, n, t1, rfl, rfl, rfl, rfl⟩ |
    ⟨sh, n, t1, rfl, rfl, rfl, rfl⟩ | ⟨t1, t2, rfl, rfl, rfl, rfl⟩ |
    ⟨a, ty, rfl, hev, rfl, hsup⟩ | ⟨ty1, ty2, t1, rfl, rfl, rfl, rfl, hsup⟩ |
    ⟨tst, ty, t1, t2, rfl, rfl, rfl, rfl, rfl, hsup⟩ | ⟨t1, t2, rfl, rfl, rfl, rfl⟩ |
    ⟨t1, rfl, rfl, rfl⟩ | ⟨t1, rfl, rfl, rfl⟩ | ⟨t1, t2, rfl, rfl, rfl, rfl, rfl⟩ |
    ⟨t1, t2, rfl, rfl, rfl, rfl, rfl⟩ | ⟨t1, rfl, rfl, rfl, rfl⟩ |
    ⟨t1, t2, t3, rfl, rfl, rfl, rfl, rfl, rfl⟩ | ⟨t1, t2, t3, rfl, rfl, rfl, rfl, rfl, rfl⟩ |
    ⟨t1, t2, t3, t4, t5, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ |
    ⟨t1, t2, t3, rfl, rfl, rfl, rfl, rfl, rfl⟩ |
    ⟨t1, t2, t3, t4, t5, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ |
    ⟨t1, rfl, rfl, rfl, rfl⟩ | ⟨t1, rfl, rfl, rfl, rfl⟩ | ⟨t1, t2, rfl, rfl, rfl, rfl, rfl⟩ |
    ⟨t1, rfl, rfl, rfl, rfl⟩ | ⟨t1, rfl, rfl, rfl, rfl⟩ | ⟨t1, ctor, rfl, rfl, rfl, rfl⟩ |
    ⟨t1, t2, rfl, rfl, rfl, rfl⟩ | ⟨t1, ctor, rfl, rfl, rfl, rfl⟩ |
    ⟨t1, t2, rfl, rfl, rfl, rfl⟩ | ⟨t1, t2, rfl, rfl, rfl, rfl⟩ | ⟨t1, t2, rfl, rfl, rfl, rfl⟩ |
    ⟨t1, ctor, rfl, rfl, rfl, rfl⟩ | ⟨t1, t2, t3, rfl, rfl, rfl, rfl, rfl⟩ |
    ⟨t1, t2, rfl, rfl, rfl, rfl, rfl⟩ | ⟨n, t1, t2, rfl, rfl, rfl, rfl, rfl⟩ |
    ⟨t1, ctor, t2, rfl, rfl, rfl, rfl, rfl⟩
  · exact absurd rfl hne
  · -- Shift W8
    obtain ⟨w, rfl, h1⟩ := Aux.LR1 hr'
    obtain ⟨x, rfl⟩ := cW8 _ h1
    exact ⟨tenvS, store, ffi, Rval _, rf, hs, rfl, type_v.word8 _ _ _ _⟩
  · -- Shift W64
    obtain ⟨w, rfl, h1⟩ := Aux.LR1 hr'
    obtain ⟨x, rfl⟩ := cW64 _ h1
    exact ⟨tenvS, store, ffi, Rval _, rf, hs, rfl, type_v.word64 _ _ _ _⟩
  · -- Equality
    obtain ⟨w1, w2, rfl, h1, h2⟩ := Aux.LR2 hr'
    have := (eq_same_type (α := Unit) (β := Unit)).1 w1 w2 0 ctMap () tenvS _ ⟨hok, h1, h2⟩
    cases hq : do_eq w1 w2 with
    | Eq_type_error => exact absurd hq this
    | Eq_val b =>
      exact ⟨tenvS, store, ffi, Rval (Boolv b), rf, hs, by simp only [do_app.eq_def, hq],
        type_v_Boolv _ _ _ _ hb⟩
  · -- Arith
    have hlen := Aux.LIST_REL_length hr'
    rw [← hlen] at hsup
    have hck : EVERY (check_type ty) ws := by
      rw [EVERY_iff_forall] at hev ⊢
      intro x hx
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
      have hi2 : i < ts.length := by omega
      have := (LIST_REL_iff_aux.mp hr').2 i _ _ (List.getElem?_eq_getElem hi)
        (List.getElem?_eq_getElem hi2)
      rw [hev _ (List.getElem_mem hi2)] at this
      exact Aux.check_type_of hok hb this
    rcases Aux.do_arith_ok hsup with ⟨v, hv, hvt⟩ | hv
    · exact ⟨tenvS, store, ffi, Rval v, rf, hs, by simp only [do_app.eq_def, if_pos hck, hv],
        Aux.type_of_check hb hvt⟩
    · exact ⟨tenvS, store, ffi, Rerr (Rraise div_exn_v), rf, hs,
        by simp only [do_app.eq_def, if_pos hck, hv], xdiv⟩
  · -- FromTo
    obtain ⟨w, rfl, h1⟩ := Aux.LR1 hr'
    have hck := Aux.check_type_of hok hb h1
    rcases Aux.do_conv_ok (v := w) hsup with ⟨v, hv, hvt⟩ | hv
    · exact ⟨tenvS, store, ffi, Rval v, rf, hs, by simp only [do_app.eq_def, if_pos hck, hv],
        Aux.type_of_check hb hvt⟩
    · exact ⟨tenvS, store, ffi, Rerr (Rraise chr_exn_v), rf, hs,
        by simp only [do_app.eq_def, if_pos hck, hv], xchr⟩
  · -- Test
    obtain ⟨w1, w2, rfl, h1, h2⟩ := Aux.LR2 hr'
    obtain ⟨b, hb'⟩ := Aux.do_test_ok hok hb hsup h1 h2
    exact ⟨tenvS, store, ffi, Rval (Boolv b), rf, hs, by simp only [do_app.eq_def, hb'],
      type_v_Boolv _ _ _ _ hb⟩
  · -- Opassign
    obtain ⟨w1, w2, rfl, h1, h2⟩ := Aux.LR2 hr'
    obtain ⟨n, rfl, hl⟩ := Aux.canon_ref h1 hok
    obtain ⟨store', a1, a2⟩ := store_assign_type_sound ctMap tenvS store (Refv w2) (Ref_t t2) n
      ⟨hs, hl, h2⟩
    exact ⟨tenvS, store', ffi, Rval (Conv none []), rf, a2, by simp only [do_app.eq_def, a1], unit⟩
  · -- Opref
    obtain ⟨w1, rfl, h1⟩ := Aux.LR1 hr'
    obtain ⟨store', tenvS', n, a1, a2, a3, a4⟩ := store_alloc_type_sound ctMap tenvS store
      (Refv w1) (Ref_t t1) ⟨hok, hs, h1⟩
    simp only [Tref, check_freevars, EVERY] at hc
    exact ⟨tenvS', store', ffi, Rval (Loc true n), a1, a3, by simp only [do_app.eq_def, a2],
      type_v.ref _ _ _ _ _ hc.1 a4⟩
  · -- Opderef
    obtain ⟨w1, rfl, h1⟩ := Aux.LR1 hr'
    obtain ⟨n, rfl, hl⟩ := Aux.canon_ref h1 hok
    obtain ⟨sv, a1, a2⟩ := Aux.type_s_lookup hs hl
    cases sv <;> simp only [type_sv] at a2
    exact ⟨tenvS, store, ffi, Rval _, rf, hs, by simp only [do_app.eq_def, a1], a2⟩
  · -- Aw8alloc
    obtain ⟨w1, w2, rfl, h1, h2⟩ := Aux.LR2 hr'
    obtain ⟨i, rfl⟩ := cInt _ h1
    obtain ⟨w, rfl⟩ := cW8 _ h2
    by_cases hi : i < 0
    · exact ⟨tenvS, store, ffi, Rerr (Rraise sub_exn_v), rf, hs,
        by simp only [do_app.eq_def, if_pos hi], xsub⟩
    · obtain ⟨store', tenvS', n, a1, a2, a3, a4⟩ := store_alloc_type_sound ctMap tenvS store
        (W8array (List.replicate (Num (INT_ABS (I i))) w)) W8array_t ⟨hok, hs, trivial⟩
      exact ⟨tenvS', store', ffi, Rval (Loc true n), a1, a3,
        by simp only [do_app.eq_def, if_neg hi, a2], type_v.w8array _ _ _ _ a4⟩
  · -- Aw8sub
    obtain ⟨w1, w2, rfl, h1, h2⟩ := Aux.LR2 hr'
    obtain ⟨n, bs, rfl, hl, hf⟩ := cArr8 _ h1
    obtain ⟨i, rfl⟩ := cInt _ h2
    by_cases hi : i < 0
    · exact ⟨tenvS, store, ffi, Rerr (Rraise sub_exn_v), rf, hs,
        by simp only [do_app.eq_def, hl, if_pos hi], xsub⟩
    · by_cases hn : Num (INT_ABS (I i)) ≥ bs.length
      · exact ⟨tenvS, store, ffi, Rerr (Rraise sub_exn_v), rf, hs,
          by simp only [do_app.eq_def, hl, if_neg hi, if_pos hn], xsub⟩
      · exact ⟨tenvS, store, ffi, Rval (Litv (lit.Word8 (EL (Num (INT_ABS (I i))) bs))), rf, hs,
          by simp only [do_app.eq_def, hl, if_neg hi, if_neg hn], type_v.word8 _ _ _ _⟩
  · -- Aw8length
    obtain ⟨w1, rfl, h1⟩ := Aux.LR1 hr'
    obtain ⟨n, bs, rfl, hl, hf⟩ := cArr8 _ h1
    exact ⟨tenvS, store, ffi, Rval (Litv (lit.IntLit (int_of_num bs.length))), rf, hs,
      by simp only [do_app.eq_def, hl],
      type_v.intLit _ _ _ _⟩
  · -- Aw8update
    obtain ⟨w1, w2, w3, rfl, h1, h2, h3⟩ := Aux.LR3 hr'
    obtain ⟨n, bs, rfl, hl, hf⟩ := cArr8 _ h1
    obtain ⟨i, rfl⟩ := cInt _ h2
    obtain ⟨w, rfl⟩ := cW8 _ h3
    by_cases hi : i < 0
    · exact ⟨tenvS, store, ffi, Rerr (Rraise sub_exn_v), rf, hs,
        by simp only [do_app.eq_def, hl, if_pos hi], xsub⟩
    · by_cases hn : Num (INT_ABS (I i)) ≥ bs.length
      · exact ⟨tenvS, store, ffi, Rerr (Rraise sub_exn_v), rf, hs,
          by simp only [do_app.eq_def, hl, if_neg hi, if_pos hn], xsub⟩
      · obtain ⟨store', a1, a2⟩ := assign8 n (LUPDATE w (Num (INT_ABS (I i))) bs) hf
        exact ⟨tenvS, store', ffi, Rval (Conv none []), rf, a2,
          by simp only [do_app.eq_def, hl, if_neg hi, if_neg hn, a1], unit⟩
  · -- CopyStrStr
    obtain ⟨w1, w2, w3, rfl, h1, h2, h3⟩ := Aux.LR3 hr'
    obtain ⟨s, rfl⟩ := cStr _ h1
    obtain ⟨i, rfl⟩ := cInt _ h2
    obtain ⟨j, rfl⟩ := cInt _ h3
    cases hq : copy_array (explode s, i) j none with
    | none =>
      exact ⟨tenvS, store, ffi, Rerr (Rraise sub_exn_v), rf, hs,
        by simp only [do_app.eq_def, hq], xsub⟩
    | some cs =>
      exact ⟨tenvS, store, ffi, Rval (Litv (lit.StrLit (implode cs))), rf, hs,
        by simp only [do_app.eq_def, hq], type_v.strLit _ _ _ _⟩
  · -- CopyStrAw8
    obtain ⟨w1, w2, w3, w4, w5, rfl, h1, h2, h3, h4, h5⟩ := Aux.LR5 hr'
    obtain ⟨s, rfl⟩ := cStr _ h1
    obtain ⟨i, rfl⟩ := cInt _ h2
    obtain ⟨j, rfl⟩ := cInt _ h3
    obtain ⟨n, bs, rfl, hl, hf⟩ := cArr8 _ h4
    obtain ⟨k, rfl⟩ := cInt _ h5
    cases hq : copy_array (explode s, i) j (some (ws_to_chars bs, k)) with
    | none =>
      exact ⟨tenvS, store, ffi, Rerr (Rraise sub_exn_v), rf, hs,
        by simp only [do_app.eq_def, hl, hq], xsub⟩
    | some cs =>
      obtain ⟨store', a1, a2⟩ := assign8 n (chars_to_ws cs) hf
      exact ⟨tenvS, store', ffi, Rval (Conv none []), rf, a2,
        by simp only [do_app.eq_def, hl, hq, a1], unit⟩
  · -- CopyAw8Str
    obtain ⟨w1, w2, w3, rfl, h1, h2, h3⟩ := Aux.LR3 hr'
    obtain ⟨n, bs, rfl, hl, hf⟩ := cArr8 _ h1
    obtain ⟨i, rfl⟩ := cInt _ h2
    obtain ⟨j, rfl⟩ := cInt _ h3
    cases hq : copy_array (bs, i) j none with
    | none =>
      exact ⟨tenvS, store, ffi, Rerr (Rraise sub_exn_v), rf, hs,
        by simp only [do_app.eq_def, hl, hq], xsub⟩
    | some cs =>
      exact ⟨tenvS, store, ffi, Rval (Litv (lit.StrLit (implode (ws_to_chars cs)))), rf, hs,
        by simp only [do_app.eq_def, hl, hq], type_v.strLit _ _ _ _⟩
  · -- CopyAw8Aw8
    obtain ⟨w1, w2, w3, w4, w5, rfl, h1, h2, h3, h4, h5⟩ := Aux.LR5 hr'
    obtain ⟨n1, bs1, rfl, hl1, hf1⟩ := cArr8 _ h1
    obtain ⟨i, rfl⟩ := cInt _ h2
    obtain ⟨j, rfl⟩ := cInt _ h3
    obtain ⟨n, bs, rfl, hl, hf⟩ := cArr8 _ h4
    obtain ⟨k, rfl⟩ := cInt _ h5
    cases hq : copy_array (bs1, i) j (some (bs, k)) with
    | none =>
      exact ⟨tenvS, store, ffi, Rerr (Rraise sub_exn_v), rf, hs,
        by simp only [do_app.eq_def, hl1, hl, hq], xsub⟩
    | some cs =>
      obtain ⟨store', a1, a2⟩ := assign8 n cs hf
      exact ⟨tenvS, store', ffi, Rval (Conv none []), rf, a2,
        by simp only [do_app.eq_def, hl1, hl, hq, a1], unit⟩
  · -- Implode
    obtain ⟨w1, rfl, h1⟩ := Aux.LR1 hr'
    obtain ⟨vs', a1, a2, a3, a4⟩ := cList _ _ h1
    obtain ⟨cs, hcs⟩ := a3 rfl
    exact ⟨tenvS, store, ffi, Rval (Litv (lit.StrLit (implode cs))), rf, hs,
      by simp only [do_app.eq_def, hcs], type_v.strLit _ _ _ _⟩
  · -- Explode
    obtain ⟨w1, rfl, h1⟩ := Aux.LR1 hr'
    obtain ⟨s, rfl⟩ := cStr _ h1
    refine ⟨tenvS, store, ffi, Rval _, rf, hs, rfl, Aux.type_v_list hlist ?_ ?_⟩
    · simp [Tchar, check_freevars, EVERY]
    · rw [EVERY_iff_forall]
      intro x hx
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hx
      exact type_v.char _ _ _ _
  · -- Strsub
    obtain ⟨w1, w2, rfl, h1, h2⟩ := Aux.LR2 hr'
    obtain ⟨s, rfl⟩ := cStr _ h1
    obtain ⟨i, rfl⟩ := cInt _ h2
    by_cases hi : i < 0
    · exact ⟨tenvS, store, ffi, Rerr (Rraise sub_exn_v), rf, hs,
        by simp only [do_app.eq_def, if_pos hi], xsub⟩
    · by_cases hn : Num (INT_ABS (I i)) ≥ strlen s
      · exact ⟨tenvS, store, ffi, Rerr (Rraise sub_exn_v), rf, hs,
          by simp only [do_app.eq_def, if_neg hi, if_pos hn], xsub⟩
      · exact ⟨tenvS, store, ffi,
          Rval (Litv (lit.Char (EL (Num (INT_ABS (I i))) (explode s)))), rf, hs,
          by simp only [do_app.eq_def, if_neg hi, if_neg hn], type_v.char _ _ _ _⟩
  · -- Strlen
    obtain ⟨w1, rfl, h1⟩ := Aux.LR1 hr'
    obtain ⟨s, rfl⟩ := cStr _ h1
    exact ⟨tenvS, store, ffi, Rval _, rf, hs, rfl, type_v.intLit _ _ _ _⟩
  · -- Strcat
    obtain ⟨w1, rfl, h1⟩ := Aux.LR1 hr'
    obtain ⟨vs', a1, a2, a3, a4⟩ := cList _ _ h1
    obtain ⟨str, hstr⟩ := a4 rfl
    exact ⟨tenvS, store, ffi, Rval (Litv (lit.StrLit str)), rf, hs,
      by simp only [do_app.eq_def, a1, hstr], type_v.strLit _ _ _ _⟩
  · -- VfromList
    obtain ⟨w1, rfl, h1⟩ := Aux.LR1 hr'
    obtain ⟨vs', a1, a2, a3, a4⟩ := cList _ _ h1
    simp only [Tvector, check_freevars, EVERY] at hc
    exact ⟨tenvS, store, ffi, Rval (Vectorv vs'), rf, hs, by simp only [do_app.eq_def, a1],
      type_v_vector_aux _ _ _ _ _ hc.1 a2⟩
  · -- Vsub
    obtain ⟨w1, w2, rfl, h1, h2⟩ := Aux.LR2 hr'
    obtain ⟨vs', rfl, hv⟩ := cVec _ _ h1
    obtain ⟨i, rfl⟩ := cInt _ h2
    by_cases hi : i < 0
    · exact ⟨tenvS, store, ffi, Rerr (Rraise sub_exn_v), rf, hs,
        by simp only [do_app.eq_def, if_pos hi], xsub⟩
    · by_cases hn : Num (INT_ABS (I i)) ≥ vs'.length
      · exact ⟨tenvS, store, ffi, Rerr (Rraise sub_exn_v), rf, hs,
          by simp only [do_app.eq_def, if_neg hi, if_pos hn], xsub⟩
      · exact ⟨tenvS, store, ffi, Rval (EL (Num (INT_ABS (I i))) vs'), rf, hs,
          by simp only [do_app.eq_def, if_neg hi, if_neg hn], Aux.EVERY_EL hv _ (by omega)⟩
  · -- Vlength
    obtain ⟨w1, rfl, h1⟩ := Aux.LR1 hr'
    obtain ⟨vs', rfl, hv⟩ := cVec _ _ h1
    exact ⟨tenvS, store, ffi, Rval _, rf, hs, rfl, type_v.intLit _ _ _ _⟩
  · -- Aalloc
    obtain ⟨w1, w2, rfl, h1, h2⟩ := Aux.LR2 hr'
    obtain ⟨i, rfl⟩ := cInt _ h1
    simp only [Tarray, check_freevars, EVERY] at hc
    by_cases hi : i < 0
    · exact ⟨tenvS, store, ffi, Rerr (Rraise sub_exn_v), rf, hs,
        by simp only [do_app.eq_def, if_pos hi], xsub⟩
    · obtain ⟨store', tenvS', n, a1, a2, a3, a4⟩ := store_alloc_type_sound ctMap tenvS store
        (Varray (List.replicate (Num (INT_ABS (I i))) w2)) (Varray_t t2)
        ⟨hok, hs, EVERY_iff_forall.mpr fun x hx => by rw [List.eq_of_mem_replicate hx]; exact h2⟩
      exact ⟨tenvS', store', ffi, Rval (Loc true n), a1, a3,
        by simp only [do_app.eq_def, if_neg hi, a2], type_v.varray _ _ _ _ _ hc.1 a4⟩
  · -- AallocEmpty
    obtain ⟨w1, rfl, h1⟩ := Aux.LR1 hr'
    obtain ⟨vs', rfl, hv⟩ := (prim_canonical_values_thm 0 ctMap tenvS w1 [] Tint Tint store
      Tint).2.2.2.2.2.2.1 ⟨h1, hok⟩
    have hv' : vs' = [] := List.eq_nil_of_length_eq_zero hv.symm
    subst hv'
    simp only [Tarray, check_freevars, EVERY] at hc
    obtain ⟨store', tenvS', n, a1, a2, a3, a4⟩ := store_alloc_type_sound ctMap tenvS store
      (Varray []) (Varray_t t2) ⟨hok, hs, trivial⟩
    exact ⟨tenvS', store', ffi, Rval (Loc true n), a1, a3, by simp only [do_app.eq_def, a2],
      type_v.varray _ _ _ _ _ hc.1 a4⟩
  · -- Asub
    obtain ⟨w1, w2, rfl, h1, h2⟩ := Aux.LR2 hr'
    obtain ⟨n, vs', rfl, hl, hv, hf⟩ := cArr _ _ h1
    obtain ⟨i, rfl⟩ := cInt _ h2
    by_cases hi : i < 0
    · exact ⟨tenvS, store, ffi, Rerr (Rraise sub_exn_v), rf, hs,
        by simp only [do_app.eq_def, hl, if_pos hi], xsub⟩
    · by_cases hn : Num (INT_ABS (I i)) ≥ vs'.length
      · exact ⟨tenvS, store, ffi, Rerr (Rraise sub_exn_v), rf, hs,
          by simp only [do_app.eq_def, hl, if_neg hi, if_pos hn], xsub⟩
      · exact ⟨tenvS, store, ffi, Rval (EL (Num (INT_ABS (I i))) vs'), rf, hs,
          by simp only [do_app.eq_def, hl, if_neg hi, if_neg hn], Aux.EVERY_EL hv _ (by omega)⟩
  · -- Alength
    obtain ⟨w1, rfl, h1⟩ := Aux.LR1 hr'
    obtain ⟨n, vs', rfl, hl, hv, hf⟩ := cArr _ _ h1
    exact ⟨tenvS, store, ffi, Rval (Litv (lit.IntLit (int_of_num vs'.length))), rf, hs,
      by simp only [do_app.eq_def, hl],
      type_v.intLit _ _ _ _⟩
  · -- Aupdate
    obtain ⟨w1, w2, w3, rfl, h1, h2, h3⟩ := Aux.LR3 hr'
    obtain ⟨n, vs', rfl, hl, hv, hf⟩ := cArr _ _ h1
    obtain ⟨i, rfl⟩ := cInt _ h2
    by_cases hi : i < 0
    · exact ⟨tenvS, store, ffi, Rerr (Rraise sub_exn_v), rf, hs,
        by simp only [do_app.eq_def, hl, if_pos hi], xsub⟩
    · by_cases hn : Num (INT_ABS (I i)) ≥ vs'.length
      · exact ⟨tenvS, store, ffi, Rerr (Rraise sub_exn_v), rf, hs,
          by simp only [do_app.eq_def, hl, if_neg hi, if_pos hn], xsub⟩
      · obtain ⟨store', a1, a2⟩ := store_assign_type_sound ctMap tenvS store
          (Varray (LUPDATE w3 (Num (INT_ABS (I i))) vs')) (Varray_t t3) n ⟨hs, hf, by
            show EVERY _ _
            rw [Aux.LUPDATE_eq, EVERY_iff_forall]
            intro x hx
            rcases List.mem_or_eq_of_mem_set hx with hx | rfl
            · exact EVERY_iff_forall.mp hv x hx
            · exact h3⟩
        exact ⟨tenvS, store', ffi, Rval (Conv none []), rf, a2,
          by simp only [do_app.eq_def, hl, if_neg hi, if_neg hn, a1], unit⟩
  · -- ConfigGC
    obtain ⟨w1, w2, rfl, h1, h2⟩ := Aux.LR2 hr'
    obtain ⟨i, rfl⟩ := cInt _ h1
    obtain ⟨j, rfl⟩ := cInt _ h2
    exact ⟨tenvS, store, ffi, Rval _, rf, hs, rfl, unit⟩
  · -- FFI
    obtain ⟨w1, w2, rfl, h1, h2⟩ := Aux.LR2 hr'
    obtain ⟨s, rfl⟩ := cStr _ h1
    obtain ⟨k, bs, rfl, hl, hf⟩ := cArr8 _ h2
    cases hq : call_FFI ffi (ExtCall n) ((explode s).map (n2w ∘ ORD)) bs with
    | FFI_return ffi' bs' =>
      obtain ⟨store', a1, a2⟩ := assign8 k bs' hf
      exact ⟨tenvS, store', ffi', Rval (Conv none []), rf, a2,
        by simp only [do_app.eq_def, hl, hq, a1], unit⟩
    | FFI_final o =>
      exact ⟨tenvS, store, ffi, Rerr (Rabort (Rffi_error o)), rf, hs,
        by simp only [do_app.eq_def, hl, hq], trivial⟩
  · -- ListAppend
    obtain ⟨w1, w2, rfl, h1, h2⟩ := Aux.LR2 hr'
    obtain ⟨xs, a1, a2, -⟩ := cList _ _ h1
    obtain ⟨ys, b1, b2, -⟩ := cList _ _ h2
    simp only [check_freevars, EVERY] at hc
    exact ⟨tenvS, store, ffi, Rval (list_to_v (xs ++ ys)), rf, hs,
      by simp only [do_app.eq_def, a1, b1],
      Aux.type_v_list hlist hc.1 (Aux.EVERY_append.mpr ⟨a2, b2⟩)⟩

/- HOL4:
Theorem build_conv_type_sound:
 !envC cn vs tvs ts ctMap tenvS ts' tn tenvC tvs' tenvE l.
 nsAll2 (type_ctor ctMap) envC tenvC ∧
 do_con_check envC (SOME cn) l ∧
 num_tvs tenvE = 0 ∧
 EVERY (check_freevars (num_tvs (bind_tvar tvs tenvE)) []) ts' ∧
 LENGTH tvs' = LENGTH ts' ∧
 LIST_REL (type_v tvs ctMap tenvS) vs
   (REVERSE (MAP (type_subst (alist_to_fmap (ZIP (tvs',ts')))) ts)) ∧
 nsLookup tenvC cn = SOME (tvs',ts,tn)
 ⇒
 ?v.
   build_conv envC (SOME cn) (REVERSE vs) = SOME v ∧
   type_v tvs ctMap tenvS v (Tapp ts' tn) -/
theorem build_conv_type_sound :
    ∀ (envC : Namespace mlstring mlstring (Nat × stamp)) (cn : ident mlstring mlstring)
      (vs : List value) (tvs : Nat) (ts : List typ) (ctMap : ctMap_ty) (tenvS : tenv_store)
      (ts' : List typ) (tn : type_ident)
      (tenvC : Namespace mlstring mlstring (List tvarN × List typ × type_ident))
      (tvs' : List tvarN) (tenvE : tenv_val_exp) (l : Nat),
      nsAll2 (type_ctor ctMap) envC tenvC ∧
      do_con_check envC (some cn) l ∧
      num_tvs tenvE = 0 ∧
      EVERY (check_freevars (num_tvs (bind_tvar tvs tenvE)) []) ts' ∧
      tvs'.length = ts'.length ∧
      LIST_REL (type_v tvs ctMap tenvS) vs
        (ts.map (type_subst (alist_to_fmap (tvs'.zip ts')))).reverse ∧
      nsLookup tenvC cn = some (tvs', ts, tn)
      →
      ∃ v,
        build_conv envC (some cn) vs.reverse = some v ∧
        type_v tvs ctMap tenvS v (Tapp ts' tn) := by
  rintro envC cn vs tvs ts ctMap tenvS ts' tn tenvC tvs' tenvE l ⟨h1, h2, h3, h4, h5, h6, h7⟩
  obtain ⟨⟨n, stamp⟩, hv, hf, -⟩ := nsAll2_nsLookup2 _ _ _ _ _ ⟨h7, h1⟩
  rw [Aux.num_tvs_bind_tvar, h3, Nat.add_zero] at h4
  refine ⟨Conv (some stamp) vs.reverse, by simp only [build_conv, hv],
    type_v_conv_aux _ _ _ _ tvs' _ _ ts _ h4 h5 ?_ hf⟩
  rw [Aux.FUPDATE_LIST_reverse]
  exact Aux.LIST_REL_reverse_iff.mpr h6

/- HOL4:
Theorem same_ctor_and_same_tid:
   !stamp1 stamp2.
    same_ctor stamp1 stamp2 ∧
    same_type stamp1 stamp2
    ⇒
    stamp1 = stamp2 -/
theorem same_ctor_and_same_tid :
    ∀ stamp1 stamp2 : stamp,
      same_ctor stamp1 stamp2 ∧
      same_type stamp1 stamp2
      →
      stamp1 = stamp2 := fun _ _ h => h.1

/- HOL4:
Theorem pat_type_sound:
  (∀(cenv : env_ctor) st p v bindings tenv ctMap tbindings t new_tbindings tenvS tvs.
   ctMap_ok ctMap ∧
   nsAll2 (type_ctor ctMap) cenv tenv.c ∧
   type_v tvs ctMap tenvS v t ∧
   type_p tvs tenv p t new_tbindings ∧
   type_s ctMap st tenvS ∧
   LIST_REL (λ(x,v) (x',t). x = x' ∧ type_v tvs ctMap tenvS v t) bindings tbindings
   ⇒
   pmatch cenv st p v bindings = No_match ∨
   (?bindings'.
     pmatch cenv st p v bindings = Match bindings' ∧
     LIST_REL (\ (x,v) (x',t). x = x' ∧ type_v tvs ctMap tenvS v t) bindings'
       (new_tbindings ++ tbindings))) ∧
  (∀(cenv : env_ctor) st ps vs bindings tenv ctMap tbindings new_tbindings ts tenvS tvs.
   ctMap_ok ctMap ∧
   nsAll2 (type_ctor ctMap) cenv tenv.c ∧
   LIST_REL (type_v tvs ctMap tenvS) vs ts ∧
   type_ps tvs tenv ps ts new_tbindings ∧
   type_s ctMap st tenvS ∧
   LIST_REL (λ(x,v) (x',t). x = x' ∧ type_v tvs ctMap tenvS v t) bindings tbindings
   ⇒
   pmatch_list cenv st ps vs bindings = No_match ∨
   (?bindings'.
     pmatch_list cenv st ps vs bindings = Match bindings' ∧
     LIST_REL (\ (x,v) (x',t). x = x' ∧ type_v tvs ctMap tenvS v t) bindings'
       (new_tbindings ++ tbindings))) -/
theorem pat_type_sound :
    (∀ (cenv : env_ctor) (st : List (store_v value)) (p : pat) (v : value)
        (bindings : List (varN × value)) (tenv : type_env) (ctMap : ctMap_ty)
        (tbindings : List (varN × typ)) (t : typ) (new_tbindings : List (varN × typ))
        (tenvS : tenv_store) (tvs : Nat),
      ctMap_ok ctMap ∧
      nsAll2 (type_ctor ctMap) cenv tenv.c ∧
      type_v tvs ctMap tenvS v t ∧
      type_p tvs tenv p t new_tbindings ∧
      type_s ctMap st tenvS ∧
      LIST_REL (fun ((x, v) : varN × value) ((x', t) : varN × typ) =>
        x = x' ∧ type_v tvs ctMap tenvS v t) bindings tbindings
      →
      pmatch cenv st p v bindings = No_match ∨
      (∃ bindings',
        pmatch cenv st p v bindings = Match bindings' ∧
        LIST_REL (fun ((x, v) : varN × value) ((x', t) : varN × typ) =>
          x = x' ∧ type_v tvs ctMap tenvS v t) bindings' (new_tbindings ++ tbindings))) ∧
    (∀ (cenv : env_ctor) (st : List (store_v value)) (ps : List pat) (vs : List value)
        (bindings : List (varN × value)) (tenv : type_env) (ctMap : ctMap_ty)
        (tbindings : List (varN × typ)) (new_tbindings : List (varN × typ)) (ts : List typ)
        (tenvS : tenv_store) (tvs : Nat),
      ctMap_ok ctMap ∧
      nsAll2 (type_ctor ctMap) cenv tenv.c ∧
      LIST_REL (type_v tvs ctMap tenvS) vs ts ∧
      type_ps tvs tenv ps ts new_tbindings ∧
      type_s ctMap st tenvS ∧
      LIST_REL (fun ((x, v) : varN × value) ((x', t) : varN × typ) =>
        x = x' ∧ type_v tvs ctMap tenvS v t) bindings tbindings
      →
      pmatch_list cenv st ps vs bindings = No_match ∨
      (∃ bindings',
        pmatch_list cenv st ps vs bindings = Match bindings' ∧
        LIST_REL (fun ((x, v) : varN × value) ((x', t) : varN × typ) =>
          x = x' ∧ type_v tvs ctMap tenvS v t) bindings' (new_tbindings ++ tbindings))) := by
  have H := Aux.type_p_ind
    (P := fun tvs tenv p t nb => ∀ (cenv : env_ctor) (st : List (store_v value)) (v : value)
        (bindings : List (varN × value)) (ctMap : ctMap_ty) (tb : List (varN × typ))
        (tenvS : tenv_store),
      ctMap_ok ctMap → nsAll2 (type_ctor ctMap) cenv tenv.c → type_v tvs ctMap tenvS v t →
      type_s ctMap st tenvS →
      LIST_REL (fun ((x, v) : varN × value) ((x', t) : varN × typ) =>
        x = x' ∧ type_v tvs ctMap tenvS v t) bindings tb →
      pmatch cenv st p v bindings = No_match ∨
      (∃ bindings', pmatch cenv st p v bindings = Match bindings' ∧
        LIST_REL (fun ((x, v) : varN × value) ((x', t) : varN × typ) =>
          x = x' ∧ type_v tvs ctMap tenvS v t) bindings' (nb ++ tb)))
    (Q := fun tvs tenv ps ts nb => ∀ (cenv : env_ctor) (st : List (store_v value))
        (vs : List value) (bindings : List (varN × value)) (ctMap : ctMap_ty)
        (tb : List (varN × typ)) (tenvS : tenv_store),
      ctMap_ok ctMap → nsAll2 (type_ctor ctMap) cenv tenv.c →
      LIST_REL (type_v tvs ctMap tenvS) vs ts →
      type_s ctMap st tenvS →
      LIST_REL (fun ((x, v) : varN × value) ((x', t) : varN × typ) =>
        x = x' ∧ type_v tvs ctMap tenvS v t) bindings tb →
      pmatch_list cenv st ps vs bindings = No_match ∨
      (∃ bindings', pmatch_list cenv st ps vs bindings = Match bindings' ∧
        LIST_REL (fun ((x, v) : varN × value) ((x', t) : varN × typ) =>
          x = x' ∧ type_v tvs ctMap tenvS v t) bindings' (nb ++ tb)))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · refine ⟨?_, ?_⟩
    · rintro cenv st p v bindings tenv ctMap tb t nb tenvS tvs ⟨h1, h2, h3, h4, h5, h6⟩
      exact H.1 _ _ _ _ _ h4 cenv st v bindings ctMap tb tenvS h1 h2 h3 h5 h6
    · rintro cenv st ps vs bindings tenv ctMap tb nb ts tenvS tvs ⟨h1, h2, h3, h4, h5, h6⟩
      exact H.2 _ _ _ _ _ h4 cenv st vs bindings ctMap tb tenvS h1 h2 h3 h5 h6
  · intro tvs tenv t hc cenv st v bindings ctMap tb tenvS h1 h2 h3 h5 h6
    exact Or.inr ⟨bindings, by simp [pmatch], h6⟩
  · intro tvs tenv x t hc cenv st v bindings ctMap tb tenvS h1 h2 h3 h5 h6
    exact Or.inr ⟨(x, v) :: bindings, by simp [pmatch], ⟨rfl, h3⟩, h6⟩
  · intro tvs tenv n cenv st v bindings ctMap tb tenvS h1 h2 h3 h5 h6
    obtain ⟨m, rfl⟩ := (prim_canonical_values_thm tvs ctMap tenvS v [] Tint Tint [] Tint).1
      ⟨h3, h1⟩
    simp only [pmatch, lit_same_type, if_true]
    split
    · exact Or.inr ⟨bindings, rfl, h6⟩
    · exact Or.inl rfl
  · intro tvs tenv n cenv st v bindings ctMap tb tenvS h1 h2 h3 h5 h6
    obtain ⟨m, rfl⟩ := (prim_canonical_values_thm tvs ctMap tenvS v [] Tint Tint [] Tint).2.1
      ⟨h3, h1⟩
    simp only [pmatch, lit_same_type, if_true]
    split
    · exact Or.inr ⟨bindings, rfl, h6⟩
    · exact Or.inl rfl
  · intro tvs tenv n cenv st v bindings ctMap tb tenvS h1 h2 h3 h5 h6
    obtain ⟨m, rfl⟩ := (prim_canonical_values_thm tvs ctMap tenvS v [] Tint Tint [] Tint).2.2.1
      ⟨h3, h1⟩
    simp only [pmatch, lit_same_type, if_true]
    split
    · exact Or.inr ⟨bindings, rfl, h6⟩
    · exact Or.inl rfl
  · intro tvs tenv n cenv st v bindings ctMap tb tenvS h1 h2 h3 h5 h6
    obtain ⟨m, rfl⟩ := (prim_canonical_values_thm tvs ctMap tenvS v [] Tint Tint [] Tint).2.2.2.1
      ⟨h3, h1⟩
    simp only [pmatch, lit_same_type, if_true]
    split
    · exact Or.inr ⟨bindings, rfl, h6⟩
    · exact Or.inl rfl
  · intro tvs tenv n cenv st v bindings ctMap tb tenvS h1 h2 h3 h5 h6
    obtain ⟨m, rfl⟩ :=
      (prim_canonical_values_thm tvs ctMap tenvS v [] Tint Tint [] Tint).2.2.2.2.1 ⟨h3, h1⟩
    simp only [pmatch, lit_same_type, if_true]
    split
    · exact Or.inr ⟨bindings, rfl, h6⟩
    · exact Or.inl rfl
  · intro tvs tenv cn ps ts tvs' tn ts' b hc hl hps hlk ih cenv st v bindings ctMap tb tenvS
      h1 h2 h3 h5 h6
    obtain ⟨⟨n, stamp⟩, hv, hf, rfl⟩ := nsAll2_nsLookup2 _ _ _ _ _ ⟨hlk, h2⟩
    obtain ⟨s2, vs, tvs2, ts2, rfl, hst, hf2, -, hr⟩ := Aux.ctor_cases h3 h1 hf
    have hlen : ps.length = ts.length := by
      rw [type_ps_length _ _ _ _ _ hps, List.length_map]
    simp only [pmatch, hv]
    rw [if_pos ⟨hst, hlen⟩]
    by_cases hsc : same_ctor stamp s2
    · rw [if_pos hsc]
      have hsc' : stamp = s2 := hsc
      subst hsc'
      rw [hf] at hf2
      cases hf2
      rw [if_pos (by rw [Aux.LIST_REL_length hr, List.length_map])]
      exact ih cenv st vs bindings ctMap tb tenvS h1 h2 hr h5 h6
    · rw [if_neg hsc]
      exact Or.inl rfl
  · intro tvs tenv ps ts b hps ih cenv st v bindings ctMap tb tenvS h1 h2 h3 h5 h6
    have := Aux.canon h3 h1 (by simp [Aux.isPrim])
    simp [Tint_num, Tchar_num, Tstring_num, Tword8_num, Tword64_num, Tdouble_num,
      Ttup_num, Tfn_num, Tref_num, Tword8array_num, Tarray_num, Tvector_num] at this
    obtain ⟨vs, rfl, hr⟩ := this
    simp only [pmatch]
    rw [if_pos (by rw [type_ps_length _ _ _ _ _ hps, Aux.LIST_REL_length hr])]
    exact ih cenv st vs bindings ctMap tb tenvS h1 h2 hr h5 h6
  · intro tvs tenv p t b hp ih cenv st v bindings ctMap tb tenvS h1 h2 h3 h5 h6
    obtain ⟨n, v2, rfl, hl, ht⟩ :=
      (prim_canonical_values_thm tvs ctMap tenvS v [] t Tint st Tint).2.2.2.2.2.2.2.2.1
        ⟨h3, h1, h5⟩
    simp only [pmatch, hl]
    exact ih cenv st v2 bindings ctMap tb tenvS h1 h2
      (type_v_weakening _ _ _ _ _ ht _ _ _ ⟨Or.inl rfl, weakCT_refl _, weakS_refl _⟩) h5 h6
  · intro tvs tenv p x t b hp ih cenv st v bindings ctMap tb tenvS h1 h2 h3 h5 h6
    simp only [pmatch]
    have := ih cenv st v ((x, v) :: bindings) ctMap ((x, t) :: tb) tenvS h1 h2 h3 h5
      ⟨⟨rfl, h3⟩, h6⟩
    rw [List.append_assoc]
    exact this
  · intro tvs tenv p t b hc1 hc2 hp ih cenv st v bindings ctMap tb tenvS h1 h2 h3 h5 h6
    simp only [pmatch]
    exact ih cenv st v bindings ctMap tb tenvS h1 h2 h3 h5 h6
  · intro tvs tenv cenv st vs bindings ctMap tb tenvS h1 h2 h3 h5 h6
    rw [Aux.LIST_REL_nil_right] at h3
    subst h3
    exact Or.inr ⟨bindings, by simp [pmatch_list], h6⟩
  · intro tvs tenv p ps t ts b b' hp hps ih1 ih2 cenv st vs bindings ctMap tb tenvS h1 h2 h3 h5 h6
    obtain ⟨v, vs, rfl, hv, hvs⟩ := Aux.LIST_REL_cons_right.mp h3
    simp only [pmatch_list]
    rcases ih1 cenv st v bindings ctMap tb tenvS h1 h2 hv h5 h6 with h | ⟨b1, h, hb1⟩
    · rw [h]
      rcases ih2 cenv st vs bindings ctMap tb tenvS h1 h2 hvs h5 h6 with h' | ⟨b2, h', -⟩
      · rw [h']; exact Or.inl rfl
      · rw [h']; exact Or.inl rfl
    · rw [h, List.append_assoc]
      exact ih2 cenv st vs b1 ctMap (b ++ tb) tenvS h1 h2 hvs h5 hb1

/- HOL4:
Theorem lookup_var_sound:
   !n tvs tenvE targs t ctMap tenvS env tenv.
    lookup_var n (bind_tvar tvs tenvE) tenv = SOME (LENGTH targs, t) ∧
    ctMap_ok ctMap ∧
    tenv_val_exp_ok tenvE ∧
    num_tvs tenvE = 0 ∧
    EVERY (check_freevars tvs []) targs ∧
    type_all_env ctMap tenvS env (tenv with v := add_tenvE tenvE tenv.v)
    ⇒
    ?v. nsLookup env.v n = SOME v ∧ type_v tvs ctMap tenvS v (deBruijn_subst 0 targs t) -/
theorem lookup_var_sound :
    ∀ (n : ident modN varN) (tvs : Nat) (tenvE : tenv_val_exp) (targs : List typ) (t : typ)
      (ctMap : ctMap_ty) (tenvS : tenv_store) (env : sem_env value) (tenv : type_env),
      lookup_var n (bind_tvar tvs tenvE) tenv = some (targs.length, t) ∧
      ctMap_ok ctMap ∧
      tenv_val_exp_ok tenvE ∧
      num_tvs tenvE = 0 ∧
      EVERY (check_freevars tvs []) targs ∧
      type_all_env ctMap tenvS env { tenv with v := add_tenvE tenvE tenv.v }
      →
      ∃ v, nsLookup env.v n = some v ∧
        type_v tvs ctMap tenvS v (deBruijn_subst 0 targs t) := by
  rintro n tvs tenvE targs t ctMap tenvS env tenv ⟨h1, h2, h3, h4, h5, h6, h7⟩
  have hlk : nsLookup (add_tenvE tenvE tenv.v) n = some (targs.length, t) := by
    unfold lookup_var at h1
    cases n with
    | Long mn id =>
      simp only [lookup_varE] at h1
      exact nsLookup_add_tenvE3 _ _ _ _ _ _ h1
    | Short x =>
      simp only [lookup_varE, Aux.tveLookup_bind_tvar] at h1
      cases hl : tveLookup x (0 + tvs) tenvE with
      | some p =>
        rw [hl] at h1
        cases h1
        exact nsLookup_add_tenvE1 _ _ _ _ _ _ ⟨tveLookup_freevars _ _ _ _ _ ⟨h3, h4, hl⟩, hl⟩
      | none =>
        rw [hl] at h1
        exact nsLookup_add_tenvE2 _ _ _ _ _ _ ⟨hl, h1⟩
  obtain ⟨v, hv, ht⟩ := nsAll2_nsLookup2 _ _ _ _ _ ⟨hlk, h7⟩
  have ht : type_v targs.length ctMap tenvS v t := ht
  exact ⟨v, hv, type_subst_thm targs tvs _ _ _ _ _ ht
    ⟨rfl, h2, h5, type_v_freevars _ _ _ _ _ ht⟩⟩

/- HOL4:
Theorem EVERY_REPLICATE:
  EVERY (\x. type_v tvs ctMap tenv x t') vs =
  EVERY (\x. type_v tvs ctMap tenv (FST x) (SND x)) (ZIP (vs, REPLICATE (LENGTH vs) t')) -/
theorem EVERY_REPLICATE (tvs : Nat) (ctMap : ctMap_ty) (tenv : tenv_store) (t' : typ)
    (vs : List value) :
    EVERY (fun x => type_v tvs ctMap tenv x t') vs ↔
    EVERY (fun x => type_v tvs ctMap tenv x.1 x.2)
      (vs.zip (List.replicate vs.length t')) := by
  induction vs with
  | nil => exact Iff.rfl
  | cons a vs ih =>
    simp only [EVERY, List.length_cons, List.replicate_succ, List.zip_cons_cons, ih]

/- HOL4:
Theorem EVERY_LIST_REL:
  EVERY (\ v. type_v n ctMap tenvS v t) vs =
  LIST_REL (type_v n ctMap tenvS) vs (REPLICATE (LENGTH vs) t)
(the second theorem of this name in the theory) -/
theorem EVERY_LIST_REL_2 (n : Nat) (ctMap : ctMap_ty) (tenvS : tenv_store) (t : typ)
    (vs : List value) :
    EVERY (fun v => type_v n ctMap tenvS v t) vs ↔
    LIST_REL (type_v n ctMap tenvS) vs (List.replicate vs.length t) :=
  EVERY_LIST_REL (fun v t => type_v n ctMap tenvS v t) t vs

/-- What a well-typed evaluation may return. -/
def Aux.ER (ctMap : ctMap_ty) (tenvS' : tenv_store) (r : result (List value) value)
    (V : List value → Prop) : Prop :=
  match r with
  | Rval vs => V vs
  | Rerr e =>
    match e with
    | Rraise v => type_v 0 ctMap tenvS' v Texn
    | Rabort a =>
      match a with
      | Rtype_error => False
      | Rtimeout_error => True
      | Rffi_error _ => True

def Aux.EG {ffi : Type} (ctMap : ctMap_ty) (tenvS : tenv_store) (s s' : state ffi)
    (r : result (List value) value) (V : tenv_store → List value → Prop) : Prop :=
  ∃ tenvS' : tenv_store, type_s ctMap s'.refs tenvS' ∧ store_type_extension tenvS tenvS' ∧
    s'.next_type_stamp = s.next_type_stamp ∧ s'.next_exn_stamp = s.next_exn_stamp ∧
    Aux.ER ctMap tenvS' r (V tenvS')

theorem Aux.EG_err {ffi : Type} {ctMap : ctMap_ty} {tenvS : tenv_store} {s s' : state ffi}
    {e : error_result value} {V V' : tenv_store → List value → Prop}
    (h : Aux.EG ctMap tenvS s s' (Rerr e) V) : Aux.EG ctMap tenvS s s' (Rerr e) V' := by
  obtain ⟨S, h1, h2, h3, h4, h5⟩ := h
  refine ⟨S, h1, h2, h3, h4, ?_⟩
  rcases e with v | a
  · exact h5
  · cases a <;> exact h5

theorem Aux.EG_mono {ffi : Type} {ctMap : ctMap_ty} {tenvS : tenv_store} {s s' : state ffi}
    {r : result (List value) value} {V V' : tenv_store → List value → Prop}
    (h : Aux.EG ctMap tenvS s s' r V) (hV : ∀ S vs, r = Rval vs → V S vs → V' S vs) :
    Aux.EG ctMap tenvS s s' r V' := by
  cases r with
  | Rerr e => exact Aux.EG_err h
  | Rval vs =>
    obtain ⟨S, h1, h2, h3, h4, h5⟩ := h
    exact ⟨S, h1, h2, h3, h4, hV S vs rfl h5⟩

theorem Aux.EG_trans {ffi : Type} {ctMap : ctMap_ty} {tenvS tenvS1 : tenv_store}
    {s s1 s' : state ffi} {r : result (List value) value} {V : tenv_store → List value → Prop}
    (h1 : store_type_extension tenvS tenvS1) (h2 : s1.next_type_stamp = s.next_type_stamp)
    (h3 : s1.next_exn_stamp = s.next_exn_stamp) (h : Aux.EG ctMap tenvS1 s1 s' r V) :
    Aux.EG ctMap tenvS s s' r V := by
  obtain ⟨S, a1, a2, a3, a4, a5⟩ := h
  exact ⟨S, a1, store_type_extension_trans _ _ _ ⟨h1, a2⟩, a3.trans h2, a4.trans h3, a5⟩

theorem Aux.EG_here {ffi : Type} {ctMap : ctMap_ty} {tenvS : tenv_store} {s : state ffi}
    {r : result (List value) value} {V : tenv_store → List value → Prop}
    (h : type_s ctMap s.refs tenvS) (hr : Aux.ER ctMap tenvS r (V tenvS)) :
    Aux.EG ctMap tenvS s s r V :=
  ⟨tenvS, h, store_type_extension_refl _, rfl, rfl, hr⟩

theorem Aux.es1 {tenv : type_env} {tenvE : tenv_val_exp} {e : exp} {t : typ}
    (h : type_e tenv tenvE e t) : type_es tenv tenvE [e] [t] :=
  type_es.cons _ _ _ _ _ _ h (type_es.nil _ _)

theorem Aux.es1_inv {tenv : type_env} {tenvE : tenv_val_exp} {e : exp} {ts : List typ}
    (h : type_es tenv tenvE [e] ts) : ∃ t, ts = [t] ∧ type_e tenv tenvE e t := by
  cases h with
  | cons _ _ _ t ts h1 h2 =>
    cases h2
    exact ⟨t, rfl, h1⟩

theorem Aux.tvs0 {tvs : Nat} {e : exp} (hv : tvs ≠ 0 → EVERY is_value [e])
    (hn : ¬ is_value e) : tvs = 0 := by
  apply Classical.byContradiction
  intro h
  exact hn (hv h).1

theorem Aux.env_weak {ctMap : ctMap_ty} {tenvS tenvS' : tenv_store} {env : sem_env value}
    {tenv : type_env} (h : store_type_extension tenvS tenvS')
    (ha : type_all_env ctMap tenvS env tenv) : type_all_env ctMap tenvS' env tenv :=
  type_all_env_weakening _ _ _ _ _ _ ⟨weakCT_refl _, store_type_extension_weakS _ _ h, ha⟩

theorem Aux.v_weak {ctMap : ctMap_ty} {tenvS tenvS' : tenv_store} {tvs : Nat} {v : value}
    {t : typ} (h : store_type_extension tenvS tenvS') (hv : type_v tvs ctMap tenvS v t) :
    type_v tvs ctMap tenvS' v t :=
  type_v_weakening _ _ _ _ _ hv _ _ _ ⟨Or.inr rfl, weakCT_refl _,
    store_type_extension_weakS _ _ h⟩

theorem Aux.can_pmatch {ctMap : ctMap_ty} {tenvS : tenv_store} {env : sem_env value}
    {tenv : type_env} {tenvE : tenv_val_exp} {refs : List (store_v value)} {tvs k : Nat}
    {v : value} {pes : List (pat × exp)} {t1 t2 : typ} (hok : ctMap_ok ctMap)
    (hc : nsAll2 (type_ctor ctMap) env.c tenv.c) (hs : type_s ctMap refs tenvS)
    (hv : type_v tvs ctMap tenvS v t1) (hp : type_pes tvs k tenv tenvE pes t1 t2) :
    can_pmatch_all env.c refs (pes.map Prod.fst) v := by
  rw [can_pmatch_all_EVERY, EVERY_iff_forall]
  intro p hm0
  obtain ⟨⟨p', e⟩, hm, rfl⟩ := List.mem_map.mp hm0
  obtain ⟨b, -, h1, -⟩ := hp _ _ hm
  rcases pat_type_sound.1 env.c refs p' v [] tenv ctMap [] t1 b tenvS tvs
    ⟨hok, hc, hv, h1, hs, trivial⟩ with h | ⟨b', h, -⟩ <;> rw [h] <;> simp

theorem Aux.exp_sound {ffi : Type} (ctMap : ctMap_ty) (hg : good_ctMap ctMap) :
    (∀ (s : state ffi) (env : sem_env value) (es : List exp) (r : result (List value) value)
        (s' : state ffi) (tenv : type_env) (tenvE : tenv_val_exp) (ts : List typ) (tvs : Nat)
        (tenvS : tenv_store),
      evaluate s env es = (s', r) → tenv_ok tenv → tenv_val_exp_ok tenvE → num_tvs tenvE = 0 →
      type_all_env ctMap tenvS env { tenv with v := add_tenvE tenvE tenv.v } →
      type_s ctMap s.refs tenvS → (tvs ≠ 0 → EVERY is_value es) →
      type_es tenv (bind_tvar tvs tenvE) es ts →
      Aux.EG ctMap tenvS s s' r (fun S vs => LIST_REL (type_v tvs ctMap S) vs ts)) ∧
    (∀ (s : state ffi) (env : sem_env value) (v : value) (pes : List (pat × exp))
        (err_v : value) (r : result (List value) value) (s' : state ffi) (tenv : type_env)
        (tenvE : tenv_val_exp) (t1 t2 : typ) (tvs : Nat) (tenvS : tenv_store),
      evaluate_match s env v pes err_v = (s', r) → tenv_ok tenv → tenv_val_exp_ok tenvE →
      num_tvs tenvE = 0 →
      type_all_env ctMap tenvS env { tenv with v := add_tenvE tenvE tenv.v } →
      type_s ctMap s.refs tenvS → type_v tvs ctMap tenvS v t1 → type_v 0 ctMap tenvS err_v Texn →
      type_pes tvs tvs tenv tenvE pes t1 t2 →
      Aux.EG ctMap tenvS s s' r (fun S vs => type_v tvs ctMap S (HD vs) t2)) := by
  obtain ⟨hok, hb, hex, hlist⟩ := id hg
  have H := Aux.eval_induct (ffi := ffi)
    (P := fun s env es => ∀ (r : result (List value) value)
        (s' : state ffi) (tenv : type_env) (tenvE : tenv_val_exp) (ts : List typ) (tvs : Nat)
        (tenvS : tenv_store),
      evaluate s env es = (s', r) → tenv_ok tenv → tenv_val_exp_ok tenvE → num_tvs tenvE = 0 →
      type_all_env ctMap tenvS env { tenv with v := add_tenvE tenvE tenv.v } →
      type_s ctMap s.refs tenvS → (tvs ≠ 0 → EVERY is_value es) →
      type_es tenv (bind_tvar tvs tenvE) es ts →
      Aux.EG ctMap tenvS s s' r (fun S vs => LIST_REL (type_v tvs ctMap S) vs ts))
    (Q := fun s env v pes err_v => ∀ (r : result (List value) value) (s' : state ffi)
        (tenv : type_env) (tenvE : tenv_val_exp) (t1 t2 : typ) (tvs : Nat) (tenvS : tenv_store),
      evaluate_match s env v pes err_v = (s', r) → tenv_ok tenv → tenv_val_exp_ok tenvE →
      num_tvs tenvE = 0 →
      type_all_env ctMap tenvS env { tenv with v := add_tenvE tenvE tenv.v } →
      type_s ctMap s.refs tenvS → type_v tvs ctMap tenvS v t1 → type_v 0 ctMap tenvS err_v Texn →
      type_pes tvs tvs tenv tenvE pes t1 t2 →
      Aux.EG ctMap tenvS s s' r (fun S vs => type_v tvs ctMap S (HD vs) t2))
    (D := fun _ _ _ => True)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact ⟨H.1, H.2.1⟩
  · -- []
    intro st env r s' tenv tenvE ts tvs tenvS he h1 h2 h3 ha hs hv ht
    rw [evaluate] at he
    cases he
    cases ht
    exact Aux.EG_here hs trivial
  · -- e1 :: e2 :: es
    intro st env e1 e2 es ih1 ih2 r s' tenv tenvE ts tvs tenvS he h1 h2 h3 ha hs hv ht
    obtain ⟨t, ts, rfl, ht1, ht2⟩ : ∃ t ts', ts = t :: ts' ∧
        type_e tenv (bind_tvar tvs tenvE) e1 t ∧
        type_es tenv (bind_tvar tvs tenvE) (e2 :: es) ts' := by
      cases ht with
      | cons _ _ _ t ts h1 h2 => exact ⟨t, ts, rfl, h1, h2⟩
    rw [Aux.evaluate_cons] at he
    split at he
    · rename_i st1 v1 he1
      obtain ⟨S1, b1, b2, b3, b4, b5⟩ := ih1 _ _ tenv tenvE [t] tvs tenvS he1 h1 h2 h3 ha hs
        (fun h => ⟨(hv h).1, trivial⟩) (Aux.es1 ht1)
      obtain ⟨x, rfl, hx⟩ := Aux.LR1 (R := type_v tvs ctMap S1) b5
      have hcl := evaluate_clock.1 _ _ _ _ _ he1
      have I2 := fun r s' he2 => ih2 st1 hcl r s' tenv tenvE ts tvs S1 he2 h1 h2 h3
        (Aux.env_weak b2 ha) b1 (fun h => (hv h).2) ht2
      split at he
      · rename_i he2
        cases he
        obtain ⟨S2, c1, c2, c3, c4, c5⟩ := I2 _ _ he2
        exact ⟨S2, c1, store_type_extension_trans _ _ _ ⟨b2, c2⟩, c3.trans b3, c4.trans b4,
          Aux.v_weak c2 hx, c5⟩
      · rename_i he2
        cases he
        exact Aux.EG_trans b2 b3 b4 (Aux.EG_err (I2 _ _ he2))
    · rename_i he1
      cases he
      exact Aux.EG_err (ih1 _ _ tenv tenvE [t] tvs tenvS he1 h1 h2 h3 ha hs
        (fun h => ⟨(hv h).1, trivial⟩) (Aux.es1 ht1))
  · -- Lit
    intro st env l r s' tenv tenvE ts tvs tenvS he h1 h2 h3 ha hs hv htt
    obtain ⟨t, rfl, ht⟩ := Aux.es1_inv htt
    rw [evaluate] at he
    cases he
    refine Aux.EG_here hs ⟨?_, trivial⟩
    cases ht with
    | intLit => exact type_v.intLit _ _ _ _
    | char => exact type_v.char _ _ _ _
    | strLit => exact type_v.strLit _ _ _ _
    | word8 => exact type_v.word8 _ _ _ _
    | word64 => exact type_v.word64 _ _ _ _
    | float64 => exact type_v.float64 _ _ _ _
  · -- Raise
    intro st env e ih r s' tenv tenvE ts tvs tenvS he h1 h2 h3 ha hs hv htt
    obtain ⟨t, rfl, ht⟩ := Aux.es1_inv htt
    have htv := Aux.tvs0 hv (by simp [is_value])
    subst htv
    obtain ⟨-, ht⟩ : _ ∧ type_e tenv (bind_tvar 0 tenvE) e Texn := by
      cases ht with
      | raise _ _ _ a b => exact ⟨a, b⟩
    rw [evaluate] at he
    split at he
    · rename_i he1
      cases he
      obtain ⟨S1, b1, b2, b3, b4, b5⟩ := ih _ _ tenv tenvE [Texn] 0 tenvS he1 h1 h2 h3 ha hs
        (fun h => absurd rfl h) (Aux.es1 ht)
      obtain ⟨x, rfl, hx⟩ := Aux.LR1 (R := type_v 0 ctMap S1) b5
      exact ⟨S1, b1, b2, b3, b4, hx⟩
    · rename_i he1
      cases he
      exact Aux.EG_err (ih _ _ tenv tenvE [Texn] 0 tenvS he1 h1 h2 h3 ha hs
        (fun h => absurd rfl h) (Aux.es1 ht))
  · -- Handle
    intro st env e pes ih1 ih2 r s' tenv tenvE ts tvs tenvS he h1 h2 h3 ha hs hv htt
    obtain ⟨t, rfl, ht⟩ := Aux.es1_inv htt
    have htv := Aux.tvs0 hv (by simp [is_value])
    subst htv
    obtain ⟨hte, hne, hpes⟩ := type_e_Handle_inv_aux _ _ _ _ _ ht
    rw [bind_tvar0, h3] at hpes
    have I1 := fun r s' he1 => ih1 r s' tenv tenvE [t] 0 tenvS he1 h1 h2 h3 ha hs
      (fun h => absurd rfl h) (Aux.es1 hte)
    rw [Aux.evaluate_Handle] at he
    split at he
    · rename_i he1
      cases he
      exact I1 _ _ he1
    · rename_i st1 v he1
      obtain ⟨S1, b1, b2, b3, b4, b5⟩ := I1 _ _ he1
      have b5 : type_v 0 ctMap S1 v Texn := b5
      have hcl := evaluate_clock.1 _ _ _ _ _ he1
      have ha' := Aux.env_weak b2 ha
      rw [if_pos (Aux.can_pmatch (tenv := tenv) (tenvE := tenvE) (k := 0) (t2 := t) hok ha'.1 b1 b5
        hpes)] at he
      refine Aux.EG_trans b2 b3 b4 (Aux.EG_mono
        (ih2 st1 v hcl r s' tenv tenvE Texn t 0 S1 he h1 h2 h3 ha' b1 b5 b5 hpes)
        (fun S vs hr hV => ?_))
      subst hr
      obtain ⟨x, rfl⟩ := Aux.len1 (evaluate_length.2.1 _ _ _ _ _ _ _ he)
      exact ⟨hV, trivial⟩
    · rename_i he1
      cases he
      exact Aux.EG_err (I1 _ _ he1)
  · -- Con
    intro st env cn es ih r s' tenv tenvE ts tvs tenvS he h1 h2 h3 ha hs hv htt
    obtain ⟨t, rfl, ht⟩ := Aux.es1_inv htt
    have hv' : tvs ≠ 0 → EVERY is_value es.reverse := by
      intro h
      have := (hv h).1
      simp only [is_value] at this
      exact Aux.EVERY_reverse.mpr this
    have I1 := fun ts' (hes : type_es tenv (bind_tvar tvs tenvE) es ts') r s' he1 =>
      ih r s' tenv tenvE ts'.reverse tvs tenvS he1 h1 h2 h3 ha hs hv'
        ((type_es_list_rel _ _ _ _).mpr
          (Aux.LIST_REL_reverse ((type_es_list_rel _ _ _ _).mp hes)))
    rw [evaluate] at he
    cases ht with
    | con _ cn es tvs' tn ts' ts hc hl hes hlk =>
      obtain ⟨⟨n, stamp⟩, hcv, hcf, hcn⟩ := nsAll2_nsLookup2 _ _ _ _ _ ⟨hlk, ha.1⟩
      have hcn : ts.length = n := hcn
      have hlen : es.length = n := by
        rw [type_es_length _ _ _ _ hes, List.length_map, hcn]
      have hck : do_con_check env.c (some cn) es.length := by
        simp only [do_con_check, hcv, hlen]
      rw [if_pos hck] at he
      split at he
      · rename_i st1 vs he1
        obtain ⟨S1, b1, b2, b3, b4, b5⟩ := I1 _ hes _ _ he1
        have ha' := Aux.env_weak b2 ha
        obtain ⟨v, hbv, hvt⟩ := build_conv_type_sound env.c cn vs tvs ts ctMap S1 ts' tn tenv.c
          tvs' tenvE es.length ⟨ha'.1, hck, h3, hc, hl, b5, hlk⟩
        rw [hbv] at he
        cases he
        exact ⟨S1, b1, b2, b3, b4, hvt, trivial⟩
      · rename_i he1
        cases he
        exact Aux.EG_err (I1 _ hes _ _ he1)
    | tup _ es ts hes =>
      have hck : do_con_check env.c none es.length := trivial
      rw [if_pos hck] at he
      split at he
      · rename_i st1 vs he1
        obtain ⟨S1, b1, b2, b3, b4, b5⟩ := I1 _ hes _ _ he1
        simp only [build_conv] at he
        cases he
        exact ⟨S1, b1, b2, b3, b4,
          type_v_tup_aux _ _ _ _ _ (Aux.LIST_REL_reverse_iff.mpr b5), trivial⟩
      · rename_i he1
        cases he
        exact Aux.EG_err (I1 _ hes _ _ he1)
  · -- Var
    intro st env n r s' tenv tenvE ts tvs tenvS he h1 h2 h3 ha hs hv htt
    obtain ⟨t, rfl, ht⟩ := Aux.es1_inv htt
    rw [evaluate] at he
    cases ht with
    | var _ _ t targs tvs0 htv hc hlk =>
      subst htv
      rw [Aux.num_tvs_bind_tvar, h3, Nat.add_zero] at hc
      obtain ⟨v, hvl, hvt⟩ := lookup_var_sound n tvs tenvE targs t ctMap tenvS env tenv
        ⟨hlk, hok, h2, h3, hc, ha⟩
      rw [hvl] at he
      cases he
      exact Aux.EG_here hs ⟨hvt, trivial⟩
  · -- Fun
    intro st env x e r s' tenv tenvE ts tvs tenvS he h1 h2 h3 ha hs hv htt
    obtain ⟨t, rfl, ht⟩ := Aux.es1_inv htt
    rw [evaluate] at he
    cases he
    cases ht with
    | fn _ _ _ t1 t2 hc he =>
      rw [Aux.num_tvs_bind_tvar, h3, Nat.add_zero] at hc
      exact Aux.EG_here hs ⟨type_v_closure_aux _ _ _ _ tenv tenvE _ _ _ _ h1 h2 h3 ha.1 ha.2 hc he,
        trivial⟩
  · -- App
    intro st env o es ih1 ih2 ih3 r s' tenv tenvE ts tvs tenvS he h1 h2 h3 ha hs hv htt
    obtain ⟨t, rfl, ht⟩ := Aux.es1_inv htt
    have htv := Aux.tvs0 hv (by simp [is_value])
    subst htv
    obtain ⟨ts, hes, hop, hck⟩ : ∃ ts, type_es tenv (bind_tvar 0 tenvE) es ts ∧ type_op o ts t ∧
        check_freevars (num_tvs (bind_tvar 0 tenvE)) [] t := by
      cases ht with
      | app _ _ _ ts _ a b c => exact ⟨ts, a, b, c⟩
    rw [bind_tvar0, h3] at hck
    have I1 := fun r s' he1 =>
      ih1 r s' tenv tenvE ts.reverse 0 tenvS he1 h1 h2 h3 ha hs (fun h => absurd rfl h)
        ((type_es_list_rel _ _ _ _).mpr
          (Aux.LIST_REL_reverse ((type_es_list_rel _ _ _ _).mp hes)))
    rw [Aux.evaluate_App] at he
    split at he
    · rename_i st1 vs he1
      obtain ⟨S1, b1, b2, b3, b4, b5⟩ := I1 _ _ he1
      have b5 : LIST_REL (type_v 0 ctMap S1) vs ts.reverse := b5
      have hcl := evaluate_clock.1 _ _ _ _ _ he1
      cases ho : getOpClass o with
      | FunApp =>
        rw [ho] at he
        have ho' : o = Opapp := by
          cases o <;> simp [getOpClass] at ho ⊢
          split at ho <;> simp at ho
        subst ho'
        obtain ⟨env2, e2, tenv2, tenvE2, c1, c2, c3, c4, c5, c6⟩ :=
          opapp_type_sound ctMap S1 vs.reverse ts t
            ⟨hok, hop, Aux.LIST_REL_reverse_iff.mpr b5⟩
        dsimp only at he
        rw [c6] at he
        dsimp only at he
        split at he
        · cases he
          exact ⟨S1, b1, b2, b3, b4, trivial⟩
        · refine Aux.EG_trans b2 b3 b4 ?_
          exact ih2 (dec_clock st1) env2 e2 (by simp only [dec_clock]; omega) r s' tenv2 tenvE2 [t]
            0 S1 he c1 c2 c3 c4 b1 (fun h => absurd rfl h)
            (Aux.es1 (by rw [bind_tvar0]; exact c5))
      | Force =>
        exfalso
        rw [type_op_cases] at hop
        cases o <;> simp [getOpClass] at ho hop
      | EvalOp =>
        exfalso
        rw [type_op_cases] at hop
        cases o <;> simp [getOpClass] at ho hop
      | Simple =>
        rw [ho] at he
        have ho' : o ≠ Opapp := by rintro rfl; simp [getOpClass] at ho
        obtain ⟨S2, store', ffi', rr, c1, c2, c3, c4⟩ := op_type_sound ctMap S1 vs o ts t
          st1.refs st1.ffi ⟨hg, ho', b1, hop, hck, b5⟩
        dsimp only at he
        rw [c3] at he
        cases he
        refine ⟨S2, c2, store_type_extension_trans _ _ _ ⟨b2, c1⟩, b3, b4, ?_⟩
        rcases rr with v | v | a
        · exact ⟨c4, trivial⟩
        · exact c4
        · cases a
          · exact c4
          · exact trivial
          · exact trivial
    · rename_i he1
      cases he
      exact Aux.EG_err (I1 _ _ he1)
  · -- Log
    intro st env l e1 e2 ih1 ih2 r s' tenv tenvE ts tvs tenvS he h1 h2 h3 ha hs hv htt
    obtain ⟨t, rfl, ht⟩ := Aux.es1_inv htt
    have htv := Aux.tvs0 hv (by simp [is_value])
    subst htv
    obtain ⟨rfl, ht1, ht2⟩ : t = Tbool ∧ type_e tenv (bind_tvar 0 tenvE) e1 Tbool ∧
        type_e tenv (bind_tvar 0 tenvE) e2 Tbool := by
      cases ht with
      | log _ _ _ _ a b => exact ⟨rfl, a, b⟩
    have I1 := fun r s' he1 => ih1 r s' tenv tenvE [Tbool] 0 tenvS he1 h1 h2 h3 ha hs
      (fun h => absurd rfl h) (Aux.es1 ht1)
    rw [Aux.evaluate_Log] at he
    split at he
    · rename_i st1 vs he1
      obtain ⟨S1, b1, b2, b3, b4, b5⟩ := I1 _ _ he1
      obtain ⟨x, rfl, hx⟩ := Aux.LR1 (R := type_v 0 ctMap S1) b5
      have hcl := evaluate_clock.1 _ _ _ _ _ he1
      obtain ⟨b, rfl⟩ := Aux.bool_cases hx hok hb
      have key : do_log l (Boolv b) e2 = some (Exp e2) ∨
          do_log l (Boolv b) e2 = some (Val (Boolv b)) := by
        cases l <;> cases b <;> simp [do_log, Boolv_11]
      have hHD : HD [Boolv b] = Boolv b := rfl
      rw [hHD] at he
      rcases key with hk | hk
      · rw [hk] at he
        refine Aux.EG_trans b2 b3 b4 ?_
        exact ih2 st1 hcl r s' tenv tenvE [Tbool] 0 S1 he h1 h2 h3 (Aux.env_weak b2 ha) b1
          (fun h => absurd rfl h) (Aux.es1 ht2)
      · rw [hk] at he
        cases he
        exact ⟨S1, b1, b2, b3, b4, hx, trivial⟩
    · rename_i he1
      cases he
      exact Aux.EG_err (I1 _ _ he1)
  · -- If
    intro st env e1 e2 e3 ih1 ih2 ih3 r s' tenv tenvE ts tvs tenvS he h1 h2 h3 ha hs hv htt
    obtain ⟨t, rfl, ht⟩ := Aux.es1_inv htt
    have htv := Aux.tvs0 hv (by simp [is_value])
    subst htv
    obtain ⟨ht1, ht2, ht3⟩ : type_e tenv (bind_tvar 0 tenvE) e1 Tbool ∧
        type_e tenv (bind_tvar 0 tenvE) e2 t ∧ type_e tenv (bind_tvar 0 tenvE) e3 t := by
      cases ht with
      | if' _ _ _ _ _ a b c => exact ⟨a, b, c⟩
    have I1 := fun r s' he1 => ih1 r s' tenv tenvE [Tbool] 0 tenvS he1 h1 h2 h3 ha hs
      (fun h => absurd rfl h) (Aux.es1 ht1)
    rw [Aux.evaluate_If] at he
    split at he
    · rename_i st1 vs he1
      obtain ⟨S1, b1, b2, b3, b4, b5⟩ := I1 _ _ he1
      obtain ⟨x, rfl, hx⟩ := Aux.LR1 (R := type_v 0 ctMap S1) b5
      have hcl := evaluate_clock.1 _ _ _ _ _ he1
      obtain ⟨b, rfl⟩ := Aux.bool_cases hx hok hb
      have hHD : HD [Boolv b] = Boolv b := rfl
      rw [hHD] at he
      refine Aux.EG_trans b2 b3 b4 ?_
      cases b with
      | true =>
        have hk : do_if (Boolv true) e2 e3 = some e2 := by simp [do_if]
        rw [hk] at he
        exact ih2 st1 hcl r s' tenv tenvE [t] 0 S1 he h1 h2 h3 (Aux.env_weak b2 ha) b1
          (fun h => absurd rfl h) (Aux.es1 ht2)
      | false =>
        have hk : do_if (Boolv false) e2 e3 = some e3 := by simp [do_if, Boolv_11]
        rw [hk] at he
        exact ih3 st1 hcl r s' tenv tenvE [t] 0 S1 he h1 h2 h3 (Aux.env_weak b2 ha) b1
          (fun h => absurd rfl h) (Aux.es1 ht3)
    · rename_i he1
      cases he
      exact Aux.EG_err (I1 _ _ he1)
  · -- Mat
    intro st env e pes ih1 ih2 r s' tenv tenvE ts tvs tenvS he h1 h2 h3 ha hs hv htt
    obtain ⟨t, rfl, ht⟩ := Aux.es1_inv htt
    have htv := Aux.tvs0 hv (by simp [is_value])
    subst htv
    obtain ⟨t1, hte, hne, hpes⟩ := type_e_Mat_inv_aux _ _ _ _ _ ht
    rw [bind_tvar0, h3] at hpes
    have I1 := fun r s' he1 => ih1 r s' tenv tenvE [t1] 0 tenvS he1 h1 h2 h3 ha hs
      (fun h => absurd rfl h) (Aux.es1 hte)
    rw [Aux.evaluate_Mat] at he
    split at he
    · rename_i st1 vs he1
      obtain ⟨S1, b1, b2, b3, b4, b5⟩ := I1 _ _ he1
      obtain ⟨x, rfl, hx⟩ := Aux.LR1 (R := type_v 0 ctMap S1) b5
      have hcl := evaluate_clock.1 _ _ _ _ _ he1
      have ha' := Aux.env_weak b2 ha
      have hHD : HD [x] = x := rfl
      rw [hHD, if_pos (Aux.can_pmatch (tenv := tenv) (tenvE := tenvE) (k := 0) (t2 := t) hok ha'.1
        b1 hx hpes)] at he
      refine Aux.EG_trans b2 b3 b4 (Aux.EG_mono
        (ih2 st1 x hcl r s' tenv tenvE t1 t 0 S1 he h1 h2 h3 ha' b1 hx
          (type_v_exn 0 ctMap S1 hex).2.2.1 hpes)
        (fun S vs hr hV => ?_))
      subst hr
      obtain ⟨x, rfl⟩ := Aux.len1 (evaluate_length.2.1 _ _ _ _ _ _ _ he)
      exact ⟨hV, trivial⟩
    · rename_i he1
      cases he
      exact Aux.EG_err (I1 _ _ he1)
  · -- Let
    intro st env xo e1 e2 ih1 ih2 r s' tenv tenvE ts tvs tenvS he h1 h2 h3 ha hs hv htt
    obtain ⟨t, rfl, ht⟩ := Aux.es1_inv htt
    have htv := Aux.tvs0 hv (by simp [is_value])
    subst htv
    obtain ⟨t1, ht1, ht2⟩ : ∃ t1, type_e tenv (bind_tvar 0 tenvE) e1 t1 ∧
        type_e tenv (opt_bind_name xo 0 t1 (bind_tvar 0 tenvE)) e2 t := by
      cases ht with
      | let' _ _ _ _ t1 _ a b => exact ⟨t1, a, b⟩
    rw [bind_tvar0] at ht2
    have I1 := fun r s' he1 => ih1 r s' tenv tenvE [t1] 0 tenvS he1 h1 h2 h3 ha hs
      (fun h => absurd rfl h) (Aux.es1 ht1)
    rw [Aux.evaluate_Let] at he
    split at he
    · rename_i st1 vs he1
      obtain ⟨S1, b1, b2, b3, b4, b5⟩ := I1 _ _ he1
      obtain ⟨x, rfl, hx⟩ := Aux.LR1 (R := type_v 0 ctMap S1) b5
      have hcl := evaluate_clock.1 _ _ _ _ _ he1
      have ha' := Aux.env_weak b2 ha
      have hHD : HD [x] = x := rfl
      rw [hHD] at he
      refine Aux.EG_trans b2 b3 b4 ?_
      cases xo with
      | none =>
        exact ih2 st1 _ hcl r s' tenv tenvE [t] 0 S1 he h1 h2 h3 ha' b1 (fun h => absurd rfl h)
          (Aux.es1 (by rw [bind_tvar0]; exact ht2))
      | some n =>
        refine ih2 st1 _ hcl r s' tenv (Bind_name n 0 t1 tenvE) [t] 0 S1 he h1 ⟨?_, h2⟩ h3
          ⟨ha'.1, nsAll2_nsBind _ _ _ _ _ _ ⟨hx, ha'.2⟩⟩ b1 (fun h => absurd rfl h)
          (Aux.es1 (by rw [bind_tvar0]; exact ht2))
        rw [h3]
        exact type_v_freevars _ _ _ _ _ hx
    · rename_i he1
      cases he
      exact Aux.EG_err (I1 _ _ he1)
  · -- Letrec
    intro st env funs e ih r s' tenv tenvE ts tvs tenvS he h1 h2 h3 ha hs hv htt
    obtain ⟨t, rfl, ht⟩ := Aux.es1_inv htt
    have htv := Aux.tvs0 hv (by simp [is_value])
    subst htv
    obtain ⟨bindings, hf, ht⟩ : ∃ bindings,
        type_funs tenv (bind_var_list 0 bindings (bind_tvar 0 tenvE)) funs bindings ∧
        type_e tenv (bind_var_list 0 bindings (bind_tvar 0 tenvE)) e t := by
      cases ht with
      | letrec _ _ _ _ bindings a b => exact ⟨bindings, a, b⟩
    have hd := type_funs_distinct _ _ _ _ hf
    rw [evaluate, if_pos hd] at he
    have hrec := Aux.type_rec_env (envV := env.v) (tenvV := add_tenvE tenvE tenv.v) h1 ha
      h2 h3 hf (nsAll2_mono (fun i v p h => h) ha.2)
    have hok2 := tenv_val_exp_ok_bvl_funs _ _ _ _ () _ ⟨hf, (Aux.ok_bind_tvar 0 tenvE).mpr h2⟩
    rw [bind_tvar0] at hok2 ht
    refine ih _ r s' tenv (bind_var_list 0 bindings tenvE) [t] 0 tenvS he h1 hok2
      (by rw [num_tvs_bind_var_list, h3]) ⟨ha.1, ?_⟩ hs (fun h => absurd rfl h)
      (Aux.es1 (by rw [bind_tvar0]; exact ht))
    rw [add_tenvE_bvl]
    exact nsAll2_mono (fun i v p h => h) hrec
  · -- Tannot
    intro st env e t0 ih r s' tenv tenvE ts tvs tenvS he h1 h2 h3 ha hs hv htt
    obtain ⟨t, rfl, ht⟩ := Aux.es1_inv htt
    rw [evaluate] at he
    have ht' : type_e tenv (bind_tvar tvs tenvE) e t := by
      cases ht with
      | tannot _ _ _ _ _ a => exact a
    refine ih r s' tenv tenvE [t] tvs tenvS he h1 h2 h3 ha hs (fun h => ?_) (Aux.es1 ht')
    have := (hv h).1
    simp only [is_value] at this
    exact ⟨this, trivial⟩
  · -- Lannot
    intro st env e t0 ih r s' tenv tenvE ts tvs tenvS he h1 h2 h3 ha hs hv htt
    obtain ⟨t, rfl, ht⟩ := Aux.es1_inv htt
    rw [evaluate] at he
    have ht' : type_e tenv (bind_tvar tvs tenvE) e t := by
      cases ht with
      | lannot _ _ _ _ a => exact a
    refine ih r s' tenv tenvE [t] tvs tenvS he h1 h2 h3 ha hs (fun h => ?_) (Aux.es1 ht')
    have := (hv h).1
    simp only [is_value] at this
    exact ⟨this, trivial⟩
  · -- match []
    intro st env v err r s' tenv tenvE t1 t2 tvs tenvS he h1 h2 h3 ha hs hv herr hp
    rw [evaluate_match] at he
    cases he
    exact Aux.EG_here hs herr
  · -- match cons
    intro st env v p e pes err ih1 ih2 r s' tenv tenvE t1 t2 tvs tenvS he h1 h2 h3 ha hs hv herr hp
    obtain ⟨bs, hd, hpt, het⟩ := hp p e List.mem_cons_self
    rw [evaluate_match, if_pos hd] at he
    rcases pat_type_sound.1 env.c st.refs p v [] tenv ctMap [] t1 bs tenvS tvs
      ⟨hok, ha.1, hv, hpt, hs, trivial⟩ with hm | ⟨bs', hm, hbs⟩
    · rw [hm] at he
      exact ih1 r s' tenv tenvE t1 t2 tvs tenvS he h1 h2 h3 ha hs hv herr
        (fun p e hm => hp p e (List.mem_cons_of_mem _ hm))
    · rw [hm] at he
      dsimp only at he
      rw [List.append_nil] at hbs
      have hok2 := type_p_bvl.1 _ _ _ _ _ hpt _ h2
      refine Aux.EG_mono (ih2 _ r s' tenv (bind_var_list tvs bs tenvE) [t2] 0 tenvS he h1 hok2
        (by rw [num_tvs_bind_var_list, h3]) ⟨ha.1, ?_⟩ hs (fun h => absurd rfl h)
        (Aux.es1 (by rw [bind_tvar0]; exact het))) (fun S vs hr hV => ?_)
      · rw [add_tenvE_bvl]
        dsimp only
        rw [nsAppend_to_nsBindList]
        refine nsAll2_nsBindList _ _ _ _ _ ⟨?_, ha.2⟩
        rw [← List.map_id bs', Aux.LIST_REL_map]
        refine Aux.LIST_REL_mono ?_ hbs
        rintro ⟨x, w⟩ ⟨x', t⟩ - - h
        exact h
      · obtain ⟨x, rfl, hx⟩ := Aux.LR1 (R := type_v 0 ctMap S) hV
        exact type_v_weakening _ _ _ _ _ hx _ _ _ ⟨Or.inl rfl, weakCT_refl _, weakS_refl _⟩
  all_goals (intros; trivial)

/- HOL4:
Theorem exp_type_sound:
  (!(s:'ffi semanticPrimitives$state) env es r s' tenv tenvE ts tvs tenvS.
    evaluate s env es = (s', r) ∧
    tenv_ok tenv ∧
    tenv_val_exp_ok tenvE ∧
    good_ctMap ctMap ∧
    num_tvs tenvE = 0 ∧
    type_all_env ctMap tenvS env (tenv with v := add_tenvE tenvE tenv.v) ∧
    type_s ctMap s.refs tenvS ∧
    (tvs ≠ 0 ⇒ EVERY is_value es) ∧
    type_es tenv (bind_tvar tvs tenvE) es ts
    ⇒
    ∃tenvS'.
      type_s ctMap s'.refs tenvS' ∧
      store_type_extension tenvS tenvS' ∧
      s'.next_type_stamp = s.next_type_stamp ∧
      s'.next_exn_stamp = s.next_exn_stamp ∧
      case r of
         | Rval vs => LIST_REL (type_v tvs ctMap tenvS') vs ts
         | Rerr (Rraise v) => type_v 0 ctMap tenvS' v Texn
         | Rerr (Rabort Rtimeout_error) => T
         | Rerr (Rabort (Rffi_error _)) => T
         | Rerr (Rabort Rtype_error) => F) ∧
 (!(s:'ffi semanticPrimitives$state) env v pes err_v r s' tenv tenvE t1 t2 tvs tenvS.
    evaluate_match s env v pes err_v = (s', r) ∧
    tenv_ok tenv ∧
    tenv_val_exp_ok tenvE ∧
    good_ctMap ctMap ∧
    num_tvs tenvE = 0 ∧
    type_all_env ctMap tenvS env (tenv with v := add_tenvE tenvE tenv.v) ∧
    type_s ctMap s.refs tenvS ∧
    type_v tvs ctMap tenvS v t1 ∧
    type_v 0 ctMap tenvS err_v Texn ∧
    type_pes tvs tvs tenv tenvE pes t1 t2
    ⇒
    ∃tenvS'.
      type_s ctMap s'.refs tenvS' ∧
      store_type_extension tenvS tenvS' ∧
      s'.next_type_stamp = s.next_type_stamp ∧
      s'.next_exn_stamp = s.next_exn_stamp ∧
      case r of
         | Rval vs => type_v tvs ctMap tenvS' (HD vs) t2
         | Rerr (Rraise v) => type_v 0 ctMap tenvS' v Texn
         | Rerr (Rabort Rtimeout_error) => T
         | Rerr (Rabort (Rffi_error _)) => T
         | Rerr (Rabort Rtype_error) => F) -/
theorem exp_type_sound {ffi : Type} (ctMap : ctMap_ty) :
    (∀ (s : state ffi) (env : sem_env value) (es : List exp) (r : result (List value) value)
        (s' : state ffi) (tenv : type_env) (tenvE : tenv_val_exp) (ts : List typ) (tvs : Nat)
        (tenvS : tenv_store),
      evaluate s env es = (s', r) ∧
      tenv_ok tenv ∧
      tenv_val_exp_ok tenvE ∧
      good_ctMap ctMap ∧
      num_tvs tenvE = 0 ∧
      type_all_env ctMap tenvS env { tenv with v := add_tenvE tenvE tenv.v } ∧
      type_s ctMap s.refs tenvS ∧
      (tvs ≠ 0 → EVERY is_value es) ∧
      type_es tenv (bind_tvar tvs tenvE) es ts
      →
      ∃ tenvS' : tenv_store,
        type_s ctMap s'.refs tenvS' ∧
        store_type_extension tenvS tenvS' ∧
        s'.next_type_stamp = s.next_type_stamp ∧
        s'.next_exn_stamp = s.next_exn_stamp ∧
        (match r with
          | Rval vs => LIST_REL (type_v tvs ctMap tenvS') vs ts
          | Rerr (Rraise v) => type_v 0 ctMap tenvS' v Texn
          | Rerr (Rabort Rtimeout_error) => True
          | Rerr (Rabort (Rffi_error _)) => True
          | Rerr (Rabort Rtype_error) => False)) ∧
    (∀ (s : state ffi) (env : sem_env value) (v : value) (pes : List (pat × exp))
        (err_v : value) (r : result (List value) value) (s' : state ffi) (tenv : type_env)
        (tenvE : tenv_val_exp) (t1 t2 : typ) (tvs : Nat) (tenvS : tenv_store),
      evaluate_match s env v pes err_v = (s', r) ∧
      tenv_ok tenv ∧
      tenv_val_exp_ok tenvE ∧
      good_ctMap ctMap ∧
      num_tvs tenvE = 0 ∧
      type_all_env ctMap tenvS env { tenv with v := add_tenvE tenvE tenv.v } ∧
      type_s ctMap s.refs tenvS ∧
      type_v tvs ctMap tenvS v t1 ∧
      type_v 0 ctMap tenvS err_v Texn ∧
      type_pes tvs tvs tenv tenvE pes t1 t2
      →
      ∃ tenvS' : tenv_store,
        type_s ctMap s'.refs tenvS' ∧
        store_type_extension tenvS tenvS' ∧
        s'.next_type_stamp = s.next_type_stamp ∧
        s'.next_exn_stamp = s.next_exn_stamp ∧
        (match r with
          | Rval vs => type_v tvs ctMap tenvS' (HD vs) t2
          | Rerr (Rraise v) => type_v 0 ctMap tenvS' v Texn
          | Rerr (Rabort Rtimeout_error) => True
          | Rerr (Rabort (Rffi_error _)) => True
          | Rerr (Rabort Rtype_error) => False)) := by
  refine ⟨?_, ?_⟩
  · rintro s env es r s' tenv tenvE ts tvs tenvS ⟨h1, h2, h3, hg, h4, h5, h6, h7, h8⟩
    obtain ⟨S, a1, a2, a3, a4, a5⟩ := (Aux.exp_sound ctMap hg).1 s env es r s' tenv tenvE ts tvs
      tenvS h1 h2 h3 h4 h5 h6 h7 h8
    refine ⟨S, a1, a2, a3, a4, ?_⟩
    rcases r with vs | v | a
    · exact a5
    · exact a5
    · cases a <;> exact a5
  · rintro s env v pes err r s' tenv tenvE t1 t2 tvs tenvS
      ⟨h1, h2, h3, hg, h4, h5, h6, h7, h8, h9⟩
    obtain ⟨S, a1, a2, a3, a4, a5⟩ := (Aux.exp_sound ctMap hg).2 s env v pes err r s' tenv tenvE
      t1 t2 tvs tenvS h1 h2 h3 h4 h5 h6 h7 h8 h9
    refine ⟨S, a1, a2, a3, a4, ?_⟩
    rcases r with vs | v | a
    · exact a5
    · exact a5
    · cases a <;> exact a5

/- HOL4:
Theorem build_tdefs_build_tenv[local]:
  !tenvT (tds : type_def) (tids : type_ident list) next (ctMap : ctMap).
    EVERY (λ(_, _, ctors). ALL_DISTINCT (MAP FST ctors)) tds ∧
    LENGTH tds = LENGTH tids ⇒
    nsAll2
      (type_ctor (ctMap |++ REVERSE (type_def_to_ctMap tenvT next tds tids)))
      (build_tdefs next tds : env_ctor)
      (build_ctor_tenv tenvT tds tids) -/
theorem build_tdefs_build_tenv :
    ∀ (tenvT : Namespace mlstring mlstring (List mlstring × typ)) (tds : type_def)
      (tids : List type_ident) (next : Nat) (ctMap : ctMap_ty),
      EVERY (fun ((_, _, ctors) : List tvarN × typeN × List (conN × List ast_t)) =>
        ALL_DISTINCT (ctors.map Prod.fst)) tds ∧
      tds.length = tids.length →
      nsAll2
        (type_ctor (FUPDATE_LIST ctMap (type_def_to_ctMap tenvT next tds tids).reverse))
        (build_tdefs next tds : env_ctor)
        (build_ctor_tenv tenvT tds tids) := by
  have key : ∀ (tenvT : Namespace mlstring mlstring (List mlstring × typ)) (M : ctMap_ty)
      (tds : type_def) (tids : List type_ident) (next : Nat),
      (∀ stamp x, (stamp, x) ∈ type_def_to_ctMap tenvT next tds tids →
        FLOOKUP M stamp = some x) →
      tds.length = tids.length →
      nsAll2 (type_ctor M) (build_tdefs next tds : env_ctor)
        (build_ctor_tenv tenvT tds tids) := by
    intro tenvT M tds
    induction tds with
    | nil =>
      intro tids next h hl
      cases tids with
      | nil => exact nsAll2_nsEmpty _
      | cons _ _ => simp at hl
    | cons td tds ih =>
      intro tids next h hl
      obtain ⟨tvs, tn, ctors⟩ := td
      cases tids with
      | nil => simp at hl
      | cons id ids =>
        simp only [build_tdefs, build_ctor_tenv]
        refine nsAll2_nsAppend _ _ _ _ _ ⟨ih ids (next + 1) (fun s x hx => h s x ?_)
          (by simpa using hl), nsAll2_alist_to_ns _ _ _ (Aux.LIST_REL_reverse ?_)⟩
        · simp only [type_def_to_ctMap, List.mem_append]
          exact Or.inl hx
        · unfold build_constrs
          rw [Aux.LIST_REL_map, LIST_REL_iff_aux]
          refine ⟨rfl, fun i a b ha hb => ?_⟩
          rw [ha] at hb
          cases hb
          obtain ⟨cn, ts⟩ := a
          refine ⟨rfl, h _ _ ?_, by simp⟩
          simp only [type_def_to_ctMap, List.mem_append, List.mem_reverse, List.mem_map]
          exact Or.inr ⟨(cn, ts), List.mem_of_getElem? ha, rfl⟩
  have nodup : ∀ (tenvT : Namespace mlstring mlstring (List mlstring × typ))
      (tds : type_def) (tids : List type_ident) (next : Nat),
      EVERY (fun ((_, _, ctors) : List tvarN × typeN × List (conN × List ast_t)) =>
        ALL_DISTINCT (ctors.map Prod.fst)) tds → tds.length = tids.length →
      ((type_def_to_ctMap tenvT next tds tids).map Prod.fst).Nodup := by
    intro tenvT tds
    induction tds with
    | nil =>
      intro tids next h hl
      cases tids with
      | nil => simp [type_def_to_ctMap]
      | cons _ _ => simp at hl
    | cons td tds ih =>
      intro tids next h hl
      obtain ⟨tvs, tn, ctors⟩ := td
      cases tids with
      | nil => simp at hl
      | cons id ids =>
        have hl' : tds.length = ids.length := by simpa using hl
        simp only [type_def_to_ctMap, List.map_append, List.nodup_append]
        refine ⟨ih ids (next + 1) h.2 hl', ?_, ?_⟩
        · rw [List.map_reverse, List.map_map]
          refine (List.reverse_perm _).symm.nodup ?_
          have hd := Aux.ALL_DISTINCT_iff.mp h.1
          have e : (ctors.map (Prod.fst ∘ fun ((cn, ts) : conN × List ast_t) =>
              (TypeStamp cn next, (tvs, ts.map (type_name_subst tenvT), id)))) =
              (ctors.map Prod.fst).map (fun cn => TypeStamp cn next) := by
            rw [List.map_map]; rfl
          rw [e]
          exact Aux.inj_nodup_map hd (fun x y _ _ hxy => by cases hxy; rfl)
        · rintro a ha b hb rfl
          obtain ⟨⟨s, x⟩, hm, rfl⟩ := List.mem_map.mp ha
          obtain ⟨cn, i, hs, hi, -⟩ := mem_type_def_to_ctMap tenvT (next + 1) tds ids s x ⟨hm, hl'⟩
          rw [List.map_reverse, List.mem_reverse, List.map_map] at hb
          obtain ⟨⟨cn', ts⟩, -, hb⟩ := List.mem_map.mp hb
          have hb : TypeStamp cn' next = s := hb
          rw [← hb] at hs
          cases hs
          omega
  rintro tenvT tds tids next ctMap ⟨h1, h2⟩
  refine key tenvT _ tds tids next (fun s x hm => ?_) h2
  rw [Aux.FLOOKUP_FUPDATE_LIST, List.reverse_reverse,
    Aux.mem_ALOOKUP (nodup tenvT tds tids next h1 h2) hm]

/- HOL4:
Theorem type_sound_invariant_union[local]:
  type_sound_invariant st env ctMap tenvS (tids1 ∪ tids2) tenv
   ⇒
   type_sound_invariant st env ctMap tenvS tids1 tenv -/
theorem type_sound_invariant_union {ffi : Type} (st : state ffi) (env : sem_env value)
    (ctMap : ctMap_ty) (tenvS : tenv_store) (tids1 tids2 : Set type_ident)
    (tenv : type_env) :
    type_sound_invariant st env ctMap tenvS (tids1 ∪ tids2) tenv
    →
    type_sound_invariant st env ctMap tenvS tids1 tenv := by
  rintro ⟨h1, h2, ⟨h3, h4⟩, h5, h6⟩
  refine ⟨h1, h2, ⟨?_, h4⟩, h5, h6⟩
  rw [Aux.DISJOINT_iff] at h3 ⊢
  exact fun x hx => h3 x (Or.inl hx)

/- HOL4:
Theorem check_ctor_tenv_dups[local]:
  !tenvT tds. check_ctor_tenv tenvT tds ⇒ EVERY check_dup_ctors tds -/
theorem check_ctor_tenv_dups :
    ∀ (tenvT : Namespace modN typeN (List tvarN × typ))
      (tds : List (List tvarN × mlstring × List (conN × List ast_t))),
      check_ctor_tenv tenvT tds → EVERY check_dup_ctors tds := by
  intro tenvT tds h
  rw [EVERY_iff_forall]
  rintro ⟨tvs, tn, ctors⟩ hm
  exact (Aux.check_ctor_tenv_mem h _ _ _ hm).2.1

/- HOL4:
Theorem type_all_env_extend:
   type_all_env ctMap tenvS env1 tenv1
    /\ type_all_env ctMap tenvS env2 tenv2
    ==> type_all_env ctMap tenvS (extend_dec_env env1 env2)
        (extend_dec_tenv tenv1 tenv2) -/
theorem type_all_env_extend (ctMap : ctMap_ty) (tenvS : tenv_store) (env1 : sem_env value)
    (tenv1 : type_env) (env2 : sem_env value) (tenv2 : type_env) :
    type_all_env ctMap tenvS env1 tenv1
      ∧ type_all_env ctMap tenvS env2 tenv2
      → type_all_env ctMap tenvS (extend_dec_env env1 env2)
        (extend_dec_tenv tenv1 tenv2) :=
  fun ⟨h1, h2⟩ => ⟨nsAll2_nsAppend _ _ _ _ _ ⟨h1.1, h2.1⟩, nsAll2_nsAppend _ _ _ _ _ ⟨h1.2, h2.2⟩⟩

/- HOL4:
Theorem type_e_con_check:
 (!tenv tenvE e t.
   type_e tenv tenvE e t ⇒
   nsAll2 (type_ctor ctMap) envc tenv.c ⇒
   every_exp (one_con_check envc) e) ∧
 (!tenv tenvE es ts.
   type_es tenv tenvE es ts ⇒
   nsAll2 (type_ctor ctMap) envc tenv.c ⇒
   EVERY (every_exp (one_con_check envc)) es) ∧
 (!tenv tenvE funs env.
   type_funs tenv tenvE funs env ⇒
   nsAll2 (type_ctor ctMap) envc tenv.c ⇒
   EVERY (λ(f,n,e). every_exp (one_con_check envc) e) funs) -/
theorem type_e_con_check (ctMap : ctMap_ty)
    (envc : Namespace mlstring mlstring (Nat × stamp)) :
    (∀ (tenv : type_env) (tenvE : tenv_val_exp) (e : exp) (t : typ),
      type_e tenv tenvE e t →
      nsAll2 (type_ctor ctMap) envc tenv.c →
      every_exp (one_con_check envc) e) ∧
    (∀ (tenv : type_env) (tenvE : tenv_val_exp) (es : List exp) (ts : List typ),
      type_es tenv tenvE es ts →
      nsAll2 (type_ctor ctMap) envc tenv.c →
      EVERY (every_exp (one_con_check envc)) es) ∧
    (∀ (tenv : type_env) (tenvE : tenv_val_exp) (funs : List (varN × varN × exp))
        (env : List (varN × typ)),
      type_funs tenv tenvE funs env →
      nsAll2 (type_ctor ctMap) envc tenv.c →
      EVERY (fun ((_, _, e) : varN × varN × exp) => every_exp (one_con_check envc) e) funs) := by
  refine Aux.type_e_ind
    (P := fun tenv _ e _ => nsAll2 (type_ctor ctMap) envc tenv.c →
      every_exp (one_con_check envc) e)
    (Q := fun tenv _ es _ => nsAll2 (type_ctor ctMap) envc tenv.c →
      EVERY (every_exp (one_con_check envc)) es)
    (R := fun tenv _ funs _ => nsAll2 (type_ctor ctMap) envc tenv.c →
      EVERY (fun ((_, _, e) : varN × varN × exp) => every_exp (one_con_check envc) e) funs)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro _ _ _ _; simp [every_exp, one_con_check]
  · intro _ _ _ _; simp [every_exp, one_con_check]
  · intro _ _ _ _; simp [every_exp, one_con_check]
  · intro _ _ _ _; simp [every_exp, one_con_check]
  · intro _ _ _ _; simp [every_exp, one_con_check]
  · intro _ _ _ _; simp [every_exp, one_con_check]
  · intro tenv tenvE e t h1 h2 ih h
    simp only [every_exp, one_con_check]
    exact ⟨trivial, ih h⟩
  · intro tenv tenvE e pes t bs h1 h2 h3 h4 h5 ih1 ih2 h
    simp only [every_exp, one_con_check]
    exact ⟨trivial, ih1 h, EVERY_iff_forall.mpr fun pe hm => ih2 pe hm h⟩
  · intro tenv tenvE cn es tvs tn ts' ts h1 h2 h3 h4 ih h
    obtain ⟨⟨n, stamp⟩, hv, -, hn⟩ := nsAll2_nsLookup2 _ _ _ _ _ ⟨h4, h⟩
    have hn : ts.length = n := hn
    simp only [every_exp, one_con_check, do_con_check, hv]
    refine ⟨?_, ih h⟩
    rw [type_es_length _ _ _ _ h3, List.length_map, hn]
  · intro tenv tenvE es ts h1 ih h
    simp only [every_exp, one_con_check, do_con_check]
    exact ⟨trivial, ih h⟩
  · intro _ _ _ _ _ _ _ _ _ _; simp [every_exp, one_con_check]
  · intro tenv tenvE n e t1 t2 h1 h2 ih h
    simp only [every_exp, one_con_check]
    exact ⟨trivial, ih h⟩
  · intro tenv tenvE o es ts t h1 h2 h3 ih h
    simp only [every_exp, one_con_check]
    exact ⟨trivial, ih h⟩
  · intro tenv tenvE l e1 e2 h1 h2 ih1 ih2 h
    simp only [every_exp, one_con_check]
    exact ⟨trivial, ih1 h, ih2 h⟩
  · intro tenv tenvE e1 e2 e3 t h1 h2 h3 ih1 ih2 ih3 h
    simp only [every_exp, one_con_check]
    exact ⟨trivial, ih1 h, ih2 h, ih3 h⟩
  · intro tenv tenvE e pes t1 t2 bs h1 h2 h3 h4 h5 ih1 ih2 h
    simp only [every_exp, one_con_check]
    exact ⟨trivial, ih1 h, EVERY_iff_forall.mpr fun pe hm => ih2 pe hm h⟩
  · intro tenv tenvE n e1 e2 t1 t2 h1 h2 ih1 ih2 h
    simp only [every_exp, one_con_check]
    exact ⟨trivial, ih1 h, ih2 h⟩
  · intro tenv tenvE funs e t bindings h1 h2 ih1 ih2 h
    simp only [every_exp, one_con_check]
    exact ⟨trivial, ih2 h, Aux.EVERY_mono (fun x _ hx => hx) (ih1 h)⟩
  · intro tenv tenvE e t h1 h2 h3 ih h
    simp only [every_exp, one_con_check]
    exact ⟨trivial, ih h⟩
  · intro tenv tenvE e l t h1 ih h
    simp only [every_exp, one_con_check]
    exact ⟨trivial, ih h⟩
  · intro _ _ _; trivial
  · intro tenv tenvE e es t ts h1 h2 ih1 ih2 h
    exact ⟨ih1 h, ih2 h⟩
  · intro _ _ _; trivial
  · intro tenv tenvE fn n e funs bs t1 t2 h1 h2 h3 h4 ih1 ih2 h
    exact ⟨ih1 h, ih2 h⟩

def Aux.DR {ffi : Type} (M : ctMap_ty) (S : tenv_store) (env : sem_env value)
    (tenv tenv' : type_env) (st' : state ffi) (r : result (sem_env value) value) : Prop :=
  match r with
  | Rval env' => type_all_env M S env' tenv' ∧
      type_sound_invariant st' (extend_dec_env env' env) M S ∅ (extend_dec_tenv tenv' tenv)
  | Rerr e =>
    match e with
    | Rraise v => type_v 0 M S v Texn ∧ type_sound_invariant st' env M S ∅ tenv
    | Rabort a =>
      match a with
      | Rtype_error => False
      | Rtimeout_error => True
      | Rffi_error _ => True

def Aux.DG {ffi : Type} (ctMap : ctMap_ty) (tenvS : tenv_store) (env : sem_env value)
    (tids : Set type_ident) (tenv tenv' : type_env) (st' : state ffi)
    (r : result (sem_env value) value) : Prop :=
  ∃ (ctMap' : ctMap_ty) (tenvS' : tenv_store),
    weakCT ctMap' ctMap ∧
    (FRANGE (o_f (Prod.snd ∘ Prod.snd) ctMap') \
      FRANGE (o_f (Prod.snd ∘ Prod.snd) ctMap)) ⊆ tids ∧
    store_type_extension tenvS tenvS' ∧
    Aux.DR ctMap' tenvS' env tenv tenv' st' r

theorem Aux.frange_self {α : Type} (s t : Set α) : (s \ s) ⊆ t := fun _ h => absurd h.1 h.2

theorem Aux.consistent_mono {ffi : Type} {st st' : state ffi} {tids tids' : Set type_ident}
    {ctMap : ctMap_ty} (h : consistent_ctMap st tids ctMap)
    (h1 : st.next_type_stamp ≤ st'.next_type_stamp) (h2 : st.next_exn_stamp ≤ st'.next_exn_stamp)
    (h3 : ∀ x, x ∈ tids' → x ∈ tids) : consistent_ctMap st' tids' ctMap :=
  ⟨Aux.DISJOINT_iff.mpr fun x hx => Aux.DISJOINT_iff.mp h.1 x (h3 x hx),
    fun cn id => ⟨fun hh => Nat.lt_of_lt_of_le ((h.2 cn id).1 hh) h1,
      fun hh => Nat.lt_of_lt_of_le ((h.2 cn id).2 hh) h2⟩⟩

theorem Aux.tsi_same {ffi : Type} {st st' : state ffi} {env : sem_env value}
    {ctMap ctMap' : ctMap_ty} {tenvS tenvS' : tenv_store} {tids tids' : Set type_ident}
    {tenv : type_env} (h : type_sound_invariant st env ctMap tenvS tids tenv)
    (hc : weakCT ctMap' ctMap) (hs : store_type_extension tenvS tenvS') (hg : good_ctMap ctMap')
    (hcons : consistent_ctMap st' tids' ctMap') (hts : type_s ctMap' st'.refs tenvS') :
    type_sound_invariant st' env ctMap' tenvS' tids' tenv :=
  ⟨h.1, hg, hcons, type_all_env_weakening _ _ _ _ _ _
    ⟨hc, store_type_extension_weakS _ _ hs, h.2.2.2.1⟩, hts⟩

theorem Aux.tsi_ext {ffi : Type} {st st' : state ffi} {env env' : sem_env value}
    {ctMap ctMap' : ctMap_ty} {tenvS tenvS' : tenv_store} {tids tids' : Set type_ident}
    {tenv tenv' : type_env} (h : type_sound_invariant st env ctMap tenvS tids tenv)
    (hc : weakCT ctMap' ctMap) (hs : store_type_extension tenvS tenvS') (hg : good_ctMap ctMap')
    (hcons : consistent_ctMap st' tids' ctMap') (hts : type_s ctMap' st'.refs tenvS')
    (hae : type_all_env ctMap' tenvS' env' tenv') (hok : tenv_ok tenv') :
    type_sound_invariant st' (extend_dec_env env' env) ctMap' tenvS' tids'
      (extend_dec_tenv tenv' tenv) :=
  ⟨extend_dec_tenv_ok _ _ ⟨hok, h.1⟩, hg, hcons, type_all_env_extend _ _ _ _ _ _ ⟨hae,
    type_all_env_weakening _ _ _ _ _ _
      ⟨hc, store_type_extension_weakS _ _ hs, h.2.2.2.1⟩⟩, hts⟩

/-- The value case of a declaration that does not change the state's types. -/
theorem Aux.DG_val {ffi : Type} {st st' : state ffi} {env env' : sem_env value}
    {ctMap : ctMap_ty} {tenvS tenvS' : tenv_store} {tids : Set type_ident}
    {tenv tenv' : type_env} (h : type_sound_invariant st env ctMap tenvS tids tenv)
    (hs : store_type_extension tenvS tenvS')
    (h1 : st'.next_type_stamp = st.next_type_stamp) (h2 : st'.next_exn_stamp = st.next_exn_stamp)
    (hts : type_s ctMap st'.refs tenvS')
    (hae : type_all_env ctMap tenvS' env' tenv') (hok : tenv_ok tenv') :
    Aux.DG ctMap tenvS env tids tenv tenv' st' (Rval env') :=
  ⟨ctMap, tenvS', weakCT_refl _, Aux.frange_self _ _, hs, hae,
    Aux.tsi_ext h (weakCT_refl _) hs h.2.1
      (Aux.consistent_mono h.2.2.1 (Nat.le_of_eq h1.symm) (Nat.le_of_eq h2.symm)
        (fun _ hx => hx.elim)) hts hae hok⟩

theorem Aux.DR_err {ffi : Type} {M : ctMap_ty} {S : tenv_store} {env : sem_env value}
    {tenv tenv' tenv'' : type_env} {st' : state ffi} {e : error_result value}
    (h : Aux.DR M S env tenv tenv' st' (Rerr e)) : Aux.DR M S env tenv tenv'' st' (Rerr e) := by
  rcases e with v | a
  · exact h
  · cases a <;> exact h

/-- Errors of the second of two parts, in terms of the environments of the first. -/
theorem Aux.DR_err2 {ffi : Type} {M0 M : ctMap_ty} {S0 S : tenv_store} {env env1 : sem_env value}
    {tenv tenv1 tenv' tenv'' : type_env} {tids : Set type_ident} {st st' : state ffi}
    {e : error_result value}
    (h0 : type_sound_invariant st env M0 S0 tids tenv) (hc : weakCT M M0)
    (hs : store_type_extension S0 S)
    (h : Aux.DR M S env1 tenv1 tenv' st' (Rerr e)) : Aux.DR M S env tenv tenv'' st' (Rerr e) := by
  rcases e with v | a
  · exact ⟨h.1, Aux.tsi_same h0 hc hs h.2.2.1 h.2.2.2.1 h.2.2.2.2.2⟩
  · cases a <;> exact h

theorem Aux.frange_trans {M0 M1 M2 : ctMap_ty} {d1 d2 : Set type_ident}
    (h1 : (FRANGE (o_f (Prod.snd ∘ Prod.snd) M1) \
      FRANGE (o_f (Prod.snd ∘ Prod.snd) M0)) ⊆ d1)
    (h2 : (FRANGE (o_f (Prod.snd ∘ Prod.snd) M2) \
      FRANGE (o_f (Prod.snd ∘ Prod.snd) M1)) ⊆ d2) :
    (FRANGE (o_f (Prod.snd ∘ Prod.snd) M2) \
      FRANGE (o_f (Prod.snd ∘ Prod.snd) M0)) ⊆ (d1 ∪ d2) := by
  intro x hx
  by_cases hm : x ∈ FRANGE (o_f (Prod.snd ∘ Prod.snd) M1)
  · exact Or.inl (h1 x ⟨hm, hx.2⟩)
  · exact Or.inr (h2 x ⟨hx.1, hm⟩)

/-- The invariant for the second of two parts. -/
theorem Aux.tsi_second {ffi : Type} {st st1 : state ffi} {env env1 : sem_env value}
    {M0 M1 : ctMap_ty} {S0 S1 : tenv_store} {d1 d2 : Set type_ident} {tenv tenv1 : type_env}
    (h0 : type_sound_invariant st env M0 S0 (d1 ∪ d2) tenv)
    (hf : (FRANGE (o_f (Prod.snd ∘ Prod.snd) M1) \
      FRANGE (o_f (Prod.snd ∘ Prod.snd) M0)) ⊆ d1)
    (hd : DISJOINT d1 d2)
    (h1 : type_sound_invariant st1 env1 M1 S1 ∅ tenv1) :
    type_sound_invariant st1 env1 M1 S1 d2 tenv1 := by
  refine ⟨h1.1, h1.2.1, ⟨?_, h1.2.2.1.2⟩, h1.2.2.2⟩
  rw [Aux.DISJOINT_iff]
  intro x hx hm
  by_cases hm0 : x ∈ FRANGE (o_f (Prod.snd ∘ Prod.snd) M0)
  · exact Aux.DISJOINT_iff.mp h0.2.2.1.1 x (Or.inr hx) hm0
  · exact Aux.DISJOINT_iff.mp hd x (hf x ⟨hm, hm0⟩) hx

theorem Aux.type_env_empty (M : ctMap_ty) (S : tenv_store) (t : tenv_abbrev) :
    type_all_env M S { v := nsEmpty, c := nsEmpty } { v := nsEmpty, c := nsEmpty, t := t } :=
  ⟨nsAll2_nsEmpty _, nsAll2_nsEmpty _⟩

theorem Aux.add_tvs_rel {M : ctMap_ty} {S : tenv_store} {tvs : Nat}
    {l : List (varN × value)} {bs : List (varN × typ)}
    (h : LIST_REL (fun ((x, v) : varN × value) ((x', t) : varN × typ) =>
      x = x' ∧ type_v tvs M S v t) l bs) :
    nsAll2 (fun _ v (p : Nat × typ) => type_v p.1 M S v p.2)
      (alist_to_ns l : env_val) (alist_to_ns (tenv_add_tvs tvs bs) : tenv_val) := by
  apply nsAll2_alist_to_ns
  unfold tenv_add_tvs
  rw [← List.map_id l, Aux.LIST_REL_map]
  refine Aux.LIST_REL_mono ?_ h
  rintro ⟨x, w⟩ ⟨x', t⟩ - - h
  exact h

theorem Aux.decs_sound {ffi : Type} :
    ∀ (st : state ffi) (env : sem_env value) (ds : List dec) (st' : state ffi)
      (r : result (sem_env value) value) (ctMap : ctMap_ty) (tenvS : tenv_store)
      (tenv : type_env) (tids : Set type_ident) (tenv' : type_env),
      evaluate_decs st env ds = (st', r) → type_ds false tenv ds tids tenv' →
      type_sound_invariant st env ctMap tenvS tids tenv →
      Aux.DG ctMap tenvS env tids tenv tenv' st' r := by
  have H := Aux.eval_induct (ffi := ffi) (P := fun _ _ _ => True) (Q := fun _ _ _ _ _ => True)
    (D := fun st env ds => ∀ (st' : state ffi)
      (r : result (sem_env value) value) (ctMap : ctMap_ty) (tenvS : tenv_store)
      (tenv : type_env) (tids : Set type_ident) (tenv' : type_env),
      evaluate_decs st env ds = (st', r) → type_ds false tenv ds tids tenv' →
      type_sound_invariant st env ctMap tenvS tids tenv →
      Aux.DG ctMap tenvS env tids tenv tenv' st' r)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact H.2.2
  iterate 18 (intros; trivial)
  · -- []
    intro st env st' r ctMap tenvS tenv tids tenv' he ht htsi
    obtain ⟨rfl, rfl⟩ := (type_ds_empty _ _ _ _).mp ht
    rw [evaluate_decs] at he
    cases he
    exact Aux.DG_val htsi (store_type_extension_refl _) rfl rfl htsi.2.2.2.2
      (Aux.type_env_empty _ _ _) tenv_ok_empty
  · -- d1 :: d2 :: ds
    intro st env d1 d2 ds ih1 ih2 st' r ctMap tenvS tenv tids tenv' he ht htsi
    obtain ⟨t1, t2, dd1, dd2, rfl, rfl, hd1, hds, hdisj⟩ := Aux.type_ds_cons_inv ht
    have I1 := fun st' r he1 => ih1 st' r ctMap tenvS tenv dd1 t1 he1
      ((type_ds_sing _ _ _ _ _).mpr hd1) (type_sound_invariant_union _ _ _ _ _ dd2 _ htsi)
    rw [Aux.evaluate_decs_cons] at he
    rcases he1 : evaluate_decs st env [d1] with ⟨st1, env1 | e1⟩
    · rw [he1] at he
      dsimp only at he
      obtain ⟨M1, S1, a1, a2, a3, a4, a5⟩ := I1 _ _ he1
      have hcl := evaluate_clock.2.2 _ _ _ _ _ he1
      have tsi2 := Aux.tsi_second htsi a2 hdisj a5
      rcases he2 : evaluate_decs st1 (extend_dec_env env1 env) (d2 :: ds) with ⟨st2, r2⟩
      rw [he2] at he
      cases he
      obtain ⟨M2, S2, b1, b2, b3, b4⟩ := ih2 st1 _ hcl _ _ M1 S1 _ dd2 t2 he2 hds tsi2
      refine ⟨M2, S2, weakCT_trans _ _ _ ⟨b1, a1⟩, Aux.frange_trans a2 b2,
        store_type_extension_trans _ _ _ ⟨a3, b3⟩, ?_⟩
      cases r2 with
      | Rval env2 =>
        refine ⟨type_all_env_extend M2 S2 env2 t2 env1 t1 ⟨b4.1,
          type_all_env_weakening _ _ _ _ _ _ ⟨b1, store_type_extension_weakS _ _ b3, a4⟩⟩, ?_⟩
        have := b4.2
        rw [extend_dec_env_assoc, extend_dec_tenv_assoc] at this
        exact this
      | Rerr e =>
        exact Aux.DR_err2 htsi (weakCT_trans _ _ _ ⟨b1, a1⟩)
          (store_type_extension_trans _ _ _ ⟨a3, b3⟩) b4
    · rw [he1] at he
      cases he
      obtain ⟨M1, S1, a1, a2, a3, a4⟩ := I1 _ _ he1
      exact ⟨M1, S1, a1, fun x hx => Or.inl (a2 x hx), a3, Aux.DR_err a4⟩
  · -- Dlet
    intro st env l p e _ st' r ctMap tenvS tenv tids tenv' he ht htsi
    have ht := (type_ds_sing _ _ _ _ _).mp ht
    have hok' := type_d_tenv_ok_helper.1 _ _ _ _ _ ht htsi.1
    obtain ⟨tvs, t, bs, rfl, rfl, hv, hd, hp, hte⟩ : ∃ tvs t bindings, tids = ∅ ∧
        tenv' = { v := alist_to_ns (tenv_add_tvs tvs bindings), c := nsEmpty, t := nsEmpty } ∧
        (tvs ≠ 0 → is_value e) ∧ ALL_DISTINCT (pat_bindings p []) ∧
        type_p tvs tenv p t bindings ∧
        type_e tenv (bind_tvar tvs tenv_val_exp.Empty) e t := by
      cases ht with
      | dlet_poly tvs _ _ _ t b _ h1 h2 h3 h4 h5 =>
        exact ⟨tvs, t, b, rfl, rfl, fun _ => h1, h2, h3, h4⟩
      | dlet_mono _ _ _ t b _ h1 h2 h3 h4 =>
        exact ⟨0, t, b, rfl, rfl, fun h => absurd rfl h, h2, h3, by rw [bind_tvar0]; exact h4⟩
    have hck : every_exp (one_con_check env.c) e :=
      (type_e_con_check ctMap env.c).1 _ _ _ _ hte htsi.2.2.2.1.1
    rw [evaluate_decs, if_pos ⟨hd, hck⟩] at he
    have I1 := fun r s' he1 => (Aux.exp_sound ctMap htsi.2.1).1 st env [e] r s' tenv
      tenv_val_exp.Empty [t] tvs tenvS he1 htsi.1 trivial rfl htsi.2.2.2.1 htsi.2.2.2.2
      (fun h => ⟨hv h, trivial⟩) (Aux.es1 hte)
    split at he
    · rename_i st1 vs he1
      cases he
      obtain ⟨S1, b1, b2, b3, b4, b5⟩ := I1 _ _ he1
      obtain ⟨x, rfl, hx⟩ := Aux.LR1 (R := type_v tvs ctMap S1) b5
      have ha' := Aux.env_weak b2 htsi.2.2.2.1
      have hHD : HD [x] = x := rfl
      rw [hHD]
      rcases pat_type_sound.1 env.c _ p x [] tenv ctMap [] t bs S1 tvs
        ⟨htsi.2.1.1, ha'.1, hx, hp, b1, trivial⟩ with hm | ⟨bs', hm, hbs⟩
      · rw [hm]
        refine ⟨ctMap, S1, weakCT_refl _, Aux.frange_self _ _, b2,
          (type_v_exn 0 ctMap S1 htsi.2.1.2.2.1).2.2.1,
          Aux.tsi_same htsi (weakCT_refl _) b2 htsi.2.1 ?_ b1⟩
        exact Aux.consistent_mono htsi.2.2.1 (Nat.le_of_eq b3.symm) (Nat.le_of_eq b4.symm)
          (fun _ hx => hx)
      · rw [hm]
        rw [List.append_nil] at hbs
        exact Aux.DG_val htsi b2 b3 b4 b1 ⟨nsAll2_nsEmpty _,
          nsAll2_mono (fun i v p h => h) (Aux.add_tvs_rel hbs)⟩ hok'
    · rename_i st1 err he1
      cases he
      obtain ⟨S1, b1, b2, b3, b4, b5⟩ := I1 _ _ he1
      refine ⟨ctMap, S1, weakCT_refl _, Aux.frange_self _ _, b2, ?_⟩
      rcases err with v | a
      · exact ⟨b5, Aux.tsi_same htsi (weakCT_refl _) b2 htsi.2.1
          (Aux.consistent_mono htsi.2.2.1 (Nat.le_of_eq b3.symm) (Nat.le_of_eq b4.symm)
            (fun _ hx => hx)) b1⟩
      · cases a <;> exact b5
  · -- Dletrec
    intro st env l funs st' r ctMap tenvS tenv tids tenv' he ht htsi
    have ht := (type_ds_sing _ _ _ _ _).mp ht
    have hok' := type_d_tenv_ok_helper.1 _ _ _ _ _ ht htsi.1
    obtain ⟨tvs, bs, rfl, rfl, hf⟩ : ∃ tvs bindings, tids = ∅ ∧
        tenv' = { v := alist_to_ns (tenv_add_tvs tvs bindings), c := nsEmpty, t := nsEmpty } ∧
        type_funs tenv (bind_var_list 0 bindings (bind_tvar tvs tenv_val_exp.Empty)) funs
          bindings := by
      cases ht with
      | dletrec _ _ b tvs _ h1 h2 => exact ⟨tvs, b, rfl, rfl, h1⟩
    have hd := type_funs_distinct _ _ _ _ hf
    have hck : EVERY (fun ((_, _, e) : varN × varN × exp) =>
        every_exp (one_con_check env.c) e) funs :=
      (type_e_con_check ctMap env.c).2.2 _ _ _ _ hf htsi.2.2.2.1.1
    rw [evaluate_decs, if_pos ⟨hd, Aux.EVERY_mono (fun x _ hx => hx) hck⟩] at he
    cases he
    refine Aux.DG_val htsi (store_type_extension_refl _) rfl rfl htsi.2.2.2.2
      ⟨nsAll2_nsEmpty _, ?_⟩ hok'
    have hrec := Aux.type_rec_env (envV := nsEmpty) (tenvV := nsEmpty) (ctMap := ctMap)
      (tenvS := tenvS) (env := env) (tenvE := tenv_val_exp.Empty) htsi.1 htsi.2.2.2.1 trivial rfl
      hf (nsAll2_nsEmpty _)
    rw [← nsAppend_to_nsBindList, (nsAppend_nsEmpty _).1] at hrec
    exact nsAll2_mono (fun i v p h => h) hrec
  · -- Dtype
    intro st env l tds st' r ctMap tenvS tenv tids tenv' he ht htsi
    have ht := (type_ds_sing _ _ _ _ _).mp ht
    have hok' := type_d_tenv_ok_helper.1 _ _ _ _ _ ht htsi.1
    cases ht with
    | dtype _ _ ti tenvT _ h1 h2 h3 h4 h5 =>
    rw [evaluate_decs, if_pos (check_ctor_tenv_dups _ _ h3)] at he
    cases he
    have habb : tenv_abbrev_ok (nsAppend tenvT tenv.t) :=
      nsAll_nsAppend _ _ _ ⟨hok'.2.2, htsi.1.2.2⟩
    obtain ⟨hg1, ⟨bt, bf, bn⟩, ⟨x1, x2, x3, x4⟩, ⟨l1, l2, l3⟩⟩ := htsi.2.1
    have hcons := htsi.2.2.1
    let N : ctMap_ty := FUPDATE_LIST FEMPTY
      (type_def_to_ctMap (nsAppend tenvT tenv.t) st.next_type_stamp tds ti).reverse
    have eM : FUPDATE_LIST ctMap
        (type_def_to_ctMap (nsAppend tenvT tenv.t) st.next_type_stamp tds ti).reverse =
        FUNION N ctMap := fupdate2_union ctMap [] _
    have hN : ∀ s tvs ts id, FLOOKUP N s = some (tvs, ts, id) → ∃ (j : Nat) (cn : conN),
        ti[j]? = some id ∧ s = TypeStamp cn (st.next_type_stamp + j) ∧ j < tds.length := by
      intro s tvs ts id hh
      have hh : FLOOKUP (FUPDATE_LIST FEMPTY (type_def_to_ctMap (nsAppend tenvT tenv.t)
        st.next_type_stamp tds ti).reverse) s = some (tvs, ts, id) := hh
      rw [Aux.FUPDATE_LIST_reverse, Aux.FLOOKUP_alist_to_fmap] at hh
      obtain ⟨j, cn, tn, ctors, tsa, a, b, c, -⟩ :=
        Aux.mem_ctMap _ _ _ _ _ _ _ _ (Aux.ALOOKUP_mem hh) h4.symm
      exact ⟨j, cn, b, c, (List.getElem?_eq_some_iff.mp a).1⟩
    have hold : ∀ cn n x, FLOOKUP ctMap (TypeStamp cn n) = some x → n < st.next_type_stamp :=
      fun cn n x hx => (hcons.2 cn n).1 (by rw [Aux.mem_FDOM, hx]; simp)
    have hdom : DISJOINT (FDOM N) (FDOM ctMap) := by
      rw [Aux.DISJOINT_iff]
      intro s hs1 hs2
      rw [Aux.mem_FDOM] at hs1 hs2
      cases hq : FLOOKUP N s with
      | none => exact hs1 hq
      | some x =>
        obtain ⟨tvs, ts, id⟩ := x
        obtain ⟨j, cn, -, rfl, -⟩ := hN _ _ _ _ hq
        cases hq2 : FLOOKUP ctMap (TypeStamp cn (st.next_type_stamp + j)) with
        | none => exact hs2 hq2
        | some y =>
          have := hold _ _ _ hq2
          omega
    have hw : weakCT (FUNION N ctMap) ctMap := disjoint_env_weakCT _ _ hdom
    have hw' := Aux.weakCT_iff.mp hw
    have hcase : ∀ s x, FLOOKUP (FUNION N ctMap) s = some x →
        FLOOKUP N s = some x ∨ FLOOKUP ctMap s = some x := by
      intro s x hh
      rw [Aux.FLOOKUP_FUNION] at hh
      cases hq : FLOOKUP N s with
      | none => rw [hq] at hh; exact Or.inr hh
      | some y => rw [hq] at hh; exact Or.inl hh
    have hlow : ∀ cn n, n < st.next_type_stamp → FLOOKUP ctMap (TypeStamp cn n) = none →
        FLOOKUP (FUNION N ctMap) (TypeStamp cn n) = none := by
      intro cn n hn hnone
      cases hq : FLOOKUP (FUNION N ctMap) (TypeStamp cn n) with
      | none => rfl
      | some x =>
        rcases hcase _ _ hq with h | h
        · obtain ⟨tvs, ts, id⟩ := x
          obtain ⟨j, cn', -, hs, -⟩ := hN _ _ _ _ h
          cases hs
          omega
        · rw [hnone] at h; cases h
    have hfr : DISJOINT (FRANGE (o_f (Prod.snd ∘ Prod.snd) N))
        (FRANGE (o_f (Prod.snd ∘ Prod.snd) ctMap)) := by
      rw [Aux.DISJOINT_iff]
      rintro x ⟨s, hs⟩ hx
      rw [Aux.FLOOKUP_o_f] at hs
      cases hq : FLOOKUP N s with
      | none => rw [hq] at hs; cases hs
      | some y =>
        obtain ⟨tvs, ts, id⟩ := y
        rw [hq] at hs
        cases hs
        obtain ⟨j, cn, hj, -⟩ := hN _ _ _ _ hq
        exact Aux.DISJOINT_iff.mp hcons.1 _ (List.mem_of_getElem? hj) hx
    have hg : good_ctMap (FUNION N ctMap) := by
      refine ⟨ctMap_ok_merge_imp _ _ ⟨hfr, ?_, hg1⟩, ⟨hw' _ _ bt, hw' _ _ bf, ?_⟩,
        ⟨hw' _ _ x1, hw' _ _ x2, hw' _ _ x3, hw' _ _ x4⟩, ⟨hw' _ _ l1, hw' _ _ l2, ?_⟩⟩
      · refine ctMap_ok_type_defs _ _ _ _ ⟨h1, ?_, h4.symm, h3, habb⟩
        rw [Aux.DISJOINT_iff] at h2 ⊢
        exact fun x hx hm => h2 x hx (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hm))
      · intro cn hcn
        exact hlow _ _ (hold _ _ _ bt) (bn cn hcn)
      · intro cn hcn
        exact hlow _ _ (hold _ _ _ l1) (l3 cn hcn)
    have hae : type_all_env (FUNION N ctMap) tenvS
        { v := nsEmpty, c := build_tdefs st.next_type_stamp tds }
        { v := nsEmpty
          c := build_ctor_tenv (nsAppend tenvT tenv.t) tds ti
          t := tenvT } := by
      refine ⟨?_, nsAll2_nsEmpty _⟩
      rw [← eM]
      refine build_tdefs_build_tenv _ _ _ _ _ ⟨?_, h4.symm⟩
      rw [EVERY_iff_forall]
      rintro ⟨tvs, tn, ctors⟩ hm
      exact (check_dup_ctors_thm tvs tn ctors).mp (Aux.check_ctor_tenv_mem h3 _ _ _ hm).2.1
    refine ⟨FUNION N ctMap, tenvS, hw, ?_, store_type_extension_refl _, hae,
      Aux.tsi_ext htsi hw (store_type_extension_refl _) hg ⟨?_, ?_⟩
        (type_s_weakening _ _ _ _ ⟨htsi.2.2.2.2, hw⟩) hae hok'⟩
    · rintro x ⟨⟨s, hs⟩, hx⟩
      rw [Aux.FLOOKUP_o_f] at hs
      cases hq : FLOOKUP (FUNION N ctMap) s with
      | none => rw [hq] at hs; cases hs
      | some y =>
        obtain ⟨tvs, ts, id⟩ := y
        rw [hq] at hs
        cases hs
        rcases hcase _ _ hq with h | h
        · obtain ⟨j, cn, hj, -⟩ := hN _ _ _ _ h
          exact List.mem_of_getElem? hj
        · exact absurd ⟨s, by rw [Aux.FLOOKUP_o_f, h]; rfl⟩ hx
    · rw [Aux.DISJOINT_iff]
      exact fun x hx => hx.elim
    · intro cn id
      constructor
      · intro hm
        rw [Aux.mem_FDOM] at hm
        cases hq : FLOOKUP (FUNION N ctMap) (TypeStamp cn id) with
        | none => exact absurd hq hm
        | some y =>
          show id < st.next_type_stamp + tds.length
          rcases hcase _ _ hq with h | h
          · obtain ⟨tvs, ts, tid⟩ := y
            obtain ⟨j, cn', -, hs, hj⟩ := hN _ _ _ _ h
            cases hs
            omega
          · have := hold _ _ _ h
            omega
      · intro hm
        rw [Aux.mem_FDOM] at hm
        cases hq : FLOOKUP (FUNION N ctMap) (ExnStamp id) with
        | none => exact absurd hq hm
        | some y =>
          rcases hcase _ _ hq with h | h
          · obtain ⟨tvs, ts, tid⟩ := y
            obtain ⟨j, cn', -, hs, hj⟩ := hN _ _ _ _ h
            cases hs
          · exact (hcons.2 cn id).2 (by rw [Aux.mem_FDOM, h]; simp)
  · -- Dtabbrev
    intro st env l tvs tn t st' r ctMap tenvS tenv tids tenv' he ht htsi
    have ht := (type_ds_sing _ _ _ _ _).mp ht
    have hok' := type_d_tenv_ok_helper.1 _ _ _ _ _ ht htsi.1
    rw [evaluate_decs] at he
    cases he
    cases ht with
    | dtabbrev _ _ _ _ _ h1 h2 h3 =>
      exact Aux.DG_val htsi (store_type_extension_refl _) rfl rfl htsi.2.2.2.2
        (Aux.type_env_empty _ _ _) hok'
  · -- Dexn
    intro st env l cn ts st' r ctMap tenvS tenv tids tenv' he ht htsi
    have ht := (type_ds_sing _ _ _ _ _).mp ht
    have hok' := type_d_tenv_ok_helper.1 _ _ _ _ _ ht htsi.1
    rw [evaluate_decs] at he
    cases he
    cases ht with
    | dexn _ _ _ _ h1 h2 =>
    obtain ⟨⟨g1, g2, g3, g4⟩, ⟨bt, bf, bn⟩, ⟨x1, x2, x3, x4⟩, ⟨l1, l2, l3⟩⟩ := htsi.2.1
    have hcons := htsi.2.2.1
    let X : List tvarN × List typ × type_ident :=
      ([], ts.map (type_name_subst tenv.t), Texn_num)
    let M : ctMap_ty := FUPDATE ctMap (ExnStamp st.next_exn_stamp, X)
    have hM : ∀ s, FLOOKUP M s = if s = ExnStamp st.next_exn_stamp then some X
        else FLOOKUP ctMap s := fun s => rfl
    have hfresh : FLOOKUP ctMap (ExnStamp st.next_exn_stamp) = none := by
      cases hq : FLOOKUP ctMap (ExnStamp st.next_exn_stamp) with
      | none => rfl
      | some x =>
        have := (hcons.2 cn st.next_exn_stamp).2 (by rw [Aux.mem_FDOM, hq]; simp)
        omega
    have hw' : ∀ s x, FLOOKUP ctMap s = some x → FLOOKUP M s = some x := by
      intro s x hx
      rw [hM, if_neg]
      · exact hx
      · rintro rfl
        rw [hfresh] at hx
        cases hx
    have hw : weakCT M ctMap := Aux.weakCT_iff.mpr hw'
    have hcase : ∀ s x, FLOOKUP M s = some x →
        (s = ExnStamp st.next_exn_stamp ∧ x = X) ∨ FLOOKUP ctMap s = some x := by
      intro s x hx
      rw [hM] at hx
      split at hx
      · rename_i hs
        cases hx
        exact Or.inl ⟨hs, rfl⟩
      · exact Or.inr hx
    have hts : ∀ s x, FLOOKUP ctMap s = none → (∀ n, s ≠ ExnStamp n) → FLOOKUP M s = x →
        x = none := by
      intro s x h hne hx
      rw [hM, if_neg (hne _), h] at hx
      exact hx.symm
    have htexn : ∀ s tvs ts', FLOOKUP ctMap s = some (tvs, ts', Texn_num) → ∃ n, s = ExnStamp n := by
      intro s tvs ts' h
      cases s with
      | ExnStamp n => exact ⟨n, rfl⟩
      | TypeStamp cn n =>
        exact absurd (by simp [prim_type_nums]) (g3 _ _ _ _ _ h)
    have hg : good_ctMap M := by
      refine ⟨⟨?_, ?_, ?_, ?_⟩, ⟨hw' _ _ bt, hw' _ _ bf, ?_⟩,
        ⟨hw' _ _ x1, hw' _ _ x2, hw' _ _ x3, hw' _ _ x4⟩, ⟨hw' _ _ l1, hw' _ _ l2, ?_⟩⟩
      · intro s x hx
        rcases hcase s x hx with ⟨rfl, rfl⟩ | hx
        · show EVERY (check_freevars 0 []) (ts.map (type_name_subst tenv.t))
          rw [EVERY_iff_forall] at h1 h2 ⊢
          intro x hx
          obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
          exact check_freevars_type_name_subst _ _ _ _ ⟨htsi.1.2.2, h2 y hy, h1 y hy⟩
        · exact g1 s x hx
      · intro ex tvs ts' ti hx
        rcases hcase _ _ hx with ⟨-, hX⟩ | hx
        · have hX : (tvs, ts', ti) =
            (([] : List tvarN), ts.map (type_name_subst tenv.t), Texn_num) := hX
          cases hX; exact ⟨rfl, rfl⟩
        · exact g2 _ _ _ _ hx
      · intro cn x tvs ts' ti hx
        rcases hcase _ _ hx with ⟨hs, -⟩ | hx
        · cases hs
        · exact g3 _ _ _ _ _ hx
      · rintro s1 tvs1 ts1 ti s2 tvs2 ts2 ⟨hx1, hx2⟩
        rcases hcase _ _ hx1 with ⟨rfl, hX⟩ | hx1
        · have hX : (tvs1, ts1, ti) =
            (([] : List tvarN), ts.map (type_name_subst tenv.t), Texn_num) := hX
          cases hX
          rcases hcase _ _ hx2 with ⟨rfl, -⟩ | hx2
          · trivial
          · obtain ⟨n, rfl⟩ := htexn _ _ _ hx2
            trivial
        · rcases hcase _ _ hx2 with ⟨rfl, hX⟩ | hx2
          · have hX : (tvs2, ts2, ti) =
              (([] : List tvarN), ts.map (type_name_subst tenv.t), Texn_num) := hX
            cases hX
            obtain ⟨n, rfl⟩ := htexn _ _ _ hx1
            trivial
          · exact g4 _ _ _ _ _ _ _ ⟨hx1, hx2⟩
      · intro cn hcn
        exact hts _ _ (bn cn hcn) (fun n h => by cases h) rfl
      · intro cn hcn
        exact hts _ _ (l3 cn hcn) (fun n h => by cases h) rfl
    have hae : type_all_env M tenvS
        { v := nsEmpty, c := nsSing cn (ts.length, ExnStamp st.next_exn_stamp) }
        { v := nsEmpty
          c := nsSing cn ([], ts.map (type_name_subst tenv.t), Texn_num)
          t := nsEmpty } := by
      refine ⟨(nsAll2_nsSing _ _ _ _ _).mpr ⟨rfl, ?_, ?_⟩, nsAll2_nsEmpty _⟩
      · rw [hM, if_pos rfl]
      · rw [List.length_map]
    refine ⟨M, tenvS, hw, ?_, store_type_extension_refl _, hae,
      Aux.tsi_ext htsi hw (store_type_extension_refl _) hg ⟨?_, ?_⟩
        (type_s_weakening _ _ _ _ ⟨htsi.2.2.2.2, hw⟩) hae hok'⟩
    · rintro x ⟨⟨s, hs⟩, hx⟩
      rw [Aux.FLOOKUP_o_f] at hs
      cases hq : FLOOKUP M s with
      | none => rw [hq] at hs; cases hs
      | some y =>
        rw [hq] at hs
        cases hs
        refine absurd ?_ hx
        rcases hcase _ _ hq with ⟨-, rfl⟩ | h
        · exact ⟨bind_stamp, by rw [Aux.FLOOKUP_o_f, x1]; rfl⟩
        · exact ⟨s, by rw [Aux.FLOOKUP_o_f, h]; rfl⟩
    · rw [Aux.DISJOINT_iff]
      exact fun x hx => hx.elim
    · intro cn' id
      constructor
      · intro hm
        rw [Aux.mem_FDOM] at hm
        cases hq : FLOOKUP M (TypeStamp cn' id) with
        | none => exact absurd hq hm
        | some y =>
          rcases hcase _ _ hq with ⟨hs, -⟩ | h
          · cases hs
          · exact (hcons.2 cn' id).1 (by rw [Aux.mem_FDOM, h]; simp)
      · intro hm
        rw [Aux.mem_FDOM] at hm
        cases hq : FLOOKUP M (ExnStamp id) with
        | none => exact absurd hq hm
        | some y =>
          show id < st.next_exn_stamp + 1
          rcases hcase _ _ hq with ⟨hs, -⟩ | h
          · cases hs; omega
          · have := (hcons.2 cn' id).2 (by rw [Aux.mem_FDOM, h]; simp)
            omega
  · -- Dmod
    intro st env mn ds ih st' r ctMap tenvS tenv tids tenv' he ht htsi
    have ht := (type_ds_sing _ _ _ _ _).mp ht
    have hok' := type_d_tenv_ok_helper.1 _ _ _ _ _ ht htsi.1
    obtain ⟨t1, rfl, hds⟩ : ∃ t1, tenv' = tenvLift mn t1 ∧ type_ds false tenv ds tids t1 := by
      cases ht with
      | dmod _ _ _ _ t1 h1 => exact ⟨t1, rfl, h1⟩
    rw [evaluate_decs] at he
    rcases he1 : evaluate_decs st env ds with ⟨st1, r1⟩
    rw [he1] at he
    obtain ⟨M1, S1, a1, a2, a3, a4⟩ := ih _ _ ctMap tenvS tenv tids t1 he1 hds htsi
    cases r1 with
    | Rval env1 =>
      cases he
      have hae : type_all_env M1 S1 { v := nsLift mn env1.v, c := nsLift mn env1.c }
          (tenvLift mn t1) :=
        ⟨(nsAll2_nsLift _ _ _ _).mpr (nsAll2_mono (fun _ _ _ h => h) a4.1.1),
          (nsAll2_nsLift _ _ _ _).mpr (nsAll2_mono (fun _ _ _ h => h) a4.1.2)⟩
      exact ⟨M1, S1, a1, a2, a3, hae, Aux.tsi_ext htsi a1 a3 a4.2.2.1 a4.2.2.2.1 a4.2.2.2.2.2 hae
        hok'⟩
    | Rerr e =>
      cases he
      exact ⟨M1, S1, a1, a2, a3, Aux.DR_err a4⟩
  · -- Dlocal
    intro st env lds ds ih1 ih2 st' r ctMap tenvS tenv tids tenv' he ht htsi
    have ht := (type_ds_sing _ _ _ _ _).mp ht
    have hok' := type_d_tenv_ok_helper.1 _ _ _ _ _ ht htsi.1
    obtain ⟨t1, dd1, dd2, rfl, hlds, hds, hdisj⟩ : ∃ t1 d1 d2, tids = d1 ∪ d2 ∧
        type_ds false tenv lds d1 t1 ∧ type_ds false (extend_dec_tenv t1 tenv) ds d2 tenv' ∧
        DISJOINT d1 d2 := by
      cases ht with
      | dlocal _ _ _ t1 _ d1 d2 h1 h2 h3 => exact ⟨t1, d1, d2, rfl, h1, h2, h3⟩
    have I1 := fun st' r he1 => ih1 st' r ctMap tenvS tenv dd1 t1 he1 hlds
      (type_sound_invariant_union _ _ _ _ _ dd2 _ htsi)
    rw [Aux.evaluate_Dlocal] at he
    rcases he1 : evaluate_decs st env lds with ⟨st1, env1 | e1⟩
    · rw [he1] at he
      dsimp only at he
      obtain ⟨M1, S1, a1, a2, a3, a4, a5⟩ := I1 _ _ he1
      have hcl := evaluate_clock.2.2 _ _ _ _ _ he1
      have tsi2 := Aux.tsi_second htsi a2 hdisj a5
      obtain ⟨M2, S2, b1, b2, b3, b4⟩ := ih2 st1 _ hcl _ _ M1 S1 _ dd2 tenv' he hds tsi2
      refine ⟨M2, S2, weakCT_trans _ _ _ ⟨b1, a1⟩, Aux.frange_trans a2 b2,
        store_type_extension_trans _ _ _ ⟨a3, b3⟩, ?_⟩
      cases r with
      | Rval env2 =>
        exact ⟨b4.1, Aux.tsi_ext htsi (weakCT_trans _ _ _ ⟨b1, a1⟩)
          (store_type_extension_trans _ _ _ ⟨a3, b3⟩) b4.2.2.1 b4.2.2.2.1 b4.2.2.2.2.2 b4.1 hok'⟩
      | Rerr e =>
        exact Aux.DR_err2 htsi (weakCT_trans _ _ _ ⟨b1, a1⟩)
          (store_type_extension_trans _ _ _ ⟨a3, b3⟩) b4
    · rw [he1] at he
      cases he
      obtain ⟨M1, S1, a1, a2, a3, a4⟩ := I1 _ _ he1
      exact ⟨M1, S1, a1, fun x hx => Or.inl (a2 x hx), a3, Aux.DR_err a4⟩
  · -- Denv
    intro st env n st' r ctMap tenvS tenv tids tenv' he ht htsi
    have ht := (type_ds_sing _ _ _ _ _).mp ht
    cases ht

/- HOL4:
Theorem decs_type_sound_no_check:
  ∀(st:'ffi semanticPrimitives$state) env ds st' r ctMap tenvS tenv tids tenv'.
   evaluate_decs st env ds = (st',r) ∧
   type_ds F tenv ds tids tenv' ∧
   type_sound_invariant st env ctMap tenvS tids tenv
   ⇒
   ∃ctMap' tenvS'.
     weakCT ctMap' ctMap ∧
     FRANGE ((SND o SND) o_f ctMap') DIFF FRANGE ((SND o SND) o_f ctMap) ⊆ tids ∧
     store_type_extension tenvS tenvS' ∧
     case r of
     | Rval env' =>
       type_all_env ctMap' tenvS' env' tenv' ∧
       type_sound_invariant st' (extend_dec_env env' env)
         ctMap' tenvS' {} (extend_dec_tenv tenv' tenv)
     | Rerr (Rraise err_v) =>
       type_v 0 ctMap' tenvS' err_v Texn ∧
       type_sound_invariant st' env ctMap' tenvS' {} tenv
     | Rerr (Rabort Rtype_error) => F
     | Rerr (Rabort Rtimeout_error) => T
     | Rerr (Rabort(Rffi_error _)) => T -/
theorem decs_type_sound_no_check {ffi : Type} :
    ∀ (st : state ffi) (env : sem_env value) (ds : List dec) (st' : state ffi)
      (r : result (sem_env value) value) (ctMap : ctMap_ty) (tenvS : tenv_store)
      (tenv : type_env) (tids : Set type_ident) (tenv' : type_env),
      evaluate_decs st env ds = (st', r) ∧
      type_ds false tenv ds tids tenv' ∧
      type_sound_invariant st env ctMap tenvS tids tenv
      →
      ∃ (ctMap' : ctMap_ty) (tenvS' : tenv_store),
        weakCT ctMap' ctMap ∧
        (FRANGE (o_f (Prod.snd ∘ Prod.snd) ctMap') \
          FRANGE (o_f (Prod.snd ∘ Prod.snd) ctMap)) ⊆ tids ∧
        store_type_extension tenvS tenvS' ∧
        (match r with
          | Rval env' =>
            type_all_env ctMap' tenvS' env' tenv' ∧
            type_sound_invariant st' (extend_dec_env env' env)
              ctMap' tenvS' ∅ (extend_dec_tenv tenv' tenv)
          | Rerr (Rraise err_v) =>
            type_v 0 ctMap' tenvS' err_v Texn ∧
            type_sound_invariant st' env ctMap' tenvS' ∅ tenv
          | Rerr (Rabort Rtype_error) => False
          | Rerr (Rabort Rtimeout_error) => True
          | Rerr (Rabort (Rffi_error _)) => True) := by
  rintro st env ds st' r ctMap tenvS tenv tids tenv' ⟨h1, h2, h3⟩
  obtain ⟨M, S, a1, a2, a3, a4⟩ := Aux.decs_sound st env ds st' r ctMap tenvS tenv tids tenv'
    h1 h2 h3
  refine ⟨M, S, a1, a2, a3, ?_⟩
  rcases r with env' | v | a
  · exact a4
  · exact a4
  · cases a <;> exact a4

/- HOL4:
Theorem decs_type_sound:
  ∀(st:'ffi semanticPrimitives$state) env ds extra_checks st' r ctMap tenvS tenv tids tenv'.
   evaluate_decs st env ds = (st',r) ∧
   type_ds extra_checks tenv ds tids tenv' ∧
   type_sound_invariant st env ctMap tenvS tids tenv
   ⇒
   ∃ctMap' tenvS'.
     weakCT ctMap' ctMap ∧
     FRANGE ((SND o SND) o_f ctMap') DIFF FRANGE ((SND o SND) o_f ctMap) ⊆ tids ∧
     store_type_extension tenvS tenvS' ∧
     case r of
     | Rval env' =>
       type_all_env ctMap' tenvS' env' tenv' ∧
       type_sound_invariant st' (extend_dec_env env' env)
         ctMap' tenvS' {} (extend_dec_tenv tenv' tenv)
     | Rerr (Rraise err_v) =>
       type_v 0 ctMap' tenvS' err_v Texn ∧
       type_sound_invariant st' env ctMap' tenvS' {} tenv
     | Rerr (Rabort Rtype_error) => F
     | Rerr (Rabort (Rffi_error _)) => T
     | Rerr (Rabort Rtimeout_error) => T -/
theorem decs_type_sound {ffi : Type} :
    ∀ (st : state ffi) (env : sem_env value) (ds : List dec) (extra_checks : Bool)
      (st' : state ffi) (r : result (sem_env value) value) (ctMap : ctMap_ty)
      (tenvS : tenv_store) (tenv : type_env) (tids : Set type_ident) (tenv' : type_env),
      evaluate_decs st env ds = (st', r) ∧
      type_ds extra_checks tenv ds tids tenv' ∧
      type_sound_invariant st env ctMap tenvS tids tenv
      →
      ∃ (ctMap' : ctMap_ty) (tenvS' : tenv_store),
        weakCT ctMap' ctMap ∧
        (FRANGE (o_f (Prod.snd ∘ Prod.snd) ctMap') \
          FRANGE (o_f (Prod.snd ∘ Prod.snd) ctMap)) ⊆ tids ∧
        store_type_extension tenvS tenvS' ∧
        (match r with
          | Rval env' =>
            type_all_env ctMap' tenvS' env' tenv' ∧
            type_sound_invariant st' (extend_dec_env env' env)
              ctMap' tenvS' ∅ (extend_dec_tenv tenv' tenv)
          | Rerr (Rraise err_v) =>
            type_v 0 ctMap' tenvS' err_v Texn ∧
            type_sound_invariant st' env ctMap' tenvS' ∅ tenv
          | Rerr (Rabort Rtype_error) => False
          | Rerr (Rabort (Rffi_error _)) => True
          | Rerr (Rabort Rtimeout_error) => True) := by
  rintro st env ds checks st' r ctMap tenvS tenv tids tenv' ⟨h1, h2, h3⟩
  obtain ⟨M, S, a1, a2, a3, a4⟩ := Aux.decs_sound st env ds st' r ctMap tenvS tenv tids tenv'
    h1 (type_d_check_uniq.2 _ _ _ _ _ h2) h3
  refine ⟨M, S, a1, a2, a3, ?_⟩
  rcases r with env' | v | a
  · exact a4
  · exact a4
  · cases a <;> exact a4

/- HOL4:
Theorem semantics_type_sound:
  ∀(st:'ffi semanticPrimitives$state) env tops r checks ctMap tenvS tenv new_tenv tids.
   semantics_prog st env tops r ∧
   type_ds checks tenv tops tids new_tenv ∧
   type_sound_invariant st env ctMap tenvS tids tenv ⇒
   r ≠ Fail -/
theorem semantics_type_sound {ffi : Type} :
    ∀ (st : state ffi) (env : sem_env value) (tops : List dec) (r : behaviour)
      (checks : Bool) (ctMap : ctMap_ty) (tenvS : tenv_store) (tenv : type_env)
      (new_tenv : type_env) (tids : Set type_ident),
      semantics_prog st env tops r ∧
      type_ds checks tenv tops tids new_tenv ∧
      type_sound_invariant st env ctMap tenvS tids tenv →
      r ≠ Fail := by
  rintro st env tops r checks ctMap tenvS tenv new_tenv tids ⟨h1, h2, h3⟩ rfl
  obtain ⟨k, hk⟩ := h1
  unfold evaluate_prog_with_clock at hk
  rcases he : evaluate_decs { st with clock := k } env tops with ⟨st', r⟩
  rw [he] at hk
  have hk : r = Rerr (Rabort Rtype_error) := hk
  subst hk
  have htsi : type_sound_invariant { st with clock := k } env ctMap tenvS tids tenv := h3
  obtain ⟨M, S, -, -, -, a4⟩ := Aux.decs_sound _ env tops st' _ ctMap tenvS tenv tids new_tenv
    he (type_d_check_uniq.2 _ _ _ _ _ h2) htsi
  exact a4

end

end CmlTS
