import CmlTS.Proofs.TypeAux
import CmlTS.Weakening

/-! Auxiliary lemmas for type soundness. -/

set_option linter.unusedVariables false

namespace CmlTS

open scoped Classical

/-! ### `LIST_REL` on lists of known length -/

section LR

variable {α β : Type} {R : α → β → Prop}

theorem Aux.LR0 {l : List α} (h : LIST_REL R l []) : l = [] := by
  cases l with
  | nil => rfl
  | cons a l => exact h.elim

theorem Aux.LRc {l : List α} {b : β} {bs : List β} (h : LIST_REL R l (b :: bs)) :
    ∃ a as, l = a :: as ∧ R a b ∧ LIST_REL R as bs := by
  cases l with
  | nil => exact h.elim
  | cons a l => exact ⟨a, l, rfl, h.1, h.2⟩

theorem Aux.LR1 {l : List α} {b : β} (h : LIST_REL R l [b]) : ∃ a, l = [a] ∧ R a b := by
  obtain ⟨a, as, rfl, h1, h2⟩ := Aux.LRc h
  cases Aux.LR0 h2
  exact ⟨a, rfl, h1⟩

theorem Aux.LR2 {l : List α} {b c : β} (h : LIST_REL R l [b, c]) :
    ∃ x y, l = [x, y] ∧ R x b ∧ R y c := by
  obtain ⟨a, as, rfl, h1, h2⟩ := Aux.LRc h
  obtain ⟨y, rfl, h3⟩ := Aux.LR1 h2
  exact ⟨a, y, rfl, h1, h3⟩

theorem Aux.LR3 {l : List α} {b c d : β} (h : LIST_REL R l [b, c, d]) :
    ∃ x y z, l = [x, y, z] ∧ R x b ∧ R y c ∧ R z d := by
  obtain ⟨a, as, rfl, h1, h2⟩ := Aux.LRc h
  obtain ⟨y, z, rfl, h3, h4⟩ := Aux.LR2 h2
  exact ⟨a, y, z, rfl, h1, h3, h4⟩

theorem Aux.LR5 {l : List α} {b c d e f : β} (h : LIST_REL R l [b, c, d, e, f]) :
    ∃ x y z u w, l = [x, y, z, u, w] ∧ R x b ∧ R y c ∧ R z d ∧ R u e ∧ R w f := by
  obtain ⟨a, as, rfl, h1, h2⟩ := Aux.LRc h
  obtain ⟨a', as, rfl, h1', h2⟩ := Aux.LRc h2
  obtain ⟨y, z, u, rfl, h3, h4, h5⟩ := Aux.LR3 h2
  exact ⟨a, a', y, z, u, rfl, h1, h1', h3, h4, h5⟩

theorem Aux.LR_replicate {l : List α} {b : β} :
    LIST_REL R l (List.replicate l.length b) ↔ ∀ x, x ∈ l → R x b := by
  induction l with
  | nil => simp [LIST_REL]
  | cons a l ih => simp [LIST_REL, List.replicate_succ, ih]

end LR

theorem Aux.length_eq_two {α : Type} {l : List α} : l.length = 2 ↔ ∃ x y, l = [x, y] := by
  rcases l with _ | ⟨x, _ | ⟨y, _ | ⟨z, l⟩⟩⟩ <;> simp

theorem Aux.length_eq_three {α : Type} {l : List α} :
    l.length = 3 ↔ ∃ x y z, l = [x, y, z] := by
  rcases l with _ | ⟨x, _ | ⟨y, _ | ⟨z, _ | ⟨w, l⟩⟩⟩⟩ <;> simp

/-! ### inversion of `type_v` -/

theorem Aux.FLOOKUP_not_prim {m : ctMap_ty} {s : stamp} {a : List tvarN} {b : List typ}
    {ti : type_ident} (h : ctMap_ok m) (hl : FLOOKUP m s = some (a, b, ti))
    (hp : ti ∈ prim_type_nums ∧ ti ≠ Texn_num) : False := by
  cases s with
  | TypeStamp cn n => exact h.2.2.1 _ _ _ _ _ hl hp.1
  | ExnStamp n => exact hp.2 (h.2.1 _ _ _ _ hl).2

/-- The values of a primitive type. -/
def Aux.prim_shape (tvs : Nat) (m : ctMap_ty) (S : tenv_store) (v : value) (ts : List typ)
    (ti : type_ident) : Prop :=
  (∃ i, v = Litv (lit.IntLit i) ∧ ts = [] ∧ ti = Tint_num) ∨
  (∃ i, v = Litv (lit.Char i) ∧ ts = [] ∧ ti = Tchar_num) ∨
  (∃ i, v = Litv (lit.StrLit i) ∧ ts = [] ∧ ti = Tstring_num) ∨
  (∃ i, v = Litv (lit.Word8 i) ∧ ts = [] ∧ ti = Tword8_num) ∨
  (∃ i, v = Litv (lit.Word64 i) ∧ ts = [] ∧ ti = Tword64_num) ∨
  (∃ i, v = Litv (lit.Float64 i) ∧ ts = [] ∧ ti = Tdouble_num) ∨
  (∃ vs, v = Conv none vs ∧ LIST_REL (type_v tvs m S) vs ts ∧ ti = Ttup_num) ∨
  (∃ env n e, v = Closure env n e ∧ True ∧ ti = Tfn_num) ∨
  (∃ env funs n, v = Recclosure env funs n ∧ True ∧ ti = Tfn_num) ∨
  (∃ n, v = Loc true n ∧ (∃ t, ts = [t] ∧ check_freevars 0 [] t ∧
    FLOOKUP S n = some (Ref_t t)) ∧ ti = Tref_num) ∨
  (∃ n, v = Loc true n ∧ (ts = [] ∧ FLOOKUP S n = some W8array_t) ∧ ti = Tword8array_num) ∨
  (∃ n, v = Loc true n ∧ (∃ t, ts = [t] ∧ check_freevars 0 [] t ∧
    FLOOKUP S n = some (Varray_t t)) ∧ ti = Tarray_num) ∨
  (∃ vs, v = Vectorv vs ∧ (∃ t, ts = [t] ∧ check_freevars 0 [] t ∧
    ∀ v, v ∈ vs → type_v tvs m S v t) ∧ ti = Tvector_num)

theorem Aux.type_v_inv {tvs : Nat} {m : ctMap_ty} {S : tenv_store} {v : value} {t : typ}
    (h : type_v tvs m S v t) : ∃ ts ti, t = Tapp ts ti ∧
    ((∃ s vs tvs' ts0, v = Conv (some s) vs ∧ EVERY (check_freevars tvs []) ts ∧
        tvs'.length = ts.length ∧
        LIST_REL (type_v tvs m S) vs (ts0.map (type_subst (alist_to_fmap (tvs'.zip ts)))) ∧
        FLOOKUP m s = some (tvs', ts0, ti)) ∨
      ((ti ∈ prim_type_nums ∧ ti ≠ Texn_num) ∧ Aux.prim_shape tvs m S v ts ti)) := by
  unfold Aux.prim_shape
  cases h with
  | intLit _ _ _ i =>
    exact ⟨[], Tint_num, rfl, Or.inr ⟨⟨by simp [prim_type_nums], by decide⟩, by simp⟩⟩
  | char _ _ _ i =>
    exact ⟨[], Tchar_num, rfl, Or.inr ⟨⟨by simp [prim_type_nums], by decide⟩, by simp⟩⟩
  | strLit _ _ _ i =>
    exact ⟨[], Tstring_num, rfl, Or.inr ⟨⟨by simp [prim_type_nums], by decide⟩, by simp⟩⟩
  | word8 _ _ _ i =>
    exact ⟨[], Tword8_num, rfl, Or.inr ⟨⟨by simp [prim_type_nums], by decide⟩, by simp⟩⟩
  | word64 _ _ _ i =>
    exact ⟨[], Tword64_num, rfl, Or.inr ⟨⟨by simp [prim_type_nums], by decide⟩, by simp⟩⟩
  | float64 _ _ _ i =>
    exact ⟨[], Tdouble_num, rfl, Or.inr ⟨⟨by simp [prim_type_nums], by decide⟩, by simp⟩⟩
  | conv _ _ _ vs tvs' s ts' ts ti h1 h2 h3 h4 h5 =>
    refine ⟨ts', ti, rfl, Or.inl ⟨s, vs, tvs', ts, rfl, h1, h2, ?_, h5⟩⟩
    rw [← Aux.FUPDATE_LIST_reverse]
    exact LIST_REL_iff_aux.2 ⟨h3, h4⟩
  | tup _ _ _ vs ts h1 h2 =>
    exact ⟨ts, Ttup_num, rfl, Or.inr ⟨⟨by simp [prim_type_nums], by decide⟩,
      Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl
        ⟨vs, rfl, LIST_REL_iff_aux.2 ⟨h1, h2⟩, rfl⟩⟩⟩
  | closure _ _ _ env tenv tenvE n e t1 t2 =>
    exact ⟨[t1, t2], Tfn_num, rfl, Or.inr ⟨⟨by simp [prim_type_nums], by decide⟩, by simp⟩⟩
  | recclosure _ _ _ env funs n t tenv tenvE b _ _ _ _ _ _ hf hl _ _ =>
    obtain ⟨t1, t2, rfl, _⟩ := type_funs_Tfn _ _ _ _ () _ _ ⟨hf, hl⟩
    exact ⟨[t1, t2], Tfn_num, rfl, Or.inr ⟨⟨by simp [prim_type_nums], by decide⟩, by simp⟩⟩
  | ref _ _ _ n t h1 h2 =>
    exact ⟨[t], Tref_num, rfl, Or.inr ⟨⟨by simp [prim_type_nums], by decide⟩,
      Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
        Or.inl ⟨n, rfl, ⟨t, rfl, h1, h2⟩, rfl⟩⟩⟩
  | w8array _ _ _ n h =>
    exact ⟨[], Tword8array_num, rfl, Or.inr ⟨⟨by simp [prim_type_nums], by decide⟩,
      Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
        Or.inr <| Or.inl ⟨n, rfl, ⟨rfl, h⟩, rfl⟩⟩⟩
  | varray _ _ _ n t h1 h2 =>
    exact ⟨[t], Tarray_num, rfl, Or.inr ⟨⟨by simp [prim_type_nums], by decide⟩,
      Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
        Or.inr <| Or.inr <| Or.inl ⟨n, rfl, ⟨t, rfl, h1, h2⟩, rfl⟩⟩⟩
  | vector _ _ _ vs t h1 h2 =>
    exact ⟨[t], Tvector_num, rfl, Or.inr ⟨⟨by simp [prim_type_nums], by decide⟩,
      Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
        Or.inr <| Or.inr <| Or.inr ⟨vs, rfl, ⟨t, rfl, h1, h2⟩, rfl⟩⟩⟩

theorem Aux.type_v_prim {tvs : Nat} {m : ctMap_ty} {S : tenv_store} {v : value}
    {ts : List typ} {ti : type_ident} (h : type_v tvs m S v (Tapp ts ti)) (hc : ctMap_ok m)
    (hp : ti ∈ prim_type_nums ∧ ti ≠ Texn_num) : Aux.prim_shape tvs m S v ts ti := by
  obtain ⟨ts', ti', he, h⟩ := Aux.type_v_inv h
  cases he
  rcases h with ⟨s, vs, tvs', ts0, _, _, _, _, hl⟩ | ⟨_, h⟩
  · exact (Aux.FLOOKUP_not_prim hc hl hp).elim
  · exact h

theorem Aux.type_v_con {tvs : Nat} {m : ctMap_ty} {S : tenv_store} {v : value}
    {ts : List typ} {ti : type_ident} (h : type_v tvs m S v (Tapp ts ti)) (hc : ctMap_ok m)
    {s : stamp} {a : List tvarN} {b : List typ} (hl : FLOOKUP m s = some (a, b, ti)) :
    ∃ s' vs tvs' ts0, v = Conv (some s') vs ∧ same_type s s' ∧
        EVERY (check_freevars tvs []) ts ∧ tvs'.length = ts.length ∧
        LIST_REL (type_v tvs m S) vs (ts0.map (type_subst (alist_to_fmap (tvs'.zip ts)))) ∧
        FLOOKUP m s' = some (tvs', ts0, ti) := by
  obtain ⟨ts', ti', he, h⟩ := Aux.type_v_inv h
  cases he
  rcases h with ⟨s', vs, tvs', ts0, h1, h2, h3, h4, h5⟩ | ⟨hp, _⟩
  · exact ⟨s', vs, tvs', ts0, h1, hc.2.2.2 _ _ _ _ _ _ _ ⟨hl, h5⟩, h2, h3, h4, h5⟩
  · exact (Aux.FLOOKUP_not_prim hc hl hp).elim

theorem Aux.type_v_conv_intro {tvs : Nat} {m : ctMap_ty} {S : tenv_store} {vs : List value}
    {tvs' : List tvarN} {s : stamp} {ts' ts : List typ} {ti : type_ident}
    (h1 : EVERY (check_freevars tvs []) ts') (h2 : tvs'.length = ts'.length)
    (h3 : LIST_REL (type_v tvs m S) vs (ts.map (type_subst (alist_to_fmap (tvs'.zip ts')))))
    (h4 : FLOOKUP m s = some (tvs', ts, ti)) :
    type_v tvs m S (Conv (some s) vs) (Tapp ts' ti) := by
  refine type_v_conv_aux _ _ _ _ _ _ _ _ _ h1 h2 ?_ h4
  rw [Aux.FUPDATE_LIST_reverse]
  exact h3

/-! ### lists -/

theorem Aux.list_subst (a : mlstring) (t : typ) :
    ([Tvar a, Tlist (Tvar a)].map (type_subst (alist_to_fmap ([a].zip [t])))) = [t, Tlist t] := by
  have h : type_subst (alist_to_fmap ([a].zip [t])) (Tvar a) = t :=
    Aux.ts_var_zip (by simp [ALOOKUP])
  have h2 : type_subst (alist_to_fmap ([a].zip [t])) (Tlist (Tvar a)) = Tlist t := by
    unfold Tlist
    rw [Aux.ts_app, List.map_cons, h]; rfl
  simp only [List.map_cons, List.map_nil, h, h2]

theorem Aux.type_v_nil {n : Nat} {m : ctMap_ty} {S : tenv_store} {t : typ}
    (hm : ctMap_has_lists m) (hc : check_freevars n [] t) :
    type_v n m S (Conv (some (TypeStamp ml!"[]" list_type_num)) []) (Tlist t) :=
  Aux.type_v_conv_intro (ts := []) ⟨hc, trivial⟩ rfl trivial hm.1

theorem Aux.type_v_cons {n : Nat} {m : ctMap_ty} {S : tenv_store} {t : typ} {x y : value}
    (hm : ctMap_has_lists m) (hx : type_v n m S x t) (hy : type_v n m S y (Tlist t)) :
    type_v n m S (Conv (some (TypeStamp ml!"::" list_type_num)) [x, y]) (Tlist t) := by
  refine Aux.type_v_conv_intro ⟨type_v_freevars _ _ _ _ _ hx, trivial⟩ rfl ?_ hm.2.1
  rw [Aux.list_subst]
  exact ⟨hx, hy, trivial⟩

theorem Aux.type_v_cons_inv {n : Nat} {m : ctMap_ty} {S : tenv_store} {t : typ} {x y : value}
    (hm : ctMap_has_lists m)
    (h : type_v n m S (Conv (some (TypeStamp ml!"::" list_type_num)) [x, y]) (Tlist t)) :
    type_v n m S x t ∧ type_v n m S y (Tlist t) := by
  obtain ⟨tvs', ts', ts, ti, he, h1, h2, h3, h4⟩ := type_v_conv_inv_aux _ _ _ _ _ _ h
  cases he
  rw [hm.2.1] at h4
  cases h4
  rw [Aux.FUPDATE_LIST_reverse, Aux.list_subst] at h3
  exact ⟨h3.1, h3.2.1⟩

theorem Aux.type_v_list_to_v_intro {n : Nat} {m : ctMap_ty} {S : tenv_store} {t : typ}
    (hm : ctMap_has_lists m) (hc : check_freevars n [] t) {xs : List value}
    (h : ∀ x, x ∈ xs → type_v n m S x t) : type_v n m S (list_to_v xs) (Tlist t) := by
  induction xs with
  | nil => exact Aux.type_v_nil hm hc
  | cons x xs ih =>
    exact Aux.type_v_cons hm (h x List.mem_cons_self)
      (ih fun y hy => h y (List.mem_cons_of_mem _ hy))

theorem Aux.v_to_list_inv (n : Nat) : ∀ (x : value) (xs : List value), sizeOf x ≤ n →
    v_to_list x = some xs → x = list_to_v xs := by
  induction n with
  | zero => intro x xs hs; cases x <;> simp at hs <;> omega
  | succ n ih =>
    intro x xs hs h
    unfold v_to_list at h
    split at h
    · split at h
      · rename_i hst; cases h; rw [hst]; rfl
      · cases h
    · rename_i st v1 v2
      split at h
      · rename_i hst
        split at h
        · cases h
        · rename_i vs hv
          cases h
          rw [list_to_v, ← ih v2 vs (by simp at hs; omega) hv, hst]
      · cases h
    · cases h

/-! ### canonical forms -/

section canon

attribute [local simp] Tarray_num Tbool_num Tchar_num Texn_num Tfn_num Tint_num Tlist_num
  Tref_num Tstring_num Ttup_num Tvector_num Tword64_num Tword8_num Tword8array_num Tdouble_num

variable {tvs : Nat} {m : ctMap_ty} {S : tenv_store} {v : value}

theorem Aux.canon_int (h : type_v tvs m S v Tint) (hc : ctMap_ok m) :
    ∃ i, v = Litv (lit.IntLit i) := by
  have h := Aux.type_v_prim (ts := []) (ti := Tint_num) h hc ⟨by simp [prim_type_nums], by decide⟩
  simpa [Aux.prim_shape] using h

theorem Aux.canon_char (h : type_v tvs m S v Tchar) (hc : ctMap_ok m) :
    ∃ i, v = Litv (lit.Char i) := by
  have h := Aux.type_v_prim (ts := []) (ti := Tchar_num) h hc ⟨by simp [prim_type_nums], by decide⟩
  simpa [Aux.prim_shape] using h

theorem Aux.canon_str (h : type_v tvs m S v Tstring) (hc : ctMap_ok m) :
    ∃ i, v = Litv (lit.StrLit i) := by
  have h := Aux.type_v_prim (ts := []) (ti := Tstring_num) h hc
    ⟨by simp [prim_type_nums], by decide⟩
  simpa [Aux.prim_shape] using h

theorem Aux.canon_word8 (h : type_v tvs m S v Tword8) (hc : ctMap_ok m) :
    ∃ i, v = Litv (lit.Word8 i) := by
  have h := Aux.type_v_prim (ts := []) (ti := Tword8_num) h hc
    ⟨by simp [prim_type_nums], by decide⟩
  simpa [Aux.prim_shape] using h

theorem Aux.canon_word64 (h : type_v tvs m S v Tword64) (hc : ctMap_ok m) :
    ∃ i, v = Litv (lit.Word64 i) := by
  have h := Aux.type_v_prim (ts := []) (ti := Tword64_num) h hc
    ⟨by simp [prim_type_nums], by decide⟩
  simpa [Aux.prim_shape] using h

theorem Aux.canon_double (h : type_v tvs m S v Tdouble) (hc : ctMap_ok m) :
    ∃ i, v = Litv (lit.Float64 i) := by
  have h := Aux.type_v_prim (ts := []) (ti := Tdouble_num) h hc
    ⟨by simp [prim_type_nums], by decide⟩
  simpa [Aux.prim_shape] using h

theorem Aux.canon_tup {ts : List typ} (h : type_v tvs m S v (Ttup ts)) (hc : ctMap_ok m) :
    ∃ vs, v = Conv none vs ∧ LIST_REL (type_v tvs m S) vs ts := by
  have h := Aux.type_v_prim (ts := ts) (ti := Ttup_num) h hc
    ⟨by simp [prim_type_nums], by decide⟩
  simpa [Aux.prim_shape] using h

theorem Aux.canon_fn {t1 t2 : typ} (h : type_v tvs m S v (Tfn t1 t2)) (hc : ctMap_ok m) :
    (∃ env n e, v = Closure env n e) ∨ (∃ env funs n, v = Recclosure env funs n) := by
  have h := Aux.type_v_prim (ts := [t1, t2]) (ti := Tfn_num) h hc
    ⟨by simp [prim_type_nums], by decide⟩
  simpa [Aux.prim_shape] using h

theorem Aux.canon_ref {t : typ} (h : type_v tvs m S v (Tref t)) (hc : ctMap_ok m) :
    ∃ n, v = Loc true n ∧ check_freevars 0 [] t ∧ FLOOKUP S n = some (Ref_t t) := by
  have h := Aux.type_v_prim (ts := [t]) (ti := Tref_num) h hc
    ⟨by simp [prim_type_nums], by decide⟩
  simpa [Aux.prim_shape] using h

theorem Aux.canon_w8array (h : type_v tvs m S v Tword8array) (hc : ctMap_ok m) :
    ∃ n, v = Loc true n ∧ FLOOKUP S n = some W8array_t := by
  have h := Aux.type_v_prim (ts := []) (ti := Tword8array_num) h hc
    ⟨by simp [prim_type_nums], by decide⟩
  simpa [Aux.prim_shape] using h

theorem Aux.canon_array {t : typ} (h : type_v tvs m S v (Tarray t)) (hc : ctMap_ok m) :
    ∃ n, v = Loc true n ∧ check_freevars 0 [] t ∧ FLOOKUP S n = some (Varray_t t) := by
  have h := Aux.type_v_prim (ts := [t]) (ti := Tarray_num) h hc
    ⟨by simp [prim_type_nums], by decide⟩
  simpa [Aux.prim_shape] using h

theorem Aux.canon_vector {t : typ} (h : type_v tvs m S v (Tvector t)) (hc : ctMap_ok m) :
    ∃ vs, v = Vectorv vs ∧ check_freevars 0 [] t ∧ ∀ v, v ∈ vs → type_v tvs m S v t := by
  have h := Aux.type_v_prim (ts := [t]) (ti := Tvector_num) h hc
    ⟨by simp [prim_type_nums], by decide⟩
  simpa [Aux.prim_shape] using h

end canon

section canon2

variable {tvs : Nat} {m : ctMap_ty} {S : tenv_store} {v : value}

theorem Aux.canon_bool (h : type_v tvs m S v Tbool) (hc : ctMap_ok m)
    (hb : ctMap_has_bools m) : ∃ b, v = Boolv b := by
  obtain ⟨s', vs, tvs', ts0, rfl, hs, h1, h2, h3, h4⟩ := Aux.type_v_con h hc hb.1
  cases s' with
  | ExnStamp n => exact hs.elim
  | TypeStamp cn n =>
    have hs : bool_type_num = n := hs
    subst hs
    by_cases hT : cn = ml!"True"
    · subst hT
      rw [hb.1] at h4; cases h4
      cases Aux.LR0 h3
      exact ⟨true, rfl⟩
    · by_cases hF : cn = ml!"False"
      · subst hF
        rw [hb.2.1] at h4; cases h4
        cases Aux.LR0 h3
        exact ⟨false, rfl⟩
      · rw [hb.2.2 cn ⟨hT, hF⟩] at h4; cases h4

theorem Aux.canon_list {t : typ} (h : type_v tvs m S v (Tlist t)) (hc : ctMap_ok m)
    (hm : ctMap_has_lists m) :
    v = Conv (some (TypeStamp ml!"[]" list_type_num)) [] ∨
    ∃ x y, v = Conv (some (TypeStamp ml!"::" list_type_num)) [x, y] ∧ type_v tvs m S x t ∧
      type_v tvs m S y (Tlist t) := by
  obtain ⟨s', vs, tvs', ts0, rfl, hs, h1, h2, h3, h4⟩ := Aux.type_v_con h hc hm.1
  cases s' with
  | ExnStamp n => exact hs.elim
  | TypeStamp cn n =>
    have hs : list_type_num = n := hs
    subst hs
    by_cases hC : cn = ml!"::"
    · subst hC
      rw [hm.2.1] at h4; cases h4
      rw [Aux.list_subst] at h3
      obtain ⟨x, y, rfl, hx, hy⟩ := Aux.LR2 h3
      exact Or.inr ⟨x, y, rfl, hx, hy⟩
    · by_cases hN : cn = ml!"[]"
      · subst hN
        rw [hm.1] at h4; cases h4
        cases Aux.LR0 h3
        exact Or.inl rfl
      · rw [hm.2.2 cn ⟨hC, hN⟩] at h4; cases h4

theorem Aux.list_canon (hc : ctMap_ok m) (hm : ctMap_has_lists m) (t : typ) (n : Nat) :
    ∀ v, sizeOf v ≤ n → type_v tvs m S v (Tlist t) →
      ∃ vs, v_to_list v = some vs ∧ (∀ x, x ∈ vs → type_v tvs m S x t) ∧
        (t = Tchar → ∃ vs, v_to_char_list v = some vs) ∧
        (t = Tstring → ∃ str, vs_to_string vs = some str) := by
  induction n with
  | zero => intro v hs; cases v <;> simp at hs <;> omega
  | succ n ih =>
    intro v hs h
    rcases Aux.canon_list h hc hm with rfl | ⟨x, y, rfl, hx, hy⟩
    · exact ⟨[], by simp [v_to_list], by simp, fun _ => ⟨[], by simp [v_to_char_list]⟩,
        fun _ => ⟨ml!"", rfl⟩⟩
    · obtain ⟨vs, h1, h2, h3, h4⟩ := ih y (by simp at hs; omega) hy
      refine ⟨x :: vs, by simp [v_to_list, h1], ?_, ?_, ?_⟩
      · intro z hz
        rcases List.mem_cons.1 hz with rfl | hz
        · exact hx
        · exact h2 z hz
      · rintro rfl
        obtain ⟨c, rfl⟩ := Aux.canon_char hx hc
        obtain ⟨cs, hcs⟩ := h3 rfl
        exact ⟨c :: cs, by simp [v_to_char_list, hcs]⟩
      · rintro rfl
        obtain ⟨c, rfl⟩ := Aux.canon_str hx hc
        obtain ⟨cs, hcs⟩ := h4 rfl
        exact ⟨strcat c cs, by simp [vs_to_string, hcs]⟩

theorem Aux.do_eq_list_ok {vs1 vs2 : List value} {ts : List typ}
    (ih : ∀ v1, v1 ∈ vs1 → ∀ v2 t, type_v tvs m S v1 t → type_v tvs m S v2 t →
      do_eq v1 v2 ≠ Eq_type_error)
    (h1 : LIST_REL (type_v tvs m S) vs1 ts) (h2 : LIST_REL (type_v tvs m S) vs2 ts) :
    do_eq_list vs1 vs2 ≠ Eq_type_error := by
  induction vs1 generalizing vs2 ts with
  | nil =>
    cases vs2 <;> simp [do_eq_list]
  | cons v1 vs1 ihl =>
    cases vs2 with
    | nil => simp [do_eq_list]
    | cons v2 vs2 =>
      cases ts with
      | nil => exact h1.elim
      | cons t ts =>
        have ha := ih v1 List.mem_cons_self v2 t h1.1 h2.1
        have hb := ihl (fun v hv => ih v (List.mem_cons_of_mem _ hv)) h1.2 h2.2
        rw [do_eq_list]
        cases hd : do_eq v1 v2 with
        | Eq_type_error => exact absurd hd ha
        | Eq_val r => cases r <;> simp [hb]

theorem Aux.do_eq_ok (hc : ctMap_ok m) (n : Nat) :
    ∀ v1, sizeOf v1 ≤ n → ∀ v2 t, type_v tvs m S v1 t → type_v tvs m S v2 t →
      do_eq v1 v2 ≠ Eq_type_error := by
  induction n with
  | zero => intro v hs; cases v <;> simp at hs <;> omega
  | succ n ih =>
    intro v1 hs v2 t h1 h2
    obtain ⟨ts, ti, rfl, h1'⟩ := Aux.type_v_inv h1
    rcases h1' with ⟨s, vs, tvs', ts0, rfl, a1, a2, a3, a4⟩ | ⟨hp, h1'⟩
    · obtain ⟨s', vs', tvs'', ts0', rfl, b0, b1, b2, b3, b4⟩ := Aux.type_v_con h2 hc a4
      rw [do_eq]
      split
      · rename_i he
        obtain ⟨he, _⟩ := he
        cases he
        rw [a4] at b4; cases b4
        refine Aux.do_eq_list_ok (fun v1 hv v2 t => ih v1 ?_ v2 t) a3 b3
        have := List.sizeOf_lt_of_mem hv
        simp at hs; omega
      · rw [if_pos (show ctor_same_type (some s) (some s') from b0)]
        simp
    · have h2' := Aux.type_v_prim h2 hc hp
      unfold Aux.prim_shape at h1' h2'
      rcases h1' with ⟨i, rfl, ht, rfl⟩ | ⟨i, rfl, ht, rfl⟩ | ⟨i, rfl, ht, rfl⟩ |
        ⟨i, rfl, ht, rfl⟩ | ⟨i, rfl, ht, rfl⟩ | ⟨i, rfl, ht, rfl⟩ | ⟨vs, rfl, ht, rfl⟩ |
        ⟨env, x, e, rfl, ht, rfl⟩ | ⟨env, x, e, rfl, ht, rfl⟩ | ⟨l, rfl, ht, rfl⟩ |
        ⟨l, rfl, ht, rfl⟩ | ⟨l, rfl, ht, rfl⟩ | ⟨vs, rfl, ht, rfl⟩ <;>
      rcases h2' with ⟨j, rfl, ht', hti⟩ | ⟨j, rfl, ht', hti⟩ | ⟨j, rfl, ht', hti⟩ |
        ⟨j, rfl, ht', hti⟩ | ⟨j, rfl, ht', hti⟩ | ⟨j, rfl, ht', hti⟩ | ⟨vs', rfl, ht', hti⟩ |
        ⟨env', x', e', rfl, ht', hti⟩ | ⟨env', x', e', rfl, ht', hti⟩ | ⟨l', rfl, ht', hti⟩ |
        ⟨l', rfl, ht', hti⟩ | ⟨l', rfl, ht', hti⟩ | ⟨vs', rfl, ht', hti⟩
      all_goals first
        | exact absurd hti (by decide)
        | (simp [do_eq, lit_same_type]; done)
        | (rw [do_eq, if_pos ⟨rfl, (Aux.LIST_REL_length ht).trans (Aux.LIST_REL_length ht').symm⟩]
           refine Aux.do_eq_list_ok (fun v1 hv v2 t => ih v1 ?_ v2 t) ht ht'
           have := List.sizeOf_lt_of_mem hv
           simp at hs; omega)
        | (obtain ⟨t, rfl, _, ht⟩ := ht
           obtain ⟨t', he, _, ht'⟩ := ht'
           cases he
           rw [do_eq]
           split
           · rename_i hl
             have hl : vs.length = vs'.length := hl
             refine Aux.do_eq_list_ok (ts := List.replicate vs.length t)
               (fun v1 hv v2 t => ih v1 ?_ v2 t) (Aux.LR_replicate.2 ht)
               (by rw [hl]; exact Aux.LR_replicate.2 ht')
             have := List.sizeOf_lt_of_mem hv
             simp at hs; omega
           · simp)

end canon2

/-! ### stores -/

theorem Aux.ste_iff {α β : Type} {S1 S2 : fmap α β} :
    (∃ S', S2 = FUNION S' S1 ∧ ∀ l, FLOOKUP S' l = none ∨ FLOOKUP S1 l = none) ↔
      ∀ x v, FLOOKUP S1 x = some v → FLOOKUP S2 x = some v := by
  constructor
  · rintro ⟨S', rfl, h⟩ x v hx
    rw [Aux.FLOOKUP_FUNION]
    rcases h x with h | h
    · rw [h]; exact hx
    · rw [h] at hx; cases hx
  · intro h
    refine ⟨⟨fun x => if FLOOKUP S1 x = none then S2.rep x else none, ?_⟩, ?_, ?_⟩
    · obtain ⟨l, hl⟩ := S2.finite
      refine ⟨l, fun a ha => hl a fun hn => ha ?_⟩
      dsimp only
      split
      · exact hn
      · rfl
    · refine Aux.fmap_ext fun x => ?_
      rw [Aux.FLOOKUP_FUNION]
      show FLOOKUP S2 x = match (if FLOOKUP S1 x = none then S2.rep x else none) with
        | some v => some v
        | none => FLOOKUP S1 x
      cases hx : FLOOKUP S1 x with
      | none =>
        rw [if_pos rfl]
        show S2.rep x = _
        cases S2.rep x <;> rfl
      | some v => simp only [reduceCtorEq, if_false]; exact h x v hx
    · intro l
      by_cases hl : FLOOKUP S1 l = none
      · exact Or.inr hl
      · exact Or.inl (if_neg hl)

theorem Aux.store_lookup_eq {α : Type} (l : Nat) (st : List (store_v α)) :
    store_lookup l st = st[l]? := by
  unfold store_lookup
  split
  · rename_i h; rw [Aux.EL_getElem? h]
  · rename_i h; rw [List.getElem?_eq_none (by omega)]

theorem Aux.type_s_lookup {m : ctMap_ty} {st : List (store_v value)} {S : tenv_store} {l : Nat}
    {t : store_t} (h : type_s m st S) (hl : FLOOKUP S l = some t) :
    ∃ sv, store_lookup l st = some sv ∧ type_sv m S sv t := by
  obtain ⟨h1, h2⟩ := h l
  obtain ⟨sv, hsv⟩ := h1.1 ⟨t, hl⟩
  exact ⟨sv, hsv, h2 _ _ ⟨hl, hsv⟩⟩

end CmlTS
