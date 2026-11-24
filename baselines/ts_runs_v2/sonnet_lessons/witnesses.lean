import CmlTS

/-!
Witnesses for the fidelity contract, run `sonnet_lessons`.
Every theorem below is an equation written only with mapped constants (and the image of `ARB`).
HOL4 side of each V-C1: the saved defining theorem (cited per witness) has two models that
disagree on the equation, because the equation fixes a value the saved theorem leaves open.
-/

open Classical

/-! ### V-C1: `HD []` (HOL4 listScript.sml:138 saves only `HD (h::t) = h`) -/
theorem vc1_HD_nil : HD ([] : List Nat) = ARB := rfl

/-! ### V-C1: `CHR n`, n >= 256 (HOL4 stringScript.sml:29 `char_BIJ`: CHR is only constrained
    by `ORD (CHR r) = r <=> r < 256` and `CHR (ORD a) = a`) -/
theorem vc1_CHR_300_eq_ARB : CHR 300 = ARB := by
  unfold CHR; simp

theorem vc1_CHR_300_eq_CHR_301 : CHR 300 = CHR 301 := by
  unfold CHR; simp

/-! ### V-C1: `int_div`, `int_mod` at 0 (HOL4 integerScript.sml:1989, :2074: new_specification
    only for j <> 0) -/
theorem vc1_int_div_zero : int_div 1 0 = int_div 2 0 := by
  unfold int_div; simp

theorem vc1_int_mod_zero_eq_ARB : int_mod 7 0 = ARB := by
  unfold int_mod; simp

/-! ### V-C1: `FAPPLY` outside `FDOM` (HOL4 finite_mapScript.sml: FAPPLY f x = OUTL (fmap_REP f x),
    only the FDOM case is saved) -/
theorem vc1_FAPPLY_outside : FAPPLY (FEMPTY : FMap Nat Nat) 0 = FAPPLY (FEMPTY : FMap Nat Nat) 1 := by
  unfold FAPPLY FEMPTY; simp

/-! ### V-C1: `CARD` of an infinite set (HOL4 pred_setScript.sml:3428 `CARD_DEF` is a
    new_specification that constrains CARD only on FINITE sets) -/
theorem vc1_CARD_UNIV : CARD (UNIV : Set Nat) = 0 := by
  have hinf : ¬ FINITE (UNIV : Set Nat) := by
    rintro ⟨l, hl⟩
    have key : ∀ l : List Nat, ∀ x ∈ l, x ≤ l.foldr (· + ·) 0 := by
      intro l
      induction l with
      | nil => simp
      | cons a t ih =>
        intro x hx
        simp only [List.mem_cons] at hx
        simp only [List.foldr_cons]
        rcases hx with rfl | hx
        · omega
        · have := ih x hx
          omega
    have h := hl (l.foldr (· + ·) 0 + 1) (by simp [UNIV])
    have := key l _ h
    omega
  unfold CARD
  simp [hinf]

/-! ### V-C1: `MAP3` (HOL4 miscScript.sml:74, only the [],[],[] and cons,cons,cons clauses saved) -/
theorem vc1_MAP3_mismatch :
    MAP3 (fun a b c : Nat => a + b + c) [1] [] [] = ARB := by
  unfold MAP3; simp

/-! ### V-C1: location accessors (HOL4 locationScript.sml:6, 11, 16, 20: only the POSN clause) -/
theorem vc1_locnrow_UNKNOWN : locnrow .UNKNOWNpt = ARB := by
  unfold locnrow; simp

theorem vc1_locncol_EOF : locncol .EOFpt = ARB := by
  unfold locncol; simp

theorem vc1_locn_rowupdate_EOF (f : Nat → Nat) : locn_rowupdate f .EOFpt = ARB := by
  unfold locn_rowupdate; simp

theorem vc1_locn_colupdate_UNKNOWN (f : Nat → Nat) : locn_colupdate f .UNKNOWNpt = ARB := by
  unfold locn_colupdate; simp

/-! ### V-C1: `dest_Refv` (HOL4 semanticPrimitivesPropsScript.sml:165: only the Refv clause) -/
theorem vc1_dest_Refv_W8array : dest_Refv (store_v.W8array [] : store_v Nat) = ARB := by
  unfold dest_Refv; simp

/-! ### V-C1: `FV_dec` for Dmod, Dlocal, Denv (HOL4 semanticPrimitivesPropsScript.sml:220:
    five clauses, none for these constructors) -/
theorem vc1_FV_dec_Denv : FV_dec (.Denv default) = ARB := by
  unfold FV_dec; simp

theorem vc1_FV_dec_Dmod : FV_dec (.Dmod default []) = ARB := by
  unfold FV_dec; simp

theorem vc1_FV_dec_Dlocal : FV_dec (.Dlocal [] []) = ARB := by
  unfold FV_dec; simp

/-! ### V-C1: `the_Litv_*` (HOL4 semanticPrimitivesScript.sml:718-734: one clause each) -/
theorem vc1_the_Litv_IntLit_Conv : the_Litv_IntLit (.Conv none []) = ARB := by
  unfold the_Litv_IntLit; simp

theorem vc1_the_Litv_Char_Conv : the_Litv_Char (.Conv none []) = ARB := by
  unfold the_Litv_Char; simp

/-! ### V-C1: `type_def_to_ctMap` on lists of different length (HOL4 typeSysPropsScript.sml:1502:
    clauses only for [] [] and (_::_) (_::_)) -/
theorem vc1_type_def_to_ctMap_mismatch (ns : Namespace modN typeN (List tvarN × Ty)) :
    type_def_to_ctMap ns 0 [] [3] = ARB := by
  unfold type_def_to_ctMap; simp

/-! ### V-C1 across constants: one shared `ARB` per type makes unrelated constants equal -/
theorem vc1_shared_ARB_Nat_HD_locnrow : HD ([] : List Nat) = locnrow .UNKNOWNpt := by
  unfold HD locnrow; simp

theorem vc1_shared_ARB_Nat_FAPPLY_locncol :
    FAPPLY (FEMPTY : FMap Nat Nat) 5 = locncol .EOFpt := by
  unfold FAPPLY FEMPTY locncol; simp

/-! ### V-C2: Hilbert choice over an unsatisfiable predicate equals `ARB`.
    HOL4: `ARB` is `new_constant` (boolScript.sml:245) without equations, `@x. F` is the choice
    function's value at the empty predicate; two HOL4 models can make them differ. -/
theorem vc2_eps_false_eq_ARB : Classical.epsilon (fun _ : Nat => False) = (ARB : Nat) := by
  unfold ARB Classical.epsilon Classical.strongIndefiniteDescription
  simp

/-- consumer in the translation: `closest_such` over the empty set of floats is `ARB`. -/
theorem vc2_closest_such_empty (x : RealX) :
    closest_such (fun _ => True) (fun _ : float 52 11 => False) x = ARB := by
  unfold closest_such ARB Classical.epsilon Classical.strongIndefiniteDescription
  have h : ∀ a : float 52 11, ¬ is_closest (fun _ : float 52 11 => False) x a :=
    fun a ha => ha.1
  simp [h]
