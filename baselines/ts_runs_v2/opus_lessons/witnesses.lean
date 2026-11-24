import CmlTS
open CmlTS
set_option autoImplicit false

/-! Witnesses for the opus_lessons translation.
    Each theorem proves an equation written only with mapped constants (and the image of ARB)
    that HOL4 does not prove from the theorems its theories save.  The HOL4 side is given in
    the comment above each witness.  Check:
      cd E:/ts_ws/runs/opus_lessons_v2/merged && lake env lean E:/ts_ws/score/opus_lessons/witnesses.lean -/

/-! ## Tier 1 (no choice term in the equation; ARB image only) -/

/- V-C1 prelude HD.  HOL4: listScript.sml:138 `Definition HD[simp]:` saves only the cons clause. -/
theorem w_hd_nil_arb : (HD ([] : List Nat)) = ARB := rfl

/- V-C1 prelude EL (inherits HD).  HOL4: listScript.sml EL_def: EL 0 = HD, EL (SUC n) l = EL n (TL l);
   nothing saved for n >= LENGTH l. -/
theorem w_el_oob_arb : (EL 3 ([] : List Nat)) = ARB := rfl

/- V-C1 prelude THE.  HOL4: optionScript.sml saves THE_DEF for SOME only. -/
theorem w_the_none_arb : (THE (none : Option Nat)) = ARB := rfl

/- V-C1 shared ARB across unrelated constants: HD [] = THE NONE (HOL4 proves neither side's value). -/
theorem w_hd_the_shared : (HD ([] : List Nat)) = THE (none : Option Nat) := rfl

/- V-C1 prelude CHR.  HOL4: stringScript.sml:29 `define_new_type_bijections {ABS="CHR", REP="ORD"}`;
   saved facts: CHR_ORD (line 39), ORD_CHR (line 40), ORD_CHR_RWT (line 42, r < 256 only),
   CHR_11 (line 32).  Nothing identifies CHR 256 with CHR 257. -/
theorem w_chr_256_257 : CHR 256 = CHR 257 := by simp [CHR]

theorem w_chr_256_arb : CHR 256 = ARB := by simp [CHR]

/- V-C1 prelude FAPPLY outside the domain.  HOL4: finite_mapScript.sml:180 FAPPLY_DEF
   `FAPPLY f x = OUTL (fmap_REP f x)`, and OUTL (INR _) is not specified by sumTheory. -/
theorem w_fapply_empty_arb : FAPPLY (FEMPTY : fmap Nat Nat) 0 = ARB := by
  simp [FAPPLY, FEMPTY]

/- V-C1 prelude int_div / int_mod at 0.  HOL4: integerScript.sml:1970-1989 and 2063-2073: the
   specifications only constrain ~(j = 0) (int_div_exists0, int_mod_exists0); INT_DIV (line 1994)
   and INT_DIV_0 (line 2034) both assume ~(m = 0) / ~(q = 0). -/
theorem w_int_div_zero_arb : int_div 5 0 = ARB := by simp [int_div]

theorem w_int_div_zero_same : int_div 1 0 = int_div 2 0 := by simp [int_div]

theorem w_int_mod_zero_same : int_mod 1 0 = int_mod 2 0 := by simp [int_mod, int_div]

theorem w_int_div_mod_shared : int_div 1 0 = int_mod 1 0 := by simp [int_div, int_mod]

/- V-C1 prelude CARD of an infinite set.  HOL4: pred_setScript.sml:3428 `CARD_DEF` (new_specification,
   theorems CARD_EMPTY line 3434 and CARD_INSERT line 3436, the latter under FINITE s).
   Two different infinite sets get the same cardinality value.
   (Proof: both predicates in `select` are unsatisfiable, so both selects are the same choice.) -/
theorem w_bdd : ∀ l : List Nat, ∃ N, ∀ x, x ∈ l → x < N
  | [] => ⟨0, by simp⟩
  | a :: t => by
    obtain ⟨N, h⟩ := w_bdd t
    refine ⟨max (a + 1) N, fun x hx => ?_⟩
    rcases List.mem_cons.mp hx with rfl | hx
    · omega
    · have := h x hx; omega

theorem w_card_unbounded (s : Set Nat) (hs : ∀ n : Nat, ∃ m, m > n ∧ m ∈ s) :
    CARD s = select (fun _ : Nat => False) := by
  unfold CARD
  congr 1
  funext n
  apply propext
  constructor
  · rintro ⟨l, _, _, hl⟩
    obtain ⟨N, hN⟩ := w_bdd l
    obtain ⟨m, hm, hms⟩ := hs N
    have := hN m ((hl m).mpr hms)
    omega
  · intro h; exact h.elim

theorem w_card_infinite_equal :
    CARD (UNIV : Set Nat) = CARD (setOf fun n : Nat => n % 2 = 0) := by
  rw [w_card_unbounded UNIV (fun n => ⟨n + 1, by omega, trivial⟩),
      w_card_unbounded (setOf fun n : Nat => n % 2 = 0)
        (fun n => ⟨2 * n + 2, by omega, by show (2 * n + 2) % 2 = 0; omega⟩)]

theorem w_card_univ_arb : CARD (UNIV : Set Nat) = ARB := by
  rw [w_card_unbounded UNIV (fun n => ⟨n + 1, by omega, trivial⟩)]
  -- select of an unsatisfiable predicate is ARB
  unfold select ARB Classical.epsilon Classical.strongIndefiniteDescription
  simp

/- V-C1 MAP3.  HOL4: miscScript.sml:74-77 saves only [] [] [] and cons/cons/cons. -/
theorem w_map3_mismatch :
    MAP3 (fun (a b c : Nat) => a) ([] : List Nat) [1] ([] : List Nat) = ARB := rfl

theorem w_map3_mismatch_shared :
    MAP3 (fun (a b c : Nat) => a) ([] : List Nat) [1] ([] : List Nat)
      = MAP3 (fun (a b c : Nat) => b) [2] ([] : List Nat) ([] : List Nat) := rfl

/- V-C1 location accessors.  HOL4: locationScript.sml:6-8, 11-13, 16-18, 20-22 save only the POSN clause. -/
theorem w_locnrow_unknown : locnrow locn.UNKNOWNpt = ARB := rfl

theorem w_locncol_eof : locncol locn.EOFpt = ARB := rfl

theorem w_locn_rowupdate_unknown : locn_rowupdate (fun x => x + 1) locn.UNKNOWNpt = ARB := rfl

theorem w_locn_colupdate_eof : locn_colupdate (fun x => x + 1) locn.EOFpt = ARB := rfl

theorem w_locn_row_col_shared : locnrow locn.UNKNOWNpt = locncol locn.EOFpt := rfl

/- V-C1 the_Litv_*.  HOL4: semanticPrimitivesScript.sml:718-736 save only the matching literal clause. -/
theorem w_the_Litv_IntLit_char (c : char) : the_Litv_IntLit (Litv (lit.Char c)) = ARB := rfl

theorem w_the_Litv_Char_int (i : Int) : the_Litv_Char (Litv (lit.IntLit i)) = ARB := rfl

theorem w_the_Litv_Word8_int (i : Int) : the_Litv_Word8 (Litv (lit.IntLit i)) = ARB := rfl

/- shared ARB between two different constants of the same type (word64): -/
theorem w_the_Litv_Word64_Float64 (i : Int) :
    the_Litv_Word64 (Litv (lit.IntLit i)) = the_Litv_Float64 (Litv (lit.IntLit i)) := rfl

/- V-C1 dest_Refv.  HOL4: semanticPrimitivesPropsScript.sml:165-167 saves only the Refv clause. -/
theorem w_dest_Refv_w8array : dest_Refv (store_v.W8array ([] : List word8) : store_v value) = ARB := rfl

/- V-C1 FV_dec.  HOL4: semanticPrimitivesPropsScript.sml:220-225 has five clauses, none for Dmod/Dlocal/Denv. -/
theorem w_FV_dec_denv (n : tvarN) : FV_dec (dec.Denv n) = ARB := rfl

/- V-C1 type_def_to_ctMap.  HOL4: typeSysPropsScript.sml:1502-1510 saves only [] [] and cons/cons. -/
theorem w_type_def_to_ctMap_mismatch (tenvT : Namespace mlstring mlstring (List mlstring × typ)) (next : Nat) :
    type_def_to_ctMap tenvT next ([] : List (List mlstring × mlstring × List (conN × List ast_t)))
      [(0 : Nat)] = ARB := rfl

/-! ## Tier 2 (a Hilbert-choice term is needed in the equation) -/

/- V-C2 select of an unsatisfiable predicate is the image of ARB.  HOL4: `@x. F` is an
   uninterpreted element; boolScript.sml:245 (ARB is a new_constant) and no saved theorem
   identifies it with ARB.  Also the origin of the prelude's `sqrt` of a negative number. -/
theorem w_select_false_arb : (select (fun _ : Nat => False)) = (ARB : Nat) := by
  unfold select ARB Classical.epsilon Classical.strongIndefiniteDescription
  simp
