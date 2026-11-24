import CmlTS

/-
  Witnesses for the fidelity findings on opus_nolessons.
  Each V-C1 finding has
    (a) a Lean theorem proving the equation that the Lean definition makes provable, and
    (b) where cheap, a statement showing that the HOL4 defining theorem does not determine
        the value (two interpretations of the HOL4 constant that satisfy every saved clause
        but disagree, the second one being "ARB is some other value").
  HOL4 side: the saved theorem and its source line are given in each comment.
  HOL4 ARB is `new_constant` (boolScript.sml:245), so no equation about ARB is in Phi.
-/
set_option autoImplicit false
namespace CmlTS
open Classical

/-! ## V-C1: location.locnrow, locncol, locn_rowupdate, locn_colupdate
HOL4: locationScript.sml: `locnrow (POSN r c) = r` etc. (single clause, new_specification via Prim_rec;
locationTheory exports only `locnrow_def`, no `_primitive` theorem). -/

theorem vc1_locnrow : locnrow EOFpt = (ARB : Nat) := rfl
theorem vc1_locnrow_model :
    ∃ (f : locn → Nat) (a : Nat), (∀ r c, f (POSN r c) = r) ∧ f EOFpt ≠ a :=
  ⟨fun x => match x with | .POSN r _ => r | _ => 0, 1, fun _ _ => rfl, by decide⟩

theorem vc1_locncol : locncol UNKNOWNpt = (ARB : Nat) := rfl
theorem vc1_locncol_model :
    ∃ (f : locn → Nat) (a : Nat), (∀ r c, f (POSN r c) = c) ∧ f UNKNOWNpt ≠ a :=
  ⟨fun x => match x with | .POSN _ c => c | _ => 0, 1, fun _ _ => rfl, by decide⟩

theorem vc1_locn_rowupdate (f : Nat → Nat) : locn_rowupdate f EOFpt = (ARB : locn) := rfl
theorem vc1_locn_rowupdate_model :
    ∃ (g : (Nat → Nat) → locn → locn) (a : locn),
      (∀ f r c, g f (POSN r c) = POSN (f r) c) ∧ ∀ f, g f EOFpt ≠ a :=
  ⟨fun f x => match x with | .POSN r c => .POSN (f r) c | _ => .UNKNOWNpt, .EOFpt,
    fun _ _ _ => rfl, fun _ => by intro h; cases h⟩

theorem vc1_locn_colupdate (f : Nat → Nat) : locn_colupdate f EOFpt = (ARB : locn) := rfl
theorem vc1_locn_colupdate_model :
    ∃ (g : (Nat → Nat) → locn → locn) (a : locn),
      (∀ f r c, g f (POSN r c) = POSN r (f c)) ∧ ∀ f, g f EOFpt ≠ a :=
  ⟨fun f x => match x with | .POSN r c => .POSN r (f c) | _ => .UNKNOWNpt, .EOFpt,
    fun _ _ _ => rfl, fun _ => by intro h; cases h⟩

/-! ## V-C1: misc.MAP3 (lower confidence, see REPORT)
HOL4: miscScript.sml:74, saved `misc.MAP3_def` = the two clauses `MAP3 f [] [] [] = []` and
`MAP3 f (h1::t1) (h2::t2) (h3::t3) = ...`; no `MAP3_*primitive*` theorem in miscTheory. -/

theorem vc1_MAP3 (f : Nat → Nat → Nat → Nat) :
    MAP3 f ([] : List Nat) [0] ([] : List Nat) = (ARB : List Nat) := rfl

/-! ## V-C1: semanticPrimitivesProps.dest_Refv
HOL4: semanticPrimitivesPropsScript.sml:165 `dest_Refv (Refv v) = v`; listed in the theory as a plain
definition, no `_primitive`. -/

theorem vc1_dest_Refv : dest_Refv (store_v.Varray ([] : List Nat)) = (ARB : Nat) := rfl

/-! ## V-C1: semanticPrimitivesProps.FV_dec
HOL4: semanticPrimitivesPropsScript.sml:220, five clauses (Dlet, Dletrec, Dtype, Dtabbrev, Dexn);
`dec` also has Dmod, Dlocal (astScript.sml:244-246).  Lean adds `| _ => ARB`. -/

theorem vc1_FV_dec (m : modN) : FV_dec (dec.Dmod m []) = (ARB : Set (ident modN varN)) := rfl
theorem vc1_FV_dec_local : FV_dec (dec.Dlocal [] []) = (ARB : Set (ident modN varN)) := rfl

/-! ## V-C1: typeSysProps.type_def_to_ctMap
HOL4: typeSysPropsScript.sml:1502, saved `type_def_to_ctMap_def` has the clauses for ([],[]) and
(td::tds, id::ids) only. -/

theorem vc1_type_def_to_ctMap (tenvT : Namespace mlstring mlstring (List mlstring × typ)) (n : Nat) :
    type_def_to_ctMap (α := Nat) (β := Nat) (γ := Nat) tenvT n [] [0]
      = (ARB : List (stamp × Nat × List typ × Nat)) := rfl

/-! ## V-C1: list.THE, list.HD, list.EL
HOL4: optionScript.sml:176 `THE (SOME x) = x`; listScript.sml:138 `HD (h::t) = h`;
EL 0 l = HD l, EL (SUC n) l = EL n (TL l).  Every saved theorem that mentions HD and [] is guarded by `<> []`
(checked by scanning the DB of the HOL4 build: list.HD_REVERSE, LIST_NOT_NIL, rich_list.HEAD_MEM, ...). -/

theorem vc1_THE_none : THE (none : Option Nat) = ARB := rfl
theorem vc1_THE_none_model :
    ∃ (g : Option Nat → Nat) (a : Nat), (∀ x, g (some x) = x) ∧ g none ≠ a :=
  ⟨fun o => match o with | some x => x | none => 0, 1, fun _ => rfl, by decide⟩

theorem vc1_HD_nil : HD ([] : List Nat) = ARB := rfl
theorem vc1_HD_nil_model :
    ∃ (g : List Nat → Nat) (a : Nat), (∀ h t, g (h :: t) = h) ∧ g [] ≠ a :=
  ⟨fun l => match l with | h :: _ => h | [] => 0, 1, fun _ _ => rfl, by decide⟩

theorem vc1_EL_nil : EL 3 ([] : List Nat) = ARB := rfl
theorem vc1_EL_nil_zero : EL 0 ([] : List Nat) = ARB := rfl

/-! ## V-C1: finite_map.FAPPLY
HOL4: finite_mapScript.sml:180 `FAPPLY f x = OUTL (fmap_REP f x)`; for x not in FDOM it is OUTL (INR one),
and OUTL has only the INL clause.  Saved: finite_map.NOT_FDOM_FAPPLY_FEMPTY (line 562):
`x NOTIN FDOM f ==> f ' x = FEMPTY ' x`, which is consistent with any value. -/

theorem vc1_FAPPLY_FEMPTY (x : Nat) : FAPPLY (FEMPTY : fmap Nat Nat) x = ARB := rfl

/-! ## V-C1: string.CHR
HOL4: stringScript.sml:29 char_BIJ: `(!a. CHR (ORD a) = a) /\ (!r. r < 256 <=> ORD (CHR r) = r)`;
CHR 256 is some char other than the one with code 256 (there is none), nothing more. -/

theorem vc1_CHR_256 : CHR 256 = (ARB : char) := by
  unfold CHR; simp

/-! ## V-C1: int_div, int_mod at 0
HOL4: integerScript.sml:1988 / 2074, new_specification with hypothesis `~(j = 0)`;
INT_DIV_0 (line 2034) is `q <> 0 ==> 0 / q = 0`. -/

theorem vc1_int_div_0 (i : Int) : int_div i 0 = ARB := by simp [int_div]
theorem vc1_int_mod_0 (i : Int) : int_mod i 0 = ARB := by simp [int_mod]
theorem vc1_int_div_0_const : int_div 7 0 = int_div 8 0 := by simp [int_div]

/-! ## V-C1: pred_set.CARD on infinite sets
HOL4: pred_setScript.sml:3428 `CARD_DEF = new_specification ("CARD_DEF", ["CARD"], CARD_EXISTS)` with only
`CARD EMPTY = 0` and `FINITE s ==> CARD (x INSERT s) = ...`.  No saved theorem fixes CARD of an infinite
set (scan of the HOL4 DB for CARD with FINITE/INFINITE: only the finite-set lemmas).
Lean: every infinite set has no duplicate-free enumeration, so SELECT returns the default, hence
CARD of any two infinite sets of the same type coincide and equal ARB. -/

theorem mem_le_sum' (l : List Nat) (x : Nat) (h : x ∈ l) : x ≤ l.sum := by
  induction l with
  | nil => simp at h
  | cons a t ih =>
    simp only [List.mem_cons] at h
    simp only [List.sum_cons]
    rcases h with rfl | h
    · omega
    · have := ih h; omega

theorem no_enum_of_unbounded (s : Set Nat) (hs : ∀ n, ∃ x, n ≤ x ∧ x ∈ s) (n : Nat) :
    ¬ ∃ l : List Nat, l.Nodup ∧ (∀ x, x ∈ l ↔ x ∈ s) ∧ l.length = n := by
  rintro ⟨l, _, h, _⟩
  obtain ⟨x, hx, hxs⟩ := hs (l.sum + 1)
  have := mem_le_sum' l x ((h x).2 hxs)
  omega

theorem vc1_CARD_infinite_ARB : CARD (UNIV : Set Nat) = ARB := by
  have hU : ∀ n, ∃ x, n ≤ x ∧ x ∈ (UNIV : Set Nat) := fun n => ⟨n, Nat.le_refl n, True.intro⟩
  have hne : ¬ ∃ n : Nat, ∃ l : List Nat, l.Nodup ∧ (∀ x, x ∈ l ↔ x ∈ (UNIV : Set Nat)) ∧ l.length = n :=
    fun ⟨n, h⟩ => no_enum_of_unbounded _ hU n h
  unfold CARD SELECT ARB
  simp only [Classical.epsilon, Classical.strongIndefiniteDescription, dif_neg hne]

theorem vc1_CARD_infinite_eq : CARD (UNIV : Set Nat) = CARD {n : Nat | 5 ≤ n} := by
  have hU : ∀ n, ∃ x, n ≤ x ∧ x ∈ (UNIV : Set Nat) := fun n => ⟨n, Nat.le_refl n, True.intro⟩
  have hF : ∀ n, ∃ x, n ≤ x ∧ x ∈ ({n : Nat | 5 ≤ n} : Set Nat) :=
    fun n => ⟨n + 5, by omega, by show 5 ≤ n + 5; omega⟩
  unfold CARD SELECT
  have e : (fun n => ∃ l : List Nat, l.Nodup ∧ (∀ x, x ∈ l ↔ x ∈ (UNIV : Set Nat)) ∧ l.length = n)
         = (fun n => ∃ l : List Nat, l.Nodup ∧ (∀ x, x ∈ l ↔ x ∈ ({n : Nat | 5 ≤ n} : Set Nat)) ∧ l.length = n) := by
    funext n
    exact propext ⟨fun h => absurd h (no_enum_of_unbounded _ hU n), fun h => absurd h (no_enum_of_unbounded _ hF n)⟩
  rw [e]

/-! ## V-C2: SELECT over an unsatisfiable predicate equals ARB
Equation in Lean: `(@n. F) = ARB`.  HOL4: ARB is `new_constant` (boolScript.sml:245), `@` is the Hilbert
operator with only SELECT_AX (`P x ==> P (@x. P x)`), which says nothing when no x satisfies P, so
`(@n:num. F) = ARB` is not provable.  Cause: Lean `ARB := Classical.choice` and `Classical.epsilon`
returns the same `Classical.choice` when the predicate is empty (Set.lean:13, 16). -/

theorem vc2_SELECT_false_eq_ARB : SELECT (fun _ : Nat => False) = ARB := by
  have hne : ¬ ∃ n : Nat, (fun _ : Nat => False) n := fun ⟨_, h⟩ => h
  unfold SELECT ARB
  simp only [Classical.epsilon, Classical.strongIndefiniteDescription, dif_neg hne]

end CmlTS
