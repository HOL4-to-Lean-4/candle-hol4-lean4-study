import CandleLean
open HOL Candle Classical
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
noncomputable section
theorem mem_fdom {α β : Type} (f : fmap α β) (x : α) : x ∈ FDOM f ↔ f.rep x ≠ none := Iff.rfl

theorem flookup_eq {α β : Type} [Nonempty β] (f : fmap α β) (k : α) : FLOOKUP f k = f.rep k := by
  unfold FLOOKUP FAPPLY
  cases h : f.rep k <;> simp [h, mem_fdom]

theorem frange_iff {α β : Type} [Nonempty β] (f : fmap α β) (y : β) :
    y ∈ FRANGE f ↔ ∃ x, f.rep x = some y := by
  unfold FRANGE FAPPLY
  constructor
  · rintro ⟨x, hx, hy⟩
    refine ⟨x, ?_⟩
    have hx' : f.rep x ≠ none := hx
    cases h : f.rep x
    · exact absurd h hx'
    · simp [h] at hy; rw [hy]
  · rintro ⟨x, hx⟩
    exact ⟨x, by simp [mem_fdom, hx], by simp [hx]⟩

/-- the standard signature -/
def stdsig : sig :=
  (FUPDATE (FUPDATE FEMPTY (mls "fun", 2)) (mls "bool", 0),
   FUPDATE FEMPTY (mls "=", Fun (Tyvar (mls "A")) (Fun (Tyvar (mls "A")) BoolTy)))

theorem fun_ne_bool : mls "fun" ≠ mls "bool" := by decide

theorem stdsig_fun : FLOOKUP (tysof stdsig) (mls "fun") = some 2 := by
  simp [flookup_eq, stdsig, tysof, FUPDATE, FEMPTY, fun_ne_bool]
theorem stdsig_bool : FLOOKUP (tysof stdsig) (mls "bool") = some 0 := by
  simp [flookup_eq, stdsig, tysof, FUPDATE, FEMPTY]
theorem stdsig_eq : FLOOKUP (tmsof stdsig) (mls "=") =
    some (Fun (Tyvar (mls "A")) (Fun (Tyvar (mls "A")) BoolTy)) := by
  simp [flookup_eq, stdsig, tmsof, FUPDATE, FEMPTY]

theorem stdsig_std : is_std_sig stdsig := ⟨stdsig_fun, stdsig_bool, stdsig_eq⟩

theorem stdsig_type_ok_Bool : type_ok (tysof stdsig) BoolTy := by
  simp [BoolTy, type_ok, stdsig_bool, EVERY]

theorem stdsig_type_ok_eq : type_ok (tysof stdsig) (Fun (Tyvar (mls "A")) (Fun (Tyvar (mls "A")) BoolTy)) := by
  have := stdsig_type_ok_Bool
  simp [Fun, type_ok, stdsig_fun, EVERY] at this ⊢
  exact this

/-- a theory over the standard signature with axioms `P` -/
theorem stdsig_theory_ok (P : term → Prop) (hP : ∀ p, P p → term_ok stdsig p ∧ has_type p BoolTy) :
    theory_ok (stdsig, P) := by
  refine ⟨?_, hP, stdsig_std⟩
  intro ty hty
  rw [thy_tmsof] at hty
  obtain ⟨x, hx⟩ := (frange_iff _ _).mp hty
  simp [tmsof, sigof, stdsig, FUPDATE, FEMPTY] at hx
  by_cases h : x = mls "="
  · simp [h] at hx
    rw [← hx]
    exact stdsig_type_ok_eq
  · simp [h] at hx


/-! A small structure `U = Nat → Prop`, `mem a x := ∃ n, a = {n} ∧ n ∈ x`; it has separation. -/
abbrev UU := Nat → Prop
def single (n : Nat) : UU := fun m => m = n
def mem0 : UU → UU → Prop := fun a x => ∃ n, a = single n ∧ x n

theorem mem0_sep : is_separation mem0 (fun x P => fun n => x n ∧ P (single n)) := by
  intro x P a
  constructor
  · rintro ⟨n, rfl, h1, h2⟩
    exact ⟨⟨n, rfl, h1⟩, h2⟩
  · rintro ⟨⟨n, rfl, h1⟩, h2⟩
    exact ⟨n, rfl, h1, h2⟩

instance : Nonempty UU := ⟨fun _ => False⟩

theorem mem0_sub : is_separation mem0 (sub mem0) := by
  unfold sub
  exact Classical.epsilon_spec (p := fun s => is_separation mem0 s) ⟨_, mem0_sep⟩

theorem mem0_empty (a : UU) : ¬ mem0 a (empty mem0) := by
  intro h
  unfold empty at h
  exact ((mem0_sub _ _ a).mp h).2

theorem single_mem : mem0 (single 0) (single 0) := ⟨0, rfl, rfl⟩

theorem single_ne_true : single 0 ≠ true_ mem0 := by
  intro h
  unfold true_ at h
  have : mem0 (single 0) (empty mem0) := by rw [← h]; exact single_mem
  exact mem0_empty _ this

/-- the trivial interpretation: every type is `{0}`, every constant is `{0}` -/
def i0 : interpretation UU := (fun _ _ => single 0, fun _ _ => single 0)
def v0 : valuation UU := (fun _ => single 0, fun _ => single 0)

theorem typesem_i0 (τ : tyval UU) (hτ : ∀ x, τ x = single 0) (ty : type) :
    typesem (tyaof i0) τ ty = single 0 := by
  cases ty with
  | Tyvar s => simp [typesem, hτ]
  | Tyapp n args => simp [typesem, i0, tyaof]

theorem v0_valuation (tysig : tysig) : is_valuation0 mem0 tysig (tyaof i0) v0 := by
  refine ⟨?_, ?_⟩
  · intro x
    exact ⟨single 0, single_mem⟩
  · intro v ty _
    have : typesem (tyaof i0) (tyvof v0) ty = single 0 := typesem_i0 _ (fun _ => rfl) ty
    rw [this]
    exact single_mem


namespace Mut
/-- mutated `entails0` (the `models0` premise is dropped) -/
def entails0 {U : Type u} [Nonempty U] (mem : U → U → Prop) (thyh : thy × List term) (c : term) : Prop :=
  theory_ok thyh.1 ∧
  EVERY (term_ok (sigof thyh.1)) (c :: thyh.2) ∧
  EVERY (fun p => has_type p BoolTy) (c :: thyh.2) ∧
  hypset_ok thyh.2 ∧
  ∀ i : interpretation U, satisfies0 mem i (sigof thyh.1, thyh.2, c)
end Mut

/-- Axiom `x : bool` with no hypotheses. The base holds (the axiom is satisfied in every model),
the mutant does not (the trivial interpretation `i0` gives `x` a value different from `true_`). -/
theorem witness : ∃ (mem : UU → UU → Prop) (thyh : thy × List term) (c : term),
    entails0 mem thyh c ∧ ¬ Mut.entails0 mem thyh c := by
  let p : term := Var (mls "x") BoolTy
  have hp : term_ok stdsig p := stdsig_type_ok_Bool
  have hb : has_type p BoolTy := has_type.Var
  have hth : theory_ok (stdsig, fun t => t = p) := by
    apply stdsig_theory_ok
    intro q hq
    subst hq
    exact ⟨hp, hb⟩
  refine ⟨mem0, ((stdsig, fun t => t = p), []), p, ?_, ?_⟩
  · refine ⟨hth, ?_, ?_, ?_, ?_⟩
    · simp [EVERY, sigof, hp]
    · simp [EVERY, hb]
    · simp [hypset_ok, SORTED]
    · intro i hi
      exact hi.2.2 p rfl
  · intro h
    have h5 := h.2.2.2.2 i0 v0 ⟨v0_valuation _, by simp [EVERY]⟩
    rw [(termsem0_def _ _ _).1] at h5
    exact single_ne_true h5

#print axioms witness
