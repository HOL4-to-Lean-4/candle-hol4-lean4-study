import CandleLean
open Candle HOL Classical

/-- Statement of the mutant (the `Const`-`Var` clause removed), abstracted over the relation `R` that stands for `term_lt`. -/
def MutStmtR (R : term → term → Prop) : Prop :=
    (∀ (x1 : mlstring) (ty1 : type) (x2 : mlstring) (ty2 : type),
      R (Var x1 ty1) (Var x2 ty2) ↔
        LEX mlstring_lt type_lt (x1, ty1) (x2, ty2)) ∧
    (∀ (a : mlstring) (b : type) (c : mlstring) (d : type),
      R (Var a b) (Const c d) ↔ True) ∧
    (∀ (a : mlstring) (b : type) (c d : term), R (Var a b) (Comb c d) ↔ True) ∧
    (∀ (a : mlstring) (b : type) (c d : term), R (Var a b) (Abs c d) ↔ True) ∧
    (∀ (x1 : mlstring) (ty1 : type) (x2 : mlstring) (ty2 : type),
      R (Const x1 ty1) (Const x2 ty2) ↔
        LEX mlstring_lt type_lt (x1, ty1) (x2, ty2)) ∧
    (∀ (a : mlstring) (b : type) (c d : term), R (Const a b) (Comb c d) ↔ True) ∧
    (∀ (a : mlstring) (b : type) (c d : term), R (Const a b) (Abs c d) ↔ True) ∧
    (∀ (a b : term) (c : mlstring) (d : type), R (Comb a b) (Var c d) ↔ False) ∧
    (∀ (a b : term) (c : mlstring) (d : type), R (Comb a b) (Const c d) ↔ False) ∧
    (∀ (s1 s2 t1 t2 : term),
      R (Comb s1 s2) (Comb t1 t2) ↔ LEX R R (s1, s2) (t1, t2)) ∧
    (∀ (a b c d : term), R (Comb a b) (Abs c d) ↔ True) ∧
    (∀ (a b : term) (c : mlstring) (d : type), R (Abs a b) (Var c d) ↔ False) ∧
    (∀ (a b : term) (c : mlstring) (d : type), R (Abs a b) (Const c d) ↔ False) ∧
    (∀ (a b c d : term), R (Abs a b) (Comb c d) ↔ False) ∧
    (∀ (s1 s2 t1 t2 : term),
      R (Abs s1 s2) (Abs t1 t2) ↔ LEX R R (s1, s2) (t1, t2))

/-- The base statement `term_lt_thm`, abstracted over `R`. -/
def BaseStmtR (R : term → term → Prop) : Prop :=
    (∀ (x1 : mlstring) (ty1 : type) (x2 : mlstring) (ty2 : type),
      R (Var x1 ty1) (Var x2 ty2) ↔
        LEX mlstring_lt type_lt (x1, ty1) (x2, ty2)) ∧
    (∀ (a : mlstring) (b : type) (c : mlstring) (d : type),
      R (Var a b) (Const c d) ↔ True) ∧
    (∀ (a : mlstring) (b : type) (c d : term), R (Var a b) (Comb c d) ↔ True) ∧
    (∀ (a : mlstring) (b : type) (c d : term), R (Var a b) (Abs c d) ↔ True) ∧
    (∀ (a : mlstring) (b : type) (c : mlstring) (d : type),
      R (Const a b) (Var c d) ↔ False) ∧
    (∀ (x1 : mlstring) (ty1 : type) (x2 : mlstring) (ty2 : type),
      R (Const x1 ty1) (Const x2 ty2) ↔
        LEX mlstring_lt type_lt (x1, ty1) (x2, ty2)) ∧
    (∀ (a : mlstring) (b : type) (c d : term), R (Const a b) (Comb c d) ↔ True) ∧
    (∀ (a : mlstring) (b : type) (c d : term), R (Const a b) (Abs c d) ↔ True) ∧
    (∀ (a b : term) (c : mlstring) (d : type), R (Comb a b) (Var c d) ↔ False) ∧
    (∀ (a b : term) (c : mlstring) (d : type), R (Comb a b) (Const c d) ↔ False) ∧
    (∀ (s1 s2 t1 t2 : term),
      R (Comb s1 s2) (Comb t1 t2) ↔ LEX R R (s1, s2) (t1, t2)) ∧
    (∀ (a b c d : term), R (Comb a b) (Abs c d) ↔ True) ∧
    (∀ (a b : term) (c : mlstring) (d : type), R (Abs a b) (Var c d) ↔ False) ∧
    (∀ (a b : term) (c : mlstring) (d : type), R (Abs a b) (Const c d) ↔ False) ∧
    (∀ (a b c d : term), R (Abs a b) (Comb c d) ↔ False) ∧
    (∀ (s1 s2 t1 t2 : term),
      R (Abs s1 s2) (Abs t1 t2) ↔ LEX R R (s1, s2) (t1, t2))

/-- transcription check: the base theorem has exactly the type `BaseStmtR term_lt` (only the type is used here) -/
example : BaseStmtR term_lt := Candle.term_lt_thm

/-- The base statement `term_lt_thm` is exactly `BaseStmtR term_lt`, so it implies the mutated statement `MutStmtR term_lt`
    (the mutant only drops a conjunct). -/
theorem base_implies_mut : BaseStmtR term_lt → MutStmtR term_lt := by
  rintro ⟨h1, h2, h3, h4, _, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩
  exact ⟨h1, h2, h3, h4, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩

/-- A relation that satisfies the remaining 15 clauses but makes `Const _ _ < Var _ _` true. -/
def R : term → term → Prop
  | Var x1 ty1, Var x2 ty2 => LEX mlstring_lt type_lt (x1, ty1) (x2, ty2)
  | Var _ _, Const _ _ => True
  | Var _ _, Comb _ _ => True
  | Var _ _, Abs _ _ => True
  | Const _ _, Var _ _ => True
  | Const x1 ty1, Const x2 ty2 => LEX mlstring_lt type_lt (x1, ty1) (x2, ty2)
  | Const _ _, Comb _ _ => True
  | Const _ _, Abs _ _ => True
  | Comb _ _, Var _ _ => False
  | Comb _ _, Const _ _ => False
  | Comb s1 s2, Comb t1 t2 => R s1 t1 ∨ (s1 = t1 ∧ R s2 t2)
  | Comb _ _, Abs _ _ => True
  | Abs _ _, Var _ _ => False
  | Abs _ _, Const _ _ => False
  | Abs _ _, Comb _ _ => False
  | Abs s1 s2, Abs t1 t2 => R s1 t1 ∨ (s1 = t1 ∧ R s2 t2)

theorem R_mut : MutStmtR R := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intros <;> simp [R, LEX]

/-- The mutated statement does not determine the dropped clause: `R` satisfies the former but not the latter. -/
theorem witness : ∃ R' : term → term → Prop, MutStmtR R' ∧ ¬ BaseStmtR R' := by
  refine ⟨R, R_mut, ?_⟩
  intro h
  have := (h.2.2.2.2.1 (mls "a") BoolTy (mls "b") BoolTy).1
  simp [R] at this

#print axioms witness
