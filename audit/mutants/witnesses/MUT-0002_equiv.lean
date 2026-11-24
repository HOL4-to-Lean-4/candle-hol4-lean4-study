import CandleLean
open Candle

/-- The base statement FST_rename_bvars is true, and so is the mutated one (extra hypothesis `names ≠ []`);
    hence the mutant is logically equivalent to the base. No sorry-backed base theorem is used. -/
theorem fst_rb : ∀ (tm : term) (names : List mlstring) (env : List (mlstring × (mlstring × type))),
    (bv_names tm).length ≤ names.length →
    (rename_bvars names env tm).1 = names.drop (bv_names tm).length := by
  intro tm
  induction tm with
  | Var s ty => intro names env h; simp [rename_bvars, bv_names]
  | Const s ty => intro names env h; simp [rename_bvars, bv_names]
  | Comb t1 t2 ih1 ih2 =>
    intro names env h
    simp only [bv_names, List.length_append] at h
    have e1 := ih1 names env (by omega)
    have e2 := ih2 (rename_bvars names env t1).1 env (by rw [e1]; simp; omega)
    simp only [rename_bvars, bv_names, List.length_append]
    rw [e2, e1]; simp [List.drop_drop]
  | Abs v t _ ih =>
    intro names env h
    cases names with
    | nil => simp [bv_names] at h
    | cons s names =>
      simp only [bv_names, List.length_cons] at h
      simp only [rename_bvars, bv_names, List.length_cons]
      rw [ih names _ (by omega)]; simp

theorem equiv_stmt :
    (∀ (names : List mlstring) (env : List (mlstring × (mlstring × type))) (tm : term),
        names ≠ [] → (bv_names tm).length ≤ names.length →
        (rename_bvars names env tm).1 = names.drop (bv_names tm).length) ↔
    (∀ (names : List mlstring) (env : List (mlstring × (mlstring × type))) (tm : term),
        (bv_names tm).length ≤ names.length →
        (rename_bvars names env tm).1 = names.drop (bv_names tm).length) :=
  ⟨fun _ names env tm h => fst_rb tm names env h, fun h names env tm _ => h names env tm⟩

#print axioms equiv_stmt
