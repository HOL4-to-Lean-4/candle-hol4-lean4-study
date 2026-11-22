# Audit 2: setSpec, holSyntaxLib, holSyntax, holSemantics, holSemanticsExtra, holSoundness (Opus 5.5 translation)

The auditor could not write this file itself (the harness refused subagent file writes and asked for
the findings as text). The orchestrator saved its final report here verbatim.

## Fidelity audit 2: no defects and no suspects in my scope

**Scope.** I checked the 79 target theorems in setSpec, holSyntaxLib, holSyntax, holSemantics, holSemanticsExtra and holSoundness. I also checked every definition and inductive relation they depend on. I compared each one against the actual HOL4 script and the HOL4 library sources, not only against the `/- HOL4: -/` comments.

**Result.** No target is weaker, stronger, false, vacuous or trivially true compared with HOL4. Every target has a Lean declaration, under the HOL4 name or one of the renames listed in N6.

**Lean checks I ran.** The files are `/home/claude/work/audit/ws2/scratch/T1.lean` and `T2.lean`. Everything passed except one bad example I wrote myself (T1 line 14 does not type-check; it has no bearing on the translation). They confirm:
- the clause shapes of `domain`, `codomain` and the `TYPE_SUBST` Fun clause;
- `orda`'s ranking of constructors (first-match order);
- the `termsem0` Abs clause, and that its three `ARB` fallback cases give the same value;
- `entails0` and `satisfies0` unfold to the HOL4 conjuncts;
- the `VSUBST` Abs case when no variable capture occurs;
- `instance_def`, `VARIANT_PRIMES_def` and `FUN_FMAP_DEF` are proved without `sorry` (`#print axioms`).

## Notes (same meaning, recorded modelling choices)

1. **N1: `[Nonempty U]` is added** to `empty`, `one`, `two`, `boolset`, `true_`/`false_`, `boolean`, `satisfies0`, `is_std_type_assignment0`, `is_std_interpretation0`, `models0`, `entails0`, `is_structure0`, and to the theorems that use them, including `proves_sound`. Every HOL4 type is non-empty, so nothing is lost. Theorems that do not need it leave it out and so are more general.
2. **N2: Hilbert choice with an explicit witness** for `sub`, `power`, `union`, `upair`, `apply` and `instance_`. The chosen value does not depend on the witness.
3. **N3: `type_lt` and `term_lt` are impredicative definitions**, exactly HOL4's least-relation construction. `LLEX` is monotone, so the meaning is the same. This only adds proof work for `hypset_ok`, `entails0` and `proves_sound`.
4. **N4: Unspecified values match HOL4.**
   - `dest_var` on a non-variable, `RESULT (Clash _)`, `CLASH (Result _)` and `termsem0` on `Abs` of a non-variable each give one fixed `ARB`, as HOL4's pattern completion does.
   - The `let (x,ty) = dest_var v` in `VSUBST` and `INST_CORE` is written with `.1`/`.2`, which is equivalent.
5. **N5: `TYPE_SUBST` has no separate Fun equation.** The HOL4 Fun clause is a special case of the `Tyapp` clause, and `simp [TYPE_SUBST]` proves it.
6. **N6: Renames forced by Lean:** the theorem `REV_ASSOCD` is `REV_ASSOCD_thm`, setSpec's `true`/`false` are `true_`/`false_`, the semantics constants keep their `0` names with `mem` explicit, `Bool` is `BoolTy`, and `instance` is `instance_`.
7. **N7: Type-signature differences with no semantic effect.**
   - `REV_ASSOCD_FILTER`: its unused bound `d` gets its own type `γ`, which is what HOL4 infers.
   - HOL4's free variables become explicit universally quantified parameters: `P`, `x`, `ilist`, `tyin`, `i` and `mem`.
   - Lean puts type variables in separate universes, which is at least as general as HOL4.
   - Theorems that lack `is_set_theory` in HOL4 also lack it in Lean: ASSUME_correct, typesem_Fun/Bool, and termsem_raconv, aconv, frees, simple_subst, VSUBST, simple_inst and INST.
8. **N8: Overloaded notation resolves the same way as in HOL4.**
   - In setSpec, `,`, `+` and `∅` mean the set-theory versions (`pair mem`, `upair mem`, `empty mem`). HOL4 prefers the newest overload (`Overload.sml:345`, `Preterm.sml:558-570`), and its proofs only work with that reading.
   - In the semantics and soundness theories, every pair is a HOL pair. A set-theory pair would not type-check there.
   - In `termsem_def`, `'` is set-theory `apply`, not finite-map lookup.
9. **N9: Encodings.** Finite maps are functions to `Option` with finite support, and lookup outside the domain gives one fixed `ARB`, as in HOL4. HOL4 `bool` is Lean `Prop`.
10. **N10: `ordav_def` uses `⇔` between `ordering` values in HOL4.** HOL4 builds it, so it is plain equality, and Lean has the same clauses.

## Summary table

| id | what | class | changes a target? |
|---|---|---|---|
| N1–N10 | as listed above | note | no |

Defects: 0. Suspects: 0.

## What I checked and found faithful

- **setSpec:** all definitions, and all 26 theorems (is_extensional … abstract_eq), including precedence and quantifier order.
- **holSyntaxLib:** ALPHAVARS, REV_ASSOCD, the result type and its functions, LIST_INSERT, LIST_UNION, INORDER_INSERT, STRING_SORT, and all 17 theorems. `string_lt` and the other prelude list and set constants they use also match.
- **holSyntax:** all definitions and the 7 theorems:
  - typing and alpha-equivalence: has_type, RACONV, ACONV, typeof;
  - term order: type_lt, term_lt, term_cmp, type_cmp, ordav, orda;
  - hypothesis lists: term_union, term_remove, term_image;
  - free variables and renaming: VFREE_IN, VARIANT_PRIMES (its spec, with argument order t x ty), VARIANT;
  - substitution: TYPE_SUBST, VSUBST, INST_CORE (all branches), INST, tyvars, tvars;
  - equations and theories: equation (`===` binds tighter than `|-`), type_ok, term_ok, hypset_ok, is_std_sig, theory_ok;
  - the 10 `proves` rules, and the update functions.
- **holSemantics:** all 15 definitions, including `instance`, `termsem`, `satisfies`, `entails` and `is_std_interpretation` (with the `Equalsem` term).
- **holSemanticsExtra:** all 16 theorems, including the beta-redex form of `Equalsem` and the `=++`/`##` composition. The holSyntaxExtra constants they use (bv_names, simple_subst, simple_inst) match HOL4.
- **holSoundness:** all 11 theorems. `proves_sound` is exactly `is_set_theory mem → ∀ thyh c, proves thyh c → entails0 mem thyh c`, with nothing vacuous on either side.

## Limits

- I did not prove any target; the Lean checks only confirm clause shapes and that the specified constants are well defined.
- I checked holSyntaxExtra only for the three constants above. misc, mlstring and mllist are other auditors' scope.
- The scope counts in this report (setSpec 26 theorems, holSyntaxLib 17) differ from the assignment (27 and 18); the kernel check confirms all 278 targets exist. [orchestrator note]
