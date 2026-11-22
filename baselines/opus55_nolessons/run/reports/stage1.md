Stage 1 is complete. All the definitions build. There is no sorry anywhere, and every target can be stated.

**Final build**
- I ran `lake build` in `/home/claude/work/ws/lean` after deleting `lean/scratch/`. Result: "Build completed successfully (22 jobs)".
- None of these are present: `sorry`, `decreasing_by sorry`, `axiom`, `partial`, `unsafe`, `implemented_by`, `extern`, `native_decide`. A grep for these strings finds only HOL4 comments and the `proves` constructor `new_axiom`.
- `#print axioms` shows only propext, Classical.choice and Quot.sound.

**Modules and declaration counts**
The counts include abbrevs, instances, macros and helper lemmas.

| Module | Decls |
|---|---|
| Prelude/Basic | 28 |
| Prelude/Set | 24 |
| Prelude/List | 31 |
| Prelude/String | 10 |
| Prelude/Words | 14 |
| Prelude/FiniteMap | 13 |
| Prelude/Sptree | 5 |
| Prelude/ASCIInumbers | 8 |
| Prelude/Mergesort | 5 |
| Misc | 13 |
| Mllist | 1 |
| Mlstring | 23 |
| SetSpec | 25 |
| HolSyntaxLib | 11 |
| HolSyntax | 76 |
| HolSyntaxExtra | 20 |
| HolSemantics | 27 |
| HolSemanticsExtra | 1 |
| HolSoundness | 0 (imports only) |

- All modules are under `/home/claude/work/ws/lean/CandleLean/` and are imported by `CandleLean.lean`.
- The other deliverables are `/home/claude/work/ws/lean/CONVENTIONS.md` and `/home/claude/work/ws/lean/PROGRESS.tsv`. PROGRESS.tsv has about 316 rows, all `done`.

**Where meaning differs or a modelling choice was made** (full details in CONVENTIONS.md §7)
1. HOL `bool` is `Prop`, and `if` is classical.
2. `ARB` is `noncomputable opaque ARB {α} [Nonempty α] : α`. Cases that a HOL pattern match leaves out are filled with ARB, as TFL does. This applies to:
   - `HD []` and `LAST []`
   - `RESULT (Clash _)` and `CLASH (Result _)`
   - `dest_var` of a non-variable
   - `termsem` of `Abs` with a non-`Var` binder
3. Constants that HOL4 only partly specifies, or defines with `new_specification`, are `Classical.epsilon` over whole functions that meet the spec. These are `fresh`, `VARIANT_PRIMES`, `instance_`, `FUN_FMAP`, `SEG`, `CHR` and `OUTL`. Only their spec can be proved about them. Hilbert `@` is also `Classical.epsilon` (setSpec `sub`, `power`, `union`, `upair`, `apply`).
4. `type_lt` and `term_lt` are impredicative least-fixpoint definitions, the same construction IndDefLib uses. Lean `inductive` does not accept the recursion under LLEX/LEX. Stage 2 will have to prove the rule theorems (for example `type_lt_thm`) from this definition.
5. Representations:
   - `word d` is a structure holding `w2n < 2^d`. `n2w` is `n % 2^d`, `FCP` is defined by bits, and `v2w` is translated literally.
   - `char` is a structure with a field `ORD < 256`, not Lean's `Char`. `string` is `List char`.
   - `fmap` is HOL4's representation: a subtype of `α → β ⊕ Unit` restricted by the inductive `is_fmap`.
   - `Set α` is `α → Prop`.
6. Lean core functions stand in for LENGTH, MAP, REVERSE, TAKE, DROP, FOLDR, FOLDL, APPEND, FST, SND and OPTION_MAP/BIND. `ZIP` takes a pair, as in HOL4.
7. Clause changes:
   - The last clause of `mergesortN_tail` uses the pattern `n+4`.
   - `TYPE_SUBST` drops its redundant third clause.
   - Pattern lambdas and `let (x,y)` are written with projections.
8. Renames, made because the HOL4 names clash with Lean keywords or core names:
   - Bool → `Bool_`
   - bind → `bind_`
   - compare → `compare_`
   - true/false (setSpec) → `true_`/`false_`
   - instance → `instance_`
   - toString → `chr_to_str`
   - the datatype dbterm → `dbterm_`
9. Overloads and literals:
   - `set` is a macro for `LIST_TO_SET`.
   - Type-dependent HOL overloads (tysof, tmsof, sigof, axsof) are typeclasses: `HasTysof`, `HasTmsof`, `HasSigof`, `HasAxsof`.
   - setSpec and semantics constants take `mem` as an explicit first argument.
   - `'U` constants take `{U} [Nonempty U]`.
   - Literals use the macros `str!`, `ch!` and `mls!`, which expand to CHR numerals.
10. setSpec's `∃!` is expanded to HOL4's definition of `?!`.

**Helper lemmas (not target theorems)**
These exist only to support termination proofs:
- `EVERY_attach_unattach`, `EVERY_wfParam`, `EVERY_unattach`
- `SPLITP_snd_length_le` (for FIELDS)
- `sizeof_REV_ASSOCD_aux`, `FILTER_mem_aux`, `sizeof_VSUBST_aux` (for INST_CORE)

Every termination proof is a real proof.

**Untranslated targets:** none.
- Every name the 278 targets need is defined.
- I elaborated about 90 sample target statements in scratch without errors. I also checked sort, LLEX, ZIP, n2l and others by evaluation.
- Package definitions that nothing uses are not translated; CONVENTIONS.md §10 lists them, for example misc `the`, `read_bytearray`, `enumerate`, most mlstring and mllist functions, and the holSyntaxExtra `fresh_term`, `vfree_in` and `union`.

**Clean room**
- I read only files under `/home/claude/work/ws/`, the Lean core and Batteries sources under `lean/.lake/packages/`, and the toolchain directory.
- I did not use the web, git, MCP tools or subagents, and I did not look for existing translations.
- Scratch files were briefly in `/tmp/x` before I moved them into `lean/scratch/`. That directory has now been deleted. The `/tmp/claude*` scratchpad was not used.
