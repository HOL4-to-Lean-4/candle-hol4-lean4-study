## Stage 2 report (workspace /home/claude/work/wsB)

**All 79 of the 79 assigned theorems are stated.** Each one is in the Lean file that `ASSIGNMENT.tsv` names, in HOL4 source order. Each has the `/- HOL4: ... -/` comment and proof `by sorry`. They sit in a "Theorems (stage 2)" block at the end of each file, so they come after all the definitions they use. The per-file counts are:

| File | Theorems |
|---|---|
| `SetSpec.lean` | 27 |
| `HolSyntaxLib.lean` | 18 |
| `HolSyntax.lean` | 7 |
| `HolSemanticsExtra.lean` | 16 |
| `HolSoundness.lean` | 11 |

`PROGRESS.tsv` in the workspace root has 79 lines, all with status `done`.

**Theorems I could not state:** none.

**One renamed theorem:** HOL4 `REV_ASSOCD` (holSyntaxLib) is `REV_ASSOCD_thm` in Lean, because `REV_ASSOCD` is already the stage-1 definition. This is recorded in `PROGRESS.tsv`.

**Definitions added:** none.

**Stage 1 definitions I believe are wrong:** none found. I did not audit them closely.

**One addition to a stage-1 file:** `HolSoundness.lean` had no `open Classical`. `CONVENTIONS.md` requires every statement file to have one, so I added it after the existing imports. Nothing existing was changed. The statements in that file do not need it.

**Places where my statements could differ in meaning from HOL4:**
- **The free HOL4 variable `mem`:** it is an explicit argument `(mem : U → U → Prop)` with `{U : Type u} [Nonempty U]`, as §3 of `CONVENTIONS.md` says. Other free variables are explicit theorem parameters, which is the same as HOL4's implicit universal closure: `x`, `ty`, `t` in `PRIMED_NAME_EXISTS`, `x` in `PRIMED_INFINITE`, `P` in `REV_ASSOCD_FILTER`, `ilist` in `INST_correct` and `tyin` in `INST_TYPE_correct`.
- **Unused bound variable in `REV_ASSOCD_FILTER`:** HOL4's `∀l a b d` binds `d` without using it, so `d` has its own type variable. In Lean I gave it a separate type `{γ : Type w} [Nonempty γ]`. Without `Nonempty`, an empty `γ` would make the statement trivially true, so the instance is needed to keep the meaning.
- **`[Nonempty U]` on statements that do not need it:** `is_extensional`, `typesem_TYPE_SUBST` and `typesem_tyvars` get it too. The conventions say this is always faithful.
- **Bool-valued equality as `↔`:** `MEM_FOLDR_LIST_UNION` uses `↔`, which matches HOL4's `⇔`. `MEM_FOLDR_INORDER_INSERT` keeps `=` on `Prop`, as in the source.
- **Pattern lambdas and `case`:** `λ(x,y)` is written with projections, as in item 13 of §7 of the conventions. `REV_ASSOCD_ALOOKUP`'s `case ... of NONE => d | SOME y => y` is a Lean `match`. These forms have the same meaning.
- **Name types for binders:** `sig`, `Γ` and `tmenv` follow how HOL4 uses them:
  - `Γ : tmsig` in `termsem_raconv`, `termsem_aconv`, `termsem_frees`, `termsem_simple_subst` and `termsem_VSUBST`, where it is passed straight to `termsem`.
  - `Γ : sig` in `termsem_Equal`, `termsem_simple_inst` and `termsem_INST`, where it is used with `is_structure` or `term_ok`.
  - `thy : thy` in `holSoundness`.
- **Operators:** precedence follows HOL4. `===` binds tighter than `|=` and `=`. `=++` is `UPDATE_LIST`, `##` is `PAIR_MAP`, and `o` is `∘`.

**Final `lake build`:** it succeeded (23 jobs). The only warnings are "declaration uses sorry".

**Clean room:** I followed the rules. I read only files inside `/home/claude/work/wsB`, and I did not need the Lean core and Batteries sources. I did not use the web, git, MCP tools or subagents, and I edited only the five assigned Lean files and `PROGRESS.tsv`.
