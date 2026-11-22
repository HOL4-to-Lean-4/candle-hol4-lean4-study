All 79 assigned theorems are stated in Lean with `sorry` proofs, and `lake build` over the whole project succeeds (19 jobs, only `sorry` and unused-variable warnings). That is 27 in SetSpec, 18 in HolSyntaxLib, 7 in HolSyntax, 16 in HolSemanticsExtra and 11 in HolSoundness. I logged all 79 in `PROGRESS.tsv`.

**Theorems not stated:** none.

**Definitions added:** none. I found no stage 1 definition that looks wrong.

**Rename:** HOL4's theorem `REV_ASSOCD` is named `REV_ASSOCD_thm` in Lean, because `REV_ASSOCD` is already the definition. It is logged as `problem` in `PROGRESS.tsv`.

**Where meaning could differ from HOL4:**
- **`mem` and `'U`:** `mem` is an explicit argument. HOL4 writes `^mem` as a free variable, so it is universally quantified. I used `[Inhabited U]` wherever the statement involves `empty`, `one`, `two`, `mtrue`, `apply`, `termsem`, `boolset`, `funspace` or `is_std_*`. Types are always inhabited in HOL4, so this is the same assumption.
- **Dropped `is_set_theory` hypothesis:** theorems that have no `is_set_theory` hypothesis in HOL4 (for example `termsem_aconv`, `termsem_frees` and `ASSUME_correct`) have none in Lean either. They take `mem` as a free argument.
- **Free variables as parameters:**
  - `P` in `REV_ASSOCD_FILTER`.
  - `ilist` in `INST_correct`.
  - `tyin` in `INST_TYPE_correct`.
  - `x`, `ty` and `t` in `PRIMED_NAME_EXISTS`, which are universally quantified binders.
  - `i` and `mem` in `is_std_interpretation_is_type`.
- **`bool` equality:** `MEM_FOLDR_INORDER_INSERT` keeps HOL4's `=` between Props rather than `↔`. All other bool equivalences use `↔`.
- **Lambda patterns and `∘`:** `λ(x,y). ...` becomes a lambda over a pair using `.1` and `.2`. `o` becomes `∘`, and `##` and `=++` are the scoped notations.
- **Placement and order:** the theorems are appended at the end of each file, after all the definitions. This is later than their HOL4 position for `domain_def` and `codomain_def`, but still in HOL4 order among themselves. In `HolSoundness.lean` I added the standard `open`s, `universe u`, `noncomputable section` and `variable {U}`.

**Clean room:** I followed the clean-room rules. I read only files inside `/home/claude/work/wsB/`, used no web, git or MCP tools, and spawned no subagents. I edited only the five assigned Lean files (`SetSpec.lean`, `HolSyntaxLib.lean`, `HolSyntax.lean`, `HolSemanticsExtra.lean`, `HolSoundness.lean`) and `PROGRESS.tsv`.
