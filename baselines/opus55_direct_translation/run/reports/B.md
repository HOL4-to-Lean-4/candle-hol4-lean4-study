79 of 79 assigned theorems stated with `sorry`; `lake build` succeeds (198 jobs), only "declaration uses sorry" warnings.
Placement: SetSpec 27, HolSyntaxLib 18, HolSyntax 7, HolSemanticsExtra 16, HolSoundness 11, after all stage 1 declarations, HOL4 source order, `/- HOL4: ... -/` comments. No stage 1 declaration changed. HolSemanticsExtra.lean and HolSoundness.lean had only an import and doc comment; added `universe u`, `namespace Candle`, `open HOL Classical`, `noncomputable section`, `variable {U : Type u}`. Added `universe w` to HolSyntaxLib.lean (REV_ASSOCD_FILTER). PROGRESS.tsv: 79 `done` lines.

Not stated: none. Definitions added: none. Stage 1 definitions believed wrong: none (spot-checked sub, power, funspace, apply, abstract, ALPHAVARS, REV_ASSOCD, LIST_UNION, INORDER_INSERT, VSUBST, simple_subst, bv_names, termsem0, UPDATE_LIST, ALOOKUP).

Possible differences:
1. HOL4 `REV_ASSOCD` theorem is `Candle.REV_ASSOCD_thm` (name clash with the definition).
2. `REV_ASSOCD_FILTER`: unused bound `d` gets its own type variable `γ`; free `P` quantified outermost.
3. Free variables made explicit leading arguments: `mem` everywhere (also theorems without `is_set_theory`: is_std_interpretation_is_type, typesem_Fun, typesem_Bool, termsem_raconv, termsem_aconv, termsem_frees, termsem_simple_subst, termsem_VSUBST, termsem_simple_inst, termsem_INST, ASSUME_correct); `x` in PRIMED_INFINITE; `x ty t` in PRIMED_NAME_EXISTS; `ilist` in INST_correct; `tyin` in INST_TYPE_correct.
4. `[Nonempty U]` only on theorems mentioning empty/one/two/boolset/true_/false_/boolean/is_std_*/is_structure0/entails0, per CONVENTIONS.md.
5. `^Equalsem` in termsem_Equal: CONVENTIONS.md §8 term applied to `[typesem i.1 v.1 ty]` as a beta-redex, as in HOL4.
6. Overloads: tmsof/tysof on thy -> thy_tmsof/thy_tysof, on sig -> tmsof/tysof. `pair_inj`: `(a,b)` read as setSpec `pair mem a b` (latest overload; HOL4 proof unfolds pair_def). `===` equation, `|=` entails0 mem (thy,h) c, `|-` proves.
7. Paired lambdas as `fun (x, y) => …`; MEM_FOLDR_INORDER_INSERT keeps boolean `=` on Prop; case as match.

Clean room: followed; one helper script and one #check file written to the session scratchpad (under /tmp/claude*, own files only). No web, git, MCP, browser, subagents.
