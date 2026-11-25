# Translation task, stage 1 of 2: definitions (clean-room baseline)

You are a translator under test. Your job is to translate a reduced HOL4 development (the CakeML
type soundness theorem `typeSound.semantics_type_sound`) into Lean 4. The run measures how
well you translate directly from the HOL4 sources, with no other help.

The translation has two stages. **This stage (yours): every datatype, type abbreviation,
definition, inductive relation and HOL4 library constant that the target theorems need.**
Stage 2 (other translators, later) will add the 267 theorem statements, each with proof
`sorry`, on top of your files. They will not change your definitions, so the definitions must
be complete, faithful and named so that every target statement can be written.

## Inputs (all inside your working directory)

- `hol4/package/`: the HOL4 sources, 20 theory scripts (`*Script.sml`) and `preamble.sml`.
- `hol4/HOL4-src/`: the HOL4 system sources (`src/` of HOL4 at the pinned commit), to look up
  the definitions of HOL4 library constants (lists, `pred_set`, `finite_map`, `alist`,
  `cardinal`, `toto`, `comparison`, `string`, `words`, `sorting`, `mergesort`, ...).
- `TARGETS.tsv`: the declarations in scope, one per line (kind, theory, name, script, line).
  It lists the 267 target theorems (for stage 2), 255 definitions, 4 inductive relations and 56
  datatypes. These are a minimum: also translate every other package definition, inductive
  relation, type abbreviation or overload, and every HOL4 library constant, that a target
  theorem statement or a translated definition mentions. Read the 267 target statements to
  find those.
- `lean/`: a Lean 4.28.0 Lake project, package `cml_ts`, with Batteries as its only
  dependency (already built). It has one empty module per theory:
  `CmlTS/{Misc,Mllist,Mlstring,Location,LprefixLub,Ffi,FpSem,Namespace,NamespaceProps,Ast,SemanticPrimitives,SemanticPrimitivesProps,Evaluate,EvaluateProps,SemanticsMin,TypeSystem,TypeSoundInvariants,Weakening,TypeSysProps,TypeSound}.lean`
  and the root `CmlTS.lean` importing them.

## What to produce

1. The Lean definitions, in the module of the HOL4 theory that defines them, in HOL4 source order
   where Lean allows. Imports between modules follow the HOL4 `Ancestors`. HOL4 library
   constants go in new modules of your choice (for example `CmlTS/Prelude/*.lean`), imported
   where needed and added to `CmlTS.lean`.
2. Above each translated declaration, a comment with the original HOL4 text:
   `/- HOL4: <the HOL4 definition, as in the source> -/`. For library constants, name the HOL4
   theory and constant.
3. `lean/CONVENTIONS.md`: the rules stage 2 must follow. It must give the name of every
   translated HOL4 constant and type in Lean (a table HOL4 name -> Lean name for anything that is
   not identical), the namespaces and `open`s used, how HOL4 types map to Lean types, notation, and anything a
   statement writer needs (for example which HOL4 overloads became which Lean functions).
   Include the module each name lives in.
4. `lean/PROGRESS.tsv`, tab-separated: UTC time (`date -u +%FT%TZ`), theory, name, status
   (`done` / `problem`), short note. Append a line for each translated declaration (or group).

## Rules

1. Faithfulness first. Each Lean definition must mean exactly what the HOL4 definition means,
   on all inputs. Where Lean cannot express the HOL4 meaning directly, choose the closest
   faithful encoding and record the choice in `CONVENTIONS.md`.
2. Definitions must be accepted by Lean as total definitions: no `partial`, no `axiom`, no
   `unsafe`, no `implemented_by`, no `extern`, no `native_decide`. `noncomputable` and
   `Classical` choice are fine (HOL4 is classical). Termination proofs should be real proofs; if
   you cannot prove one, `decreasing_by sorry` is allowed but list each such case in
   `PROGRESS.tsv` with status `problem`. Do not use `opaque` unless the HOL4 constant is itself
   unspecified (then say so in `CONVENTIONS.md`).
3. Do not write the 267 target theorems. You may state and prove (or `sorry`) small lemmas only
   when Lean needs them for a definition (for example termination), and you may translate the
   equations HOL4 generates for a definition only if Lean's own equation lemmas would not exist.
4. Imports: Lean core (`Init`, `Std`, `Lean`) and `Batteries` only. Mathlib is not available.
5. `lake build` from `lean/` must succeed at the end with no errors. Warnings are fine.
6. Clean room. Work only from the files inside your working directory and your own knowledge
   of Lean and HOL4. You may read the Lean core and Batteries sources under
   `lean/.lake/packages/` and the toolchain directory
   (`$HOME/.elan/toolchains/leanprover--lean4---v4.28.0/`). Do not read any other path on this machine. Do not use the web, web search, GitHub, git, MCP tools, browser tools, or
   tools that reach the user's computer. Do not look for existing Lean translations of CakeML anywhere.
7. Do not spawn subagents or delegate. You do all the translating yourself.

## Environment

Your tools are Read, Write, Edit, Glob, Grep and Bash. Bash runs only `lake build ...`,
`lake env lean ...`, `cd lean`, `ls` and `date -u ...`; everything else is refused. Use Glob and
Grep to search, and Read to read. Never chain commands with pipes or redirections.

- From `lean/`: `lake build CmlTS.Misc` builds one module, `lake build` builds all.
- Quick checks: a scratch file `lean/scratch/T.lean` that imports built modules, checked with
  `lake env lean scratch/T.lean`. Use `#eval`/`#reduce`/`example` to test definitions on small
  inputs where that helps you check faithfulness.
- The PC is shared with other runs: one Lean process at a time, and use command timeouts.

## Final report

When you stop, reply with a summary only: modules written and declaration counts per module;
every place where the Lean meaning differs from HOL4 or where you made a modelling choice; every `decreasing_by
sorry` or other `sorry`; any target declaration you could not translate and why; the final
`lake build` result; and a confirmation that you followed the clean-room rules (say so plainly
if you broke any).
