# Translation task, stage 1 of 2: definitions (clean-room baseline)

You are a translator under test. Your job is to translate a reduced HOL4 development (CakeML's
Candle kernel soundness theorem `holSoundness.proves_sound`) into Lean 4. The run measures how
well you translate directly from the HOL4 sources, with no other help.

The translation has two stages. **This stage (yours): every datatype, type abbreviation,
definition, inductive relation and HOL4 library constant that the target theorems need.**
Stage 2 (other translators, later) will add the 278 theorem statements, each with proof
`sorry`, on top of your files. They will not change your definitions, so the definitions must
be complete, faithful and named so that every target statement can be written.

## Inputs (all inside `/home/claude/work/ws/`)

- `hol4/package/`: the HOL4 sources, 10 theories:
  `misc/miscScript.sml`, `basis/pure/mllistScript.sml`, `basis/pure/mlstringScript.sml`,
  `candle/set-theory/setSpecScript.sml`, `candle/syntax-lib/holSyntaxLibScript.sml`,
  `candle/standard/syntax/holSyntaxScript.sml`, `candle/standard/syntax/holSyntaxExtraScript.sml`,
  `candle/standard/semantics/holSemanticsScript.sml`,
  `candle/standard/semantics/holSemanticsExtraScript.sml`,
  `candle/standard/semantics/holSoundnessScript.sml`.
- `hol4/HOL4-src/`: the HOL4 system sources (`src/` of HOL4 at the pinned commit), to look up
  the definitions of HOL4 library constants (lists, `pred_set`, `finite_map`, `alist`,
  `cardinal`, `toto`, `comparison`, `string`, `words`, `sorting`, `mergesort`, ...).
- `TARGETS.tsv`: the declarations in scope, one per line (kind, theory, name, script, line).
  It lists the 278 target theorems (for stage 2), 114 definitions, 3 inductive relations and 6
  datatypes. These are a minimum: also translate every other package definition, inductive
  relation, type abbreviation or overload, and every HOL4 library constant, that a target
  theorem statement or a translated definition mentions. Read the 278 target statements to
  find those.
- `lean/`: a Lean 4.28.0 Lake project, package `candle_lean`, with Batteries as its only
  dependency (already built). It has one empty module per theory:
  `CandleLean/{Misc,Mllist,Mlstring,SetSpec,HolSyntaxLib,HolSyntax,HolSyntaxExtra,HolSemantics,HolSemanticsExtra,HolSoundness}.lean`
  and the root `CandleLean.lean` importing them.

## What to produce

1. The Lean definitions, in the module of the HOL4 theory that defines them, in HOL4 source order
   where Lean allows. Imports between modules follow the HOL4 `Ancestors`. HOL4 library
   constants go in new modules of your choice (for example `CandleLean/Prelude/*.lean`), imported
   where needed and added to `CandleLean.lean`.
2. Above each translated declaration, a comment with the original HOL4 text:
   `/- HOL4: <the HOL4 definition, as in the source> -/`. For library constants, name the HOL4
   theory and constant.
3. `lean/CONVENTIONS.md`: the rules stage 2 must follow. It must give the name of every
   translated HOL4 constant and type in Lean (a table HOL4 name -> Lean name for anything that is
   not identical), the namespaces and `open`s used, how HOL4 types map (num, int, char, string,
   mlstring, sets, finite maps, options, pairs, words if any, ...), notation, and anything a
   statement writer needs (for example which HOL4 overloads became which Lean functions).
   Include the module each name lives in.
4. `lean/PROGRESS.tsv`, tab-separated: UTC time (`date -u +%FT%TZ`), theory, name, status
   (`done` / `problem`), short note. Append a line for each translated declaration (or group).

## Rules

1. Faithfulness first. Each Lean definition must mean exactly what the HOL4 definition means,
   on all inputs, including edge cases (division and modulus, subtraction on naturals,
   characters and strings, order and duplicates in lists, partial functions and `ARB`, Hilbert
   choice, sets that may be infinite, finite maps). Where Lean cannot express the HOL4 meaning
   directly, choose the closest faithful encoding and record the choice in `CONVENTIONS.md`.
2. Definitions must be accepted by Lean as total definitions: no `partial`, no `axiom`, no
   `unsafe`, no `implemented_by`, no `extern`, no `native_decide`. `noncomputable` and
   `Classical` choice are fine (HOL4 is classical). Termination proofs should be real proofs; if
   you cannot prove one, `decreasing_by sorry` is allowed but list each such case in
   `PROGRESS.tsv` with status `problem`. Do not use `opaque` unless the HOL4 constant is itself
   unspecified (then say so in `CONVENTIONS.md`).
3. Do not write the 278 target theorems. You may state and prove (or `sorry`) small lemmas only
   when Lean needs them for a definition (for example termination), and you may translate the
   equations HOL4 generates for a definition only if Lean's own equation lemmas would not exist.
4. Imports: Lean core (`Init`, `Std`, `Lean`) and `Batteries` only. Mathlib is not available.
5. `lake build` from `lean/` must succeed at the end with no errors. Warnings are fine.
6. Clean room. Work only from the files inside `/home/claude/work/ws/` and your own knowledge
   of Lean and HOL4. You may read the Lean core and Batteries sources under
   `lean/.lake/packages/` and the toolchain directory
   (`$HOME/.elan/toolchains/leanprover--lean4---v4.28.0/`). Do not read any other path on this
   machine (in particular nothing under `/home/claude/candle-hol4-lean4-study`, `/mnt/`, or
   `/tmp/claude*`). Do not use the web, web search, GitHub, git, MCP tools, browser tools, or
   tools that reach the user's computer. Do not look for existing Lean translations of CakeML or
   Candle anywhere.
7. Do not spawn subagents or delegate. You do all the translating yourself.

## Environment

- `export PATH=$HOME/.elan/toolchains/leanprover--lean4---v4.28.0/bin:$PATH` before using
  `lake` or `lean`.
- Build one module: `lake build CandleLean.Misc` (from `lean/`). Whole project: `lake build`.
- Quick checks: a scratch file in `lean/scratch/` that imports built modules, checked with
  `lake env lean scratch/T.lean`. Use `#eval`/`#reduce`/`example` to test definitions on small
  inputs where that helps you check faithfulness. Delete `scratch/` when done.
- 4 cores and 15 GB RAM. Use command timeouts.

## Final report

When you stop, reply with a summary only: modules written and declaration counts per module;
every place where the Lean meaning differs from HOL4 or where you made a modelling choice
(sets, finite maps, chars/strings, div/mod, choice, `ARB`, termination); every `decreasing_by
sorry` or other `sorry`; any target declaration you could not translate and why; the final
`lake build` result; and a confirmation that you followed the clean-room rules (say so plainly
if you broke any).
