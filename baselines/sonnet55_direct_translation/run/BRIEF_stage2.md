# Translation task, stage 2 of 2: theorem statements (clean-room baseline)

You are a translator under test. Your job is to translate theorem statements of a reduced HOL4
development (CakeML's Candle kernel soundness theorem `holSoundness.proves_sound`) into Lean 4.
The run measures how well you translate directly from the HOL4 sources, with no other help.

Stage 1 (already done by another translator) translated the datatypes, definitions, inductive
relations and HOL4 library constants into the Lean project in `lean/`, and wrote the naming and
type conventions in `lean/CONVENTIONS.md`. **Your stage: add the Lean statements of the target
theorems assigned to you below, each with proof `sorry`.** Other translators do the other
theorems in parallel, in their own copies.

## Your workspace: WORKSPACE

- `hol4/package/`: the HOL4 sources (10 theories). `hol4/HOL4-src/`: HOL4 system sources, to look
  up library constants.
- `TARGETS.tsv`: all target declarations (kind, theory, name, script, line).
- `ASSIGNMENT.tsv`: **your** theorems (theory, name, script, line, Lean file). Translate exactly
  these.
- `lean/`: the Lean 4.28.0 Lake project (Batteries only, already built), with stage 1's files and
  `CONVENTIONS.md`.

## What to produce

1. For each assigned theorem, a Lean `theorem` in the Lean file named in `ASSIGNMENT.tsv`, in
   HOL4 source order, after the definitions it needs, with:
   - the same name as in HOL4 (inside the namespace that `CONVENTIONS.md` prescribes for that
     file), unless `CONVENTIONS.md` says otherwise or Lean rejects the name (then record the
     Lean name in `PROGRESS.tsv`);
   - directly above it, the comment `/- HOL4: <the HOL4 statement, as in the source> -/`;
   - proof `:= by sorry` (or `:= sorry`).
   A HOL4 theorem that is a conjunction stays one Lean theorem with a conjunction. Keep HOL4's
   quantifier structure and hypotheses; do not strengthen, weaken, split or merge statements.
2. `PROGRESS.tsv` in the workspace root, tab-separated: UTC time (`date -u +%FT%TZ`), theorem
   name, status (`done` / `problem`), short note. Append a line per theorem.

## Rules

1. Faithfulness first. Each Lean statement must mean exactly what the HOL4 statement means,
   with the same types (watch implicit HOL4 type variables, numeral types, `num` subtraction,
   overloaded operators, sets and finite maps, and free variables, which HOL4 quantifies
   universally).
2. Do not change any existing declaration from stage 1 (definitions, datatypes, instances,
   `open`s, options, order). If a statement needs a HOL4 constant that stage 1 did not
   translate, add a faithful translation of it as a new definition in your assigned file,
   placed before its first use, with a `/- HOL4: ... -/` comment, and log it in `PROGRESS.tsv`
   with status `problem` and the note `added definition`. If you believe a stage 1 definition is
   wrong, do not edit it: log it with status `problem` and the precise reason.
3. Only `sorry` proofs for the theorems. No `axiom`, `partial`, `unsafe`, `implemented_by`,
   `extern`, `native_decide`.
4. Edit only the Lean files named in your `ASSIGNMENT.tsv`. Do not edit `lakefile.lean`,
   `lean-toolchain`, `CandleLean.lean` or other files.
5. Imports: Lean core and Batteries only. Mathlib is not available.
6. `lake build` must succeed at the end. Keep your files compiling.
7. Clean room. Work only from files inside your workspace and your own knowledge of Lean and HOL4.
   You may read the Lean core and Batteries sources under `lean/.lake/packages/` and the
   toolchain directory. Do not read any other path on this machine (in particular nothing under
   `/home/claude/candle-hol4-lean4-study`, `/mnt/`, `/tmp/claude*`, or other `ws*` directories).
   Do not use the web, web search, GitHub, git, MCP tools, browser tools, or tools that reach the
   user's computer. Do not look for existing Lean translations of CakeML or Candle anywhere.
8. Do not spawn subagents or delegate.

## Environment

- `export PATH=$HOME/.elan/toolchains/leanprover--lean4---v4.28.0/bin:$PATH`.
- From `lean/`: `lake build CandleLean.HolSyntaxExtra` for one module, `lake build` for all.
- The machine has 4 cores and 15 GB RAM shared with other translators: one Lean process at a time,
  use command timeouts.

## Final report

When you stop, reply with a summary only: theorems written out of the number assigned; any
assigned theorem you could not state and why; definitions you added; stage 1 definitions you
believe are wrong (with reasons); every place where your statement could differ in meaning from
HOL4 and why; the final `lake build` result; and a confirmation that you followed the clean-room
rules (say so plainly if you broke any).
