# S0: model-free structural scan (audit arm S0)

Compares each Lean theorem statement with the HOL4 kernel export of the same theorem. No language model, no
knowledge of which statements carry seeded errors. HOL4 is the reference; the scan flags a statement when the
Lean statement, translated into one canonical form, differs from the HOL4 term.

## Files
- `DumpLean.lean`: dumps elaborated statements (Expr trees, binder kinds, instance arguments) and all project
  definitions (kind, axioms used, dependencies, matcher info). Run inside a Lean project via `lake env lean`.
  `DumpTypes.lean`, `names.txt`: the earlier constant-count dump (kept, not used).
- `map.tsv`: HOL4 constant -> Lean names, argument permutations, type map, unfold list, normalisation rules.
  Column `status`: convention (CONVENTIONS.md), lean-core, fitted (added after a base statement disagreed; 9 rows).
- `scan.py`: the scan. `run.sh PROJECT_DIR [OUT_DIR] [MANIFEST]`: dump + scan, writes `report.json`, `summary.txt`.
- `selftest/`: `mutate.py` (12 mutations), `results.txt`.

## What is checked (reason classes in the report)
unmapped (a constant without a map row), constants (multiset of canonical constants), literals (numerals,
strings, chars), binders (counts of forall/exists/lambda, leading forall count), hypotheses (premise count),
connectives, quantifier-order, structure (canonical strings differ; the first difference is shown),
binder-types (types of quantified variables, compared through the type map), instances (instance binders such as
Nonempty, DecidableEq, BEq against the classes the mapped Lean constants need), trivial (conclusion True or
reflexive, False hypothesis, unused quantified variables differing from HOL4), definitions (a definition reachable
from the statement is axiom, opaque, partial, unsafe, or uses sorry, native_decide or a non-standard axiom),
hash (statement text differs from a manifest; `S0_MAKE_MANIFEST=file ./run.sh ...` writes one), missing.

## Normalisation (see RULE rows in map.tsv)
HOL4 free variables become universal binders; runs of adjacent same-kind quantifiers are order-insensitive;
A /\ B ==> C = A ==> B ==> C; /\ and \/ chains are flat; Iff = Eq on Prop; numerals, strings, chars are
literals; UNCURRY and one-alternative pair matchers become projections; setOf becomes GSPEC; reducible Lean
definitions and the UNFOLD rows are unfolded; (f o g) x = f (g x); eta; instance arguments are ignored.

## Not detected (by construction)
- Wrong definitions: constants are compared by name, so a changed body of a definition is invisible unless it
  introduces sorry/axiom/opaque/partial/native_decide (probe: MAX changed to the minimum, not flagged).
- Type annotations inside the body (implicit type arguments, e.g. `n2w : Nat -> word32` for word8). Only
  quantified variables carry types in the comparison (probe: not flagged).
- Changes the normalisation identifies: permuting same-kind adjacent binders, consistent renaming, currying of
  hypotheses, associativity of /\ and \/, type-variable identity across conjuncts, eta.
- Semantics of Lean-only constants and of instances; universe levels; proofs (all are `sorry`).
- Errors shared by the Lean statement and the HOL4 export (a wrong HOL4 export would be copied).

## Honest false alarms
Clean base: 2 of 278 flagged, both binder-types: `mlstring_common_char_prefix` and `VSUBST_WELLTYPED` have an
unused quantified variable that HOL4 types as a type variable and Lean types as `mlstring` / `type`. They are real
differences between the two statements (harmless), not tuned away. Statements the translator rewrites
(reordered conjuncts, swapped equation sides, different but equivalent shapes) would be flagged as well.

## Self-test (selftest/results.txt)
12 mutations in a scratch copy: 12 of 12 flagged (11 of 11 on statements clean in the base). Mutations change
statements the way the HOL4 export would expose; the blind spots above are the realistic misses.
Runtime: about 30 s per project (Lean dump) plus under 1 s (scan). Offline, standard library only.

## Review notes (24 Nov 2026, main session)

- The 2/278 base false-alarm figure is **in-sample**: the tool was debugged against this base (215, then 36, then 2 flags), and 9 rules
  are marked `fitted`. Expect more false alarms on a translation with other conventions. The two flags that remain are type deviations
  already known from the earlier HOL4 checks (`VSUBST_WELLTYPED`, `mlstring_common_char_prefix`).
- The 12 self-test mutations were chosen by the tool's author. Four further mutations chosen by the reviewer
  (`ACONV_SYM` conclusion, `ACONV_TRANS` conclusion, swapped pair in `VFREE_IN_RACONV`, swapped append in `TYPE_SUBST_compose`) were all flagged
  (4 of 4; two more were planned but not applied).
- S0 sees statements, not definition bodies. Consequence for the audit design: statement-level mutants are close to solved by S0,
  so definition-level and library-level mutants carry most of the information about model auditors.
