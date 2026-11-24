# Re-scoring of the baselines against the v3.3 contract (conservativity), 24 Nov 2026

Draft. Contract: `plan/v3/plan_v3.3.tex`, section "Fidelity contract".
Method: each baseline was built (Lean 4.28.0) in a scratch copy and the file named after it here was
checked with `lake env lean` (0 errors for all four). HOL4 defining theorems were printed from the
built package (HOL4 9783a499); `ARB` is an undefined constant there (`new_constant` in boolScript.sml).

- **Tier 1**: an equation between mapped constants with no choice term (`ARB` allowed) is provable in
  Lean and is free in HOL4's defining theorem (two models of the theorem disagree on it).
- **Tier 2**: only an equation whose right side is a Hilbert-choice term is provable, for example
  `HD = @f. !h t. f (h::t) = h`. HOL4 does not prove it either (`HD` comes from `new_specification`
  style definitions), but every epsilon encoding has it.

| Baseline | Tier 1 instances shown in Lean | Tier 2 |
|---|---|---|
| Fable 5.2 | none found (`HD [] = ARB`, `HD [] = LAST []` are not definitional equalities) | yes: `HD`, `ARB`, `CHR` (all use epsilon) |
| Opus 5.5 | `HD []`, `LAST []`, `dest_var` off `Var`, `RESULT (Clash _)`, `CLASH (Result _)`, `CHR n` for n >= 256 equal `ARB`; so `HD [] = LAST []`, and `RESULT (Clash s) = RESULT (Clash t)` | `ARB`, `SEG` (and `FUN_FMAP`, `instance_`, by the same definitions) |
| Opus 5.5, no lessons | `HD []`, `LAST []`, `dest_var`, `RESULT`, `CLASH` = `ARB` (its `ARB` is `opaque`) | `SEG` |
| Sonnet 5.5 | `ARB = default` (so `ARB = 0` on num, `HD [] = 0`, `LAST [] = 0`), `SEG 1 0 [] = []`, `CHR 256 = CHR 0`, `RESULT (Clash t) = t`, `CLASH (Result t) = t`, `FUN_FMAP f P = FEMPTY` for infinite `P` | `fresh` |

Limits: "none found" for Fable is not a proof of absence. Only the constants already named in the four
`RESULTS.md` files were tested; a systematic pass over every library constant is still to do. The
`Sonnet` `instance_` default is visible in the source but was not tested. The HOL4 side is a reading of
defining theorems, not a HOL4 independence proof; the two-model arguments are simple but were not
machine-checked.

Consequence for the audit base: the Opus baseline needs repair before it can be called clean.
A faithful repair that also removes tier 2 is `opaque` with a subtype, e.g.
`opaque HD_pkg : {f : List a -> a // forall h t, f (h :: t) = h}` with a witness, which is what
HOL4's `new_specification` gives. The structural scan must allow `opaque` for these constants.

## Added later on 24 Nov

- Opus also fixes `FAPPLY` outside the domain to `ARB` (HOL4: `OUTL (INR one)`, unspecified): `FAPPLY FEMPTY 0 = ARB` is a tier-1
  equation. I missed it in the first pass because it is not in `RESULTS.md`.
- The Opus baseline's comment for `ARB` quotes HOL4 as `ARB = @x. F`. HOL4 has no such definition: `ARB` is
  `new_constant`, with no axiom (`src/bool/boolScript.sml` line 245). Earlier audits did not report this comment.
- `audit_base/` is a draft repair of the Opus baseline: `make_repairs.py` makes `ARB`, `HD`, `LAST`, `SEG`,
  `CHR`, `FAPPLY` outside the domain, `FUN_FMAP`, `RESULT`, `CLASH`, `dest_var`, `VARIANT_PRIMES`, `fresh`
  and `instance_` opaque (subtypes of HOL4's defining theorem). It builds with exactly 278 `sorry` theorems,
  no `sorry` definitions and no axioms beyond `propext`, `Quot.sound`, `Classical.choice`. The equations tested in
  this folder for those constants are no longer definitional. Not shown: that none of the rest is provable.

## Systematic pass over the repaired base (24 Nov)

A Sonnet 5.5 agent compared 352 declarations of `audit_base/` with HOL4 and reported no confirmed unfaithful definition. One
lead: `termsem0` on `Abs` of a non-variable was `ARB`. I had told it that TFL definitions are completed with `ARB`, so its
"not a defect" was not independent. I checked HOL4: the theory saves only the four-clause `termsem_def`, and no primitive
definition. `termsem0` is now opaque too (its four clauses are provable, and `= ARB` no longer reduces). Its audit is same-family
as the translator, so it is a candidate search, not evidence of absence. The agent itself says it did not read the 278 statements,
and that VSUBST, INST_CORE, orda, term_union and the other recursions were only read, not tested.
