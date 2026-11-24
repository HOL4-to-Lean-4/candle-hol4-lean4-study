# Mutation operators, eligibility, sampling (draft, 24 Nov 2026, not approved or frozen)

Base: `E:/ts_ws/audit_base/lean` (repaired Opus baseline; builds, 278 `sorry` theorems). Never edit it.

## Presentation to auditors
All block comments and doc comments that quote HOL4 are removed from every unit (clean, mutant, decoy), and from the read-only context.
Reason: the base quotes each HOL4 definition above its Lean definition; an auditor could find a mutant by comparing the two
lines, which would measure reading one file. Auditors get the HOL4 sources and the query tool instead. Line comments that carry a
translator claim about HOL4 are removed too. (Open for the author: the same audit with comments kept, as a subset, would measure how much they help.)

## Site model
A site is one declaration (def, opaque spec, inductive constructor, abbrev, theorem statement) in the comment-stripped base.
Candidates are produced by scripted text operators on the declaration's own source, never by hand.

## Operators (family: operator ids)
- numbers: N1 literal +1 or -1; N2 `<` to `≤` or the reverse; N3 `+` to `-`, or the reverse (Nat); N4 0/1 base case.
- characters and strings: C1 one character of a string or char literal changed; C2 strict/non-strict char or string order swapped; C3 string/mlstring conversion dropped or added where the types allow it.
- overloads: O1 `∪`/`∩`, `pair`/`upair`, `LESS`/`GREATER`, `LIST_TO_SET`/other set image, fmap vs alist lookup helper.
- hypotheses and quantifiers: H1 drop one premise of a constructor or statement; H2 `∀`/`∃` swap; H3 move a bound variable inside or outside a conjunct.
- definitions: D1 swap two same-typed arguments of a call; D2 swap the branches of an `if` or two match arms of equal type; D3 replace a recursive call argument by a sibling of the same type; D4 reorder or remove a match arm.
- type signatures: T1 change the type of a quantified variable or argument to another type already imported (compiles).
- unspecified values (V-C): U1 replace an `opaque` specification by a def that fixes the unspecified case to one value or to another mapped constant.
- weakenings: W1 drop a conjunct of a conclusion or definition; W2 add a hypothesis; W3 replace `∧` by `∨`; W4 replace `↔`/`=` by an implication.

Held out (not named in any brief, reported separately): X1 finite-map update or union order (left-bias), X2 binder capture or substitution-condition swap (`x ∉ FV`, avoided name), X3 list order or multiplicity (`++` swap, `reverse`, `nub`, `EVERY`/`EXISTS`).

## Eligibility
1. The mutated project elaborates (compile check of the module and its dependents, `sorry` allowed).
2. Not byte-identical to the base and not an operator on an auxiliary lemma (`Aux.*`) or on a proof.
3. Not syntactically the same change as an accepted mutant at the same declaration.
4. Has a witness (below). Mutants without a witness are dropped and counted.

## Witness
- Definition, prelude or inductive: a Lean file importing the base, with the mutated declaration restated in namespace `Mut` (renamed recursion and its dependents as
  needed), and a proof of a concrete difference: `∃ inputs, Mut.f … ≠ f …` (functions) or `¬ ∀ inputs, (Mut.R … ↔ R …)` (relations, Props).
  For U1: a proved equation on the mutated constants that is not in Φ, with the HOL4 defining theorem that leaves it open.
- Statement: a proof that the mutated statement is false, or (silent weakening) that it is strictly weaker: a proof of it from the base statement plus an argument, stated as a Lean
  theorem about the difference, or it is dropped.
Equivalent or undecided mutants are dropped, never relabelled.

## Sampling
Seed 20261124. Enumerate all sites and operators, filter by 1-3, shuffle with the seed, keep a pool of at least 150 candidates with at most 2 per declaration and
quotas: 60% definition modules, 25% prelude, 15% statements; at least 6 per family, at least 5 per held-out operator. Witnesses are then attempted in shuffled order.
Tags per mutant: id, family, operator, scope, module, declaration, label (V-P or V-C), silent or visible, seed position.
`silent` = weakened conclusion, dropped conjunct, extra hypothesis, or a weaker definition that a proof of every target statement would not expose.
The tag is the operator's default and is marked provisional; it is not used in the primary analysis until checked.

## Decoys
Meaning-preserving rewrites of a declaration, produced by operators R1 rename bound variables, R2 commute `∧`/`∨`/`=`/`↔`, R3 swap independent quantifiers, R4 eta/beta, R5 unfold or fold one abbreviation,
R6 equivalent `match`/`if` forms. Each needs a Lean proof of equivalence with the base declaration. Pool at least 40.

## Amendments after a spot check of 32 mutants (24 Nov 2026, before any witness was attempted)
- D4: reordering arms that cannot overlap is equivalent, so it is a decoy operator; D4 mutants reorder overlapping arms or remove an arm a later wildcard covers.
- C3: identity conversions are equivalent, so they are dropped as mutants. T1: only used variables, only non-convertible types.
- Mutants and decoys must not carry text fingerprints (redundant parentheses); the generator reports the share.
- No operator may exceed 12% of the pool.
- Candidates dropped only because a proved auxiliary lemma of the base stops compiling are a selection bias; the count is reported.
- Known limits: the spec, operators and spot check come from Claude sessions, the same family as one audit arm; the operators are scripted and the samples are seeded.
