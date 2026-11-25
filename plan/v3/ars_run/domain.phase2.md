contract_role: domain
## Dimension Scores

### D1: methodology_rigor
score: not_assessed

### D2: domain_accuracy
score: block
trigger: "omission of directly competing prior work such that the claimed gap may not exist"
block_class: repairable

### D3: argumentative_coherence
score: not_assessed

### D4: cross_disciplinary_relevance
score: not_assessed

### D5: writing_and_structure
score: not_assessed

### D6: venue_fit_and_contribution
score: not_assessed

## Review Body

Reviewer identity: researcher in proof-assistant interoperability (OpenTheory, HOL importers into Isabelle and Lean, Dedukti) and in HOL4 and Lean 4 semantics. Confidence overall: 4. Calibration status: `NOT_CALIBRATED`. No criteria binding was supplied, so this card makes no venue-alignment claim.

Summary. The plan is reviewed as a design for an ITP 2027 paper. Its descriptions of the source and target systems are mostly accurate: the treatment of unspecified values under `Prim_rec`, the standard Lean axiom set, the 8-bit HOL4 `char`, and the known study-1 defects (`CARD` on infinite sets; floored HOL4 integer division versus Lean's Euclidean `/`) are all stated correctly. D2 is still scored `block` (repairable) for three reasons. First, the plan never positions itself against the established alternative to LLM-read scripts: exporting typed HOL4 kernel terms, or using symbolic importers. That alternative bears directly on the claimed certification gap. Second, the seeded-defect design treats a modelling choice as a defect even though the baselines accept the same choice as a valid model of the HOL4 specification. That makes the ground truth for one mutant class inconsistent. Third, the plan overstates what the HOL4/Lean oracle and proving can certify. All three are repairable in the plan before the freeze. None makes the study infeasible, so the block is not fatal.

### S1: HOL4 used as the arbiter of HOL4 meaning, with a correct finding on Prim_rec
The plan correctly tells HOL4's `Define` pattern completion apart from definitions built through `Prim_rec` or recursion theorems, which leave missing cases unspecified. It also uses a HOL4 query, rather than model consensus, to settle the question. This is the right epistemic stance for a translation study.
**Evidence Anchor**: text: Part B item 2 "HOL4 check showed these definitions leave cases unspecified (Prim_rec)"

### S2: Precise kernel-level axiom accounting in Lean
The baselines state exactly which axioms the non-target declarations depend on (the three standard Lean axioms), and confine `sorryAx` to the 278 targets. This is the correct and checkable notion of "standard axioms only" in Lean 4.
**Evidence Anchor**: text: Part B common setup "everything else uses only propext, Classical.choice, Quot.sound"

### S3: Known real defects that are domain-accurate
The known-defect target uses real semantic mismatches between HOL4 and Lean 4: HOL4's integer `/` is floored while Lean 4 core `Int` division is Euclidean, and `CARD` on infinite sets is unspecified in HOL4 but has fixed conventions in Lean libraries. These are good stress cases.
**Evidence Anchor**: text: §7 item 2 "Euclidean instead of floored integer division"

### W1: Fixed defaults for unspecified values are a valid model in the baselines but a seeded defect in §8
**Severity**: Major
**Evidence Anchor**: text: §8 Mutants "unspecified values fixed to a default"
**Confidence**: 5 — HOL4 definitional semantics and Lean modelling of underspecification
Part B accepts Sonnet's fixed values (`RESULT (Clash t) = t`, `CHR n = CHR 0`, `FUN_FMAP` on infinite sets) as "each a model of the HOL4 spec". It also accepts Opus fixing `HD []` to a single `ARB` because no target is affected. §8, however, seeds exactly this change (`HD []` fixed to a default) as a defect, so any detector that flags it is scored as correct and any that accepts it as wrong. Under a statement-meaning criterion, a fixed default is a sound refinement: every HOL4 theorem about the constant still holds. It makes the Lean theory strictly stronger, so equations such as `HD [] = ARB` become provable in Lean but not in HOL4. That matters for provability and for the later proofs, not for whether a frozen statement is faithful. The plan needs one explicit fidelity definition (statement meaning, conservativity of the definitional theory, or both) and must score both the baselines and the mutants against it. Otherwise the detection rate and false-alarm rate for this class are undefined. If conservativity is the criterion, the baseline verdicts of "no meaning defects" need revisiting for Opus and Sonnet.

### W2: No positioning against kernel-term export or symbolic importers
**Severity**: Major
**Evidence Anchor**: absence: §2 What is known already and Part A contributions — expected positioning against typed HOL4 kernel-term export and symbolic importers (OpenTheory, HOL importers into Isabelle, Dedukti/Logipedia); checked Part A, Part B, §1, §2, §5, §6, §7, §8, Threats to validity
**Confidence**: 4 — interoperability literature; exact HOL4 export coverage for this package not verified
The translators read HOL4 scripts, including ML-built theorems (`SIMP_CONV`, `EVAL`, `CONJUNCTS`). Several of the HOL4 questions in §6 (which overload `(a,b)` resolves to, ML-built statement shapes, the inferred types of unused binders) exist only because of that choice. HOL4 can print or export every stored theorem as a fully typed kernel term, and HOL4 has OpenTheory support. With such an export, these questions become mechanical, and a symbolic statement translator with a fixed constant map would give an independent reference translation. There is a long line of work on this: OpenTheory, the HOL importers into Isabelle/HOL, scalable LCF-style proof translation from HOL Light to Isabelle, and HOL-to-Dedukti translation. The plan cites none of it and does not explain why an LLM audit is needed where a kernel-term export plus a constant map would do. The gap is real in part: importers yield theorems about imported constants rather than idiomatic Lean types such as `Nat`, `Int` or `String`, and the gap lies in this mapping step. The paper must argue this, ideally with a kernel-term-export baseline for statement shapes. This is the basis of the D2 block, because the main contribution in Part A rests on it.

### W3: The HOL4/Lean oracle cannot settle most meaning questions, yet it is presented as ground truth
**Severity**: Major
**Evidence Anchor**: text: §1 item 2 "HOL4 runs and Lean counterexamples check claims about meaning, so the study does not rely on a model's word."
**Confidence**: 4 — limits of decision procedures and evaluation in both systems
The query tool answers four kinds of question: print, parse, ground evaluation, and a short proof attempt. Lean grounding uses `#eval` or `decide`. No kernel can check whether a Lean statement means the same as a HOL4 statement, because the two have no shared semantics. Ground evaluation also misses the usual defects: higher-order or quantified statements, inductive relations such as `type_lt`, and anything defined through `Classical.epsilon`. The baselines use `Classical.epsilon` for unspecified values, so those declarations are noncomputable and `#eval` cannot run on them. A failed short proof is not a refutation. In addition, a model writes the "cited check", so a check that is valid but irrelevant can still confirm a wrong finding. The paper should say which finding classes are decidable by grounding and which are not, report grounding as partial evidence, and validate the query construction itself, for example by checking that queries mention the constants at issue.

### W4: Proving the statements is presented as certification of fidelity
**Severity**: Major
**Evidence Anchor**: text: Part A contribution 3 "proving the 278 statements in Lean (kernel-checked, frozen statements, standard axioms only)"
**Confidence**: 4 — standard ITP fidelity reasoning
Kernel-checked proofs show that the Lean statements are true relative to the Lean definitions. They do not show that statements or definitions match HOL4. A weakened conclusion, a dropped conjunct, an added hypothesis, or a definition that diverges consistently between statement and proof is still provable. Proving exposes only translations that are too strong. Without a human, the plan also has no criterion for telling a stuck proof (prover failure within budget) from a false statement (a translation defect). RQ1 ("do proof attempts again expose defects") needs such a criterion, for example a Lean counterexample or a proof of the negation before a statement counts as false. The paper should present proving as one-sided evidence and say which mutant classes in §8 it can and cannot detect.

### W5: The "pattern completion" error is described too broadly
**Severity**: Minor
**Evidence Anchor**: text: Part A motivating evidence "three Claude auditors independently made the same wrong claim about HOL4 semantics"
**Confidence**: 4 — HOL4 TFL/`Define` behaviour
HOL4's `Define` does complete missing patterns with `ARB`. The auditors' error was attributing that behaviour to constants defined through `Prim_rec`, recursion theorems or datatype destructors. Calling it a wrong claim about HOL4 semantics overstates the case, and §2 says two auditors while Part A says three. State the precise mechanism and the count per run. This also makes the motivating example more convincing to ITP readers.

### W6: An extra Nonempty instance is seeded as a defect, although HOL types are inhabited
**Severity**: Minor
**Evidence Anchor**: text: §8 Mutants "type signatures: an unused binder at a fixed type, or an extra"
**Confidence**: 4 — HOL type inhabitation versus Lean typeclass hypotheses
Every HOL4 type is nonempty by construction, and the baselines model unspecified values with `Classical.epsilon`, which needs `Nonempty`. An added `[Nonempty α]` or `[Inhabited α]` on a polymorphic statement is therefore often a faithful encoding of a HOL invariant, not a defect. It becomes a defect only where it changes which instances the statement covers in practice. The mutant list should say which binders count, or this mutant should be reclassified as a decoy.

### W7: No related work on evaluating autoformalisation faithfulness or on large-scale porting
**Severity**: Minor
**Evidence Anchor**: absence: §2 What is known already — expected prior work on evaluating statement faithfulness in autoformalisation and on large library ports; checked Part A, §1, §2, §10 Research questions, Threats to validity
**Confidence**: 3 — familiar with the benchmarks; their coverage of this setting is limited
The audit experiment measures how well LLMs judge statement faithfulness. Benchmarks such as miniF2F and ProofNet, and alignment evaluators such as FormalAlign, are the obvious comparison points for detection and false-alarm measures, even though they target mathematics rather than language semantics. The Lean 3 to Lean 4 Mathlib port (Mathport plus human repair) is the main large-port precedent for the Phase 2 claims. Candle itself should be cited for the target's provenance.

### Missing Key References
- Hurd, "The OpenTheory Standard Theory Library" (NFM 2011): the HOL-family statement and proof exchange format.
- Obua and Skalberg, "Importing HOL into Isabelle/HOL" (IJCAR 2006), and Kaliszyk and Krauss, "Scalable LCF-style proof translation" (ITP 2013): symbolic HOL importers.
- Assaf and Burel, "Translating HOL to Dedukti" (PxTP 2015): logic-level translation; see also the Logipedia effort.
- Zheng, Han and Polu, "MiniF2F: a cross-system benchmark for formal Olympiad-level mathematics" (ICLR 2022), and Azerbayev et al., "ProofNet: Autoformalizing and Formally Proving Undergraduate-Level Mathematics" (2023).
- FormalAlign, "FormalAlign: Automated Alignment Evaluation for Autoformalization" (2024): automated faithfulness scoring.
- Abrahamsson et al., "Candle: A Verified Implementation of HOL Light" (ITP 2022): the target development.
- Mathport, the Lean community's Lean 3 to Lean 4 porting tool.

~~~yaml suggested-references
- title: "The OpenTheory Standard Theory Library"
  authors: ["Hurd, J."]
  year: "2011"
  doi: null
  arxiv_id: null
- title: "Importing HOL into Isabelle/HOL"
  authors: ["Obua, S.", "Skalberg, S."]
  year: "2006"
  doi: null
  arxiv_id: null
- title: "Scalable LCF-style proof translation"
  authors: ["Kaliszyk, C.", "Krauss, A."]
  year: "2013"
  doi: null
  arxiv_id: null
- title: "Translating HOL to Dedukti"
  authors: ["Assaf, A.", "Burel, G."]
  year: "2015"
  doi: null
  arxiv_id: null
- title: "MiniF2F: a cross-system benchmark for formal Olympiad-level mathematics"
  authors: ["Zheng, K.", "Han, J. M.", "Polu, S."]
  year: "2022"
  doi: null
  arxiv_id: "2109.00110"
- title: "ProofNet: Autoformalizing and Formally Proving Undergraduate-Level Mathematics"
  authors: ["Azerbayev, Z."]
  year: "2023"
  doi: null
  arxiv_id: "2302.12433"
- title: "FormalAlign: Automated Alignment Evaluation for Autoformalization"
  authors: []
  year: "2024"
  doi: null
  arxiv_id: null
- title: "Candle: A Verified Implementation of HOL Light"
  authors: ["Abrahamsson, O."]
  year: "2022"
  doi: null
  arxiv_id: null
~~~

### Questions for Authors
1. Which fidelity notion does the study certify: statement meaning only, or also conservativity of the Lean definitional theory over HOL4's?
2. Why not export typed HOL4 kernel terms for the 278 targets and compare statement shapes mechanically before any LLM audit?
3. Which classes of finding can grounding decide, and how is a model-written query checked for relevance?
4. How will a stuck proof be told apart from a false statement without a human adjudicator?

### Minor Issues
- Record how `ARB` is represented in Lean (one constant across types, or one per type), because that decides which equations become provable.
- Fix the auditor count (two in §2, three in Part A and Part B) so it agrees across sections.
