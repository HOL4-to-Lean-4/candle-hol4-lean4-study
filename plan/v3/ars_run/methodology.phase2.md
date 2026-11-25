# Methodology Review (Peer Reviewer 1) — Phase 2

contract_role: methodology
## Dimension Scores

### D1: methodology_rigor
score: block
trigger: "the sample size for a primary measure is unstated or plainly too small to distinguish the claimed effect from run-to-run variance"
block_class: repairable

### D2: domain_accuracy
score: not_assessed

### D3: argumentative_coherence
score: block
trigger: "attributing an outcome to one component without an ablation"
block_class: repairable

### D4: cross_disciplinary_relevance
score: not_assessed

### D5: writing_and_structure
score: not_assessed

### D6: venue_fit_and_contribution
score: not_assessed

## Review Body

The submission is a study plan, so I judge whether the design, run as written, would support the claims the planned ITP paper intends to make. The reframing in Part A moves the paper's main contribution onto the seeded-defect audit experiment: cross-family audit (Astra validates, Neon reviews, HOL4 grounds) measured against single-family Claude auditors on detection rate, false alarms and cost. That makes the audit experiment the primary measurement, and it is where my concerns concentrate.

The plan has real methodological assets: a freeze with hashes before any model sees the target, isolated headless sessions after the baseline context leak was noticed, a per-call cost ledger reconciled against logs, decoys for false-alarm measurement, and an evidence rule that records every case where an oracle check overturns the reviewer. These are above the norm for LLM-in-ITP work.

The design does not yet identify the effect it wants to claim. The five setups compare single auditors from three families (S1 to S3) with an Astra-then-Neon pipeline (S4) and that pipeline plus grounding (S5). Three variables change together between S3 and S4/S5: model family, the number of stages (find then filter), and access to an oracle. No setup holds family fixed while adding a second stage (for example Opus auditing then a separate Opus or Sonnet reviewer filtering), and none gives a single model the grounding tool. Any S4/S5 advantage in false alarms could therefore come from filtering or grounding rather than from crossing families. A second structural problem: if S4 is S1's output filtered by Neon, then S4 cannot detect more than S1 and S5 cannot detect more than S4. Detection gains are then impossible by construction, and only precision can improve. The plan should state this and frame the hypothesis as a precision and recall trade-off.

The sample is too small for the measures promised. 36 seeded defects spread over roughly thirteen defect subtypes gives two to three instances per subtype. With one run per setup per copy (30 runs = 5 setups x 6 copies), "detection rate per defect type" will be a fraction like 1/3 or 2/3 whose run-to-run noise is unmeasured, while the same plan runs each validation round three times precisely because variation was expected. RQ4 asks how validation varies, yet the audit experiment that carries the main claim has no repeats.

Construct validity of the mutants needs work. The auditors receive the same brief as the baseline audits, and that brief lists the study-1 defect classes from which the mutants are drawn, so detection is partly measured on a checklist the auditor was handed. The HD [] mutant class is labelled a defect, while the baseline analysis treats fixing unspecified values (HD [], RESULT, CHR, FUN_FMAP) as a valid model of the HOL4 spec with no meaning difference. The mutant set leans toward defects that a proof attempt would also expose (strengthened conclusion, dropped hypothesis), and has no provable but silently wrong mutants (weakened conclusion, added or vacuity-inducing hypothesis). Those silent mutants are exactly where certification adds value beyond proving.

Ground truth outside the mutants is not established. False alarms "on unchanged code" assume the Opus baseline is clean, but its cleanliness rests on Claude auditors, comparison agents and targeted HOL4 queries, and the 278 statements are not proved. A finding on unchanged code might be a real defect, and the plan names no procedure (grounding, proof, or adjudication) to decide. The same unproved status undercuts contribution (1) in Part A, which presents "no meaning defects" as a measured finding. The "wrong reasons" measure and the matching of findings to mutants also need a named scorer. With no human expert and an author who "does not adjudicate", the plan does not say who decides that a reason is wrong.

The analysis plan has no uncertainty intervals, no pre-specified rule for when one setup "beats" another, no deterministic-scan baseline for the mutant classes the structural scans already target, and no cost-matched single-family comparison. All of these are repairable before the freeze at modest cost relative to the US$1,150 to 2,550 budget, so I class both blocks as repairable rather than fatal: the design can in principle answer RQ2 once controls, repeats and ground-truth procedures are added.

### S1: Pre-registration-style freeze and isolation
The plan pins commits, manifest, briefs, model identifiers and budgets with hashes before any model sees the target, and moves to isolated headless sessions after the documented chat-message leak. This addresses contamination and drift as procedures, not just as threats.
**Evidence Anchor**: text: §Workflow item 1 "Record their hashes in the repository before any model sees the target."

### S2: Decoys for false-alarm measurement
Adding meaning-preserving rewrites as decoys gives the false-alarm measure a mechanically known negative class, which most LLM-auditor studies lack.
**Evidence Anchor**: text: §Audit experiment, Mutants "A report on a decoy counts as a false alarm."

### S3: Oracle overturns are recorded
The grounding step logs every case where HOL4 or Lean contradicts the reviewer, giving an auditable trail of reviewer error, which the baseline runs already show is needed.
**Evidence Anchor**: text: §Workflow item 8 "We record every case where the check overturns the reviewer."

### S4: Complete cost ledger
Every model call is logged with tokens, billed and API-equivalent cost, and checked against logs before proving rounds, which supports the cost claims in RQ5 and Phase 2 sizing.
**Evidence Anchor**: text: §Costs and token usage "A script checks the ledger against the logs before each proving round, so that no run is missing."

### W1: Cross-family benefit is confounded with staging and grounding
**Problem**: The setups change family, number of stages and oracle access together. There is no same-family two-stage control (Claude auditor then Claude reviewer) and no single-model-plus-grounding control, so an S4/S5 advantage cannot be attributed to crossing families. If S4 filters S1's output, S4 and S5 are also bounded above by S1 on detection by construction.
**Evidence Anchor**: text: §Audit experiment, Setups "Astra followed by Neon review: the workflow as designed."
**Why it matters**: The reframed main contribution is a cross-family certification method measured against single-family auditors. Without these controls the headline attribution is not licensed.
**Suggestion**: Add S6 (Opus audit then a separate Claude reviewer, same instructions as Neon) and S7 (Opus alone with the HOL4/Lean grounding tool). State whether S4 reuses S1's output, and frame the hypothesis as precision gained at a recall cost.
**Severity**: Critical
**Confidence**: 4 — core expertise: experimental design and LLM-judge evaluation

### W2: Too few defects and no repeats for per-type detection rates
**Problem**: 36 defects over about thirteen subtypes gives two to three instances per subtype, and each setup runs once per copy. Per-type rates will be coarse fractions with unmeasured run-to-run noise, although the plan itself runs validation three times to measure variation.
**Evidence Anchor**: text: §Audit experiment, Copies "6 copies, each with 6 seeded defects and 3 decoys placed at random"
**Why it matters**: Differences between setups of one or two detections cannot be separated from nondeterminism, so RQ2 comparisons may be uninterpretable.
**Suggestion**: Run each setup at least three times per copy, report pooled rates with exact binomial or bootstrap intervals, and report per-type results descriptively only. Alternatively, raise the defect count per subtype by using more copies.
**Severity**: Major
**Confidence**: 4 — core expertise: mutation-testing study design

### W3: Audit brief names the seeded defect classes
**Problem**: Mutant types are drawn from the classes the audit briefs list, and auditors receive that same brief. Detection is therefore partly checklist recall rather than open-ended auditing.
**Evidence Anchor**: text: §Audit experiment, Copies "The auditors get the same brief as the baseline audits, with no hint that defects were seeded."
**Why it matters**: Detection rates will overstate performance on defects outside the brief, which is what certification of a new development requires.
**Suggestion**: Cross brief condition (with-lessons vs no-lessons brief) with setup, or hold out some mutant classes not named in any brief and report them separately.
**Severity**: Major
**Confidence**: 4 — core expertise: fault-injection validity

### W4: Clean-baseline ground truth is unproved
**Problem**: False alarms "on unchanged code" and the Part A claim of "no meaning defects" both rest on Claude auditors, comparison agents and targeted HOL4 queries; the statements are not proved. No procedure decides whether a finding on unchanged code is a false alarm or a real defect.
**Evidence Anchor**: text: Part B, Note "the 278 statements have not been proved in Lean yet"
**Why it matters**: Misclassified real defects would inflate false-alarm rates for the best auditors and penalise exactly the behaviour the method rewards.
**Suggestion**: Ground every unchanged-code finding by HOL4 query, Lean counterexample or proof before scoring, report an "unresolved" category, and run the planned proving on the baseline translation used for the mutants.
**Severity**: Major
**Confidence**: 4 — core expertise: ground-truth construction for evaluation

### W5: HD [] mutant contradicts the baseline's own labelling
**Problem**: Fixing an unspecified value to a default is seeded as a defect, yet the baseline analysis accepts Opus's and Sonnet's fixed unspecified values as valid models of the HOL4 spec with no meaning difference.
**Evidence Anchor**: text: §Audit experiment, Mutants "unspecified values fixed to a default"
**Why it matters**: An auditor that correctly reports no meaning change would be scored as a miss, so the label is not valid ground truth.
**Suggestion**: Either drop this class, or define precisely which fixes count as defects (for example ones that make a false HOL4 statement provable) and verify each label with HOL4 before the freeze.
**Severity**: Major
**Confidence**: 3 — adjacent field: relies on the plan's own HOL4 semantics account

### W6: Mutant set lacks provable but silently wrong defects
**Problem**: The listed hypothesis and quantifier mutants (dropped hypothesis, strengthened conclusion) mostly make statements false, so proof attempts would catch them anyway. There are no weakened-conclusion or extra-hypothesis mutants that stay provable while changing meaning. The script records an "expected effect", but nothing checks that effect with the oracle.
**Evidence Anchor**: text: §Audit experiment, Mutants "a dropped hypothesis, a swapped quantifier, a strengthened conclusion"
**Why it matters**: Certification matters most where proofs cannot help. The experiment underweights that case and so cannot show the method's distinctive value.
**Suggestion**: Balance provable-silent against unprovable mutants, tag each mutant by whether proving would expose it, report detection separately for the two groups, and confirm each expected effect with a HOL4 or Lean check.
**Severity**: Major
**Confidence**: 4 — core expertise: mutation-operator design

### W7: No deterministic-scan baseline
**Problem**: The structural scans already target extra typeclass hypotheses and binder types that differ from HOL4's, which are two of the seeded mutant classes, but no scan-only setup is scored.
**Evidence Anchor**: text: §Workflow item 4 "extra or missing typeclass hypotheses"
**Why it matters**: LLM detection of these classes cannot be credited to the auditors if a script finds them for free.
**Suggestion**: Add S0 (structural scans only) and report each LLM setup's increment over S0.
**Severity**: Major
**Confidence**: 4 — core expertise: baseline selection in tool evaluation

### W8: Reason-correctness and finding matching have no named scorer
**Problem**: The plan measures how many reasons are wrong and must also match findings to mutants, but it removes the human expert and says the author does not adjudicate. It names no rater, rubric or agreement check.
**Evidence Anchor**: text: §Audit experiment, Measures "how many reported reasons are wrong even when the verdict is right"
**Why it matters**: If an LLM or the author scores these measures without a protocol, the measure inherits the judge's errors, which is the failure the study sets out to measure.
**Suggestion**: Pre-specify a matching rule (declaration plus mutation class) and a rubric for reason correctness. Have two scorers apply it blind to setup, one human, and report agreement.
**Severity**: Major
**Confidence**: 4 — core expertise: LLM-judge validation

### W9: Cost matching and output reuse unspecified
**Problem**: The single auditors S1 to S3 use one model call per copy while S4 and S5 use two or more, and the plan does not say whether S4 reuses S1's run.
**Evidence Anchor**: absence: §Audit experiment, Setups and Budget — expected a statement of output reuse across S1, S4 and S5 and a cost-matched single-family comparison; checked Setups, Measures, Budget, Budget estimate table
**Why it matters**: A multi-stage pipeline can look better simply by spending more.
**Suggestion**: Report detection and false alarms per dollar, and add a cost-matched single-family arm (for example the union or a vote of two Opus runs).
**Severity**: Minor
**Confidence**: 4 — core expertise: cost-aware evaluation

### W10: No pre-specified analysis or decision rule
**Problem**: RQ2 asks whether two families "beat" a single auditor, but no primary metric, uncertainty interval, paired test or threshold is pre-specified.
**Evidence Anchor**: absence: §Audit experiment and §Research questions — expected a primary metric, interval method and decision rule for RQ2; checked Measures, Budget, Research questions, Threats to validity
**Why it matters**: With many per-type and per-setup comparisons, post-hoc choice of the favourable contrast is easy.
**Suggestion**: Fix one primary contrast (for example S5 vs S3 precision and recall on pooled defects) with paired per-defect comparison and intervals, and label everything else exploratory.
**Severity**: Minor
**Confidence**: 4 — core expertise: evaluation statistics

### W11: "Lessons change nothing" rests on one run and an LLM comparison
**Problem**: The no-lessons conclusion comes from a single Opus run, judged against the baseline by an Opus comparison agent on a target where the with-lessons runs were already clean, so a ceiling effect is likely.
**Evidence Anchor**: text: Part A "removing study 1's lessons from the briefs changes nothing"
**Why it matters**: It is stated as a measured finding in contribution (1). The planned known-defect target is the right test, but the claim should wait for it.
**Suggestion**: State the Candle result as no detected difference at ceiling, and draw the lessons conclusion from the type-soundness closure with repeated runs.
**Severity**: Minor
**Confidence**: 4 — core expertise: ablation design

### W12: Motivating evidence counts and "independent" are loose
**Problem**: Part A says three Claude auditors independently made the same wrong claim; the plan says two, and the third is a comparison agent. The runs shared a harness context, so "independently" is not established.
**Evidence Anchor**: text: Part A "three Claude auditors independently made the same wrong claim"
**Why it matters**: The shared-error motivation for crossing families is evidence of correlated error only if the instances are actually independent.
**Suggestion**: Report the exact count and roles, and describe them as same-family agents in related sessions rather than as independent auditors.
**Severity**: Minor
**Confidence**: 3 — adjacent field: relies on the summaries in Part B

## Arithmetic Receipts

no_recomputable_statistics: the plan and baseline summaries report only counts, costs, durations and planned sample sizes (for example 36 defects, 30 audit runs, 245/278 identical statements); there are no test statistics, p-values, df, or means with SDs, so no bounded procedure applies
