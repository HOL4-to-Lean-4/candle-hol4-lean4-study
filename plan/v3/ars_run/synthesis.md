# Editorial Decision Package

## Calibration Resolution

`calibration_status: NOT_CALIBRATED`

Current runtime boundary: this package is not upgraded from any candidate or prose-named profile. `PROFILE_MEASURED` remains unavailable until a closed profile artifact and replay validator bind the target fields to the completed panel's `execution_topology_sha256`.

## Criteria Binding

The dispatcher declared this run explicitly unbound (`criteria_binding_unavailable`). No venue-criteria-alignment claim is made in this package beyond what the reports themselves say. Conformance note (not a score, failure condition, severity or verdict): only the domain card states the unbound status in its own text ("No criteria binding was supplied, so this card makes no venue-alignment claim"); the EIC, methodology, perspective and DA cards do not repeat it. `[CRITERIA-BINDING-DISCLOSURE: 1/5 cards disclose explicitly; run declared unbound by dispatcher]`

## Sprint Contract Synthesizer Protocol (v3.6.2) — mechanical audit

Contract: `reviewer/reviewer_full/v2`, panel_size 5, roles eic, methodology, domain, perspective, da. All five cards usable; no `[PANEL-SHRUNK]`.

**Step 1 — Role-scoped scoring matrix** (only assessed scores from eligible roles; `not_assessed` from ineligible seats excluded from numerator and denominator):

| Dimension | Priority | Eligible roles | Assessed eligible scores | n | Verdict (worst) | Fatal? |
|---|---|---|---|---|---|---|
| D1 methodology_rigor | mandatory | methodology | methodology=block (repairable) | 1 | block | no |
| D2 domain_accuracy | mandatory | domain | domain=block (repairable) | 1 | block | no |
| D3 argumentative_coherence | mandatory | da, methodology | da=block (repairable), methodology=block (repairable) | 2 | block | no |
| D4 cross_disciplinary_relevance | high | perspective | perspective=warn | 1 | warn | no |
| D5 writing_and_structure | normal | eic | eic=warn | 1 | warn | no |
| D6 venue_fit_and_contribution | mandatory | eic | eic=warn | 1 | warn | no |

No dimension is unassessed.

**Step 2 — Failure conditions** (two-stage: cross_reviewer_quantifier per dimension over assessed eligible seats, then the expression's dimension quantifier):

| Condition | Severity | Quantifier | Expression | Per-dimension evaluation | Fired |
|---|---|---|---|---|---|
| F1 | 95 | any | any mandatory dimension has a fatal block | D1, D2, D3, D6: no seat declared `block_class: fatal` | false |
| F2 | 90 | any | any mandatory dimension scores 'block' | D1 true (1/1), D2 true (1/1), D3 true (2/2), D6 false | true |
| F3 | 70 | majority | two or more mandatory dimensions score 'warn' or worse | D1 owner n=1 true; D2 owner n=1 true; D3 n=2 both true; D6 owner n=1 true → 4 ≥ 2 | true |
| F4 | 60 | any | any high-priority dimension scores 'block' | D4 = warn → false | false |
| F5 | 40 | any | any dimension scores 'warn' or worse | all six dimensions true | true |
| F0 | 10 | all | every dimension scores 'pass' | no dimension passes | false |

**Step 3 — Precedence.** Fired: F2 (90), F3 (70), F5 (40). Highest severity is F2, action major revision. The action is not softened.

```
dimension_verdicts: [D1=block, D2=block, D3=block, D4=warn, D5=warn, D6=warn]
fired_conditions: [F2, F3, F5]
da_critical_adjudications: [C1=VALIDATED]
editorial_decision=major_revision
```

No `[DA-CRITICAL-VS-ACCEPT]` marker is needed: the mechanical decision is not accept.

### DA CRITICAL C1 adjudication (visible)

- **DA's argument (C1, D3)**: circular premise. Contribution (1), "translation now works", is established only by single-family Claude checking, which contribution (2) is motivated by showing to be unreliable. The reframing asserts the conclusion the audit method is meant to test. DA proposes reordering: measure the checkers first, then apply the best grounded setup to the baselines before claiming fidelity.
- **Corroboration by other seats**: EIC W5 ("Headline translation finding rests on same-family judgement", Major, conf. 3); methodology W4 ("Clean-baseline ground truth is unproved ... The same unproved status undercuts contribution (1)", Major, conf. 4); domain W1 adds that under a conservativity criterion "the baseline verdicts of 'no meaning defects' need revisiting for Opus and Sonnet" (Major, conf. 5). Perspective W4 raises a related but distinct threat (contamination) to the same contribution.
- **Check against the plan** (data, consulted only to verify the claim): Part B carries the note "'no meaning defects' in 2-4 is judged by Claude auditors/comparison agents plus targeted HOL4 queries; the 278 statements have not been proved in Lean yet", and Part A states "Translation now works" as contribution (1). The DA's anchors are accurate.
- **Adjudication**: **VALIDATED.** The premise is evidenced in the plan and independently corroborated by two scoring seats with different remits. It is repairable, as the DA classes it (`block_class: repairable`).
- **Required author response**: re-scope contribution (1) as conditional, or reorder the paper so the baseline fidelity claim is reported only from the measured, grounded audit and the Lean proofs (roadmap R15, with R3).

## Review Panel Provenance (#540/#740)

- **Typed artifact**: not supplied. No replay-valid `review-panel-provenance/1.0` artifact was provided to this synthesis. `[PROVENANCE-ARTIFACT-MISSING]`
- **Artifact SHA-256**: unknown
- **Panel ID**: unknown
- **Normalized manifest SHA-256**: unknown
- **Execution topology SHA-256**: unknown
- **Fresh-context scope**: `within_panel_attempt_only` (does not compare retries or prior rounds)

| Seat | Role ID | Actor type | Context ID | Peer outputs visible | Model family | Provider | Human reviewer ID |
|---|---|---|---|---|---|---|---|
| EIC | eic | unknown | unknown | unknown | unknown | unknown | unknown |
| R1 | methodology | unknown | unknown | unknown | unknown | unknown | unknown |
| R2 | domain | unknown | unknown | unknown | unknown | unknown | unknown |
| R3 | perspective | unknown | unknown | unknown | unknown | unknown | unknown |
| DA | da | unknown | unknown | unknown | unknown | unknown | unknown |

| Provenance axis | Status |
|---|---|
| Role-separated | unknown |
| Within-panel invocation-context separation | unknown |
| Blind to peer outputs | unknown |
| Model-family distinct | unknown |
| Provider distinct | unknown |
| Human-reviewer distinct | unknown |

- **Binary independence claim**: not computed. Role diversity proves only role separation; the panel is not relabelled as independent.
- **Dispatcher statement (not an artifact observation)**: the dispatching layer reports that all five seats ran on one Claude model family (Opus 5.5) in fresh subagent contexts with no peer-output visibility. Because no artifact backs it, the axes above stay `unknown`.
- **Correlated-error disclosure**: the model family is not verified as distinct across seats, and by the dispatcher's own report every seat ran on the same model family. Agreement across seats may therefore reflect shared model errors rather than independent confirmation. Consensus labels below count role-separated seats; they are not independent votes. This is also the very failure mode the manuscript studies (same-family shared wrong claims), so the author should weigh panel agreement accordingly.
- **Cross-Model Reviewer Track**: not active. No cross-model decision check was run (`ARS_CROSS_MODEL` not set).

---

## Part 1: Editorial Decision Letter

Dear Author,

Thank you for submitting the study plan "Migrating CakeML from HOL4 to Lean 4 with a three-family AI workflow: study plan (v3.2) with proposed reframing", reviewed as a design for a planned ITP 2027 regular paper. The plan was assessed by five role-separated review seats: a Journal-Fit Reviewer (EIC), a methodology reviewer (R1), a domain reviewer (R2), a cross-disciplinary reviewer (R3) and a Devil's Advocate (DA). Their execution provenance is reported above and is not reduced to an independence claim.

### Decision: Major Revision

### Consensus Analysis

Consensus is counted per sub-claim over the four non-DA seats (EIC, R1, R2, R3). Silence is not agreement.

#### Points of Agreement (Consensus)
- **[CONSENSUS-4] SC-8**: the motivating evidence is reported inconsistently (two Claude auditors in Section C versus three in Parts A/B) and the word "independently" is not supported. Raised by EIC W8, R1 W12, R2 W5, R3 W2; also noted by the DA (Minor Issues; M4). Severity differs by seat (Minor for EIC/R1/R2; Major as part of R3's broader W2); all four recommend the same fix.
- No sub-claim reached CONSENSUS-3.

#### Corroborated findings (two seats, no conflict)
- **SC-3** headline "no meaning defects" finding rests on unproved, same-family judgement (EIC W5, R1 W4; DA C1).
- **SC-11** cross-family benefit is confounded with staging and grounding; a same-family two-stage control is missing (R1 W1 Critical, R3 W2 Major; DA M3). The severity difference is adjacent (both decision-bearing) and both seats ask for the same control, so it is not treated as a conflict.
- **SC-13** auditor brief names the seeded defect classes; detection measures recall of announced classes (R1 W3, R3 W1; DA M2).
- **SC-15** "unspecified value fixed to a default" (`HD []`) is seeded as a defect but accepted as valid in the baselines (R1 W5, R2 W1; DA M1).
- **SC-23** the HOL4/Lean oracle cannot settle most meaning questions and is over-presented as ground truth (R2 W3, R3 W1; DA M7 is related).

#### Points of Disagreement
- **SC-4 — severity of "certification" wording**: EIC W3 rates it Minor (terminology at ITP); R3 W1 rates it Major (assurance readers will read it as a residual-risk guarantee). Both agree on the existence of the problem and on compatible remedies.
  - **Editor's Resolution**: treated as must-fix. Rationale: "certification method" is the label of the declared main contribution, R3's concern sits in its core expertise (assurance cases), and the DA independently notes the label outruns the evidence (M2). EIC's remedy (use "audit" / "validation evidence") and R3's (state an explicit assurance argument) are both acceptable; the author chooses.
- **SC-24 — what Lean proving contributes**: R2 W4 holds that proving shows provability, not fidelity, and exposes only too-strong translations (R1 W6 agrees that proofs catch only some defect classes; DA M8 concurs). R3 W1 suggests treating proving all 278 statements as "the strongest evidence leg".
  - **Editor's Resolution**: R2's position governs the claim. What a kernel-checked proof certifies is a domain question within R2's remit, and R1 and the DA support it. R3's assurance-argument structure is kept, but proving enters it as one-sided evidence (it refutes too-strong statements only), not as unqualified strongest evidence. Recorded as arbitrated, not unanimous.

#### Single-reviewer findings
All other sub-claims (see Part 2) were raised by one non-DA seat and are evaluated on their named criterion and evidence anchor. Several carry decision weight because they underlie a block score: SC-12 (sample size, R1's D1 trigger) and SC-22 (missing kernel-term-export/importer positioning, R2's D2 trigger).

### Decision Rationale

The decision is mechanical under the sprint contract: three mandatory dimensions score block. Methodology rigour (D1) is blocked because the audit experiment that carries the main claim has about 36 defects over roughly thirteen subtypes, one run per setup per copy, and no pre-specified analysis, so setup differences cannot be separated from run-to-run variance (R1 W2, W10). Domain accuracy (D2) is blocked because the plan does not position itself against typed HOL4 kernel-term export and symbolic importers, which bear directly on whether the claimed certification gap exists (R2 W2). Argumentative coherence (D3) is blocked by two seats: R1 because the cross-family benefit is attributed without a same-family two-stage or single-model-plus-grounding control (R1 W1), and the DA because the headline "translation now works" finding rests on exactly the single-family checking the paper argues is unreliable (C1, validated). Venue fit (D6), writing (D5) and cross-disciplinary relevance (D4) score warn: the plan carries two competing framings, does not answer the ITP porting bar explicitly, has no 16-page outline, and uses "certification", "independence" and "no human expert" more strongly than the measurements support (EIC W1, W2, W6; R3 W1–W3).

Every block is classed repairable by its seat, and no seat declared a fatal flaw. All seats credit real strengths: the hashed freeze and isolated sessions, decoys for false-alarm measurement, HOL4 as arbiter of HOL4 meaning, the wrong-reason count, and the full cost ledger. The repairs are mostly design additions before the freeze (controls, repeats, a fidelity definition, scoring protocol, positioning) plus re-scoping of contribution (1). The plan should be revised and re-reviewed before execution.

### Blocking Issues (immutable source order)

| Transport ref | Blocking issue | Source reviewer(s) | Evidence anchor | Resolving roadmap item |
|---|---|---|---|---|
| R7 | Too few defects and no repeats for per-type and between-setup claims (D1 block) | R1 (DA M5) | text: §Audit experiment, Copies "6 copies, each with 6 seeded defects and 3 decoys placed at random" | REV-R7 |
| R12 | No positioning against kernel-term export or symbolic importers (D2 block) | R2 | absence: §2 What is known already and Part A contributions — expected positioning against typed HOL4 kernel-term export and symbolic importers | REV-R12 |
| R15 | Circular premise: contribution (1) rests on single-family checking the paper deems unreliable (D3 block, DA C1 validated) | DA (EIC W5, R1 W4) | text: Section B Note "is judged by Claude auditors/comparison agents plus targeted HOL4 queries" and Section A "Translation now works" | REV-R15 |

The D3 block from R1 (SC-11, roadmap R6) is equally decision-bearing; it is listed in the roadmap rather than here only because this table is capped at three rows.

---

## Part 2: Revision Roadmap

Schema target: `revision-roadmap/1.0`, reviewer-owned core. Items are keyed to `sub_claim_id` and kept in immutable source order (roster order of first raising seat: EIC, R1, R2, R3, then DA-only). `R<n>` and `S<n>` are transport references, not ranks. `proposed_targets[]`: unavailable — no bound block manifest was supplied, so no block ids or operations are proposed. Consequence codes are drawn from a closed set: `decision_blocking:<Dn>`, `claim_unsupported:<target>`, `measure_invalid:<target>`, `reviewer_objection_risk:<target>`, `clarity:<target>`.

### Step 1b — Weakness Sub-Claim Inventory

Severity and confidence are transported from the cards. DA findings are listed in the last column for visibility only; they do not count toward consensus.

| sub_claim_id | parent_weakness | EIC | R1 | R2 | R3 | agree / conflict | Disposition | DA |
|---|---|---|---|---|---|---|---|---|
| SC-1 | Two competing framings (EIC W1) | raised (Major, 4) | — | — | — | 1/0 | single | Minor Issue (RQ1) |
| SC-2 | ITP porting bar unanswered (EIC W2) | raised (Major, 4) | — | — | — | 1/0 | single | M8 |
| SC-3 | Headline finding rests on unproved same-family judgement (EIC W5; R1 W4) | raised (Major, 3) | corroborated (Major, 4) | — | — | 2/0 | corroborated | C1 |
| SC-4 | "Certification" overstates the measure (EIC W3; R3 W1) | raised (Minor, 4) | — | — | disputed-severity (Major, 4) | 2/1 | SPLIT, arbitrated | M2 |
| SC-5 | Delta from FormaliSE paper not stated (EIC W4) | raised (Major, 4) | — | — | — | 1/0 | single | — |
| SC-6 | No outline or page budget (EIC W6) | raised (Major, 4) | — | — | — | 1/0 | single | — |
| SC-7 | Scope too broad (EIC W7) | raised (Minor, 4) | — | — | — | 1/0 | single | — |
| SC-8 | Motivating-evidence count and "independently" (EIC W8; R1 W12; R2 W5; R3 W2) | raised (Minor, 5) | corroborated (Minor, 3) | corroborated (Minor, 4) | corroborated (Major, 4) | 4/0 | CONSENSUS-4 | Minor Issue; M4 |
| SC-9 | Plan text stale vs Part B (EIC W8) | raised (Minor, 5) | — | — | — | 1/0 | single | — |
| SC-10 | Anonymisation plan missing (EIC W9) | raised (Minor, 4) | — | — | — | 1/0 | single | — |
| SC-11 | Cross-family effect confounded with staging/grounding; S4 bounded by S1 (R1 W1; R3 W2) | — | raised (Critical, 4) | — | corroborated (Major, 4) | 2/0 | corroborated | M3 |
| SC-12 | Too few defects, no repeats (R1 W2) | — | raised (Major, 4) | — | — | 1/0 | single | M5 |
| SC-13 | Brief names seeded classes (R1 W3; R3 W1) | — | raised (Major, 4) | — | corroborated (Major, 4) | 2/0 | corroborated | M2 |
| SC-14 | No procedure to adjudicate findings on unchanged code (R1 W4) | — | raised (Major, 4) | — | — | 1/0 | single | — |
| SC-15 | `HD []` mutant contradicts baseline labelling; fidelity undefined (R1 W5; R2 W1) | — | raised (Major, 3) | corroborated (Major, 5) | — | 2/0 | corroborated | M1; Unexamined Premise |
| SC-16 | No provable-but-silently-wrong mutants (R1 W6) | — | raised (Major, 4) | — | — | 1/0 | single | — |
| SC-17 | No deterministic-scan baseline (R1 W7) | — | raised (Major, 4) | — | — | 1/0 | single | — |
| SC-18 | No named scorer for reason-correctness and matching (R1 W8) | — | raised (Major, 4) | — | — | 1/0 | single | — |
| SC-19 | Cost matching and output reuse unspecified (R1 W9) | — | raised (Minor, 4) | — | — | 1/0 | single | — |
| SC-20 | No pre-specified analysis or decision rule (R1 W10) | — | raised (Minor, 4) | — | — | 1/0 | single | — |
| SC-21 | "Lessons change nothing" rests on one run (R1 W11) | — | raised (Minor, 4) | — | — | 1/0 | single | M6 |
| SC-22 | No positioning vs kernel-term export / importers (R2 W2) | — | — | raised (Major, 4) | — | 1/0 | single | — |
| SC-23 | Oracle cannot settle most meaning questions (R2 W3; R3 W1) | — | — | raised (Major, 4) | corroborated (Major, 4) | 2/0 | corroborated | M7 (related) |
| SC-24 | Proving is one-sided evidence, not fidelity (R2 W4; R1 W6; R3 W1) | — | corroborated (Major, 4) | raised (Major, 4) | disputed-weight (Major, 4) | 2/1 | SPLIT, arbitrated | M8 |
| SC-25 | No criterion for stuck proof vs false statement (R2 W4) | — | — | raised (Major, 4) | — | 1/0 | single | — |
| SC-26 | "Pattern completion" error stated too broadly (R2 W5) | — | — | raised (Minor, 4) | — | 1/0 | single | — |
| SC-27 | Extra `Nonempty` instance seeded as defect (R2 W6) | — | — | raised (Minor, 4) | — | 1/0 | single | — |
| SC-28 | Missing autoformalisation-faithfulness and port literature (R2 W7) | — | — | raised (Minor, 3) | — | 1/0 | single | — |
| SC-29 | Cross-family independence premise untested (R3 W2) | — | — | — | raised (Major, 4) | 1/0 | single | M4; Ignored Alternative 3 |
| SC-30 | Human effort not accounted (R3 W3) | — | — | — | raised (Major, 4) | 1/0 | single | — |
| SC-31 | Contamination acknowledged, not mitigated (R3 W4) | — | — | — | raised (Major, 3) | 1/0 | single | Ignored Alternative 2 |
| SC-32 | Reproducibility under drifting closed models (R3 W5) | — | — | — | raised (Minor, 4) | 1/0 | single | — |
| SC-33 | Key terms undefined; adjacent-field positioning missing (R3 W6) | — | — | — | raised (Minor, 4) | 1/0 | single | Unexamined Premise |
| SC-34 | CakeML maintenance plan missing (R3 W7) | — | — | — | raised (Minor, 3) | 1/0 | single | — |

### Required Revisions (Must Fix)

| Transport ref | Revision Item | Sub-Claim(s) | Severity | Evidence Anchor | Confidence | Source | Obligation class | Cost scope | Bounded consequence |
|---|---|---|---|---|---|---|---|---|---|
| R1 | Choose one framing (audit/certification), rewrite Goal and RQ list around it; move the workflow-holds question to a secondary RQ | SC-1 | Major | text: "the main contribution, a certification method: cross-family audit" | 4 | EIC | must_fix | section: Goal and framing; Research questions | decision_blocking:D6 |
| R2 | State the ITP-specific insight beyond a port (catalogue of HOL4-to-Lean semantic gaps that defeat auditors; measured effect of oracle grounding) | SC-2 | Major | text: "the call says porting a proof to another prover yields no new insight by default" | 4 | EIC | must_fix | section: Part A contributions | decision_blocking:D6 |
| R3 | Present contribution (1) as conditional until the cross-family audit and Lean proofs confirm it; report it from those results | SC-3 | Major | text: "the 278 statements have not been proved in Lean yet" | EIC 3; R1 4 | EIC, R1 | must_fix | section: Part A contribution (1) | claim_unsupported:contribution-1 |
| R4 | Replace "certification" with "audit"/"validation evidence", or state an explicit assurance argument with evidence per leg and open residual risks | SC-4 | EIC Minor; R3 Major (arbitrated: must_fix) | text: "The open problem is certifying that a translation can be trusted." | 4 | EIC, R3 | must_fix | section: Part A; Goal | reviewer_objection_risk:main-contribution-label |
| R5 | Fix the shared-error count (two auditors plus one comparison agent) and drop "independently"; describe them as same-family agents in related sessions | SC-8 | EIC Minor; R1 Minor; R2 Minor; R3 Major | text: "three Claude auditors independently made the same wrong claim" | EIC 5; R1 3; R2 4; R3 4 | EIC, R1, R2, R3 | must_fix | sentence: Part A motivating evidence; §2 | claim_unsupported:motivating-evidence |
| R6 | Add a same-family two-stage control (S6) and a single-model-plus-grounding control (S7); state whether S4 reuses S1's output; frame the hypothesis as precision vs recall | SC-11 | R1 Critical; R3 Major | text: §Audit experiment, Setups "Astra followed by Neon review: the workflow as designed." | 4 | R1, R3 | must_fix | re_analysis: §Audit experiment Setups | decision_blocking:D3 |
| R7 | Run each setup at least three times per copy (or add copies); report pooled rates with exact binomial or bootstrap intervals; per-type results descriptive only | SC-12 | Major | text: "6 copies, each with 6 seeded defects and 3 decoys placed at random" | 4 | R1 | must_fix | new_data: §Audit experiment Copies | decision_blocking:D1 |
| R8 | Hold out mutant classes not named in any brief (or cross brief condition with setup) and report them separately | SC-13 | Major | text: "The auditors get the same brief as the baseline audits, with no hint that defects were seeded." | 4 | R1, R3 | must_fix | re_analysis: §Audit experiment Mutants | measure_invalid:detection-rate |
| R9 | Ground every finding on unchanged code (HOL4 query, Lean counterexample or proof) before scoring; add an "unresolved" category | SC-14 | Major | text: Part B, Note "the 278 statements have not been proved in Lean yet" | 4 | R1 | must_fix | re_analysis: §Audit experiment Measures | measure_invalid:false-alarm-rate |
| R10 | Define meaning fidelity once (statement meaning, conservativity, or both) and score baselines and mutants against it; drop or re-label the `HD []` class and verify labels with HOL4 before the freeze | SC-15 | Major | text: §8 Mutants "unspecified values fixed to a default" | R1 3; R2 5 | R1, R2 | must_fix | section: §8 Mutants; Part B verdicts | measure_invalid:ground-truth |
| R11 | Pre-specify a matching rule and a reason-correctness rubric; two scorers blind to setup, one human; report agreement | SC-18 | Major | text: "how many reported reasons are wrong even when the verdict is right" | 4 | R1 | must_fix | section: §Audit experiment Measures | measure_invalid:wrong-reason-count |
| R12 | Position the work against typed HOL4 kernel-term export and symbolic importers (OpenTheory, HOL importers into Isabelle, Dedukti); argue the mapping-step gap, ideally with a kernel-term-export baseline for statement shapes | SC-22 | Major | absence: §2 and Part A — expected positioning against kernel-term export and symbolic importers | 4 | R2 | must_fix | section: §2 What is known already | decision_blocking:D2 |
| R13 | State which finding classes grounding can decide; report grounding as partial evidence; validate query relevance | SC-23 | Major | text: §1 item 2 "HOL4 runs and Lean counterexamples check claims about meaning, so the study does not rely on a model's word." | 4 | R2, R3 | must_fix | section: §Workflow grounding; Threats | claim_unsupported:grounding-as-ground-truth |
| R14 | Present proving as one-sided evidence (exposes too-strong translations only); say which §8 mutant classes it can and cannot detect | SC-24 | Major | text: Part A contribution 3 "proving the 278 statements in Lean (kernel-checked, frozen statements, standard axioms only)" | R2 4; R1 4; R3 4 | R2, R1 (R3 disputed weight; arbitrated) | must_fix | section: Part A contribution (3) | claim_unsupported:contribution-3 |
| R15 | Resolve the circular premise: reorder so checkers are measured first and the best grounded setup is applied to the baselines before any fidelity claim | — | Critical (DA) | text: Section B Note "is judged by Claude auditors/comparison agents plus targeted HOL4 queries" and Section A "Translation now works" | 4 | DA C1 (corroborated by EIC W5, R1 W4) | must_fix | section: Part A; paper structure | decision_blocking:D3 |

- **Acceptance criteria**: each R-item is resolved when the revised plan contains the stated change and the response letter maps it to the item; R6, R7, R8, R9, R10 and R11 must appear in the frozen design before any model sees the mutant copies.

### Suggested Revisions (Should Fix / Consider)

| Transport ref | Revision Item | Sub-Claim(s) | Severity | Evidence Anchor | Confidence | Source | Obligation class | Cost scope | Bounded consequence |
|---|---|---|---|---|---|---|---|---|---|
| S1 | Add a short novelty statement relative to the FormaliSE 2027 paper, tied to RQs | SC-5 | Major | text: "which updates study 1 (the author's FormaliSE 2027 experience report, where a human expert was needed)" | 4 | EIC | should_fix | section: Introduction | reviewer_objection_risk:novelty |
| S2 | Add a one-page outline with page counts, key tables/figures, and results deferred to the artifact | SC-6 | Major | absence: whole plan and Part A — expected a page budget and figure/table plan | 4 | EIC | should_fix | section: new outline | clarity:paper-structure |
| S3 | Mark which arms are core to the chosen claim and which go to the artifact or follow-up | SC-7 | Minor | table: Section "Budget estimate", item list | 4 | EIC | consider | section: Budget estimate | clarity:scope |
| S4 | Update to v3.3 with Part B results folded in; rewrite ablation section as completed work | SC-9 | Minor | text: "Two Claude auditors gave the same wrong reason for a correct verdict." | 5 | EIC | should_fix | section: What is known; Ablations | clarity:plan-currency |
| S5 | Add an anonymisation checklist (repository names, commit metadata, transcripts, self-citation) | SC-10 | Minor | text: "All plans, briefs, scripts, records and results live in the organization repository" | 4 | EIC | should_fix | section: Artifact plan | reviewer_objection_risk:double-blind |
| S6 | Balance provable-silent and unprovable mutants; tag each by whether proving exposes it; confirm expected effects with HOL4/Lean | SC-16 | Major | text: "a dropped hypothesis, a swapped quantifier, a strengthened conclusion" | 4 | R1 | should_fix | re_analysis: §8 Mutants | measure_invalid:distinctive-value |
| S7 | Add S0 (structural scans only) and report each LLM setup's increment over S0 | SC-17 | Major | text: §Workflow item 4 "extra or missing typeclass hypotheses" | 4 | R1 | should_fix | re_analysis: Setups | claim_unsupported:LLM-increment |
| S8 | Report results per dollar; add a cost-matched single-family arm | SC-19 | Minor | absence: §Audit experiment Setups and Budget — expected output-reuse statement and cost-matched comparison | 4 | R1 | should_fix | re_analysis: Setups; Budget | reviewer_objection_risk:cost-confound |
| S9 | Fix one primary contrast (e.g. S5 vs S3 on pooled defects) with paired comparison and intervals; label the rest exploratory | SC-20 | Minor | absence: §Audit experiment and §Research questions — expected primary metric, interval method, decision rule | 4 | R1 | should_fix | section: Analysis plan | measure_invalid:RQ2-inference |
| S10 | State the Candle no-lessons result as no detected difference at ceiling; draw the lessons conclusion from the type-soundness closure with repeats | SC-21 | Minor | text: Part A "removing study 1's lessons from the briefs changes nothing" | 4 | R1 | should_fix | sentence: Part A | claim_unsupported:lessons-ablation |
| S11 | Define a criterion for stuck proof vs false statement (e.g. Lean counterexample or proof of the negation) | SC-25 | Major | text: Part A contribution 3 "proving the 278 statements in Lean" | 4 | R2 | should_fix | section: Proving; RQ1 | measure_invalid:RQ1 |
| S12 | State the precise pattern-completion mechanism (`Define` vs `Prim_rec`/recursion theorems) | SC-26 | Minor | text: Part A "three Claude auditors independently made the same wrong claim about HOL4 semantics" | 4 | R2 | consider | sentence: Part A | clarity:motivating-example |
| S13 | Say which binders count for the `Nonempty` mutant, or reclassify it as a decoy | SC-27 | Minor | text: §8 Mutants "type signatures: an unused binder at a fixed type, or an extra" | 4 | R2 | should_fix | sentence: §8 Mutants | measure_invalid:ground-truth |
| S14 | Cite autoformalisation-faithfulness work (miniF2F, ProofNet, FormalAlign), Mathport, and Candle | SC-28 | Minor | absence: §2 — expected prior work on statement faithfulness and large ports | 3 | R2 | should_fix | section: Related work | reviewer_objection_risk:related-work |
| S15 | Report pairwise joint-miss rates vs the independence prediction; state what result refutes the diversity premise | SC-29 | Major | text: "three Claude auditors independently made the same wrong claim about HOL4 semantics" | 4 | R3 | should_fix | re_analysis: Measures | claim_unsupported:family-diversity |
| S16 | Add a human-effort log (task, minutes, expertise needed) reported next to model costs | SC-30 | Major | absence: §Costs and token usage and §Budget estimate — expected author hours | 4 | R3 | should_fix | new_data: ledger | claim_unsupported:no-human-expert |
| S17 | Add a contamination probe (renaming/permutation, or post-cutoff theories), or scope contribution (1) to public developments | SC-31 | Major | text: §Threats "CakeML and Candle are public, so all three model families may have seen them." | 3 | R3 | should_fix | new_data: probe sample | claim_unsupported:generalisation |
| S18 | Pin CLI versions; separate artifact-recheckable claims from closed-model claims | SC-32 | Minor | text: §Threats "Model versions can change during the study. We pin identifiers and record dates." | 4 | R3 | consider | section: Artifact; Threats | clarity:reproducibility |
| S19 | Define outcome terms ("meaning defect", "form-only", "by-design", "grounding"); add adjacent-field related work (N-version, LLM-as-judge, mutant validity) | SC-33 | Minor | absence: §1 and §2 — expected definitions and positioning | 4 | R3 | should_fix | section: Goal; Related work | clarity:terminology |
| S20 | Add a maintenance and synchronisation plan for the Lean copy and name intended users | SC-34 | Minor | absence: §Phase 2 — expected maintenance plan | 3 | R3 | consider | section: Phase 2 | clarity:practical-impact |
| S21 | Extend grounding to rejected findings (or a sample), so reviewer false negatives become visible | — | Major (DA) | text: Section C Grounding "For every accepted finding that makes a claim about meaning, a script runs the cited check" | 4 | DA M7 | should_fix | section: §Workflow grounding | claim_unsupported:every-decision-grounded |

### Source-Traceability Checklist

Source order is preserved; it is not a work order. Author triage is collected later as a separate sidecar.

- [ ] R1 — obligation `must_fix`: choose one framing and rewrite Goal and RQs
- [ ] R2 — obligation `must_fix`: answer the ITP porting bar explicitly
- [ ] R3 — obligation `must_fix`: make contribution (1) conditional on audit and proofs
- [ ] R4 — obligation `must_fix`: replace or bound "certification"
- [ ] R5 — obligation `must_fix`: fix shared-error count; drop "independently"
- [ ] R6 — obligation `must_fix`: add same-family two-stage and grounding-only controls
- [ ] R7 — obligation `must_fix`: repeats or more mutants; pooled rates with intervals
- [ ] R8 — obligation `must_fix`: held-out mutant classes not named in briefs
- [ ] R9 — obligation `must_fix`: adjudicate findings on unchanged code before scoring
- [ ] R10 — obligation `must_fix`: one fidelity definition applied to baselines and mutants
- [ ] R11 — obligation `must_fix`: matching rule, rubric, blind scorers, agreement
- [ ] R12 — obligation `must_fix`: position against kernel-term export and importers
- [ ] R13 — obligation `must_fix`: bound what grounding can decide
- [ ] R14 — obligation `must_fix`: proving as one-sided evidence
- [ ] R15 — obligation `must_fix`: resolve the DA C1 circular premise
- [ ] S1–S21 — obligations `should_fix` / `consider` as tabled above

### Response Letter Template
Respond to every R and S item using `templates/revision_response_template.md`, stating for each item what changed and where, or why it was declined. A declined item stays visible as unresolved.

---

## Part 3: Reviewer Report Summary (Appendix)

### Journal-Fit Review Report Summary (EIC)
- Scores: D5 warn, D6 warn | Confidence: 3–5 per finding
- Key Point: a real ITP contribution (an oracle-grounded audit of HOL4-to-Lean translation) is present, but the plan must commit to one framing, answer the porting bar, and plan the 16-page paper.

### Reviewer 1 (Methodology) Summary
- Scores: D1 block (repairable), D3 block (repairable) | Confidence: 3–4 per finding
- Key Point: the audit experiment cannot yet attribute gains to cross-family checking and is too small, unrepeated and unscored by protocol to support per-type or between-setup claims.

### Reviewer 2 (Domain) Summary
- Scores: D2 block (repairable) | Confidence: 4 overall
- Key Point: system descriptions are mostly accurate, but the plan omits kernel-term export and importer work, labels a valid modelling choice as a defect, and overstates what the oracle and proofs certify.

### Reviewer 3 (Perspective) Summary
- Scores: D4 warn | Confidence: 3–4 per finding
- Key Point: "certification", "cross-family independence" and "no human expert" read as stronger claims to adjacent fields than the planned measurements support.

### Devil's Advocate Summary
- Scores: D3 block (repairable) | Recommendation: N/A — findings only
- Key Challenge: C1 (validated) — the claim that translation now works is asserted before the instrument that could test it is built; eight Major issues (M1–M8) are mapped into the roadmap above.

## Attachment: Suggested-Reference Check (advisory, #1001)

Suggested-reference check (script output, not a reviewer finding; #1001)
Seats read: R2, R3 (complete).

| Seat | # | Reference | Result |
|---|---|---|---|
| R2 | 1 | Hurd, J. (2011) "The OpenTheory Standard Theory Library" | Found in an index |
| R2 | 2 | Obua, S. et al. (2006) "Importing HOL into Isabelle/HOL" | Found in an index |
| R2 | 3 | Kaliszyk, C. et al. (2013) "Scalable LCF-style proof translation" | Found in an index |
| R2 | 4 | Assaf, A. et al. (2015) "Translating HOL to Dedukti" | Found in an index |
| R2 | 5 | Zheng, K. et al. (2022) "MiniF2F: a cross-system benchmark for formal Olympiad-level mathematics" arXiv:2109.00110 | Found in an index |
| R2 | 6 | Azerbayev, Z. (2023) "ProofNet: Autoformalizing and Formally Proving Undergraduate-Level Mathematics" arXiv:2302.12433 | Found in an index |
| R2 | 7 | (2024) "FormalAlign: Automated Alignment Evaluation for Autoformalization" | Found in an index |
| R2 | 8 | Abrahamsson, O. (2022) "Candle: A Verified Implementation of HOL Light" | Found in an index |
| R3 | 1 | Knight, J. C. et al. (1986) "An Experimental Evaluation of the Assumption of Independence in Multiversion Programming" | Found in an index |
| R3 | 2 | Just, R. et al. (2014) "Are Mutants a Valid Substitute for Real Faults in Software Testing?" | Found in an index |
| R3 | 3 | Jia, Y. et al. (2011) "An Analysis and Survey of the Development of Mutation Testing" | Found in an index |
| R3 | 4 | Zheng, L. et al. (2023) "Judging LLM-as-a-Judge with MT-Bench and Chatbot Arena" arXiv:2306.05685 | Found in an index |

"Found" means an index holds a record with this DOI or arXiv ID and title, or with this title. It does not show that the work supports the recommendation, or that the authors and year are right.

## Attachment: Reviewer Claim Check (advisory, #1002)

The judge answered 44 of 44 findings from 5 reviewers: it marked 0 as contradicted, and 0 cannot be checked from the manuscript alone.

The author decides what to do with each row. This check does not change the decision, the consensus counts, or the Revision Roadmap. The judge is the session model; as this judge, the #1002 contrast test passed Claude Opus 5.5 and Claude Fable 5.1 (gpt-6-astra and Gemini 4 Argon passed it in part one, through other transports); other models are untested.

## Attachment: Acronym Check (advisory, #849)

### Acronym check (advisory; no reply needed)
Coverage: body (partial)
Not in this input: English abstract, Chinese abstract.
Not checked:
- Body, line 11: CLASH (the initials before its parentheses do not spell it)
- Body, line 61: AoE (the initials before its parentheses do not spell it)
- Body, line 106: OpenAI (the initials before its parentheses do not spell it)

| Scope | Line | Rule | Acronym | Uses |
|---|---|---|---|---|
| Body | 5 | Not defined | AI | 6 |
| Body | 5 | Not defined | ARB | 7 |
| Body | 5 | Not defined | CARD | 3 |
| Body | 5 | Not defined | CakeML | 12 |
| Body | 5 | Not defined | GPT | 5 |
| Body | 5 | Not defined | HOL4 | 51 |
| Body | 5 | Not defined | ITP | 7 |
| Body | 5 | Not defined | LIPIc | 2 |
| Body | 5 | Not defined | RESULT | 5 |
| Body | 11 | Not defined | API | 5 |
| Body | 11 | Not defined | HD | 3 |
| Body | 11 | Not defined | LEX | 1 |
| Body | 13 | Not defined | ML | 4 |
| Body | 17 | Not defined | CHR | 2 |
| Body | 17 | Not defined | FEMPTY | 1 |
| Body | 17 | Not defined | FMAP | 1 |
| Body | 17 | Not defined | FUN | 1 |
| Body | 17 | Not defined | RACONV | 1 |
| Body | 61 | Not defined | CICM | 2 |
| Body | 95 | Not defined | CLI | 4 |
| Body | 113 | Not defined | PC | 4 |
| Body | 174 | Not defined | CONV | 1 |
| Body | 174 | Not defined | EVAL | 1 |
| Body | 174 | Not defined | SIMP | 1 |
| Body | 204 | Not defined | HOL | 1 |
| Body | 206 | Not defined | BEq | 1 |
| Body | 247 | Not defined | RQ | 1 |
| Body | 312 | Not defined | PEG | 1 |
| Body | 325 | Not defined | LaTeX | 1 |
