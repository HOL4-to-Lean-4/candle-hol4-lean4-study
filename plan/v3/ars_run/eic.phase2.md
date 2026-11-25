contract_role: eic
## Dimension Scores

### D1: methodology_rigor
score: not_assessed

### D2: domain_accuracy
score: not_assessed

### D3: argumentative_coherence
score: not_assessed

### D4: cross_disciplinary_relevance
score: not_assessed

### D5: writing_and_structure
score: warn
trigger: "the space budget or figure and table plan is vague"

### D6: venue_fit_and_contribution
score: warn
trigger: "split between competing framings that dilute its significance to ITP readers"

## Review Body

I read the submission as a research design for an ITP 2027 regular paper, as the contract asks. The main point first: there is a real ITP contribution in this material, namely a measured, oracle-grounded audit of HOL4-to-Lean statement translation, but the plan does not yet commit to it. Version 3.2 frames the paper as a test of whether study 1's workflow holds once an AI reviewer replaces the human expert. The proposed reframing in part A instead makes a certification method the main contribution and the translation result a secondary measured finding. These are two different papers with different headline claims, research questions and page budgets. Until one is chosen, the contribution reads as over-broad for 16 LIPIcs pages and its significance to ITP readers is diluted. This is a warn on D6, not a block: the contribution is distinguishable from prior work and the design can deliver it.

On venue fit, the ITP call's position that porting a proof to another prover yields no new insight by default is the bar the paper has to clear explicitly. The proving of the 278 statements in Lean, taken alone, is a port. The insight the plan can offer ITP readers is elsewhere: which HOL4 semantic features (unspecified values through Prim_rec, ARB, Hilbert choice, overload resolution, ML-built statements) defeat model auditors, and how much a HOL4 or Lean oracle changes audit outcomes. The plan should name that as the ITP-relevant result. The word "certification" also needs care at this venue, where it usually means a kernel-checked guarantee rather than an empirical detection rate on seeded mutants.

On writing and structure (D5), the plan is well organised: goal, scope, roles, workflow, oracle, ablations, audit experiment, proving, RQs, ledger, budget, timeline, Phase 2, threats and a decision log are each easy to locate. What it lacks is any outline of the planned 16-page paper, and parts of it are stale relative to the measured results in part B. Anonymisation of a project tied to named public repositories and to the author's own FormaliSE paper needs an explicit plan. These are fixable and justify warn.

### S1: Seeded-defect audit with decoys gives a measurable contribution
The mutant design (defect classes drawn from real study-1 failures, meaning-preserving decoys, fixed seed, five setups, per-type detection and false-alarm rates, wrong-reason counts) turns "the checks work" into something an ITP reader can evaluate and reuse.
**Evidence Anchor**: `text: "6 copies, each with 6 seeded defects and 3 decoys placed at random"`

### S2: HOL4 used as an oracle rather than trusting model claims
Settling meaning questions by running HOL4 is the most ITP-native element of the design and is directly motivated by the observed shared auditor error.
**Evidence Anchor**: `text: "A model can only guess these, while HOL4 answers them directly."`

### S3: Artifact plan matches the venue's supplementary-material expectation
Session logs, findings, verdicts, check outputs and the ledger are planned as an anonymous artifact, which fits the call's request for anonymised supplementary material with the formalisation.
**Evidence Anchor**: `text: "packaged as an anonymous Zenodo artifact"`

### S4: Roles and family separation are stated clearly
The roles table makes the cross-family checking structure and the oracle role unambiguous, which will translate well into a compact methods figure.
**Evidence Anchor**: `table: Section "Roles and models", role/family/model/task table`

### W1: Two competing framings of the main contribution
**Problem**: Version 3.2 frames the paper as testing whether study 1's workflow holds without a human expert (RQ1), while part A makes a certification method the main contribution and demotes the workflow question. The research questions still follow the older framing.
**Evidence Anchor**: `text: "the main contribution, a certification method: cross-family audit"`
**Why it matters**: Reviewers will judge the paper against its headline claim; with two headlines, neither is argued at full strength in 16 pages.
**Suggestion**: Choose the audit/certification framing, rewrite the Goal section and RQ list around it, and move the workflow-holds question to a secondary RQ.
**Severity**: Major
**Confidence**: 4 — core editorial judgement on contribution framing

### W2: ITP porting bar is not explicitly answered
**Problem**: The plan quotes the call's porting caveat but never states what ITP-specific insight the paper delivers beyond a port of Candle's closure.
**Evidence Anchor**: `text: "the call says porting a proof to another prover yields no new insight by default"`
**Why it matters**: A PC member applying the call literally could read Phase 1 proving as a port and discount the paper.
**Suggestion**: State the transferable proof-engineering lesson up front, for example a catalogue of HOL4-to-Lean semantic gaps that defeat auditors and the measured effect of oracle grounding on them.
**Severity**: Major
**Confidence**: 4 — familiarity with ITP call norms

### W3: "Certification" overstates an empirical audit measure
**Problem**: The plan calls the workflow's value certification, but what it measures is detection and false-alarm rates on seeded defects from known classes.
**Evidence Anchor**: `text: "the workflow's value is certification: evidence that a translation can be trusted"`
**Why it matters**: At ITP, certification connotes a formal guarantee; the term invites an objection the data cannot answer.
**Suggestion**: Use "audit" or "validation evidence" and reserve stronger wording for what the Lean kernel and HOL4 actually check.
**Severity**: Minor
**Confidence**: 4 — ITP terminology norms

### W4: Delta from the author's FormaliSE 2027 paper is not stated
**Problem**: Study 1 already used a Claude translator and a cross-family Gemini validator; the plan does not set out, in one place, which claims are new relative to that paper.
**Evidence Anchor**: `text: "which updates study 1 (the author's FormaliSE 2027 experience report, where a human expert was needed)"`
**Why it matters**: Without an explicit delta, reviewers may see overlap with a prior publication, and double-blind handling of the self-citation becomes harder.
**Suggestion**: Add a short novelty statement: seeded-defect measurement, oracle grounding, removal of the human expert, and the second development, each tied to an RQ.
**Severity**: Major
**Confidence**: 4 — core editorial judgement

### W5: Headline translation finding rests on same-family judgement
**Problem**: Contribution (1) says translation now works without meaning defects, but this is judged by Claude auditors and comparison agents, the same family the plan shows making shared wrong claims, and the statements are not yet proved.
**Evidence Anchor**: `text: "the 278 statements have not been proved in Lean yet"`
**Why it matters**: A stated contribution of the paper is currently unsupported by the kind of evidence the paper itself argues is needed.
**Suggestion**: Present the finding as conditional until the cross-family audit and Lean proofs confirm it, and report it from those results.
**Severity**: Major
**Confidence**: 3 — editorial reading; methodology detail is another seat's remit

### W6: No outline or page budget for the 16-page paper
**Problem**: The plan has no section-by-section allocation, figure or table plan, or statement of what goes to appendix or artifact, despite five RQs, five audit setups, two provers and three ablations.
**Evidence Anchor**: `absence: whole study plan and part A — expected a page budget and figure/table plan for the 16-page LIPIcs paper; checked Goal and framing, Research questions, Timeline, Decisions taken, part A`
**Why it matters**: Writing is scheduled for 1 to 15 February only, and the call forbids substantial AI-generated text, so the author must draft by hand in two weeks; an unplanned paper of this breadth is unlikely to fit.
**Suggestion**: Add a one-page paper outline with page counts per section, the two or three key tables and figures, and an explicit list of results deferred to the artifact.
**Severity**: Major
**Confidence**: 4 — experience with LIPIcs page limits

### W7: Scope too broad for one regular paper
**Problem**: The budgeted work includes translation, validation rounds, the audit experiment, two ablations, a conditional Sonnet arm and two proving families, each a potential result section.
**Evidence Anchor**: `table: Section "Budget estimate", item list`
**Why it matters**: Breadth dilutes the single contribution ITP readers need to take away.
**Suggestion**: Mark which arms are core to the chosen claim and which are reported only in the artifact or a follow-up.
**Severity**: Minor
**Confidence**: 4 — editorial scoping judgement

### W8: Plan text is stale relative to measured results
**Problem**: The "What is known" section reports two baselines and two mistaken auditors, while part B reports four runs and a third auditor making the same claim; the no-lessons ablation and Sonnet arm are still described as future or conditional.
**Evidence Anchor**: `text: "Two Claude auditors gave the same wrong reason for a correct verdict."`
**Why it matters**: Readers of the plan cannot tell which design decisions are still open.
**Suggestion**: Update the plan to version 3.3 with part B's results folded in and the ablation section rewritten as completed work.
**Severity**: Minor
**Confidence**: 5 — direct comparison of parts B and C

### W9: Anonymisation plan is not stated
**Problem**: The plan names the organization repositories and depends on the author's own FormaliSE paper, but says nothing about how the submission and artifact will be anonymised beyond the Zenodo upload.
**Evidence Anchor**: `text: "All plans, briefs, scripts, records and results live in the organization repository"`
**Why it matters**: Lightweight double-blind review requires third-person self-citation and scrubbed repository names in paper and artifact.
**Suggestion**: Add an anonymisation checklist covering repository names, commit metadata, transcripts and the self-citation of study 1.
**Severity**: Minor
**Confidence**: 4 — ITP double-blind conventions
