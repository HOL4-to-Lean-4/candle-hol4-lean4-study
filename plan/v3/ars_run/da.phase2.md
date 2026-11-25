contract_role: da

## Dimension Scores

### D1: methodology_rigor
score: not_assessed

### D2: domain_accuracy
score: not_assessed

### D3: argumentative_coherence
score: block
trigger: "the argument relies on a fallacy or an untested premise that the conclusion depends on"
block_class: repairable

### D4: cross_disciplinary_relevance
score: not_assessed

### D5: writing_and_structure
score: not_assessed

### D6: venue_fit_and_contribution
score: not_assessed

## Review Body

### Calibration Status
`NOT_CALIBRATED`

### Criterion-Bound Judgements
- D3 argumentative_coherence (contract dimension D3, Phase 1 scoring plan): DOES_NOT_MEET. The headline premise of the reframing rests on a measurement that the paper's own main contribution says is unreliable; see C1. Scope limit: judged on a study plan plus measured baselines, not a finished paper. Decision bearing: yes, it is the premise the whole reframing depends on.
- Claim-evidence match for contribution (2), the certification method: PARTLY_MEETS. The design can measure recall on seeded known classes, but cannot isolate "cross-family" from "two stages" and leaks the defect classes into the auditor brief; see M2 and M3. Decision bearing: yes for the strength of the main claim, not for its existence.
- Claim-evidence match for contribution (3), end-to-end proofs: PARTLY_MEETS. Proofs can expose false statements but cannot certify that a provable statement means what HOL4 means; see M8. Decision bearing: no on its own.

### What the plan does well
The plan is unusually honest about its own weak points. It records the context leak, the training-data risk, the fact that the 278 statements are unproved, and the case where HOL4 refuted the auditors. Grounding findings in HOL4 runs and Lean checks, rather than in a model's word, is the right instinct, and the seeded-defect experiment with decoys is a real measurement rather than an anecdote.

### Strongest Counter-Argument
The reframing says translation is solved and trust is the open problem. A sceptic would say the evidence supports the opposite reading just as well: the translations may contain defects that nobody has detected, because every "no meaning defects" verdict in Section B comes from Claude auditors and Claude comparison agents, plus a handful of targeted HOL4 queries. The same section reports that three Claude checkers independently made the same wrong claim about HOL4 semantics. If single-family Claude checking shares errors, which is exactly the motivation for contribution (2), then a zero-defect verdict from single-family Claude checking is the least trustworthy number in the paper, and the claim "translation now works" is unsupported. Worse, the evidence is consistent with a simpler story: the checkers share the translator's blind spots, so agreement between Fable, Opus and Sonnet translations and their Claude judges is agreement within one family, not fidelity. The "no lessons" ablation shows only that an Opus agent cannot tell two Opus outputs apart. On top of this, the plan itself treats "unspecified values fixed to a default" as a seeded defect, yet Opus and Sonnet do exactly that and are still counted as defect-free. Under this reading, contribution (1) is not a finding at all; it is the untested premise that contribution (2) is needed to test. The coherent paper is therefore the reverse order: first measure how well each checking setup detects defects, then apply the best measured setup to the baselines, and only then say whether translation works. As framed now, the paper asserts its conclusion before it builds the instrument that could support it.

### Ignored Alternative Explanations
1. Shared blind spots. Zero defects across three Claude translators judged by Claude checkers is what one would expect if the checkers share the translators' errors. The plan has no non-Claude, grounded re-check of the baselines before asserting claim (1).
2. Memorisation. CakeML and Candle are public, so clean translations may reflect training-data recall of HOL4 idioms, which would not transfer to a non-public development. The plan names the threat but the reframing generalises anyway.
3. Pipeline depth, not family diversity. Any gain of S4 or S5 over S3 can come from having two passes, or from grounding, rather than from using different families.

### Missing Stakeholder Perspectives
- ITP proof engineers who would use a ported library: they care whether provable-but-stronger Lean definitions (for example a fixed `HD []`) break downstream reuse, which "no target affected" does not address.
- HOL4 maintainers: whether "a model of the HOL4 spec" is an acceptable notion of fidelity is a semantic judgement the plan leaves to models.

### Unexamined Premise
The plan never defines "meaning defect". Section B counts a Lean definition that fixes an unspecified HOL4 value as faithful when the target statements are unaffected, while Section C seeds the same change as a defect. Every count in the paper depends on which definition is used.

### Minor Issues
- Section A says three Claude auditors made the shared wrong claim; Section C says two. Pick one count and say which runs it covers. Confidence 4, direct reading.
- RQ1 still asks whether the workflow holds once an AI reviewer replaces the human expert, which is the old framing; the RQs should be rewritten to match the reframing if it is adopted. Confidence 4, direct reading.
- Decoys come from only three rewrite kinds, so the false-alarm rate measures those three, not false alarms in general. Confidence 3, adjacent: evaluation design.

### Issue List

#### CRITICAL
| # | Dimension | Issue Description | Evidence Anchor | Confidence | Field-Norm Boundary | Evidence-Crossing Rationale |
|---|-----------|-------------------|-----------------|------------|---------------------|-----------------------------|
| C1 | D3 | Circular premise. Contribution (1), translation now works, is established only by single-family Claude checking, which contribution (2) is motivated by showing to be unreliable. The headline finding is therefore untested by the plan's own standard, and the reframing's thesis (translation solved, trust open) asserts the conclusion the certification method is meant to test. Repairable by reordering: measure the checkers first, then apply the best grounded setup to the baselines before claiming fidelity. | text: Section B Note "is judged by Claude auditors/comparison agents plus targeted HOL4 queries" and Section A "Translation now works" | 4 — core: argument analysis; adjacent: ITP proof engineering | n/a, not norm-based | n/a |

#### MAJOR
| # | Dimension | Issue Description | Evidence Anchor | Confidence | Field-Norm Boundary | Evidence-Crossing Rationale |
|---|-----------|-------------------|-----------------|------------|---------------------|-----------------------------|
| M1 | D3 | Internal contradiction on what counts as a defect. The mutant list seeds fixing an unspecified value to a default as a defect, yet the Opus and Sonnet baselines do exactly this and are reported as having no meaning defects. Either the baselines have defects or the mutant class is a decoy; the plan must define meaning fidelity once and apply it to both. | text: Section C Mutants "unspecified values fixed to a default" and Section B item 2 "is provable in Opus only; no target affected" | 4 — direct reading of both sections | n/a, not norm-based | n/a |
| M2 | D3 | Seeded classes leak into the auditor brief. Mutants are drawn from the classes the audit briefs name, and the auditors get that same brief, so detection rates measure recall of announced classes. This cannot support a general certification claim, which is the main contribution. The threats section concedes unknown classes are not measured, but the reframing still calls the method certification. | text: Section C Mutants "from the classes the audit briefs name" and Copies "The auditors get the same brief as the baseline audits, with no hint that defects were seeded." | 4 — core: evaluation design | n/a, not norm-based | n/a |
| M3 | D3 | The design cannot attribute any gain to cross-family checking. The only single-family setup is one Opus pass, while the cross-family setups have two model passes and optionally grounding. A same-family two-stage control is missing, so the claim that family diversity is what helps stays untested. | absence: Section C audit experiment Setups S1 to S5 — expected a same-family two-stage setup such as a Claude validator followed by a separate Claude reviewer, with and without grounding; checked Setups list, Measures, RQ2 and Section A contribution (2) | 4 — core: experimental controls | n/a, not norm-based | n/a |
| M4 | D3 | Motivating evidence does not match the claim it motivates. The shared Claude error is a wrong reason for a correct verdict, not a missed defect or a false alarm, so it shows correlated reasoning, not that single-family audit misses defects. The paper should not present it as evidence that cross-family audit detects more. | text: Section C What is known "Two Claude auditors gave the same wrong reason for a correct verdict." | 4 — direct reading | n/a, not norm-based | n/a |
| M5 | D3 | Too few units for the planned per-type claims. 36 defects over roughly a dozen defect kinds gives about three per kind, and 6 copies per setup, so per-type detection rates and between-setup differences will not separate from run-to-run variation, which the plan itself expects to measure. Conclusions about one setup beating another need either more mutants or a pooled primary measure fixed in advance. | text: Section C Copies "That gives 36 defects and 18 decoys in total." and Measures "the detection rate per defect type" | 3 — adjacent: evaluation statistics | n/a, not norm-based | n/a |
| M6 | D3 | Overgeneralisation from single runs on one closure. The claim that lessons change nothing rests on one no-lessons run on Candle, judged by an Opus agent against an Opus baseline. The plan's own known-defect target is meant to test this beyond Candle, but the reframing states the result before that test. | text: Section A "removing study 1's lessons from the briefs changes nothing" and Section B item 3 "Opus-agent comparison with Opus baseline" | 4 — core: argument analysis | n/a, not norm-based | n/a |
| M7 | D3 | Grounding runs only on accepted findings, so a true defect that Neon wrongly rejects is never checked against HOL4 or Lean. In the main workflow this leaves the reviewer's false negatives invisible, which weakens the claim that every decision is grounded rather than taken on a model's word. | text: Section C Grounding "For every accepted finding that makes a claim about meaning, a script runs the cited check" | 4 — direct reading of workflow | n/a, not norm-based | n/a |
| M8 | D3 | Contribution (3) cannot carry the weight given to it. Proving frozen statements shows they are provable, not that they mean what HOL4 means; a faithful-looking but stronger definition can make more statements provable. It is also the kind of porting result the venue call discounts, so it cannot shore up either the trust claim or the significance claim. | text: Section A "the call says porting a proof to another prover yields no new insight by default" | 3 — adjacent: ITP venue norms | n/a, not norm-based | n/a |
