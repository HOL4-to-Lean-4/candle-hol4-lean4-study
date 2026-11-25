## Contract Paraphrase

D1 (methodology_rigor, mandatory, owned by methodology): Because the submission is a plan rather than a finished study, I read this as asking whether the proposed design, if carried out as written, would produce evidence that survives empirical peer review. That means clearly operationalised outcome measures, a justified sampling frame and sample size for the units being studied, controls and baselines that isolate the effect being claimed, a pre-specified analysis and reporting plan, explicit handling of data provenance and contamination, and enough planned artifact detail (versions, prompts, seeds, budgets, logs) for an independent group to rerun it.

D2 (domain_accuracy, mandatory, owned by domain): From a methodology viewpoint this concerns whether the plan's factual premises about the field and about prior work are correct, because a design built on a misdescribed baseline or a mischaracterised tool measures the wrong thing. I do not score it, but I note where an inaccurate premise would undermine a measurement.

D3 (argumentative_coherence, mandatory, owned by the devil's advocate, methodology eligible): I read this as asking whether the claims the planned paper intends to make are actually licensed by the planned evidence. For methodology, the key test is the alignment between each stated research question or hypothesis, the measure chosen for it, and the conclusion the plan says it will draw, with no step that overreaches from what the design can show (for example causal attribution without a controlling comparison, or generalisation beyond the sampled population).

D4 (cross_disciplinary_relevance, high, owned by perspective): This asks whether definitions and implications are understandable to readers in adjacent fields and whether claims that cross field boundaries are supported. Methodologically, consistent definitions of the measured constructs across communities matter, but I do not score this dimension.

D5 (writing_and_structure, normal, owned by the editor): This covers how clearly the plan is organised and whether the eventual paper would fit the venue's format and length conventions, including anonymity requirements. I do not score it, though an unclear description of procedure would also surface as a reproducibility concern under D1.

D6 (venue_fit_and_contribution, mandatory, owned by the editor): This asks whether the planned paper suits the target venue and would make an original, significant contribution for its readers. I do not score it; methodology bears on it only insofar as a weak design would shrink what can credibly be claimed as a contribution.

## Scoring Plan

### D1: methodology_rigor
dimension_id: D1
what_to_look_for: Operational definitions for every planned outcome measure; a stated sampling frame, unit of analysis and justified sample sizes; baselines and ablations that isolate each component of the proposed workflow; validation of any automated or LLM-based judging against human ground truth with agreement statistics; controls for training-data contamination and for nondeterminism (repeated runs, seeds, fixed model versions); a pre-specified analysis plan with effect sizes and uncertainty intervals; cost and budget accounting; and a concrete artifact and logging plan sufficient for independent reproduction.
what_triggers_block: A primary research question has no operational measure or no comparison condition, or the central outcome depends on an automated or LLM judge with no planned validation against human or mechanical ground truth, or the sample size for a primary measure is unstated or plainly too small to distinguish the claimed effect from run-to-run variance.
what_triggers_warn: The design is sound in outline but secondary measures lack precise definitions, contamination or nondeterminism controls are mentioned without a concrete procedure, the analysis plan omits uncertainty reporting or multiple-comparison handling, or reproducibility details (versions, prompts, budgets, logs) are incomplete but recoverable in revision.
what_triggers_fatal: The planned design cannot in principle answer its own primary research question, for example because the outcome is defined circularly by the system under test, the only evaluator shares the generator's failure modes with no independent check, or the success criterion is unfalsifiable as specified.

### D3: argumentative_coherence
dimension_id: D3
what_to_look_for: A traceable chain from each research question or hypothesis to a planned measure and to the specific conclusion the plan says it will draw; claimed attributions (for example credit given to a particular component or model family) backed by a planned comparison that isolates that component; scope statements that keep generalisations within the sampled population; and any reframing of goals kept consistent with the measures actually planned.
what_triggers_block: A headline claim the plan intends to make would require evidence the design does not collect, such as attributing an outcome to one component without an ablation, or generalising from a narrow sample to a broad population without justification.
what_triggers_warn: Some secondary claims are stated more strongly than the planned evidence supports, research questions and measures are loosely aligned or renumbered inconsistently, or a reframing leaves earlier goals and new goals in tension without explaining which the evidence will address.
what_triggers_fatal: The central thesis of the planned paper is contradicted by the plan's own stated design or success criteria, so that no outcome of the planned study could support the claim as framed.

criteria_binding_unavailable

[CONTRACT-ACKNOWLEDGED]
