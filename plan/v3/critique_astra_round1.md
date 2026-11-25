# Astra critique, round 1 (raw reply, gpt-6.2-astra)

Model: `gpt-6.2-astra` via `codex exec -m gpt-6.2-astra -s read-only --skip-git-repo-check --json` (codex-cli 0.169.0), 23 Nov 2026. Input: plan v3.2 LaTeX, the 23 Nov reframing, summaries of the four baseline RESULTS.md. Usage (turn.completed / token_count): input 104,417, cached 3,712, output 5,416 (reasoning 3,055). Earlier the same day Codex rejected gpt-6.2-astra; the reply from that earlier attempt with gpt-6-astra is in `critique_astra_round1_gpt-6-astra.md`.

---

# Review of the research design

**Verdict — reject-likely as currently planned.** The plan has a potentially publishable certification study, but its central empirical claims are currently underidentified, underpowered, and partly supported by model judgment rather than formal evidence. The paper also risks being read as a large porting exercise with an AI workflow attached.

## Ranked top issues

### 1. The central result is currently overstated

The reframing says that “translation now works” because Fable, Opus, and Sonnet produced 278 statements with “no meaning defects.” The evidence supports a narrower claim.

The statements still contain `sorry` proofs. Their meaning was assessed through Claude audits, comparison agents, and targeted HOL4 queries. The Lean kernel has not yet certified the 278 statements as the intended Candle theorems. A targeted query can refute a suspected discrepancy, but it cannot establish general semantic equivalence. Likewise, failure to find a Lean counterexample is not a proof of equivalence.

The paper should say that the runs found no *detected* meaning discrepancy under the specified audits and checks. It should reserve “correct,” “trusted,” and “certified” for claims supported by explicit formal obligations.

### 2. The contribution may fail the ITP novelty test

The supplied call explicitly warns that porting a proof to another prover yields no new insight by default. The current plan still presents a 278-theorem migration, a larger CakeML roadmap, multiple model families, and a proving campaign as the main story.

The certification protocol could provide new insight if it establishes a rigorous, reproducible result about semantic auditing of proof-assistant translations. The current plan does not yet establish that result. “Astra validates, Neon reviews, and HOL4 grounds findings” is a workflow description. It becomes a research contribution only if the study identifies a measurable advantage over carefully matched alternatives and explains why that advantage arises.

A reviewer could reject the paper for presenting an engineering pipeline whose formal output remains largely unproved, with no theorem about translation, no new verification method, and no convincing causal evaluation of the AI roles.

### 3. The claimed independence of the certification pipeline is weak

Cross-family separation is treated as a proxy for independence. That assumption is unsupported.

The models may share training data, benchmark exposure, conventions, and failure modes. CakeML and Candle are public, and the plan acknowledges possible training-data contamination. Astra is also used as both validator and second prover. Opus is the translator and one audit baseline. Neon reviews Astra’s findings, so its measured performance depends on the validator’s selection and presentation of issues.

The plan should measure component value directly. A useful design would compare matched pipelines such as

- Opus alone
- Astra alone
- Neon alone
- Astra followed by Neon
- Astra followed by a human expert
- Astra followed by Neon plus formal grounding

The human condition can be an independent evaluation baseline without placing a human inside the operational workflow.

### 4. The seeded-defect experiment is too small and too confounded

There are 36 defects across six copies, with only 18 decoys. Six copies are insufficient for strong claims about reliability. If each defect is treated as an independent Bernoulli observation, a detection rate near 50% has an approximate 95% margin of ±16 percentage points with 36 observations. The interval is wider once defects within the same copy are treated as clustered. Per-class estimates will be especially unstable.

The six copies also contain six defects and three decoys each. This creates interaction effects. One mutant may make another easier or harder to detect. Random placement does not remove that problem.

The defect classes are explicitly listed in the audit briefs. This leaks the hypothesis space. Auditors can search for division, quantifier, `ARB`, `CARD`, character, and type-signature issues because the protocol tells them those are expected concerns. The experiment therefore measures detection under a prompted mutation taxonomy. It does not measure general defect discovery.

The paper needs a held-out mutation set whose classes and locations are absent from the briefs. It should include independently designed real defects from the study-1 closure. Each mutant needs a formally checked gold label and a precomputed witness, theorem, or source-level argument showing its semantic effect. Each decoy should have a machine-checked equivalence justification.

### 5. The setup comparison is unfairly specified

S1–S5 differ in model family, model capability, context, role, and likely cost. “Opus alone” is not a generic single-family baseline. It is a particular model with a particular prompt and is also the translator family. The plan does not define equal token budgets, equal time limits, equal evidence access, or equal number of independent repetitions across setups.

S4 and S5 also measure different objects. S4 is a reviewer pipeline. S5 adds a selective grounding step applied to findings that survived earlier stages. Grounding therefore cannot recover defects that Astra and Neon never report. The result should be described as incremental value conditional on a report reaching grounding, with missed-defect sensitivity reported separately.

The audit experiment has one run per setup and copy. The broader workflow plans three runs per validation round. This makes run-to-run variance a stated research question that the audit experiment cannot answer.

### 6. “Ground truth” is narrower than the plan claims

HOL4 is a valuable oracle for elaboration, overload resolution, executable behavior, and selected proof questions. It does not automatically provide a complete semantic oracle for all translated definitions and propositions.

Lean `#eval` and `decide` only cover executable or decidable cases. HOL4 ground evaluation can demonstrate a counterexample, but positive results on selected terms do not establish equivalence for arbitrary inputs. A checker can also fail because a statement is noncomputable or because the queried instance is insufficient.

The evidence rule is asymmetric. Accepted findings receive grounding. An undetected defect receives no grounding attempt. The protocol therefore measures the correctness of surfaced findings more directly than the completeness of certification.

The paper needs a predeclared catalogue of formal obligations, including which claims can be decided by evaluation, which require counterexamples, and which require proof. It should report unresolved cases explicitly.

### 7. The research questions are too broad for one 16-page paper

RQ1 through RQ5 combine translation fidelity, audit accuracy, workflow ablations, proving success, cost, literalness, run variance, and a second development. Phase 2 adds a CakeML roadmap that cannot contribute evidence by the deadline.

The “per accepted statement” and “per proved theorem” cost measures are unstable because acceptance depends on the audit policy and proving depends heavily on tactic discovery. They should be secondary descriptive statistics.

The paper needs one primary question about certification performance and one secondary question about cost and reproducibility. The CakeML Phase 2 plan should be removed from the paper except for a brief future-work sentence.

## Certification contribution

The cross-family audit plus formal grounding could be novel enough for ITP if framed as an empirical study of *translation certification*, rather than as evidence that multiple models can port a development.

It becomes convincing if the paper demonstrates all of the following.

- A blind, preregistered evaluation set with independently verified defect labels.
- Held-out defects whose classes are absent from the audit prompts.
- A comparison against single-model, same-family, cross-family, human, static-analysis, and grounding-only controls.
- Repeated runs with matched budgets and complete reporting of tokens, time, cost, evidence access, and interventions.
- Separate measurements for detection, false alarms, verdict correctness, reason correctness, evidence validity, and unresolved cases.
- A formal account of what HOL4 and Lean checks establish.
- At least one held-out set of real defects from the study-1 migration.

Without these elements, “certification method” will sound like an informal ensemble workflow.

## Missing baselines and related work

The related-work section needs substantial expansion. A reviewer will expect discussion of translation between proof assistants and proof representations, including OpenTheory, HOL Light and Isabelle importers, Lean import pipelines, Dedukti and Logipedia, and existing approaches to replaying or checking proof objects across systems.

The empirical framing also needs comparison with autoformalization evaluation, statement-fidelity benchmarks, LLM-as-judge reliability studies, and mutation testing of programs or formal specifications. These works provide relevant terminology and experimental controls for judge bias, seeded defects, false alarms, and metamorphic or semantics-preserving transformations.

The plan should include a simple non-LLM baseline. Examples include the structural scans already listed, a source-to-target declaration matcher, and a fixed suite of HOL4 queries. This establishes how much of the reported performance comes from language-model reasoning.

## Feasibility and budget

The period from 23 November 2026 to 15 February 2027 is roughly twelve weeks. The schedule allocates data collection through 17 January and leaves less than four weeks for statistical analysis, artifact cleanup, anonymisation, paper writing, and supplementary material.

The plan also includes a HOL4 oracle, multiple translation arms, up to five validation rounds, 30 audit runs, reviewer calls per finding, repairs, two proving rounds, a second prover, and possible Phase 2 setup. This is too much for a reliable study on one investigator’s machine.

The budget range of US$1,150–2,550 is plausible only as a loose API-equivalent estimate. Reviewer calls scale with the number of findings, proving costs have high variance, and subscription usage is not equivalent to a reproducible monetary cost. The plan should set a hard experimental budget and stop adding arms once the primary comparison is complete.

## Concrete changes

### Cut

- Remove Phase 2 from the paper.
- Remove the conditional Sonnet workflow arm unless the primary study finishes early.
- Drop literalness as a headline result.
- Use one translator and one carefully controlled alternative.
- Limit proving to one clearly defined end-to-end result, or present the paper as statement migration and certification if the 278 proofs remain incomplete.
- Replace the five-round open-ended loop with a fixed number of rounds or a preregistered stopping rule.

### Add

- A blind mutation set generated independently of the audit briefs.
- Formal gold labels and witnesses for every mutant and decoy.
- A held-out set of real study-1 defects.
- A human-expert reference evaluation on a subset.
- Matched prompts, context, token budgets, time budgets, and repetition counts.
- Exact binomial or cluster-aware confidence intervals.
- A preregistered analysis separating defect sensitivity, false-alarm rate, reason accuracy, and grounding yield.
- A contamination control, such as proof-hidden translation runs or a private held-out statement set.
- A static-analysis and fixed-query baseline.

### Restate the research questions

1. How accurately do specified audit pipelines detect semantic defects in proof-assistant translations under blind, formally labelled evaluation?
2. What is the incremental effect of a second reviewer and formal grounding on sensitivity, false alarms, evidence correctness, and cost?
3. How stable are these measurements across repeated runs and model families?
4. How do the results transfer from seeded defects to held-out real defects?

The main claim should then be limited to what the experiment can establish. A strong final paper could show that formal grounding improves the correctness of *reported audit findings* and quantify its cost. The current plan does not yet show that the workflow certifies a translation in the stronger sense.