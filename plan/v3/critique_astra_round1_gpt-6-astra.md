# Astra critique, round 1 (raw reply)

Model: `gpt-6-astra` via `codex exec -m gpt-6-astra -s read-only --skip-git-repo-check --json` (codex-cli 0.169.0), 23 Nov 2026. `gpt-6.2-astra` was rejected for this ChatGPT-account login. Input: plan v3.2 LaTeX, the 23 Nov reframing, summaries of the four baseline RESULTS.md. Usage (turn.completed): input 31,335, cached 0, output 2,708 (reasoning 445).

---

1. **“Certification” exceeds the evidence.** The workflow checks selected claims about selected declarations. It supplies neither a formal correspondence between HOL4 and Lean nor a completeness guarantee for finding translation errors. Successful proofs of all 278 Lean statements would establish those statements relative to their Lean definitions; they would not establish that those definitions faithfully represent Candle.

2. **The experiment lacks a settled definition of a defect.** The baselines accept fixing unspecified values as legitimate modelling, while the mutant list treats fixing `HD []` as a defect. Type-signature changes described as equivalent in the results also appear among seeded defects. Until the fidelity criterion is explicit, the experiment’s labels—and therefore detection rates—are contestable.

3. **The proposed comparisons cannot establish a cross-family advantage.** S3 is one Opus auditor; S4 adds a second model and S5 adds executable checks. Differences conflate model capability, family, number of calls, review structure, tools and expenditure. Three Claude auditors repeating an error motivate investigation; they do not demonstrate that family diversity prevents correlated errors.

4. **The benchmark is small, coached and clustered.** Thirty-six defects across six copies, drawn from classes named in the audit briefs, primarily test recognition of anticipated mistakes. They provide weak evidence about general translation fidelity or per-class performance.

5. **The novelty remains vulnerable to the venue’s stated objection.** A Candle port, inexpensive translation runs and an ensemble of existing models may amount to an engineering case study. The paper needs a generalizable technical or empirical insight beyond “models now translate this development.”

6. **The schedule prioritizes proving before securing the research contribution.** The January go/no-go tests whether proving finished. It should first test whether the fidelity criterion, benchmark and controlled comparison support a defensible claim.

**Verdict: reject-likely as currently planned.** The central claim is stronger than its evidence, and the proposed experiment cannot isolate the claimed advantage.

### What the existing results actually establish

Reframing A’s “translation now works” and “no meaning defects” are unsupported as stated. Results B establish that **the checks performed found no target-statement meaning defects**, with discrepancies and modelling differences still requiring classification. Results 2–4 inherit confidence through Claude comparisons with an incompletely established reference. Agreement between translations does not independently establish correctness.

The no-lessons run establishes one observed null result on Candle. It does not establish that lessons have no effect generally. Likewise, $7–31 describes initial translation costs, excluding the work required to justify fidelity.

The leaked chat messages compromise the affected runs as controlled evidence. Removing messages in future runs cannot repair earlier comparisons. Retain them as pilot observations and rerun the comparisons essential to the paper under clean conditions. The Sonnet and no-lessons results also make several conditional branches in §Baselines obsolete; freeze a revised protocol now.

The purported replacement of the human expert is another overclaim. There is no matched human-review arm, and the author still chooses mutations, determines their expected effects, designs checks and interprets unresolved cases. Distinguish **automated operational review** from **independent benchmark adjudication**.

### What would make the contribution convincing

First define the translation contract. Does fidelity require logical equivalence under an interpretation, preservation of source consequences, preservation of all allowed models, or correctness only for the 278 target statements? These yield different judgments.

Selecting one allowed value for an underspecified operation can preserve source theorems while adding target equations. That may be acceptable under a refinement contract and unacceptable under an equivalence contract. Shared defaults can also introduce equalities between otherwise unrelated unspecified values. Resolve these questions explicitly for `ARB`, choice, partial-looking definitions, type encodings and finite maps.

Then distinguish three evidence levels:

- **Formal correspondence:** kernel-checked relationships between source and target representations.
- **Verified discrepancy witnesses:** checked counterexamples or derivations demonstrating a specific contract violation.
- **Empirical assurance:** an auditor’s measured ability to detect selected violations.

Only the first supports a strong certification claim for the covered correspondence. The second and third can support a valuable **evidence-backed translation audit**.

The HOL4 query interface is useful infrastructure, but §HOL4 overstates its oracle status. Failure of a short proof attempt does not establish non-provability. Evaluation cannot settle arbitrary propositions involving infinite sets, choice or unspecified values. A Lean counterexample requires a justified connection to the corresponding source interpretation. A checked theorem can still answer the wrong semantic question.

Require each benchmark label to have a reproducible witness or correspondence argument established independently of the evaluated auditors. Preserve unresolved cases as unresolved. Ground rejected findings as well as accepted ones on the benchmark: §Grounding currently verifies only survivors, so reviewer false negatives disappear from scrutiny.

A convincing contribution would identify which error mechanisms executable evidence resolves, where it remains insufficient, and the resulting accuracy–cost tradeoff. A reusable benchmark and evidence protocol could supply that insight even without a cross-family win.

### Repairing the seeded-defect experiment

**Mutant validity.** “Still builds” is insufficient. Every mutation needs a demonstrated contract violation. A strengthened conclusion may already follow; reordered clauses may be equivalent; derived `BEq` may implement the intended equality; an extra hypothesis may be redundant under the encoding. Mutations concerning division or infinite sets must actually reach relevant operations in this closure.

Separate definition fidelity from target-theorem impact. A semantic change invisible to all 278 statements is different from a mistranslated target. Include localized mistakes, shared-prelude mistakes and realistic multi-edit defects, but label their scope.

**Generation and independence.** Publish mutation operators, eligibility rules and sampling procedures before evaluation. Have an independent evaluator validate labels and witnesses. Use held-out mutation mechanisms and historical defects unseen during prompt development. The two study-1 defects provide useful historical cases, but repeated fresh translations of that closure are not guaranteed to reproduce them.

Start with single-mutant packages to avoid masking, interactions and one shared mistake generating many apparent detections. Retain multi-mutant packages as a secondary deployment test. Six full copies with six defects each create clustered observations; 36 is not automatically the effective sample size.

**Power.** With roughly a dozen listed classes, there are only a few examples per class. Per-class percentages would be unstable. Even 36 independent successes out of 36 give a two-sided 95% exact lower sensitivity bound of only about 90%; clustering weakens that evidence.

Power depends on discordant paired outcomes and the smallest improvement worth claiming. Pilot those quantities, then size the study. Preselect one primary comparison, report paired uncertainty, and account for package and mutation-site clustering. More independent defect sites matter more than repeatedly querying the same six packages.

**Decoys and false alarms.** A report on a decoy is not automatically a false alarm: a correct “equivalent rewrite” note is useful classification. Count an erroneous defect accusation or unnecessary repair recommendation. Independently verify decoy equivalence.

Eighteen decoys cannot establish a low false-positive rate; zero errors still permits a substantial rate. Add untouched clean packages and broader legitimate representation changes. Report false accusations per clean package or declaration, alongside precision. Precision on defect-enriched packages does not predict precision in naturally near-clean translations.

**Blinding and contamination.** Randomize anonymous package identifiers and execution order; hide mutation locations, counts and answers; keep generators and answer keys outside auditor workspaces. Freeze prompts before held-out evaluation. Listing the mutation classes is legitimate for a checklist-assisted task, but must be disclosed and tested separately from generic auditing and held-out classes.

Transcript scans identify some access violations; they do not prove isolation. Restrict access operationally. Public-source training exposure remains unresolved; fresh, unpublished mutations reduce answer exposure without making Candle itself unseen.

**Comparable setups.** Add Opus→Opus, repeated Opus with aggregation, and a strong single auditor with the same tools and total budget. Compare independent parallel auditing with sequential review. Under fixed Astra findings, S4’s filtering reviewer cannot discover additional defects; measure its retention of true findings and rejection of false ones separately.

To claim a *family* effect, vary role assignments and ideally include multiple models within families. Otherwise report a comparison of these particular configurations.

Repeat the seeded experiment, including reviewer decisions. §Workflow’s three validation runs do not provide replication for §Audit’s apparently single runs. Separate variation across defects, packages and model executions. Report both fixed-budget comparisons and accuracy–cost curves.

### Baselines and related work

The paper needs an explicit comparison with proof-assistant translation and proof transport: OpenTheory, HOL Light/Isabelle/Lean import routes, and Dedukti/Logipedia. Explain the differences in trusted components, supported fragments, semantic guarantees, automation and representation flexibility. Do not imply that importing a checked proof automatically resolves every representation choice.

Also position the work against autoformalization evaluation, statement-fidelity benchmarks, specification mutation testing and LLM-as-judge research. Compile success, proof success and source-statement fidelity are distinct outcomes.

Add a structural-scan-only baseline, a tool-enabled single auditor, and a bounded expert-adjudicated evaluation subset. These establish whether the extra models outperform simple checks and whether benchmark judgments deserve trust. The supplied ITP call’s porting warning makes this comparison central to acceptance.

### Scope, questions and delivery

Cut Phase 2 from the experimental commitment and remove linear extrapolation from cost per Candle theorem to CakeML. Library infrastructure, dependency reuse and difficult milestone proofs dominate such estimates. Deprioritize the second prover and repeated proving rounds unless proof-search variability remains a central research question.

Use three questions:

1. **How accurately do specified audit configurations detect independently verified fidelity violations, including held-out mechanisms and historical defects?**
2. **At matched expenditure and tool access, what do independent auditing, sequential review and executable grounding each contribute?**
3. **What residual mismatches emerge during proof completion, and which fidelity obligations remain outside kernel checking?**

Measure verified recall, false accusations, abstentions, evidence validity, reviewer-induced misses, correct-verdict/wrong-reason cases, repair correctness, residual defects, total cost and elapsed time. Report final proof coverage with transitive admission checks and frozen definitions as well as statements. Proof failure alone is not evidence of falsity.

There are 12 weeks from 23 November to 15 February. That is feasible for a narrow audit paper, but fragile for the full plan plus the FormaliSE camera-ready. Start the paper structure now; freeze the contract and benchmark protocol by early December, pilot before Christmas, and make the scientific go/no-go in early January.

The $270 audit estimate counts configurations as equal-cost audits. S4 and S5 contain multiple stages, per-finding review and potentially iterative grounding. Replication, matched controls and independent label validation increase costs further. Pilot actual stage costs, record human preparation effort, and fund the primary controlled comparison before optional proving arms. A complete Candle proof is valuable supporting evidence; it cannot rescue an invalid audit experiment.