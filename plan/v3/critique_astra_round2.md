# Astra critique, round 2 (raw reply, gpt-6.2-astra)

Resumed round 1 thread with `codex exec resume <thread> -m gpt-6.2-astra --skip-git-repo-check --json`, 23 Nov 2026. Input: the 16 main points of the ARS panel (Claude Opus 5.5 seats). Usage of this turn: input 111,284, cached 3,712, output 3,091 (reasoning 1,119); thread total 215,701 in / 8,507 out.

---

# Second review

**Overall assessment of the panel:** I agree with most of it. The panel correctly moved the central problem from “more controls would help” to “the current claim is not yet well-defined or identifiable.” Its main weakness is that some proposed controls would expand an already overlarge experiment. The author should adopt the diagnostic principles while reducing the number of arms.

## (a) Assessment of the 16 panel points

1. **Agree.** The “translation now works” claim is circular when its evidence comes mainly from Claude auditors, while the paper argues that model auditors can share systematic errors. The result should be conditional until grounded audits and Lean proofs support it.

2. **Agree strongly.** The plan has two papers competing inside one manuscript. The audit and validation-evidence framing is sharper and better aligned with the actual proposed experiment. The workflow question can become a secondary application of that framework.

3. **Agree.** The transferable insight must appear before the implementation details. A useful candidate is a taxonomy of HOL4-to-Lean semantic gaps, together with evidence about which audit configurations detect them and which grounding checks resolve them. The delta from the FormaliSE paper must state exactly what is new in protocol, evidence, and measured outcome.

4. **Agree.** “Certification” implies an assurance argument with a defined soundness boundary. The current study measures audit performance and evidence quality. “Validation evidence” or “auditing translated statements” is more accurate unless the author formalizes what the certificate establishes.

5. **Partly agree.** The suggested controls diagnose the confounding well. S0 is essential. S7 is useful because it tests whether grounding adds value independently of cross-family review. S6 is informative, although it may become a costly and low-priority arm. A cost-matched Opus control is also necessary.

   Joint-miss rates should be reported. The product of marginal miss rates is a reference under independence, not evidence that the families are independent. Shared prompts, shared code, public training data, and the same defect classes can invalidate that comparison.

6. **Partly agree.** The panel is right that 36 defects cannot support reliable per-subtype claims and that one run per setup is inadequate for variance. Repeating every setup three times on every copy would create 126 audit runs for seven setups and six copies, before grounding. That is probably infeasible and still would not create more independent mutants.

   I would use a paired primary design with three repeats for the core setups, fewer repeats for exploratory arms, and per-copy or per-mutant bootstrap intervals. Report subtype results descriptively.

7. **Agree.** Listing the seeded classes creates a serious prompt leak. The author should cross the brief condition with the mutation condition and include held-out unnamed classes.

8. **Agree.** The mutant taxonomy is internally inconsistent. A default for `HD []` may be a defect in one translated encoding and a permitted model of HOL4’s unspecified behavior in another. An extra `[Nonempty]` can be a faithful Lean encoding when the relevant HOL type is inhabited. Mutants need labels based on semantic effect and fidelity to the source specification, not on syntactic deviation.

9. **Agree strongly.** This is a major omission. A weakened conclusion or dropped conjunct can remain provable and therefore evade the proving stage. Every mutant should be tagged by whether proving can expose it, whether a counterexample exists, and which oracle obligation should detect it.

10. **Partly agree.** Unchanged code needs a defined status before it enters the denominator. An “unresolved” category is essential. I would not require exhaustive grounding of every unchanged declaration. Instead, define a scored subset with formal checks and blinded human adjudication, then report the remainder as unresolved.

   The matching rule and reason rubric must be fixed before results are seen. Two blind scorers are preferable, with agreement and adjudication recorded.

11. **Agree strongly.** The missing systems work is a major threat to novelty. Typed HOL4 kernel-term export, OpenTheory, HOL Light and Isabelle importers, symbolic importers associated with Obua-Skalberg and Kaliszyk-Krauss, Dedukti, Logipedia, and Mathport are directly relevant. A kernel-term export may make several proposed “HOL4 oracle” questions mechanical. A symbolic statement translator could provide an independent reference translation.

   The autoformalisation-faithfulness literature, including miniF2F, ProofNet, FormalAlign, and LLM-as-judge evaluation, supplies relevant methods for statement fidelity and judge reliability.

12. **Agree, with one refinement.** The panel is right that HOL4 and Lean do not share semantics automatically. `#eval` does not settle definitions involving `Classical.epsilon`. A failed proof attempt is evidence of difficulty, not a refutation. Proving can expose an over-strong or inconsistent translation, but successful proving does not establish fidelity.

   Some questions remain mechanically answerable, such as overload resolution, elaborated types, selected theorem identities, and concrete counterexamples. The plan should classify oracle checks by what they establish. RQ1 needs a criterion distinguishing a false statement from an unproved statement, such as a proof of the negation or a source-level semantic witness.

13. **Agree.** The panel’s correction matters. HOL4’s `Define` can complete missing patterns with `ARB`. The reported auditor error concerned attributing that behavior to `Prim_rec` or datatype-destructor definitions. The plan also inconsistently says two auditors and three auditors, and “independent” is unjustified when they shared prompts and context.

14. **Agree.** “No human expert” describes the operational workflow, not the total research process. The author designed the defect classes, briefs, mutation operators, and oracle queries. A human-effort log should record time, task, and required CakeML or HOL4 expertise.

15. **Agree.** Acknowledging contamination is insufficient. A renaming or permutation probe would test memorisation and pattern retrieval. A post-cutoff or private held-out theory would be stronger if available.

16. **Agree.** This is a practical publication risk. The plan is stale relative to the measured runs, lacks a 16-page outline, and needs an anonymisation checklist and pinned CLI versions. A maintainer-value paragraph should explain how the artifact helps maintainers decide whether a port is safe to inspect, replay, or repair.

## (b) What the panel missed and what I revise

The panel covers most of my first-round concerns, especially the overclaim about ground truth, the weak mutant design, missing related work, and setup confounding.

It underemphasizes four points.

- **Multiple mutants create interaction effects.** Six defects and three decoys in one copy can change the visibility of each other. The analysis must treat copies as clusters and report whether each mutant is detectable in isolation.
- **The budget and schedule remain unrealistic.** Adding S6 and S7 worsens the problem. A core experiment must be selected before freeze.
- **Proof-visible translation is a confound.** Translators see full HOL4 scripts and proofs, while the task is described as statement translation. A proof-hidden condition or explicit limitation is needed.
- **Phase 2 should be cut from the paper.** It adds scope and promises without contributing evidence by February.

I revise my first-round view in two ways. First, I previously treated the 36-defect set mainly as underpowered. The deeper issue is that it is also leaked, clustered, and semantically heterogeneous. Second, I treated cross-family separation as a weak independence argument. The panel is right that this needs direct joint-miss measurements and matched same-family controls.

## (c) Eight changes before the freeze

1. **Choose the audit framing and rewrite the title, goal, abstract premise, and RQs.** Make the primary contribution validation evidence for translated statements.

2. **Replace “certification” with a defined assurance claim.** State precisely what HOL4 queries, Lean proofs, counterexamples, and structural checks establish.

3. **Freeze a primary paired experiment.** Use S0, Opus alone, Astra alone, Astra plus Neon, and Astra plus grounding. Add S6 or S7 only if the budget permits.

4. **Redesign the mutant set.** Use blind held-out classes, formally validated gold labels, isolated mutants, decoys with equivalence proofs, and tags for whether proving can expose each defect.

5. **Pre-register scoring and statistics.** Define matching, reason correctness, unresolved cases, primary contrast, clustering, repeated runs, and confidence intervals before execution.

6. **Add independent reference baselines.** Include structural checks, symbolic or kernel-term reference translation where feasible, and a blinded human adjudication subset.

7. **Add contamination and human-effort controls.** Use renaming or permutation probes, a private or post-cutoff holdout if possible, proof-hidden analysis, CLI pinning, and an effort ledger.

8. **Cut scope and produce a page-and-budget plan.** Remove Phase 2, reduce optional translation and proving arms, reserve space for related work and limitations, and set a hard spend and completion date.

**Verdict if these eight changes are completed:** **borderline with a credible path to accept.** The plan would then answer the ITP porting bar through a measurable proof-engineering insight and a defensible audit study. Acceptance would still depend on the primary contrast being positive, the formal artifact being reproducible, and the authors reporting unresolved cases without upgrading them into correctness claims.