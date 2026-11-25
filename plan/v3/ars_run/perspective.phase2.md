contract_role: perspective

## Dimension Scores

### D1: methodology_rigor
score: not_assessed

### D2: domain_accuracy
score: not_assessed

### D3: argumentative_coherence
score: not_assessed

### D4: cross_disciplinary_relevance
score: warn
trigger: "Some key terms or cross-field implications are undefined, loosely used or overstated"

### D5: writing_and_structure
score: not_assessed

### D6: venue_fit_and_contribution
score: not_assessed

## Review Body

I read this submission as an AI-assurance researcher who works on scalable oversight, correlated model errors and assurance cases. I am an outsider to HOL4 and Lean kernel detail and to ITP venue norms, and I defer to the domain seat on those. My score covers D4 only. It reflects the design as planned: whether the planned paper would let readers from AI evaluation, software assurance and ML reliability understand what the results show, and whether its cross-field claims would be backed.

The design is stronger than most LLM-evaluation plans I see. It grounds meaning claims in an external oracle, it seeds defects with decoys, and it counts wrong reasons behind right verdicts. Those features transfer well beyond theorem proving. My concern is the language and the inferences around three cross-field ideas that the reframing in section A puts at the centre: "certification", "cross-family independence" and "no human expert". As written, an adjacent-field reader would take each one to mean more than the planned measurements can show. Each gap can be closed by reframing and by small additions to the design, so I score warn, not block.

### S1: External oracle grounding of meaning claims
The plan settles questions about meaning with HOL4 runs and Lean counterexamples rather than with a model's opinion. For AI-assurance readers this is the most transferable idea in the plan, because it turns an LLM-as-judge setup into one with a non-model ground truth for a defined class of claims. The baseline record already shows it working: HOL4 refuted the shared Claude claim about `RESULT (Clash t)`.
**Evidence Anchor**: text: §1 Goal and framing, item 2 "so the study does not rely on a model's word"

### S2: Seeded defects, decoys and wrong-reason counting
The audit experiment measures detection by defect type, false alarms on meaning-preserving decoys, and right verdicts given for wrong reasons. The last measure is unusual and valuable. Evaluation work on LLM judges usually scores verdicts only, and the baseline runs show that wrong reasons occur even when verdicts are right.
**Evidence Anchor**: text: §8 Measures "how many reported reasons are wrong even when the verdict is right"

### S3: Cost ledger from day one
A per-call ledger of tokens, money and time, checked against logs before each proving round, gives practitioners and CakeML maintainers the numbers they need to decide whether to adopt the workflow. Few AI-for-proof papers report cost this way.
**Evidence Anchor**: text: §1 Goal and framing, item 3 "A full ledger of tokens, money and time from day one."

### W1: "Certification" claims more than known-mutant recall can show
**Problem**: Section A names the main contribution a certification method and frames the open problem as certifying that a translation can be trusted. The planned evidence is detection rate on 36 seeded defects drawn from classes already known from study 1, which the threats section itself says does not cover unknown classes. In assurance-case terms, recall on known mutants is evidence about the checker, not an argument that a given translation has no remaining defects. The gap matters most in Phase 2, where the plan relies on the same checks for closures with new kinds of content, such as lazy lists, PEG parsing and unification.
**Evidence Anchor**: text: §A Proposed reframing "The open problem is certifying that a translation can be trusted."
**Why it matters**: AI-assurance and safety readers take "certification" to mean a bounded claim about residual risk. If the paper uses the word for known-class recall, that audience will read the results as a much stronger guarantee than the experiment supports.
**Suggestion**: Either replace "certification" with "measured audit evidence" or "checker validation", or state the claim as an explicit assurance argument: what the 278 statements are claimed to satisfy, which evidence supports each leg (oracle-grounded findings, mutant recall per class, proofs that go through), and which residual risks stay open. Treat proving all 278 statements as the strongest evidence leg, and report which defect classes the oracle can and cannot decide. Adding a few mutants from classes the briefs do not name would test generalisation directly.
**Severity**: Major
**Confidence**: 4 — core expertise: assurance cases and evaluation of AI checkers

### W2: Cross-family independence is assumed from within-family evidence
**Problem**: The motivating evidence is a shared wrong claim made by three Claude agents. That shows correlated error within one family. It does not show that GPT-6.2 Astra and Gemini Neon fail independently of Claude or of each other. All three families may share pretraining sources, including the public CakeML and Candle sources and HOL4 documentation, which is the mechanism most likely to produce the "pattern completion" misconception. The three Claude cases were also not independent draws: they shared briefs, and two of them saw leaked author chat messages. The plan measures overlap between families, which is good, but it does not say how overlap will be tested against what independent failures would predict, or what result would refute the independence premise.
**Evidence Anchor**: text: §A Proposed reframing "three Claude auditors independently made the same wrong claim about HOL4 semantics"
**Why it matters**: Correlated failure across diverse versions is well documented in software engineering (N-version programming) and is now being measured for LLMs. A reader from those fields will ask whether "different family" actually buys diversity. Without that test, the S4 versus S3 comparison could reflect validator strength, not diversity.
**Suggestion**: Report pairwise joint-miss rates per defect class for S1 to S3 and compare them with the product of the marginal miss rates, as Knight and Leveson did for multiversion programs. Add a same-family two-stage control (Opus followed by Opus review), so that the effect of family diversity is separated from the effect of having two stages. Also stop calling the three Claude cases "independent", and state that the count is two auditors plus one comparison agent (section C says "Two Claude auditors").
**Severity**: Major
**Confidence**: 4 — core expertise: correlated model errors

### W3: Human engineering effort is not accounted for under the "no human expert" claim
**Problem**: The plan removes the human adjudicator but keeps substantial human work: writing and revising briefs, building the mutants and decoys, building the HOL4 query tool, fixing merges (the Sonnet run needed a name fix at merge), deciding what goes back to Neon, and reading results. The ledger records model tokens, money and time but has no column for human hours. RQ1 and RQ5 are framed as replacing the human expert and as cost per theorem.
**Evidence Anchor**: absence: §Costs and token usage and §Budget estimate — expected a record of author hours and manual interventions per phase; checked §Workflow step Records, §Costs and token usage, §Budget estimate, §Threats to validity, §Research questions
**Why it matters**: For practitioners deciding whether to adopt the workflow, human effort is usually the main cost. A "no human expert" headline without that number invites the same criticism that hidden human-in-the-loop work attracts in other AI-automation claims.
**Suggestion**: Add a human-effort log: date, task, minutes, and whether the step needed CakeML or HOL4 expertise. Report it next to the model costs, and say plainly which human steps carried expert knowledge. The briefs that carry study-1 lessons, for example, encode expert judgement even with no human adjudicator.
**Severity**: Major
**Confidence**: 4 — adjacent field: human-in-the-loop accounting in AI-automation evaluations

### W4: Training-data contamination is acknowledged but not mitigated
**Problem**: Contribution (1) says translation now works, at $7 to $31, without lessons. Both Candle and the study-1 closure are public, and the plan lists contamination as a threat with no mitigation. The no-lessons ablation cannot separate a capability from recall of the public development.
**Evidence Anchor**: text: §Threats to validity "CakeML and Candle are public, so all three model families may have seen them."
**Why it matters**: ML-evaluation readers will discount any "it now works" claim on public benchmarks unless contamination is probed. The Phase 2 decision to let Sonnet translate the rest also rests on this generalisation.
**Suggestion**: Add a small contamination probe. Options include renaming constants and permuting theory order in a sample of definitions, or translating a few HOL4 theories written or changed after the models' stated training cutoffs. Then compare defect and literalness rates. If that is not feasible, scope contribution (1) to public developments and say so in the abstract.
**Severity**: Major
**Confidence**: 3 — adjacent field: ML benchmark contamination; I cannot judge which HOL4 theories post-date each model's training data

### W5: Reproducibility under closed, drifting models and CLIs
**Problem**: The validator is described as the latest Codex model, and the models run through vendor CLIs that may update silently or run under subscriptions. Pinning identifiers and recording dates documents drift but does not prevent it, and a third party cannot rerun the closed models later.
**Evidence Anchor**: text: §Threats to validity "Model versions can change during the study. We pin identifiers and record dates."
**Why it matters**: The artifact will be reproducible at the level of logs and Lean checks but not at the level of model behaviour. Readers should be told which claims an artifact reviewer can actually recheck.
**Suggestion**: Pin the CLI versions as well as the model strings, record any version change seen during the study, and separate claims an artifact reviewer can recheck (builds, axioms, oracle queries, scripted counts) from claims that need the closed models.
**Severity**: Minor
**Confidence**: 4 — core expertise: reproducibility of closed-model evaluations

### W6: Adjacent-field positioning and key terms are missing
**Problem**: Terms such as "meaning defect", "form-only difference", "by-design difference", "pattern completion" and "grounding" carry the results but are not defined for readers outside ITP. The plan also does not position the validator-plus-reviewer design against related work on N-version diversity, LLM-as-judge reliability, or mutant validity.
**Evidence Anchor**: absence: §1 Goal and framing and §2 What is known already — expected definitions of the outcome terms and positioning against N-version, LLM-as-judge and mutation-testing work; checked section A, section B, §1, §2, §8, §Research questions, §Threats to validity
**Why it matters**: The audit method is the part of the paper most likely to be cited outside ITP. Without the definitions and the positioning, readers from those fields cannot judge the contribution.
**Suggestion**: Add a short glossary-style paragraph defining the outcome categories, and one paragraph of related work from the fields listed below. On mutant validity, cite evidence on whether mutants stand in for real faults, and use the two real study-1 defects (CARD, integer division) as a check on that.
**Severity**: Minor
**Confidence**: 4 — core expertise for the evaluation literature; outsider for ITP terminology

### W7: Practical value for CakeML maintainers is not addressed
**Problem**: Phase 2 plans a separate Lean repository that mirrors CakeML. The plan does not say how the Lean copy stays in step as HOL4 CakeML changes, who maintains it, or whether CakeML developers were consulted about which milestones they would use.
**Evidence Anchor**: absence: §Phase 2 more of CakeML — expected a maintenance and synchronisation plan and a statement of the intended users; checked §Phase 2 Repository, §Phase 2 Order, §Scope, §Threats to validity
**Why it matters**: The practical impact claim for a migrated CakeML depends on whether anyone can maintain or use it once the study ends.
**Suggestion**: Add a paragraph on keeping the copy in step, such as re-running the workflow on changed theories with the ledger used to estimate the cost, and name the intended users of each milestone.
**Severity**: Minor
**Confidence**: 3 — adjacent field: practical adoption of verified software artifacts

### Cross-Disciplinary Reading Recommendations
- Knight and Leveson (1986), the classic experiment showing that independently developed program versions fail in correlated ways. It is the direct precedent for testing the cross-family independence premise (W2).
- Just et al. (2014), on whether mutants are a valid substitute for real faults. It informs how far seeded-defect recall can stand in for real defects (W1, W6).
- Jia and Harman (2011), a survey of mutation testing, for mutant design and the equivalent-mutant problem behind the decoys.
- Zheng et al. (2023), on LLM-as-a-judge reliability and biases. It is relevant to Neon's role as adjudicator.

~~~yaml suggested-references
- title: "An Experimental Evaluation of the Assumption of Independence in Multiversion Programming"
  authors: ["Knight, J. C.", "Leveson, N. G."]
  year: "1986"
  doi: null
  arxiv_id: null
- title: "Are Mutants a Valid Substitute for Real Faults in Software Testing?"
  authors: ["Just, R.", "Jalali, D.", "Inozemtseva, L.", "Ernst, M. D.", "Holmes, R.", "Fraser, G."]
  year: "2014"
  doi: null
  arxiv_id: null
- title: "An Analysis and Survey of the Development of Mutation Testing"
  authors: ["Jia, Y.", "Harman, M."]
  year: "2011"
  doi: null
  arxiv_id: null
- title: "Judging LLM-as-a-Judge with MT-Bench and Chatbot Arena"
  authors: ["Zheng, L.", "Chiang, W.-L.", "Sheng, Y."]
  year: "2023"
  doi: null
  arxiv_id: "2306.05685"
~~~

### Questions for Authors
1. What claim, stated as an assurance argument, will the ITP paper make about the 278 translated statements, and which evidence supports each part of it?
2. What overlap result between Astra, Neon and Opus would lead you to conclude that family diversity does not help?
3. How many author hours went into briefs, mutants, the query tool and merge fixes in the baselines, and will the paper report them?
