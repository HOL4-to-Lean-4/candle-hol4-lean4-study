DECISION: accept with edits

### Card #1 — Journal-Fit Reviewer (EIC)
- Identity: ITP PC chair/member experienced in large-scale proof engineering and ITP/CPP/CICM standards.
- Focus: (1) whether the work clears ITP's "porting yields no new insight by default" bar and whether calling an empirical LLM audit "certification" fits ITP norms; (2) resolving the v3.2 vs 23 Nov reframing split into one 16-page claim feasible by 15 Feb; (3) delta vs the author's FormaliSE 2027 paper, plus double-blind and AI-generated-text rules.
- Particularly cares about: whether this is an ITP theorem-proving contribution or an LLM-evaluation paper.
- Blind spots: experimental statistics; HOL4/Lean encoding detail.

### Card #2 — Peer Reviewer 1 (Methodology)
- Identity: empirical SE researcher specialising in mutation testing, fault-injection design, and LLM-judge evaluation.
- Focus: (1) seeded-defect validity: brief-to-mutant circularity (briefs list seeded classes), author-mutant realism, small per-subtype counts (36 across ~13 subtypes), and imbalance toward unprovable mutants over provable silent defects (weakened conclusions, extra hypotheses); (2) S1–S5 identification: missing controls (same-family two-stage, single-model+grounding, deterministic-scan baseline), Neon's filter-only recall ceiling (`S5 <= S4 <= S1`), cost parity, and 1-run-per-copy variance; (3) unproved baseline ground truth for "0 meaning defects" and false alarms.
- Particularly cares about: whether cross-family gains are identified or confounded by model strength, filtering, grounding, and checklist prompts.
- Blind spots: ITP norms; HOL4/Lean proof-theoretic detail.

### Card #3 — Peer Reviewer 2 (Domain)
- Identity: researcher in proof-assistant interoperability (OpenTheory, HOL→Lean/Isabelle importers, Dedukti) and HOL4/Lean 4 semantics.
- Focus: (1) why LLMs parse HOL4 scripts (including ML-built theorems) rather than exporting typed HOL4 kernel terms or using symbolic importers; (2) HOL4/Lean semantic fidelity, especially the contradiction treating fixed underspecified values (`HD []`, `Prim_rec`, `ARB`) as valid models in baselines yet as seeded defects in §7; (3) formal limits of the HOL4/Lean oracle (higher-order claims, query validity) and proving as fidelity evidence (silent unsoundness; distinguishing stuck proofs from defective statements without a human).
- Particularly cares about: whether kernel-level export or symbolic importers undercut the LLM-audit premise.
- Blind spots: LLM cost economics; statistical power.

### Card #4 — Peer Reviewer 3 (Cross-disciplinary / practical)
- Identity: AI-assurance researcher working on scalable oversight, correlated model errors, and assurance cases.
- Focus: (1) cross-family independence vs shared-corpus error correlation and public CakeML/Candle training contamination across translation, proving, and auditing; (2) assurance-case gap between known-mutant recall and certifying absence of unknown bugs at Phase-2 scale; (3) reproducibility under closed, drifting models/CLIs and hidden human engineering (briefs, merge fixes, oracle/mutant building) vs the "no human expert" claim.
- Particularly cares about: generalizing from n=3 Claude coincidences to family independence and practical value for CakeML maintainers.
- Blind spots: Lean/HOL4 kernel detail; ITP venue politics.

## Rationale
- Keep **full** mode: the plan's fatal risks span venue fit, experimental identification, HOL4/Lean semantics, and AI assurance, which `methodology-focus` would miss.
- Card #1 adds the v3.2-vs-reframing split, Feb-15/16-page feasibility, ITP's strict "certification" bar, and AI-prose/double-blind rules.
- Card #2 adds missing S1–S5 controls (same-family two-stage, single-model+grounding, static scans), Neon's filter-only recall ceiling, silent-mutant balance, and single-run variance.
- Card #3 targets the `HD []` valid-model-vs-defect contradiction, HOL4 kernel-term export vs text scraping, and oracle/proving blind spots.
- Card #4 adds CakeML/Candle data contamination, hidden human-in-the-loop effort, and the assurance-case gap from known mutants to certification.
