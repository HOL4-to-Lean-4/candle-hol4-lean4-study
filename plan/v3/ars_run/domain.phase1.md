## Contract Paraphrase

D1 (methodology_rigor, mandatory, owned by methodology): The planned design, data handling, measurement and reproducibility provisions must reach the peer-review bar of the field. Because the submission is a study plan, this means the planned measures, sample sizes, controls and artifact-release arrangements would, if executed, support the claims a proof-engineering venue expects. From a domain-accuracy standpoint I only note whether domain facts that the method depends on are stated correctly; scoring this dimension is not my role.

D2 (domain_accuracy, mandatory, owned by domain): Claims about the relevant proof assistants, their logics and kernels, prior translation and porting efforts, and the state of AI-assisted formalisation must agree with current evidence. Prior work must be represented correctly and fairly, terminology specific to interactive theorem proving must be used precisely, and reported or cited results must not be misstated. This is the dimension I score.

D3 (argumentative_coherence, mandatory, owned by devil's advocate): The central thesis of the plan must hang together, the anticipated evidence must be capable of supporting the claims it is meant to support, and no fallacy may undermine the core argument. Domain misstatements can feed into this, but its scoring belongs to other roles.

D4 (cross_disciplinary_relevance, high priority, owned by perspective): Framing, definitions and implications should be readable by adjacent communities, for example machine-learning evaluation readers and programming-languages readers, and any interdisciplinary claim must be substantiated rather than asserted.

D5 (writing_and_structure, normal priority, owned by the editor): The plan must be clearly organised and expressed, figures and tables (if any) must be fit for purpose, and the planned paper must fit the venue's conventions, including the stated page limit, LIPIcs format and lightweight double-blind rules.

D6 (venue_fit_and_contribution, mandatory, owned by the editor): The planned paper must fit the target venue and make an original, significant contribution for that readership. Novelty relative to existing interoperability and porting work matters here, but the editor owns the score.

## Scoring Plan

### D2: domain_accuracy
dimension_id: D2
what_to_look_for: Correct description of the source and target systems' logics, kernels and library conventions (e.g. HOL4 simple type theory versus Lean 4 dependent type theory with universes, definitional unfolding, quotient and choice handling); accurate and fair representation of prior interoperability, translation and porting work (OpenTheory, HOL-to-Isabelle and HOL-to-Lean importers, Dedukti-based exchange, prior large verified-system ports) and of prior LLM-for-ITP evaluations; precise use of terms such as certified translation, kernel-checked, axiom, sorry, faithful statement, and equivalence of theorem statements; correct citation of reported numbers and claims from prior work.
what_triggers_block: A mischaracterisation of a core system's logic or of an important prior effort that the plan's design or novelty claim relies on, or omission of directly competing prior work such that the claimed gap may not exist; fixable by revision but must be fixed before the plan is sound.
what_triggers_warn: Imprecise or loose terminology, minor misattribution or outdated citation of prior work, or incomplete coverage of related efforts that does not change the plan's design or core novelty claim.
what_triggers_fatal: A factual error about the systems or prior work so fundamental that the planned study is infeasible or meaningless as designed (for example a correctness or faithfulness guarantee that the stated target logic or method cannot provide), or a central novelty claim already fully achieved by existing published work.

criteria_binding_unavailable

[CONTRACT-ACKNOWLEDGED]
