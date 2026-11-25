# Astra decisions on five open questions, 24 Nov 2026

The author delegated the decisions to Astra ("all ask astra to decide", 24 Nov). Call: `codex exec -m gpt-6.2-astra -s read-only --skip-git-repo-check --json` (codex-cli 0.169.0), prompt `decision_prompt_2026-11-24.md`; usage input 97,331 (cached 3,840), output 990 (reasoning 148). Verbatim reply:

---

### 1. Tier 2 choice equations

**Decision** Score a verified Tier 2 violation in a separate secondary category. Count it when Lean proves a specific equation in the mapped HOL4 vocabulary and the source contract leaves that equation open. Using `Classical.epsilon` alone earns no flag.

**Reason** A choice-based definition can preserve its specification. The fidelity issue arises when the encoding commits to an observable equality between choices that HOL4 permits to differ.

**Reporting rule** Publish Tier 2 hits, eligible seeds, and false accusations separately, with a sensitivity analysis that adds verified Tier 2 cases to the primary score.

### 2. Scoring

**Decision** Use a frozen script for cases where it can verify both the declaration match and the stated reason against the mutant key. Give all remaining findings, stripped of arm and reviewer identifiers, to an independent human with HOL4 and Lean expertise.

**Reason** Naming the right declaration and mutation family can coincide with giving the wrong explanation. The scorer should see the witness, the source contract, and the finding, and should be able to recognize a genuine unseeded defect.

**Reporting rule** Publish the matching rubric, counts by scoring route, and anonymized rationales for judgment calls, distinguishing genuine unseeded findings from false accusations.

### 3. Spending limits

**Decision** Cap each audit at 128,000 cumulative input and 48,000 output tokens, and each review at 64,000 input and 40,000 output, counting reasoning and retries. Apply the same role limits to Opus. For 124 runs, reserve 21.824 million tokens for Astra audits and 12.896 million for Neon reviews. Enable S2 only if a further 21.824 million Neon tokens fit the author’s spend ceiling after reserving the reviews.

**Reason** These ceilings accommodate the supplied critique observations at audit scale. The observations do not establish the cost of a short review or guarantee that the workspace can fund the run. At a per-unit cap, retain completed findings and mark the run capped. At a provider ceiling, stop that provider’s remaining runs in the preregistered randomized unit order.

**Reporting rule** Report actual usage, capped runs, unrun units, and paired coverage for S5 versus S6g, with bounds showing how missing outcomes could affect the contrast.

### 4. HOL4 reference theory

**Decision** Use derivability from a frozen public interface consisting of the named saved theorems of the selected theories and their dependencies, under HOL4 inference rules. For each scored V-C seed, require a Lean derivation independent of `sorry` and source-side evidence of non-derivability, preferably an interpretation satisfying the interface while falsifying the equation.

**Reason** An equation can follow from the saved theorems without appearing among them. A kernel-checked difference from the Lean base establishes a different claim from independence of the HOL4 interface.

**Reporting rule** Call the measure “conservativity relative to the saved HOL4 interface,” publish that interface and the evidence for each seed, and label unresolved candidates explicitly.

### 5. Fixing a polymorphic type

**Decision** Score a proper specialization as V-P when fixing the type removes instances of the HOL4 claim. Retain the note-only rule for an unused binder when changing its type leaves the claim equivalent under the agreed mapping.

**Reason** A proof at one concrete type supplies only one instance of a polymorphic result. That loss of generality is measurable even if the concrete theorem is true.

**Reporting rule** Report specialization counts per translation with denominators, using the same criterion for Sonnet and Opus.

**Conflicts** I participate in the Astra arm and in validation. The fidelity rules determine which of my findings earn credit, the caps affect my opportunity to find defects, and my validation judgments could influence labels. Freeze the rules before scoring and give the independent scorer final authority over disputed labels.

**Confidence** Q1 medium, Q2 high, Q3 medium, Q4 high for the interface-relative claim, Q5 high.

---

## Notes of the main session (not Astra)

- Q2 names an independent human with HOL4 and Lean expertise. No such person has been found; the author must name one.
- Q3: each Codex call carries about 95,000 input tokens of overhead before the task (this 2 KB prompt used 97,331), so a 128,000 cumulative input cap leaves room for about one turn unless the overhead is reduced or cached input is excluded. To be measured in the pilot before the cap is frozen.
- Q3: "the same role limits to Opus" conflicts with the author instruction of 24 Nov (no limit for Opus and Sonnet). Not adopted; the pilot records Opus tokens so that a cap can be applied as a sensitivity analysis. The author decides.
- Astra is an arm and a validator in the study; it decided rules that govern its own credit and said so.
- Model identity: the Codex config on this PC sets `openai_base_url` to a local proxy (127.0.0.1:15721) with a local model catalog (file dated 23 Nov 23:52). With the user config ignored, Codex says `gpt-6.2-astra` is not supported for the ChatGPT account. So the answers in this file, and the earlier 6.2 critique, came through that proxy and I cannot verify which model or which company's server produced them.
