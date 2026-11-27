<!-- Reply of gpt-6.2-astra (gateway-reported; codex exec via SSS gateway, read-only, high effort) to reuse_rule_prompt_2026-11-27.md, on study@4e7d5be + cakeml-lean4@3ed5ce1. Unedited. 96,156 input tokens (67,840 cached), 1,619 output, 88 s. -->

**Keep item 11 as a rule for when work can proceed. Change how it treats theorems, and give the final migration a stricter acceptance rule.**

For **ITP 2027**, item 11 does not weaken the main result as designed. Phase 1 measures which real errors the audit found in eight translations. Phase 2 contributes no evidence to that paper. A reviewer would have grounds to object if the paper counted V-C when reporting audit success, then discounted the same defect when describing migration quality. All 63 V-C pairs in the 105-entry audit key survived rechecking against HOL4’s saved theorems. Deferring a repair leaves both the detection and the defect on record. [Plan, goal and framing](study/plan/v3/plan_v3.4.tex#L22) · [Audit tables](study/audit/real/TABLES.md) · [Phase 2](study/plan/v3/plan_v3.4.tex#L196)

For a **journal or migration release**, a confirmed V-C error defeats “a faithful migration” for any claimed scope containing its cause. Proving every Opus target cannot rescue that claim. The crucial detail is that v3.4 defines V-C at the *definition* that makes an extra equation provable. An unused theorem witnessing `HD [] = v` does not confine the error to that theorem. A later proof can obtain the equation by unfolding `HD` without citing the witness. Item 11(a) already blocks that definition. Item 11 also leaves the disposition of an unused V-P theorem unclear, particularly if it is the current milestone’s advertised result. [Fidelity contract](study/plan/v3/plan_v3.4.tex#L58) · [Decision 11](cakeml-lean4/plan/DECISIONS.md#L42)

**Changes and cost**

1. **Track the cause, witness and affected dependencies separately.** Apply the gate to the current target and its transitive dependencies. Permit reuse around a defective leaf theorem only when the dependency record establishes it is unused. Check again before each new use. Classification and dependency checks take zero model repair rounds. Batch required Opus fixes by module, then re-audit and reprove affected work. The readiness review gives roughly 219k Astra tokens per audited module as a historical guide. Opus repair and reproof costs need measurement. [Readiness review](study/plan/v3/readiness_astra_migration_2026-11-27.md)
2. **Preserve the comparison before repair.** Freeze both raw translations. Report V-P and V-C by translation and audited unit, verified tier-2 cases in the sensitivity analysis, and `unsure` separately. Report residuals after Opus repair in a second table. This costs zero extra repair rounds. Phase 2 can compare descriptive counts on matched scope. Its sampled review, reused modules and lack of an equivalent independent error key preclude treating its detection rate as a replication of Phase 1 recall. [Audit design](study/plan/v3/plan_v3.4.tex#L125)

**Suggested paper wording:** “We measured detection of translation errors against HOL4’s saved interface on Candle and type soundness. The whole-CakeML migration applies that contract and records deferred repairs separately.”

**Suggested README wording:** “At commit `[hash]`, Opus proves `[targets]`. Across `[audited scope]`, `[p]` confirmed V-P and `[c]` confirmed V-C findings remain open. `[t]` verified choice cases and `[u]` unresolved findings are listed separately. Sonnet was audited only.” Link each issue to its declaration, witness, affected targets, reuse status and resolution commit. Generating this summary from the issue list costs zero repair rounds.

**Conflict.** I was Astra/S1 and helped choose the contract. S1 missed four keyed errors that the scripts found. Neon accepted my false `store_ffi` finding. Sampling my reports cannot reveal what I omitted, so I would claim only “no known violations in the audited scope.” [Audit results](study/audit/real/RESULTS.md)

**Preferred rule**

- Block structural failures and open findings on definitions or datatypes.
- Block confirmed errors and unresolved fidelity questions affecting a claimed target or its transitive dependencies.
- Record unused theorem findings and recheck before first use.
- Require closure of all confirmed fidelity errors before claiming whole-migration fidelity, and disclose remaining uncertainty.