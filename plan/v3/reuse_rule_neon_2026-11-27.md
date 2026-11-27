<!-- Reply of gemini-4-neon-high (agy, cloud thread) to reuse_rule_prompt_2026-11-27.md; conversation 6d0cbda2. Unedited; links point to Neon's local copy. 26,141 input, 12,691 output (10,767 thinking), 10,882 cache read, 109 s. -->

**Disclosure (conflict of interest).** I am Gemini Neon, the study’s reviewer (arm S4), and my outputs informed Phase 1 framing ([plan_v3.4.tex](file:///root/neon_work/20261127-0650-reuse-rule/plan_v3.4.tex#L243-L246)). Taking the reading less favourable to myself: in Phase 1, Neon accepted 173/174 Astra findings ([DECISIONS.md](file:///root/neon_work/20261127-0650-reuse-rule/DECISIONS.md#L22-L23)), including Astra’s false `store_ffi` finding, and sampled review cannot catch Astra’s omissions ([readiness_astra_migration_2026-11-27.md](file:///root/neon_work/20261127-0650-reuse-rule/readiness_astra_migration_2026-11-27.md#L37)). Neon’s sampled review provides weak assurance, so I favour stricter deterministic gates rather than relying on review.

### 1. Does item 11 weaken either contribution?

Phase 2 contributes no evidence to the ITP 2027 paper ([plan_v3.4.tex](file:///root/neon_work/20261127-0650-reuse-rule/plan_v3.4.tex#L197)), so Phase 1’s audit is unaffected. For a journal paper—or an ITP reviewer evaluating the migration workflow (Contribution 2)—item 11 ([DECISIONS.md](file:///root/neon_work/20261127-0650-reuse-rule/DECISIONS.md#L42-L48)) weakens both contributions:

- **Unblocked unimported V-P:** Clause 11(b) blocks V-P only on theorems imported by later milestones. A V-P error on a leaf or milestone-target theorem is neither blocked nor listed as a known issue, contradicting "faithful migration."
- **V-C contract clash:** The contract defines V-C on *definitions* ([plan_v3.4.tex](file:///root/neon_work/20261127-0650-reuse-rule/plan_v3.4.tex#L63)) and applies unchanged to Phase 2 ([plan_v3.4.tex](file:///root/neon_work/20261127-0650-reuse-rule/plan_v3.4.tex#L197)). Since 11(a) blocks open definition findings, deferring "V-C on unused statements" (11(d)) is either vacuous or a loophole letting definition-level V-C leak downstream.
- **Double standard with Phase 1’s audit:** Phase 1’s main evidence relies heavily on V-C (63 confirmed pairs, [plan_v3.4.tex](file:///root/neon_work/20261127-0650-reuse-rule/plan_v3.4.tex#L76)). Treating V-C as a headline violation when grading auditors in Phase 1, then waiving confirmed V-C as non-blocking in Phase 2, invites reviewers to question V-C’s validity.
- **Broken Phase 1 / Phase 2 comparability:** Phase 2 gives translators HOL4 proofs, samples Neon’s review, and defers fixes based on future imports. Post-repair defect rates are therefore incomparable to Phase 1 unless pre-repair audit scores are logged under the exact Phase 1 contract.

### 2. What should change (what, why, cost)

1. **Block confirmed V-P on *all* manifest theorems.** *Why:* Prevents shipping wrong leaf or target theorems. *Cost:* 0–1 repair round; negligible tokens (Phase 1 Candle baselines had 0 V-P found) against the 7.7B-token core estimate ([plan_v3.4.tex](file:///root/neon_work/20261127-0650-reuse-rule/plan_v3.4.tex#L212)).
2. **Block confirmed V-C everywhere; defer only `unsure` and verified tier-2 choice cases on unimported statements.** *Why:* Restores consistency with 11(a), removes the Phase 1/Phase 2 double standard, and fixes base definitions once rather than reopening frozen milestones. *Cost:* ~1 early repair round on shared definitions plus targeted re-audits (~219k Astra tokens/module, [readiness_astra_migration_2026-11-27.md](file:///root/neon_work/20261127-0650-reuse-rule/readiness_astra_migration_2026-11-27.md#L41)).
3. **Add S0 and post-proof kernel checks to 11(c).** Block statement/type-variable mismatches against the HOL4 export, vacuous statements, bodyless definitions, unapproved transitive axioms, and remaining `sorry` after proving. *Why:* Astra missed 4 selected errors S0 caught, and S0 found 40 key errors ([readiness_astra_migration_2026-11-27.md](file:///root/neon_work/20261127-0650-reuse-rule/readiness_astra_migration_2026-11-27.md#L37)); sampled Neon review cannot catch misses. *Cost:* 0 script tokens; ≤1 repair round per catch.
4. **Log pre-repair Phase 2 audit findings under the full Phase 1 contract.** *Why:* Preserves Phase 1/Phase 2 comparability (V-P and V-C separate). *Cost:* 0 rounds, 0 tokens.

### 3. Stating known issues accurately

- **Paper:** Keep the no-certification framing ([plan_v3.4.tex](file:///root/neon_work/20261127-0650-reuse-rule/plan_v3.4.tex#L23)), note Phase 1 uses no reuse gate, and—where Phase 2 is discussed—report pre-repair audit counts separately from post-gate release status, placing deferred-item counts in Limitations ([plan_v3.4.tex](file:///root/neon_work/20261127-0650-reuse-rule/plan_v3.4.tex#L251)).
- **README:** Replace unqualified "faithful migration" with *"audited and kernel-checked against the saved-theorem contract, with zero open blocking defects and a public known-issues register."* Publish a per-milestone table giving declaration, class, downstream-import status, witness status, and resolution commit.

### 4. Preferred rule (≤5 lines)

1. **Block reuse/release:** any open or confirmed finding (V-P, V-C, `unsure`) on a definition, datatype, or inductive; any confirmed V-P or V-C on any manifest theorem; any S0, structural, transitive-axiom, or post-proof `sorry` failure.
2. **Known issues (non-blocking until imported):** verified tier-2 choice cases and `unsure` items on unimported theorems, plus naming/style notes.
3. **Escalation & cap:** importing a deferred item makes it immediately blocking; allow ≤3 repair rounds, halting release rather than demoting remaining blockers.
4. **Evidence:** every repair or dismissal requires a checked Lean/HOL4 witness or author tie-break, never model agreement alone.
