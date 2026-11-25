# Gemini Neon: decision on the critique findings

Model: `gemini-4-neon-high` through `agy --sandbox --mode plan`, 23-24 Nov 2026. Input: `critique_2026-11-23.md` and plan v3.2. Usage: input 28,918; output 33,451 (thinking 31,311); cache read 34,607. I1-I8 are the report section 1 items, C1-C9 the section 4 items.

---

| ID | Decision | Priority | Reason | Exact change |
|---|---|---|---|---|
| I1 | accept | before freeze | §2/§7 circularly claim zero defects via single-family audits and overclaim "certification"; proofs catch only overly strong statements. | — |
| I2 | accept | before freeze | Without a fidelity contract, `HD []`, type-signature, and `[Nonempty]` labels contradict baselines and break scoring. | — |
| I3 | accept with change | before freeze | S4/S5 confound family, stage, grounding, and spend vs S3; S1–S3 also differ in tool access. | S5 only filters S4's accepted set (precision gain unguaranteed); note S1's tool advantage. |
| I4 | accept | before freeze | 36 clustered mutants over 13 subtypes (~2.8/type; 36/36 bound 90.3%), coached briefs, and missing rubrics weaken inference. | — |
| I5 | accept with change | before freeze | Missing ITP insight, related work, and kernel-export baseline miss the venue bar; kernel export dissolves 3/4 of §6's oracle questions. | §1 states the FormaliSE delta; add ITP insight/kernel export pre-freeze, related work post-freeze. |
| I6 | accept | before freeze | §1/§4/§5 overclaim the oracle: `#eval`/`decide` fail on `Classical.epsilon`/quantifiers, failed proofs aren't refutations, and rejected findings stay ungrounded. | — |
| I7 | accept with change | before freeze | 12 weeks (23 Nov–15 Feb) cannot hold two provers and two proving rounds; 25 Jan tests the wrong milestone. | §3 puts Phase 2 post-paper; cut Astra prover, round-2 proving, extrapolation, and unrun Sonnet arm. |
| I8 | accept with change | before freeze | Author input in briefs/mutants/checks is unlogged and `Define`/`Prim_rec` needs precision, though §13 separates design from adjudication. | Log effort; state "no human adjudication"; fix "three/independent" outside `plan.tex`; probe optional. |
| C1 | accept | before freeze | Evidence-backed audit framing resolves I1 and supplies the ITP contribution and FormaliSE delta. | — |
| C2 | accept with change | before freeze | A frozen fidelity contract must precede labels, but C2 misstates `HD []` semantics. | Define preservation + conservativity; classify `HD [] = default` by conservativity (adds non-HOL4 equations, not false theorems). |
| C3 | accept with change | before freeze | Matched controls and one contrast are vital, but C3 conflates tool access with scripted grounding and underuses reuse. | Core: S0, S1, S3, S4, S5 (Neon), S1+grounding, S6 (reuses S3), free 2-run Opus union; drop S2; separate tool access from scripted grounding; contrast S5 vs S6+grounding. |
| C4 | accept with change | before freeze | Witnessed, tagged, too-weak mutants, held-out classes, and checked decoys are vital, but 1-mutant whole-package copies blow budget. | Use ≤1 mutant/module (module audits or non-interacting bundles); drop whole-package 1-mutant and dual runs. |
| C5 | accept with change | before freeze | Matching rules, false-accusation metrics, clustered CIs, and pilot sizing are needed, but 3× whole-package repeats and a second scorer over-reach. | Favor independent module mutants over 3× whole-package repeats (3× on variance subset); second scorer optional. |
| C6 | accept with change | before freeze | Grounding rejected findings, bounding decidability, keeping `unresolved`, and kernel export fix I5–I6 cheaply. | Restrict kernel export to S0/reference (not translator input) to isolate LLM audit value. |
| C7 | accept with change | before freeze | Cutting non-core proving arms and moving go/no-go to early January protects the primary experiment and funds C3–C6. | Run Claude proving on the clean/repaired base (not "mutant base"), definitions/statements frozen; defer outline post-freeze. |
| C8 | accept with change | before freeze | Pins, effort logs, run baselines, and motivating-example fixes belong at freeze; extra arms and submission checks do not. | Pin CLI versions, log effort, fold baselines, fix `Define`/`Prim_rec`, disclose proof-visible translation (no proof-hidden arm); anonymisation post-freeze, probe optional. |
| C9 | accept | after freeze | Cited literature (HOL importers, autoformalization, mutation validity, diversity, LLM-as-judge) is needed for ITP, not freezing. | — |

### Rejected or weakened claims

- **Run-count contradiction (§3 vs C3–C5):** §3 rejects 7×6×3 = 126 runs as infeasible, yet C4 (1 mutant/package + multi-mutant + isolation/package) plus C5 (≥3 repeats/package) demands ≥216 full-package LLM scans (36×3×2, ~$1,944) before clean/secondary runs. Conversely, S6 reuses S3's scan and 2-run Opus union is free from S3 repeats; `plan.tex`'s "30 audits" also overcounts full scans (18, since S4/S5 reuse S1).
- **Fidelity logic (C2):** Fixing underspecified `HD []` to a default is a valid model and will not falsify HOL4 theorems; it violates *conservativity* by making extra non-HOL4 equations provable.
- **Monotonicity & tool confound (I3/C3):** Grounding only accepted findings cannot guarantee higher precision (dropping a true positive lowers recall and can cut precision); §6 already gives S1 the HOL4 tool, conflating interactive tool access with scripted grounding.
- **Plan mismatches (I5, I7, I8, C7):** `plan.tex` puts Phase 2 post-paper (§3), states the FormaliSE delta (§1), separates design from adjudication (§13), and says "Two Claude auditors" (§2), never "three/independent"; C7's "mutant base" misnames the clean/repaired base. (I4's 36/36 Clopper–Pearson bound, 90.3%, and 12-week span check out.)
- **Over-reach & missing dependencies:** C5 assumes an unbudgeted second expert; C8's proof-hidden arm contradicts C7; grounding rejected findings (C6) breaks I3's `recall(S5) ≤ recall(S4)`; kernel-export visibility (C6) changes S0 vs S1/S3 (C3).

### Minimal set (before freeze, ordered)

1. **Reframe & cut scope (C1, C7):** Adopt evidence-backed audit framing; cut Astra prover, round-2 proving, extrapolation, unrun Sonnet arm; move go/no-go to early January on primary data. *(Funds/scopes all steps.)*
2. **Freeze fidelity contract (C2):** Define preservation + conservativity (`HD []`, `ARB`/choice, `[Nonempty]`, unused binders, finite maps); re-score baselines. *(Depends on 1.)*
3. **Add kernel export & bound oracle (C6):** Export typed HOL4 statements for S0/reference only; bound decidability + `unresolved`; ground rejected and accepted findings. *(Depends on 2.)*
4. **Lock setups & contrast (C3):** Fix core arms (S0, S1, S3, S4, S5, S1+grounding, S6, free 2-run Opus union); separate tool access from scripted grounding; drop S2; contrast S5 vs S6+grounding. *(Depends on 1, 3.)*
5. **Build module-isolated mutants (C4):** Reclassify mutants/decoys; add too-weak and 2–3 held-out classes with witnesses/tags; ≤1 mutant/module plus clean modules. *(Depends on 2, 3.)*
6. **Freeze scoring & pilot size (C5):** Fix declaration+class matching, false-accusation metric, reason rubric, clustered CIs, and pilot sizing. *(Depends on 4, 5.)*
7. **Lock pins, logs & disclosures (C8):** Pin CLI/model versions, start effort log, fold baselines, fix `Define`/`Prim_rec`, disclose proof-visible translation. *(Parallel; finalizes freeze.)*
