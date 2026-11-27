<!-- Reply of gpt-6.2-astra (reported by the gateway; codex exec via SSS gateway, read-only, high effort) to readiness_prompt_migration_2026-11-27.md, on clones study@7a2648a and cakeml-lean4@733fa18. Unedited. 777,359 input tokens (697,728 cached), 6,574 output (864 reasoning), 207 s. -->

**Start preparing milestone 1 now. Hold the first translation until its source closure, acceptance rules and isolation check are frozen.** The cloud tools have been exercised. The migration checkout contains 11 files, including directory descriptions and a ledger header, but no executable milestone. [Cloud results, lines 13–25 and 47–64](study/CLOUD.md:13) · [Migration layout, lines 24–32](cakeml-lean4/README.md:24)

### M1. Method — NOT READY

**Blocking.** The author can settle the following in about half a day. The two translations, full-script translator access, module-level audits, Opus-only repair and proof, and cost report are decided. The three-round loop is explicitly deferred. Its requirement that Neon accept every edit is incompatible with sampling unless someone can accept unsampled findings. [Phase 2, lines 199–210](study/plan/v3/plan_v3.4.tex:199) · [Loop and open decisions, lines 214–238](study/plan/v3/plan_v3.4.tex:214)

- Freeze two-stage briefs and the audit packet: one module, corresponding HOL4 sources, read-only neighbouring modules, and a declaration coverage record. Give Neon a reproducible sampling rule across both translators and finding classes. Fix the realized count after findings exist, as planned. [Translation brief, lines 7–27](study/baselines/ts_runs_v2/run/briefs/lessons_stage1.md:7) · [Audit brief, lines 16–32](study/audit/real/BRIEF_audit.md:16)
- Name the decision-maker for unsampled, disputed and script-only findings. Require a checked witness for accepted repairs, re-scan and re-audit affected declarations and dependents, and return proof-exposed defects to review. Set a stopping rule. I suggest three rounds, with outstanding material defects recorded as blocking release at the cap. [Fidelity test, lines 68–76](study/plan/v3/plan_v3.4.tex:68) · [Repair and stopping, lines 222–227](study/plan/v3/plan_v3.4.tex:222)

**Not blocking.** A second S1 run and the remaining Phase 1 discovery and tier-2 checks can proceed separately. [Open items, lines 231–238](study/plan/v3/plan_v3.4.tex:231)

### M2. Repository — NOT READY

**Blocking.** Author plus scripts, roughly one to two engineering days, subject to the upstream build.

- Pin CakeML, HOL4, Poly/ML, Lean and Batteries. `080a3bd` is the size-estimate revision. Generate the milestone manifest from the chosen build, including qualified declarations, source paths, dependency order and batches. Create one mirrored Lake layout with separate Sonnet and Opus worktrees and a root importing every milestone module. [Estimate, line 3](cakeml-lean4/plan/token_estimate_2026-11-27.md:3) · [Vendor, line 2](cakeml-lean4/vendor/README.md:2) · [Manifest, line 2](cakeml-lean4/manifest/README.md:2) · [Lake project, line 2](cakeml-lean4/lean/README.md:2)
- Port the briefs, typed export, statement and type-variable scans, kernel checks, grounding, cloud launchers and ledger writer. The query tool hard-codes Candle. Build a fresh prover workspace from allowed inputs, strip proof-bearing comments, deny access to source trees and prior proofs, and test that planted proof text fails preflight. The old scanner examines Lean comments and top-level Markdown and merely prints its count. [Workflow, line 2](cakeml-lean4/workflow/README.md:2) · [Query tool, lines 18 and 62–64](study/tools/hol4_query/hol4q.py:18) · [Scanner, lines 69–87](study/proving_nohol4/prooftext.py:69)

**Not blocking.** The whole-development manifest and later batch plans can wait.

### M3. First milestone — READY WITH CONDITIONS

**Blocking.** Author chooses the upstream pin and confirms the root, about one hour. `typeSound.semantics_type_sound` is a good calibration target with a known proof-only baseline. I counted 267 theorem rows, 255 definitions, 56 datatypes and four inductives across 20 theories. The reduced `semantics_min` deliberately removes parser dependencies. Reconcile the historical manifest against the pinned upstream closure, including local names and library dependencies. The historical export modifies scripts and uses `--fast`, which replaces tactics with `cheat`. [Target, line 268](study/baselines/ts_runs_v2/run/TARGETS.tsv:268) · [Reduction, lines 2–4](study/package_ts/semantics_minScript.sml:2) · [Export, lines 5–10](study/tools/hol4_query/out_ts/exp_ts3.sh:5) · [HOL4 option, line 297](study/vendor/HOL/tools/Holmake/core/HM_Core_Cline.sml:297)

**Done** means both translations cover the manifest, build, pass structural checks and receive audits, with exactly the targets admitted before proving. The repaired Opus closure must rebuild with frozen statements and definitions, zero `sorry`, only approved transitive axioms, and all findings dispositioned. Commit, push and publish cost. **Not blocking.** Candle and parser completeness are later milestones. [Kernel-check precedent, lines 19–25](study/proving_nohol4/RESULTS.md:19) · [Milestone order, lines 6–13](cakeml-lean4/README.md:6)

### M4. Cost and scale — READY WITH CONDITIONS

**Blocking.** A script author needs a few hours to wire per-call accounting before launch. I reproduced the ledger’s **602.2M tokens, $418.18 API-equivalent**, and the two translation rates and proof rate. The historical type-soundness combination alone was **120.5M Claude tokens, $64.90** before audit and repair. The **7.7B/$4,100** core projection suffices to justify calibration. Two logic closures with one run per cell give little basis for forecasting compiler proofs. [Ledger, lines 10–51](study/ledger/costs.csv:10) · [Estimate, lines 50–72](cakeml-lean4/plan/token_estimate_2026-11-27.md:50)

Measure new versus reused declarations, modules and source lines, tokens by cache category and stage, billed and equivalent dollars, elapsed and human time, quota waits, findings sampled, repair rounds and failed proof attempts. **Not blocking.** A whole-project budget cap. [Ledger schema, line 1](cakeml-lean4/ledger/costs.csv:1)

### Higher-priority gate. Fidelity of reused definitions — READY WITH CONDITIONS

**Blocking.** Author, about one hour to assign acceptance authority independent of my verdict, with checked evidence before reuse. I was S1 and helped choose fidelity rules. I missed four selected errors. S0 found all four, and 40 errors entered the key through S0. Neon accepted my false `store_ffi` finding. A sampled review cannot detect my omissions. **Not blocking.** Reopening the saved-theorem decision. I counted 42 recheck entries covering 63 pairs and confirmed the struck `FAPPLY` witness has a surviving replacement. [Audit, lines 21–26 and 45–47](study/audit/real/RESULTS.md:21) · [Conflict, line 47](study/plan/v3/critique_astra_decisions_2026-11-24.md:47) · [Recheck, lines 9 and 34](study/audit/real/vc_recheck/RECHECK.md:34)

### Errors found

- The estimate divides selected-module audit cost by 1,913 whole-translation theorems and says seven translations. There were eight. Use approximately 219k tokens per audited module and price Neon by sampled workload. Its 7.8M reported tokens and 52.8M ledger tokens use different cache conventions. [Estimate, line 17](cakeml-lean4/plan/token_estimate_2026-11-27.md:17) · [Audit, lines 7 and 54](study/audit/real/RESULTS.md:7) · [Ledger, line 48](study/ledger/costs.csv:48)
- Listed script lines sum to 917,938. At one to two windows per $22, $3,100 implies roughly 141–282 windows. [Estimate, lines 25–48](cakeml-lean4/plan/token_estimate_2026-11-27.md:25)
- Local execution and the pending gateway smoke test are stale. The plan also says both translations finish before audit, while the decision permits independent starts. [README, line 19](cakeml-lean4/README.md:19) · [Decisions, lines 15 and 29](cakeml-lean4/plan/DECISIONS.md:29) · [Plan, line 210](study/plan/v3/plan_v3.4.tex:210)

### Smallest path to starting

1. Choose the pin and root.
2. Build HOL4 normally, export and reconcile the closure.
3. Freeze batches, briefs, sampling and release rules.
4. Create both worktrees and wire checks and accounting.
5. Exercise one module end-to-end, including isolation failure, then launch the first batch.

**Author decisions.** Which CakeML revision anchors the migration? Who settles disputed or unsampled findings? Which unresolved classes prevent reuse?

I checked local files and arithmetic. I could not verify Git identities from these snapshots, replay builds or models, or independently recount upstream CakeML. I used no network, raw transcripts or withheld scoring keys.