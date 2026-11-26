<!-- Reply of gpt-6.2-astra (codex exec, read-only, high effort, clone at f0471317) to readiness_prompt_2026-11-27.md. Unedited, except that a path prefix in its links, which does not exist on the PC, was removed. Codex reported one failed shell start (CreateProcessWithLogonW 267) during the run. 2,816,126 input tokens (2,450,048 cached), 9,760 output (1,129 reasoning). -->

**Start writing now. Keep the real-error audit as the main evidence. Do not freeze v3.4 as written.** The seven removals are justified under the kernel-theory reading. The remaining issue is whether each credited equation and each claim of a correct reason has the evidence the paper promises.

### G1. Adopt and freeze v3.4 — NOT READY

**Blocking.** The author must choose one reference theory and record when it changed. Section 3 opens by saying the missing `termsem0` case is V-C under the saved interface, then excludes that same case because the kernel fixes it. A model of the full theory suffices to refute derivability from the saved interface. The converse requires showing that the kernel definition belongs to the chosen premises. I recommend adopting the kernel reading and preserving the original analysis under its original rule. The readers received the saved-interface rule. Their answers cannot retrospectively validate the stronger test. **Author, half a day.** [Plan §3 opening](plan/v3/plan_v3.4.tex:59) · [Revised test](plan/v3/plan_v3.4.tex:76) · [Reader instructions](audit/real/check/README.md:33)

**Not blocking.** The two unresolved word cases can stay unresolved. Version 3.2 remains adopted until the author records the amendment.

### G2. Use the audit as the main evidence — READY WITH CONDITIONS

**Blocking.** Report recall on the selected key, distinguish directly checked reasons from carried-forward hits, and apply §3 to discoveries and tier 2 before calling them verified. The recheck covers keyed V-C entries. The ten remaining discoveries include eight unflagged by S0, five inherited from known errors, and only four both unflagged and non-inherited. Three of those four are V-C candidates. Give each a source-side argument or mark it unresolved. **Author plus an independent HOL4/Lean reader, 1–2 days.** [Discovery table](audit/real/TABLES.md:50) · [Recheck scope](audit/real/vc_recheck/RECHECK.md:3)

I am S1, and Astra helped choose its scoring rules. My less favourable reading is that **27 of S1’s 30 extra hits over S8 are specializations already caught by S0**, and 24 of the 30 come from `ts_sonnet`. On open values the difference is 56 versus 53, +0.05 [0.00, 0.15]. S0 plus S1 covers 98/98, S0 plus S8 covers 95/98. These runs support configuration-specific findings. They cannot establish family superiority or S1 repeatability. [Arm counts](audit/real/TABLES.md:9) · [Per-translation counts](audit/real/TABLES.md:33) · [Astra disclosure and proxy uncertainty](plan/v3/critique_astra_decisions_2026-11-24.md:47)

**Not blocking.** A second S1 run is optional. The reviewer result already merits reporting: Neon accepted 173/174 findings and removed no keyed hit.

### G3. Start writing — READY

**Blocking.** None. The author can write the methods, the `PERMUTES` example, and the account of how the recheck corrected the readers. The kernel export resolves uppercase `PERMUTES` to `BIJ`. The Lean witness separates the two predicates on a singleton. This is a concrete contribution even if later counts move. [Kernel export](tools/hol4_query/out/statements.jsonl:253) · [Lean witness](audit/real/proofs/New_sonnet.lean:18)

**Not blocking.** Final tables can follow. The author should write the submission prose and disclose AI use as specified in the [venue notes](plan/v3/plan_v3.4.tex:42).

### G4. Accept the V-C recheck — READY WITH CONDITIONS

**Method and removals.** Reinterpreting a genuinely loose constant, proving its introducing specification, and extending the model through dependent definitions is sound. Failed rewrite tactics do not refute that argument. The CHR proofs preserve the joint specification with ORD. SEG has both a replacement satisfying the recursion and a concrete failed equation. The TFL copies prove the relevant `ARB` branches for **MAP3 ×3, type_def_to_ctMap ×3, Candle Opus termsem0 ×1**. I would remove all seven and the separate Candle Fable discovery. The logs prove facts about reconstructed copies. The type-soundness build used `--fast`. [Manual proofs](audit/real/vc_recheck/logs/spec_manual.log:2) · [TS log](audit/real/vc_recheck/logs/arb_value_ts.log:65) · [Candle log](audit/real/vc_recheck/logs/arb_value_candle.log:44)

**Blocking.** The author’s rule is not fully documented per witness. In TS Sonnet, `FAPPLY FEMPTY 0 = FAPPLY FEMPTY 1` holds in HOL4: both sides are `OUTL (INR one)`. Varying `OUTL` changes both together. Strike that witness. The separate equality to `locncol EOFpt` can retain the pair. For each retained pair, identify one Lean equation and a choice that actually falsifies it after dependencies change. Mark unsupported pairs `unsure`. **Author and checker, about one day.** [Witnesses](audit/real/vc_recheck/spec.json:303) · [HOL4 definitions](vendor/HOL/src/finite_maps/finite_mapScript.sml:176)

**Not blocking.** Re-proving every saved theorem individually.

### Errors found and checks performed

- After removal of the V-C label, the name matcher accepts S1’s rejected `type_def_to_ctMap` reason against the surviving V-P label. S1 separately found the genuine V-P, so headline recall survives. The finding-level disposition is wrong. [Matcher](audit/real/final.py:28) · [Both findings](audit/real/runs/be73a930/S1.json:7)
- “Reason also right” includes unchecked hits. Only 12 of 58 agreements were sampled, one finding per sampled error. Nine rows associated with the subsequent removals received `yes`. The 8/8 controls passed their threshold, but they test recognizable type mismatches. [Sampling rule](audit/real/check/SPEC.md:11) · [Carry-forward code](audit/real/check/analyse.py:108) · [Nine rows](audit/real/check/CHECK_RESULTS_recheck.md:73)

At `f0471317`, I ran `final.py` for both keys and reproduced both complete tables in memory. S1 moved from 101/105 to 94/98. S3a/S3b/S8 stayed 63/59/64. The overall S1–S8 interval moved from +0.35 [0.16, 0.53] to +0.31 [0.10, 0.50]. I counted 93 yes, eight no, seven unsure and 1,706 estimated minutes across 108 rows. The 51-row sheet contains 17 weaker, 27 same, four note and three unsure. The fixed analysis attributes 15 weaker verdicts to provisional errors. I did not replay the private joins, transcripts, Lean or HOL4.

### Strongest objection and plan to February

**The more important January gate is transferable evidence beyond script-selected errors.** Could another reader reproduce a substantive discovery and explain what it adds over typed export, symbolic import and study 1? That objection is answerable before February for a bounded case study.

1. Reconcile §3 and freeze the dated amendment.
2. Check retained witnesses, discoveries and disputed reasons. Publish both key versions and an anonymous scoring crosswalk.
3. Correct the matcher and regenerate tables. **Zero new model runs required.** Drop further proving, mutants and the workflow loop.
4. On **4 January 2027**, retain ITP if the independent checks and transferable examples stand. Otherwise narrow the claim or use CICM.
5. Submit the author-written abstract **8 February** and paper **15 February 2027**.

**Decision for the author.** Will you adopt the kernel-theory contract explicitly? Who can independently sign off the disputed witnesses and the anonymous evidence package?
