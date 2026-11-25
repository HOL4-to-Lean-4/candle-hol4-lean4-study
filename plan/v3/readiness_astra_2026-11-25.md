<!-- Reply of gpt-6.2-astra (codex exec, read-only, high effort, clone at 5dc4c01b) to readiness_prompt_2026-11-25.md. Unedited, except that a path prefix in its links, which does not exist on the PC, was removed. The file errors it lists were checked and corrected afterwards. 603,306 input tokens (471,296 cached), 6,190 output. -->

**Start writing now. Keep v3.2 as the adopted plan, hold the 100-unit mutant run, and develop the real-error audit as the paper’s main case study.** The more urgent gate is independent scoring: another model run cannot establish whether the existing findings deserve credit.

**Author’s first step:** complete the blinded sheet before reading the arm-level details below. I checked that all 51 verdicts and reasons are blank. I did not score any row or reconstruct the key. Save the completed sheet before running the key generator, which overwrites it. [CONTINUE.md, lines 48–51](CONTINUE.md:48)

### G1. Freeze v3.3 as written — NOT READY

**Blocking.** The author needs a dated amendment separating completed exploratory work from prospective tests. Choose the primary claim, scorer, tool access, caps and treatment of unresolved findings. The draft calls labels frozen, names no independent scorer, specifies interactive queries that neither audit provided, and makes grounded S5 versus S6g primary. Its V-C rule also requires evidence that two models of the saved HOL4 interface can disagree. A failed proof search cannot supply that evidence. **Effort:** author, about one day, plus scorer agreement. [Plan, lines 51–61](plan/v3/plan_v3.3.tex:51) · [Plan, lines 164–178](plan/v3/plan_v3.3.tex:164)

**Not blocking.** Retain the preservation/conservativity distinction and report verified Hilbert-choice cases separately.

### G2. Start the main mutant experiment — NOT READY

**Blocking.** I matched the pilot key to the findings. All three auditor runs named all six mutants. Opus alone found a genuine specialization in an untouched module. Of 19 proposed checks, 18 compiled in Lean, zero succeeded with the initial HOL4 tactic, and seven succeeded after tactics changed. There were no discordant mutant pairs from which to size the planned comparison. **Author and model runs, 1–2 days:** if pursuing this question, pilot a fresh, harder, prespecified sample and set a stop rule before launch. [Pilot results, lines 14–26](audit/pilot/RESULTS.md:14)

**Blocking.** I counted 162 witnessed, 11 equivalent and seven undecided mutants in `accepted.tsv`. The verification table marks 152 `OK` and ten `CHECK`. Prove equivalence for the selected decoys, repair or exclude affected controls, and independently check that selected witnesses establish the claimed difference. **Author, scripts and independent scorer, roughly 2–4 days.** [Mutant README, lines 104–109](audit/mutants/README.md:104) · [Plan, lines 156–162](plan/v3/plan_v3.3.tex:156)

**Not blocking.** Proving all 60 candidate decoys or clearing every flagged witness.

### G3. Use real errors as the main audit evidence — READY WITH CONDITIONS

**Blocking.** Use the audit for recall on **selected known errors**. I ran `python -B audit/real/final.py`. It reproduced 101/105 for S1, 63 and 59 for Opus, 64 for their union, 101 after Neon review and 62 after Opus review. Removing the 15 provisional statement labels gives S1 86/90 and the Opus union 59/90. One translation contributes 47/105 cases and 26 of S1’s 37 extra hits. Scripts supplied all 40 specialization cases and caught the four everyone missed. **Author and script, one day:** report S0, per-translation results, paired module-level uncertainty and sensitivity to provisional labels. [Real results, lines 9–21](audit/real/RESULTS.md:9)

**Blocking.** Claude constructed the key and adjudicated discoveries. The scorer usually accepts a declaration name alone. On the historical division case it credits both S1’s division finding and an unrelated floating-point finding on the same declaration. Neon accepted 173/174 findings, including the false one. **Independent HOL4/Lean reader, 2–4 days:** blind and check reasons for discordant hits, discoveries, disputed controls and a sample of agreements. Keep unresolved study-1 findings separate. I am the measured S1 system, and Astra helped set its own credit rules. I give S1 no family-superiority claim. Its requested model name also lacks independent backend verification. [Matcher, lines 15–31](audit/real/final.py:15) · [S1 findings, lines 163–180](audit/real/runs/28fb71c3/S1.json:163) · [Astra decision record, lines 47–59](plan/v3/critique_astra_decisions_2026-11-24.md:47)

**Not blocking.** Whole-corpus prevalence or a new reviewer arm.

### G4. Start writing — READY

**Blocking.** None. The author can write the methods, semantic examples and limits now. I counted 278 and 267 distinct proved targets in the proof-hidden progress logs. Those runs establish provability of the translated statements. The earlier runs exposed HOL4 proofs. [Proof-hidden results, lines 8–25](proving_nohol4/RESULTS.md:8)

**Not blocking.** Final tables. Distinguish the contribution from study 1 and symbolic import, and follow the venue’s AI disclosure and authorship rules. [Plan, lines 25–34](plan/v3/plan_v3.3.tex:25)

### Errors found

- `CONTINUE.md:20` predicts a key-file correction. Both `audit/real/build_units.py:48` and `key.json:220` still say `do_app`. Only `final.py:15` applies the location correction.
- `audit/real/RESULTS.md:36` says “above 116.” Its arithmetic gives **116 if all provisional labels stand**. Further unresolved reports do not establish a higher total.
- `CONTINUE.md:53–54` overlooks two proved pilot decoys and the two Opus audit draws. S1 still has only one draw.
- `baselines/ts_runs_v2/RESULTS.md:32` reverses the direction of specialization. Lean loses generality. I reproduced the final scan flags, 9/7/23, and found 267 `sorry` users in each kernel report.
- `ledger/costs.csv:44` has 22 fields under a 21-field header. The real-audit Opus metadata sum to $132.65. The “every run” description at `CONTINUE.md:36` omits about 1.07M scoring tokens documented in `baselines/ts_runs_v2/RESULTS.md:62`.

I did not replay Lean or HOL4, inspect unavailable transcripts, or verify every semantic witness.

### Strongest reviewer objection

“How much does the auditor discover beyond the scripts that selected the errors, and who checked its reasons?” A blinded rescore, an explicit S0 comparison and independently witnessed discoveries can answer that by February for these two developments. The existing runs cannot establish a general benefit from grounding.

### Plan to February

1. Finish and preserve blind scoring. Record any prior exposure.
2. Adopt the amendment and freeze the rescore rubric.
3. Adjudicate findings, rerun tables, and reconcile costs and human time.
4. **New runs required for the descriptive paper: zero.** Add one S1 repeat on a fixed stratified subset only if retaining a stability claim. Drop the main mutant run and further proving.
5. On **4 January**, narrow to witnessed cases or switch to CICM if adjudication is incomplete. Finish the anonymous artifact, abstract by **8 February**, paper by **15 February**.

**Decision for the author:** Will you make the real-error case study primary? Who can independently adjudicate disputed reasons? Has prior exposure compromised your sheet blinding?