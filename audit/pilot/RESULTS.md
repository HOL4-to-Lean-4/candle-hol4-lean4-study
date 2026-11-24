# Audit pilot (24 Nov 2026)

Draft. 10 units: 6 mutants (witnessed; one held-out operator, one V-C), 2 decoys (proved equivalent in Lean, `proofs/`), 2 untouched modules. Units were sampled with a fixed seed; the design choices are Claude's.
Each unit is one module of the comment-stripped repaired Candle base in its own folder with a random name; the key is `key.json`. Auditors could only read files (deviation from the plan: no query tool, for any arm). S2 (Neon alone) was not run.

| Arm | 6 mutants found | 2 decoys flagged | 2 untouched modules flagged | Cost per unit (list price) | Time per unit |
|---|---|---|---|---|---|
| S1 Astra | 6 | 0 | 0 | subscription quota | 47 s |
| S3 Opus, run a | 6 | 0 | 1, a true finding (below) | $0.66 | 72 s |
| S3 Opus, run b | 6 | 0 | 0 | $0.68 | 74 s |
| S4 Astra, reviewed by Neon | 6 of 6 accepted | 0 | 0 | subscription quota | 60 s per reviewed unit |
| S6 Opus a, reviewed by Opus | 7 of 7 accepted | 0 | 1, the same | $0.24 per reviewed unit | 19 s |

Declaration and class were matched by reading the findings (main session); this is not the blinded human scoring. S5, S6g and S7 made the same decisions as S4, S6 and S1, because grounding contradicted nothing.

## What the pilot shows
1. **Ceiling.** Every arm found every mutant. With no disagreement between arms, the primary contrast (S5 against S6g) has nothing to measure on mutants like these. Six of six gives a one-sided 95% lower bound of about 61%, so the
   sample is small, but harder cases are needed before a main run is worth its cost.
2. **An untouched module had a violation.** Opus run a flagged `interprets0` (`HolSemantics`): HOL4's constant is polymorphic in two more type variables than the Lean definition. Confirmed with the HOL4 query tool:
   `interprets0 : ('a -> 'a -> bool) -> ('b -> 'a list -> 'c) -> 'b -> mlstring list -> ('a list -> 'c) -> bool`. By the adopted rule (a proper type specialisation is V-P) it is a true finding.
   Astra and the second Opus run missed it. It is used in one place, at the fixed instance, so no target statement changes meaning. The module is not "clean" any more.
3. **A script finds it for free.** `consts.sml` / `consts_ts.sml`, `TyVars.lean` and `tv.py` compare the number of type variables of each HOL4 constant with its Lean definition. S0 scanned statements only, so this is a new S0 step.
   Candle base: 156 constants compared, 1 differs (`interprets0`). Type-soundness translations (about 480 compared): Opus with lessons 3 (`build_ctor_tenv`, `ctMap_has_exns`, `ctMap_has_bools`), Opus without lessons 0,
   Sonnet up to 18. The name match ignores `thunk_op` (a type in Lean) and `shift_lookup` (word length is a number in Lean). The Sonnet 18 are not reviewed one by one. Counting type variables does not prove equality of types.
4. **Grounding.** Lean checks: 18 of 19 compile; the one that fails belongs to a correct finding (Astra's `REV_ASSOCD_ALOOKUP`), so a failed check is not a refutation. Auditors write the checks, and a compiling check proves only what it states:
   Opus's `interprets0` check is `⟨_, rfl⟩`. HOL4 checks: 0 of 19 with the default tactic, 7 of 19 with evaluation tactics tried afterwards (post hoc). The other 12 need case-specific tactics.
5. **Input tokens.** No single Opus call had more than 95k tokens of context (`tokens.py`). The totals above 128k (17 of 30 audit runs, maximum 385k) sum the input of all calls in a run, and each call re-sends the
   transcript (3 to 7 calls per run). New text per Opus audit is about 62k tokens, the rest is cached re-reading. Neon's 611k total is one 10-call review (largest call 97k). Codex only reports totals per run: 52k uncached tokens per run.
   Author's decision (24 Nov): no 128k cap. The 64k review cap is dropped for the same reason (Claude's reading of that decision).
6. **Isolation.** The transcript scan found 0 accesses outside the unit folder and no Lean or HOL4 execution. Codex used 98k input tokens per call by default and 9k with unneeded features disabled (pilot setting).
   Astra's reasoning-token count is low (about 190 per unit); the effort setting does change it.

## Cost
Opus $15.16 list price (audits $6.64 and $6.84, reviews $1.68). Astra 1.11M input and 11k output tokens; Neon 0.95M input (0.73M cached) and 20k output tokens; both on subscription quota.
