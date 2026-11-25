You are asked to decide five open design questions of a research study. The author delegated the decisions to you. Give a decision for each, not a survey.
You are the OpenAI model gpt-6.2-astra. You are also one of the audited components (the "Astra" arm and the validator in the workflow), so where a decision touches your own arm, say so and pick what a skeptical ITP reviewer would accept.
Do not run commands or read files; decide from the text below.

## Study in short
Claude Opus 5.5 translated HOL4 theories (the CakeML/Candle soundness closure, 278 theorem statements and their definitions) to Lean 4 (statements only, proofs are `sorry`).
The paper (ITP, about February) measures how well auditing setups find translation errors, with errors seeded by scripted operators ("mutants") and meaning-preserving decoys.
Mutants have kernel-checked witnesses that they differ from the base. Planned size: 60 mutants and 20 decoys, plus clean modules, about 100 units.
Arms: S0 scripted statement scan (no model); S1 Astra alone; S2 Neon (Google Gemini, via the agy CLI) alone, only if budget allows; S3 Opus alone; S4 Astra findings reviewed by Neon; S5 = S4 plus scripted grounding
(mechanical checks of each finding); S6 Opus findings reviewed by a second Opus session, S6g with grounding; S7 Astra with grounding, S8 union of two Opus runs. Primary contrast: S5 against S6g on pooled recall and false accusations. First 12 units run three times.
So there are roughly 100 + 24 Astra runs in S1 and 124 short Neon reviews (S4), and optionally 124 Neon audits (S2). One audit unit is one Lean module of 100 to 1,200 lines with the matching HOL4 source.
Claude-side runs have no limit. Cost evidence so far: one Astra critique of a 60 KB text used 104k input and 5.4k output tokens (3k reasoning); one Neon critique used 29k input and 33k output (mostly thinking). The Codex workspace has its own spend cap, which stopped one earlier run. Neon is billed to the author through agy.

## Fidelity contract (draft)
- Preservation violation (V-P): the Lean statement differs from the HOL4 statement so that it asserts a different theorem: too strong, too weak, wrong quantifier, operator, type.
- Conservativity violation (V-C): a Lean definition makes an equation about mapped constants provable that HOL4 does not prove. Example: `HD [] = ARB`; HOL4 proves nothing about `HD []`. The author has already decided that this is a violation.
  Draft reading of "what HOL4 proves": facts provable from the theorems that HOL4's theories save (not from primitive definitions that are not saved).
- Tier 1: an extra equation between mapped constants with no choice term. Tier 2: an equation whose proof needs a Hilbert-choice term, e.g. `select (fun _ => False) = ARB`, or a constant encoded as `Classical.epsilon` of its specification.
- HOL4's own `@` and `ARB` exist in HOL4 as constants, with `ARB` having no axiom; a Lean encoding with `Classical.choice` gives extra facts.

## Questions
1. Tier 2. Do constants defined by Hilbert choice (tier 2) count as violations in the scored results, as a separate, milder category, or not at all? The seeded base can be made free of both tiers.
2. Who scores the audit experiment (decides whether a finding matches a seeded mutant, and whether its reason is right)? The author designed the protocol and, under the previous plan, does not adjudicate. Scoring against seeded ground truth is mechanical in the clear cases (same declaration and family, by script) and needs judgement in the unclear ones. Candidates: the author blind to arm; another human blind to arm; a script only, with unclear ones reported as unresolved; a model scorer (Neon, Opus or Astra), with or without a human sample check.
3. Spending limits for Astra and for Neon in the audit runs. Give a number or a rule (tokens or US dollars, per unit and total) and what to do when it is reached.
4. Confirm or change the reading that V-C is measured against facts provable from theorems that HOL4 theories save.
5. Does fixing a type that HOL4 leaves polymorphic (a Lean statement that is a proper instance of the HOL4 theorem, because a type parameter was replaced by a concrete type) count as a preservation violation? Observed: 16 of 267 statements in one translation (Sonnet 5.5), 2 or fewer in the two Opus ones. Contract wording so far: "too weak" is V-P; a type deviation on an unused binder is only a note.

## Output
For each question: **Decision** (one or two sentences, implementable), **Reason** (at most three sentences), **Reporting rule** (one sentence: how the paper states it). Then: **Conflicts** (where your decision touches your own arm), and **Confidence** per question (high, medium, low). At most 700 words.
