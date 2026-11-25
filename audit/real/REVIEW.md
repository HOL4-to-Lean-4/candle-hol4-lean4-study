# Review of audit findings

An auditor compared the Lean 4 module `@MODULE@` with its HOL4 source and reported the findings at the end of this message. Decide for each whether it is a true violation of the contract.
Judge only these findings. They can be right or wrong; check each against the files yourself.

- **V-P (preservation):** the Lean declaration does not have the meaning of the HOL4 one under the type mapping visible in the Lean library modules: a definition that differs on some input,
  or a statement that is weaker, stronger, a special case, false, vacuous or trivially true when the HOL4 one is not.
- **V-C (conservativity):** Lean proves a specific equation, about a constant in the mapped vocabulary, that the theorems HOL4 saves about that constant leave open.
- Not a violation: a different but equivalent formulation, a faithful choice of representation, auxiliary lemmas, missing proofs, style.

Files (working directory, read-only, stay inside it): `lean/`, `hol4/package/`, `hol4/HOL4-src/`. You can only read files.

Your final message is one JSON object and nothing else:

{"verdicts": [{"id": "F1", "verdict": "accept" or "reject", "class": "V-P" or "V-C" or "none", "reason": "<at most 80 words>"}]}

Findings:

