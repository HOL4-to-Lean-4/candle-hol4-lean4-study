# Type-soundness translations (v2 runs): scoring against the v3.3 contract, 24 Nov 2026

Draft. Runs: Opus 5.5 with the lessons briefs, Opus 5.5 without, Sonnet 5.5 with lessons (complete HOL4 sources).
One run per arm, so no variance estimate. Projects: `E:/ts_ws/runs/*_v2/merged`. Run-0 (incomplete sources) was discarded before scoring.

## Build and kernel check (`KernelCheck.lean`, `*/kernel.txt`)
All three build with no errors. Each has exactly 267 theorems that use `sorry`, 0 `sorry` definitions, 0 declared axioms; the other constants use only
propext, Quot.sound, Classical.choice. 263 of 267 theorem names equal the target name; the other four (`concrete_v_list`, `tveLookup_freevars`, `type_subst`,
`EVERY_LIST_REL`) clash with definitions or duplicates and were renamed in all three runs.

## Statements against the typed HOL4 export (S0 scan, `s0/`)
| run | flags, first maps | flags, final | fitted rows or rules | flags that are real differences |
|---|---|---|---|---|
| Opus, lessons | 77 | 9 | 7 | 2 (`check_ctor_tenv_ok`, `type_env_conv_thm`) |
| Opus, no lessons | 74 | 7 | 5 | 1 (`type_env_conv_thm`) |
| Sonnet, lessons | 84 | 23 | 9 | 16 (types specialised where HOL4 is polymorphic, includes the two above) |

- `type_env_conv_thm` adds `[Nonempty]` on an unused existential type: a note under the contract.
- The 16 Sonnet statements fix type variables that HOL4 leaves free (for example `fmap` keys fixed to `num`, namespace names to `mlstring`). Each Lean statement
  is an instance of the HOL4 theorem, strictly weaker in generality. Under the contract's "too weak" they count as V-P; whether a lost type parameter
  should count when the closure never needs it is a decision for the author. The table keeps them as "real differences".
- The same five statements are flagged in all three runs (`op_type_sound`, `exp_type_sound`, two `decs_type_sound`, `is_clock_io_mono_do_app_simple`) and look like nested or wildcard
  patterns with the same meaning; one was read line by line, four by shape only.
- `do_app_cases` (all runs) and `type_op_cases` (two runs): undecided. Constant counts differ (HOL4 85 disjunctions, Lean 74/63/63). A proof of each statement from the
  definitions settles whether it is true; both are in the proving round.
- Final counts come from maps fitted after looking at disagreements; the first-map numbers are the honest starting point. Self-test on a scratch copy: 14 of 14 self-chosen statement mutations caught; the definition-body and the
  universe-level probes were missed, as expected; swapping the sides of an equality was a false positive.

## Definitions (Sonnet 5.5 scorers, one per run; witness files compiled by me)
Preservation violations found: 0 in all three runs. This is a same-family search with partial coverage, not evidence of absence:
for Sonnet the "ok" lines are generic and written in batches; Opus-lessons statements: 98 read line by line, 167 by token diff only; no-lessons `BinaryIeee` and `Real` unread.
All three scorers logged the Sonnet or Opus statements as `ok`, including the statements that S0 shows to be less polymorphic in Lean than in HOL4.
So the model reading missed what the scan found.

Conservativity, tier 1 (kernel-checked witnesses; the value is fixed in Lean, open in HOL4's saved theorems):

| constant or case | Opus lessons | Opus no lessons | Sonnet lessons |
|---|---|---|---|
| `HD []` (hence `EL` out of range) | yes | yes | yes |
| `THE NONE` | yes | yes | no `THE` in its prelude |
| `CHR n`, n >= 256 | yes | yes | yes |
| `FAPPLY` outside the domain | yes | yes | yes (`= ARB`; my own witness `extra_sonnet.lean`) |
| `int_div`, `int_mod` by 0 | yes | yes | yes |
| `CARD` of an infinite set | choice term, all infinite sets equal | choice term, all equal | **0** (`CARD UNIV = 0`) |
| `MAP3` on other shapes, `type_def_to_ctMap` on unequal lengths | yes | yes | yes |
| `locnrow`, `locncol`, `locn_rowupdate`, `locn_colupdate` off `POSN` | yes | yes | yes |
| `dest_Refv` off `Refv`; `FV_dec` on three constructors | yes | yes | yes |

Tier 2: `ARB` is `Classical.choice`, so `select (fun _ => False) = ARB` (one witness in each run).
Study-1 `CARD` defect (an enumerating list that may contain duplicates; FormaliSE paper, `main.tex` line 420): absent in all three runs, whose definitions require
`Nodup`. Fixing the value on infinite sets is a different issue. (An earlier message of mine to the author wrongly equated the two.)
Integer division (study-1 defect 2): all three runs use floored division (`Int.fdiv`); only the value at 0 is open.
Natural `DIV`/`MOD` by 0 is saved in HOL4 (`DIV_0`, `MOD_0`), so it is not a violation (Sonnet's comment that it is unspecified is wrong).

## Checks that overturned scorer findings
- `the_Litv_IntLit`, `_Word8`, `_Word64`, `_Float64`, `_Char`: two scorers called these V-C1. HOL4 saves `*_def_primitive` (found in the built theory), and
  `the_Litv_IntLit (Litv (Char #"a")) = ARB` was proved in HOL4 from it (`q2.sml`). Only that constant was proved; the other four have the same saved form. Dropped as false accusations.
- Sonnet's witness `FAPPLY FEMPTY 0 = FAPPLY FEMPTY 1` is provable in HOL4 and is not a violation; replaced by `FAPPLY FEMPTY 0 = ARB`.
- The non-recursive, single-clause constants (`locnrow`, `dest_Refv`, `HD`, ...) have only the clause theorem saved, so under "facts provable from saved theorems" (draft Φ) they stay V-C1.

## Cost (list price, from the run logs; rows in `ledger/costs.csv`)
Opus lessons $25.4, Opus no lessons $25.9, Sonnet $17.5 (stage 1 plus stage 2), run 0 (discarded) $34.5. The four Sonnet agents that scored and scanned used about 1.07 million tokens, not in the ledger.

## Not done
One run per arm. No HOL4 evaluation of definitions. The real numbers and floats are only partly read. Stage-2 agents could not write their progress log (`Write` at the workspace root is denied by the
settings I gave them), so the per-agent progress files are missing; the Lean files are unaffected.
