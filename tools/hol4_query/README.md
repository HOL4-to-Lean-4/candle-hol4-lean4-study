# HOL4 query tool and typed statement export

Needs the pinned HOL4 and package built in WSL (`~/candle_build/repo`, `sh scripts/build.sh native`, about 16 min on this PC, 24 Nov 2026).

- `export_statements.sml` + `targets.sml` (generated from `TARGETS.tsv`): run inside the built package directory with `hol run export_statements.sml`. Prints each of the 278 target theorems as a raw kernel term (`Var`/`Const`/`Comb`/`Abs` with every type explicit, `Theory$name` constants), so no parser or overload setting affects it, plus the pretty form with `show_types`.
- `postprocess.py`: writes `out/statements.jsonl` and `out/statements_pretty.txt` from `out/export.raw` (the exporter's output; delete `export.raw` after). Checks that each conclusion and hypothesis has type bool and every application is well typed. Result on 24 Nov 2026: 278 statements, 0 missing, 0 with hypotheses, 0 ill-typed; `statements.jsonl` sha256 `fa815082fd50d69bfd05b3cdfea048ef49cd38e618d745d2652540ca5c74c13a`.
- `hol4q.py print|parse|eval|prove ...`: the four query kinds of plan section 6 (HOL4 as oracle). Logs every query to `out/query_log.jsonl`.
  A FAILED `prove` is not a refutation; `prove` uses `simp[]` then `metis_tac[]` unless a tactic is given, with a 90 s limit.


## Type-soundness closure (24 Nov 2026)

`out_ts/`: typed export of 267 type-soundness statements (the 269 canonical names of study 1 minus
`lookup_tenv_names` and `tenv_names_bind_var_list`, which sit inside a HOL4 comment block that starts
at `typeSysPropsScript.sml` line 2209 and are absent from the compiled theory). Built from a WSL copy of
`hol4-ultramin` at HOL4 9783a499 with `Holmake --fast`: proofs are skipped (some fail at this HOL4
version), so these statements are **elaborated by HOL4, not proved by its kernel here**. For the 37
`[local]` targets the copy drops `local` and renames duplicates (`EVERY_LIST_REL_local`,
`tveLookup_freevars_local`); `preamble.sml` loses the `set_prover` line, whose API changed.
