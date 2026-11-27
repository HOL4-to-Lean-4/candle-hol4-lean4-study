"""Write RECHECK.md: the V-C recheck of 27 November, one row per spec entry.  python make_recheck.py
Reads spec.json, results/*.json (vcheck.py) and logs/{spec_manual,arb_value_ts,arb_value_candle,saved_ts}.log (run_sml.py)."""
import collections, glob, io, json, os, re

H = os.path.dirname(os.path.abspath(__file__)) + "/"
S = json.load(io.open(H + "spec.json", encoding="utf-8"))
R = {}
for f in glob.glob(H + "results/*.json"):
    r = json.load(io.open(f, encoding="utf-8"))
    R[(r["entry"]["key_decl"], r["entry"]["family"], tuple(r["entry"]["translations"]), r["entry"]["P"])] = r
MAN = {}
for f in ("spec_manual", "arb_value_ts", "arb_value_candle", "saved_ts"):
    for l in io.open(H + "logs/%s.log" % f, encoding="utf-8"):
        m = re.match(r"(PROVED|FAILED) (\S+)", l)
        if m:
            MAN[m.group(2)] = (m.group(1), f + ".sml")

# How HOL4 introduces the constant at kernel level (source lines in HOL4 / CakeML), and the evidence that the varied model keeps it true.
# L: loose specification (vary the constant); A: TFL definition whose kernel definition fills the missing pattern with ARB (not a saved theorem).
INTRO = {
    "bool$ARB": ("L", "new_constant, no axiom (boolScript.sml:245)", None),
    "pred_set$CARD": ("L", "new_specification, guarded by FINITE (pred_setScript.sml:3428)", ("pred_set", "CARD_DEF")),
    "string$CHR": ("L", "type bijection: joint specification char_BIJ with ORD (stringScript.sml:25-29)", "CHR"),
    "holSyntaxLib$CLASH": ("L", "primitive recursion, one clause (holSyntaxLibScript.sml:92)", ("holSyntaxLib", "CLASH_def")),
    "holSyntaxLib$RESULT": ("L", "primitive recursion, one clause (holSyntaxLibScript.sml:88)", ("holSyntaxLib", "RESULT_def")),
    "sum$OUTL": ("L", "new_recursive_definition OUTL (INL x) = x (sumScript.sml:286); FAPPLY f x = OUTL (fmap_REP f x) is an abbreviation (finite_mapScript.sml:180) and changes with OUTL", ("sum", "OUTL")),
    "finite_map$FUN_FMAP": ("L", "new_specification, guarded by FINITE (finite_mapScript.sml:1585)", ("finite_map", "FUN_FMAP_DEF")),
    "semanticPrimitivesProps$FV_dec": ("L", "primitive recursion, no clause for Denv, Dmod, Dlocal (semanticPrimitivesPropsScript.sml:220)", ("semanticPrimitivesProps", "FV_dec_def")),
    "list$HD": ("L", "primitive recursion HD (h::t) = h (listScript.sml:138)", "HD_spec"),
    "list$LAST": ("L", "primitive recursion on h::t (listScript.sml:2124)", ("list", "LAST_DEF")),
    "misc$MAP3": ("A", "TFL definition; pattern completion gives ARB on unequal shapes (miscScript.sml:74)", "MAP3"),
    "rich_list$SEG": ("L", "new_specification (rich_listScript.sml:285); SEG (SUC m) k [] is open", "SEG"),
    "option$THE": ("L", "new_recursive_definition THE (SOME x) = x (optionScript.sml:176)", ("option", "THE_DEF")),
    "semanticPrimitivesProps$dest_Refv": ("L", "primitive recursion, one clause (semanticPrimitivesPropsScript.sml:165)", ("semanticPrimitivesProps", "dest_Refv_def")),
    "holSyntax$dest_var": ("L", "primitive recursion, one clause (holSyntaxScript.sml:57)", ("holSyntax", "dest_var_def")),
    "integer$int_div": ("L", "new_specification, guarded by j <> 0 (integerScript.sml:1989)", ("integer", "int_div")),
    "integer$int_mod": ("L", "new_specification, guarded by j <> 0 (integerScript.sml:2074)", ("integer", "int_mod")),
    "location$locnrow": ("L", "primitive recursion on POSN (locationScript.sml:6)", ("location", "locnrow_def")),
    "location$locncol": ("L", "primitive recursion on POSN (locationScript.sml:16)", ("location", "locncol_def")),
    "location$locn_rowupdate": ("L", "primitive recursion on POSN (locationScript.sml:11)", ("location", "locn_rowupdate_def")),
    "location$locn_colupdate": ("L", "primitive recursion on POSN (locationScript.sml:20)", ("location", "locn_colupdate_def")),
    "holSemantics$termsem0": ("A", "TFL definition; pattern completion gives ARB for Abs of a non-variable (holSemanticsScript.sml:134)", "termsem"),
    "typeSysProps$type_def_to_ctMap": ("A", "TFL definition; pattern completion gives ARB for tds = [], ids non-empty (typeSysPropsScript.sml:1502)", "tdc"),
}
CHR_P = {"n = 256": "CHR_256", "n = 256 \\/ n = 257": "CHR_256_257", "n = 300 \\/ n = 301": "CHR_300_301"}
ARBV = {"MAP3": {"(l1 = [] /\\ ~(l2 = []) /\\ l3 = []) \\/ (~(l1 = []) /\\ l2 = [] /\\ l3 = [])": ["MAP3_a", "MAP3_b"],
                 "l1 = [] /\\ ~(l2 = []) /\\ l3 = []": ["MAP3_a"], "~(l1 = []) /\\ l2 = [] /\\ l3 = []": ["MAP3_b"]}}

rows, cnt, pairs = [], collections.Counter(), collections.Counter()
for e in S:
    r = R.get((e["key_decl"], e["family"], tuple(e["translations"]), e["P"]))
    cat, intro, ev = INTRO[e["hol_const"]]
    if ev is None:
        evid, ok = "no axiom mentions ARB; the type `itself`, defined from ARB (boolScript.sml:4481), is reinterpreted with it", True
    elif isinstance(ev, tuple):
        hit = [x for x in r["results"] if x[0] == ev[0] and x[1] == ev[1]]
        ok = bool(hit) and hit[0][3] not in ("FAILED",) and not hit[0][3].startswith("ERROR")
        evid = "`%s` with the replacement: %s (vcheck.py)" % (ev[1], hit[0][3] if hit else "not found")
    else:
        names = {"CHR": [CHR_P.get(e["P"])], "SEG": ["SEG_spec", "SEG_witness_fails"],
                 "MAP3": ["MAP3_def"] + [x.replace("MAP3_", "MAP3_open_") for x in ARBV["MAP3"].get(e["P"], ["MAP3_missing"])],
                 "tdc": ["type_def_to_ctMap_def", "eq_len", "ctMap_ok_type_defs", "mem_type_def_to_ctMap", "type_def_to_ctMap_mem", "tdc_open"],
                 "termsem": ["termsem0: 13 saved theorems, and satisfies (defined from termsem0), not checked"]}.get(ev, [ev])
        ok = all(n in MAN and MAN[n][0] == "PROVED" for n in names)
        evid = ", ".join("`%s` %s (%s)" % (n, MAN[n][0].lower(), MAN[n][1]) if n in MAN else "`%s` missing" % n for n in names)
        if ev == "SEG":
            evid += "; SEG' m k l = TAKE m (DROP k l) ++ REPLICATE (m - (LENGTH l - k)) a"
    v = "V-C" if ok else "unsure"
    cnt[v] += 1
    pairs[v] += len(e["translations"])
    sup = "%d of %d" % (r["proved"], r["relevant"]) if r and r["relevant"] is not None else "not run (argument type did not parse)"
    wit = []
    for t in e["translations"]:
        ws = [w for w in e["witnesses"] if w["translation"] == t]
        live = [w for w in ws if not w.get("recheck")]
        wit.append("%s: `%s`%s" % (t, (live or ws)[0]["eq"].split(" (stated")[0].replace("|", "\\|")[:90],
                                    "" if len(live) == len(ws) else " (struck: `%s`, %s)" % (ws[[w.get("recheck") is not None for w in ws].index(True)]["eq"].replace("|", "\\|"), [w["recheck"] for w in ws if w.get("recheck")][0])))
    rows.append("| %s | %s | %s | `%s` | %s | %s | %s | %s | %s |" % (e["key_decl"], e["family"], ", ".join(e["translations"]), e["P"].replace("|", "\\|"), intro, evid, "<br>".join(wit), sup, v))

out = ["# V-C recheck (27 November 2026)", "",
       "Plan v3.4, section 3, asks that every counterexample behind a V-C label respect the saved HOL4 theorems and their dependencies, and that the label stay `unsure` where this is not verified. "
       "This file checks the %d HOL4 counterexamples behind the %d V-C (declaration, translation) pairs of the key." % (len(S), sum(len(e["translations"]) for e in S)), "",
       "## Result", "",
       "| Verdict | Entries | Pairs |", "|---|---|---|"] + ["| %s | %d | %d |" % (k, cnt[k], pairs[k]) for k in ("V-C", "unsure")] + ["",
       "- **V-C** (%d pairs): the counterexample is a model of the HOL4 theory, so every saved theorem holds in it, and the Lean equation fails in it." % pairs["V-C"],
       "- **unsure** (%d pair): `termsem0` (candle_opus). Not counted as V-C; unresolved in the tables (`key.json`, field `recheck`; key as run: `../TABLES_pre_recheck.md`). The new error `termsem0` (candle_fable) is unsure for the same reason." % pairs["unsure"],
       "", "## Method", "",
       "1. How each constant is introduced was read from the HOL4 and CakeML sources and from HOL4's definition code (`Defn.prim_mk_defn`, src/tfl/src/Defn.sml:1281). "
       "A one-argument pattern definition over a datatype goes through `Prim_rec.new_recursive_definition`, a `new_specification`: the missing cases are left open (loose). "
       "A multi-argument or nested pattern definition goes through TFL, which fills missing patterns with `ARB` (Pmatch.sml) in the kernel definition `f = WFREC R (\\f a. case a of ... => ARB ...)`; this kernel definition is not among the saved theorems.",
       "2. Loose (L): the counterexample replaces the constant c by c' = (\\x. if P x then g x else c x), with g arbitrary (for SEG a different closed form, since its specification ties the open values together). "
       "HOL4 proves, for every g, that c' satisfies c's specification. Constants defined later from c are reinterpreted by their own definitions (a constant definition fixes them; a later specification is met by some witness, because its existence theorem holds in the new model). "
       "Then the new interpretation is a model of the HOL4 theory, so every saved theorem holds in it (soundness of HOL with loose specifications; Candle proves this for its own kernel). The Lean equation e fixes c inside P, so it fails for a suitable g.",
       "3. TFL constants (A), reference = the saved theorems (author, 27 November): the kernel definition, which fixes the missing cases to ARB, is not a saved theorem and does not count. "
       "The counterexample is a constant defined by the saved clauses plus a catch-all clause with an arbitrary function g (`saved_ts.sml`). HOL4 proves every saved theorem that mentions the constant for it (MAP3: 1; type_def_to_ctMap: 4, three of them through a lemma that the replacement equals the constant when the lengths agree), and that its value on P is g. "
       "Only the constant changes, and no other saved theorem mentions it, so all other saved theorems keep their truth value. For `termsem0` the 13 saved theorems that mention it were not all proved for such a replacement, and `satisfies`, defined from it, would change too: unsure. "
       "Under the kernel reading (the alternative the author did not adopt) these equations would hold in HOL4: `arb_value_*.sml` proves c args = ARB on P for copies of MAP3, type_def_to_ctMap and termsem0 made by the same `Define`.",
       "4. Supplement: `vcheck.py` also rewrote every saved theorem that mentions c (with the ancestors; HD also changes EL) and tried fixed tactics with a 15 s limit (column \"theorems re-proved\"). "
       "A failure there is not a refutation: most failures are definitions of other constants built on c, which the model reinterprets, or tactic limits. This check alone would leave most entries `unsure`.",
       "", "## Entries", "",
       "| Key declaration | Family | Translations | P (region varied) | How HOL4 introduces it | Evidence | Lean equation falsified by the model, per translation | Theorems re-proved (supplement) | Verdict |",
       "|---|---|---|---|---|---|---|---|---|"] + rows + ["",
       "## Limitations", "",
       "- The argument rests on soundness of HOL4 with loose specifications, not on a proof of each saved theorem in the new model. The type-soundness theories here come from a fast build (`--fast`), whose proofs are not re-run; their theorems are proved in CakeML's full build.",
       "- The V-C label for the TFL constants depends on the reference: with the saved theorems (adopted) they are V-C; with the kernel definitions they would hold in HOL4 (`arb_value_*.sml`, on copies). Both readings are reported.",
       "- Varying ARB reinterprets the type `itself` with it (its carrier is {ARB}); this is a model change, not a theorem checked in HOL4.", ""]
io.open(H + "RECHECK.md", "w", encoding="utf-8", newline="\n").write("\n".join(out))
print(dict(cnt), dict(pairs))
