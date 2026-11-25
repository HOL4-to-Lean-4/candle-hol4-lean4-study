"""Tables for the real-error audit: the model-free scripts (S0) next to the arms, per translation, without the provisional statement errors,
with module-level uncertainty.  python audit/real/report.py  (writes TABLES.md; no model, no network).
S0 = the typed statement scan and the type-variable count (definitions). Their outputs: ../../baselines/ts_runs_v2/s0/results, tv/, ../pilot/consts*.tsv."""
import collections, io, json, random
import final as F
import score as s

H = s.HERE
TV = {"candle_opus": "tv_opus55_direct_translation", "candle_opus_nolessons": "tv_opus55_nolessons", "candle_sonnet": "tv_sonnet55_direct_translation",
      "candle_fable": "tv_fable52_direct_translation", "ts_opus": "tv_ts_opus_lessons", "ts_opus_nolessons": "tv_ts_opus_nolessons", "ts_sonnet": "tv_ts_sonnet_lessons"}
PK = set("misc mllist mlstring location lprefix_lub ffi fpSem namespace namespaceProps ast semanticPrimitives semanticPrimitivesProps evaluate evaluateProps "
         "semantics_min typeSystem typeSoundInvariants weakening typeSysProps typeSound".split())
REN = {"true": "true_", "false": "false_", "instance": "instance_"}
ARMS = ["S1 Astra", "S3a Opus", "S3b Opus", "S8 Opus a or b", "S4 Astra+Neon", "S6 Opus+Opus"]
TRS = list(TV) + ["study1"]
out = []
w = out.append


def tv_flags(t):
    L = {}
    for l in io.open(H + "tv/%s.tsv" % TV[t], encoding="utf-8", errors="replace"):
        c = l.rstrip("\n").split("\t")
        if c[0] == "L":
            L.setdefault(c[2].split(".")[-1], set()).add(int(c[3]))
    ts = t.startswith("ts_")
    fl, n = set(), 0
    for l in io.open(H + "../pilot/consts%s.tsv" % ("_ts" if ts else ""), encoding="utf-8", errors="replace"):
        c = l.rstrip("\n").split("\t")
        if c[0] != "CONST" or (ts and c[1] not in PK):
            continue
        nm = REN.get(c[2], c[2])
        if nm in L:
            n += 1
            if int(c[3]) not in L[nm]:
                fl.add(nm)
    return fl, n


def st_flags(t):
    p = {"ts_opus": "opus_lessons", "ts_opus_nolessons": "opus_nolessons", "ts_sonnet": "sonnet_lessons"}.get(t)
    if not p:
        return None
    d = json.load(io.open(H + "../../baselines/ts_runs_v2/s0/results/%s/report.json" % p, encoding="utf-8"))
    return {r["lean"].split(".")[-1]: [x["class"] for x in r["reasons"]] for r in d["results"] if r["flag"]}


tv = {t: tv_flags(t) for t in TV}
st = {t: st_flags(t) for t in TV}
s0 = set()
for x, (k, e) in F.key.items():
    t = k["translation"]
    if t != "study1" and e["class"] == "V-P" and (e["declaration"] in tv[t][0] or (st[t] and e["declaration"] in st[t])):
        s0.add(x)
hits = dict(F.ARMS)
hits["S0 scripts"] = s0
G = F.G
prov = {x for x, (k, e) in F.key.items() if e["kind"] == "type specialised (statement)"}
allk = set(F.key)


def row(name, h):
    c = collections.Counter(F.g(F.key[x][1]) for x in h)
    b = h - prov
    return "| %s | %d | %s | %d |" % (name, len(h), " | ".join(str(c[q]) for q in G), len(b))


tot = collections.Counter(F.g(e) for k, e in F.key.values())
w("# Tables of the audit on real errors\n\nWritten by `report.py`. Known errors only; a hit means the finding names the declaration (reasons are not checked here).\n")
w("## Known errors found\n")
w("| Arm | All (%d) | Open value fixed (%d) | Type too specific, definitions (%d) | Type too specific, statements, provisional (%d) | Study 1 (%d) | Without provisional (%d) |" % (
    len(allk), *[tot[q] for q in G], len(allk - prov)))
w("|---|---|---|---|---|---|---|")
for a in ["S0 scripts"] + ARMS:
    w(row(a, hits[a]))
w(row("S0 or S1", s0 | hits["S1 Astra"]))
w(row("S0 or S8", s0 | hits["S8 Opus a or b"]))
w("\nThe S0 column is not an independent result: the 40 \"type too specific\" errors entered the key *because* these scripts flagged them. S0 cannot see open values. "
  "The open-value errors were known from named-constant tests written by hand or by models (Lean witnesses), not from S0. Study 1 errors were known from failed proofs.\n")
w("## Per translation (known errors found)\n")
w("| Translation | Known | S0 | " + " | ".join(ARMS) + " |")
w("|---|---|---|" + "---|" * len(ARMS))
for t in TRS:
    ks = {x for x in allk if F.key[x][0]["translation"] == t}
    w("| %s | %d | %d | %s |" % (t, len(ks), len(s0 & ks), " | ".join(str(len(hits[a] & ks)) for a in ARMS)))
w("\n## S0 flags and false alarms\n")
w("| Translation | Constants compared | Constants flagged | of these known or new errors | Statements flagged | of these known or new errors |")
w("|---|---|---|---|---|---|")
new = collections.defaultdict(set)
for u, d in F.CATS["new"]:
    new[next(k["translation"] for k in s.K if k["unit"] == u)].add(d)
for t in TV:
    ks = {F.key[x][1]["declaration"] for x in allk if F.key[x][0]["translation"] == t} | new[t]
    f, n = tv[t]
    ok = {x for x in f if x in ks or x + "'" in ks}
    if st[t] is None:
        w("| %s | %d | %d | %d | not run per translation | |" % (t, n, len(f), len(ok)))
    else:
        w("| %s | %d | %d | %d | %d | %d |" % (t, n, len(f), len(ok), len(st[t]), len(set(st[t]) & ks)))
w("\nA flag that is no known or new error is a name match between different things (`thunk_op` is a type in two translations), a word length that is a number in Lean (`shift_lookup`), "
  "or a statement with another shape that was not shown to differ in meaning.\n")
w("## Errors outside the key (11, confirmed by the main session; the author's check is open)\n")
INH = {"tenv_val_ok_nsEmpty": "tenv_val_ok", "tenv_ctor_ok_nsEmpty": "tenv_ctor_ok", "tenv_abbrev_ok_nsEmpty": "tenv_abbrev_ok",
       "fix_clock_do_eval_res": "fix_clock, do_eval_res", "type_env_conv_thm": "type_ctor"}  # statement mentions a keyed constant whose type is too specific
w("| Translation | Declaration | Flagged by S0 | Follows from a known error | S1 | S3a | S3b |")
w("|---|---|---|---|---|---|---|")
beyond = 0
for u, d in F.CATS["new"]:
    t = next(k["translation"] for k in s.K if k["unit"] == u)
    f = []
    if d in tv[t][0] or d.rstrip("'") in tv[t][0]:
        f.append("type variables (name clash with a type, dismissed)" if d == "thunk_op'" else "type variables")
    if st[t] and d in st[t]:
        f.append("statement (%s)" % ", ".join(st[t][d]))
    beyond += not f
    w("| %s | `%s` | %s | %s | %s |" % (t, d, "; ".join(f) or "no", "`%s`" % INH[d] if d in INH else "no", " | ".join("yes" if (u, d) in F.extra[a]["new"] else "no" for a in ("S1", "S3a", "S3b"))))
w("\n%d of the 11 are not flagged by S0. Flagged ones were dismissed or not keyed before the run, so they are not discoveries beyond the scripts. %d only repeat the type of a constant that is itself a known error; %d are neither flagged nor repeated. Many of the 15 provisional statement errors are of the repeating kind too (not checked one by one).\n" % (
    beyond, len(INH), sum(d not in INH and d != "thunk_op'" for u, d in F.CATS["new"])))
w("## Paired comparison by module\n")
mods = sorted({x[0] for x in allk})
B = 10000


def comp(a, b, sel):
    ks = [x for x in allk if x in sel]
    by = collections.defaultdict(list)
    for x in ks:
        by[x[0]].append((x in hits[a]) - (x in hits[b]))
    M = sorted(by)
    d = sum(sum(v) for v in by.values()) / len(ks)
    rng = random.Random("report-20261126")
    bs = []
    for _ in range(B):
        c = [by[rng.choice(M)] for _ in M]
        bs.append(sum(map(sum, c)) / sum(map(len, c)))
    bs.sort()
    ms = [sum(v) for v in by.values()]
    obs = abs(sum(ms))
    p = (1 + sum(abs(sum(m if rng.random() < .5 else -m for m in ms)) >= obs for _ in range(B))) / (B + 1)
    tr = []
    for t in TRS:
        q = [x for x in ks if F.key[x][0]["translation"] != t]
        tr.append(sum((x in hits[a]) - (x in hits[b]) for x in q) / len(q))
    return "| %s vs %s | %d | %d | %+.2f | [%+.2f, %+.2f] | %.4f | %+.2f to %+.2f |" % (a, b, len(ks), len(M), d, bs[int(.025 * B)], bs[int(.975 * B)], p, min(tr), max(tr))


sel = {"all known errors": allk, "without provisional": allk - prov, "open values only": {x for x in allk if F.g(F.key[x][1]) == "open value fixed"},
       "type too specific, definitions": {x for x in allk if F.g(F.key[x][1]) == "type specialised"}}
for n, q in sel.items():
    w("\n%s:\n" % n)
    w("| Comparison | Errors | Modules | Difference in recall | 95% interval (bootstrap over modules) | p (sign flips per module) | Leave one translation out |")
    w("|---|---|---|---|---|---|---|")
    w(comp("S1 Astra", "S3a Opus", q))
    w(comp("S1 Astra", "S8 Opus a or b", q))
w("\nAstra has one draw and Opus two, so the interval does not include run-to-run variation of Astra. Modules of one translation share a translator, and the same constant fails in several translations, "
  "so modules are not independent; with 8 translations no cluster interval at that level is reported. These numbers describe the selected errors, not model families.")
io.open(H + "TABLES.md", "w", encoding="utf-8", newline="\n").write("\n".join(out) + "\n")
print("\n".join(out))
