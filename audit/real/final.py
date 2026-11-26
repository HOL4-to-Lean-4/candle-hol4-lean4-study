"""Final table: known errors plus adjudicated findings outside the key (adjudicated by the main session; Lean checks in proofs/, HOL4 types in tools/hol4_query)."""
import collections, glob, json
import score as s

CATS = {
    "new": [("e1b2254a", "PERMUTES"), ("a892cd34", "instance_"), ("a892cd34", "termsem")] + ([("24717e82", "termsem0")] if s.PRE else []) + [("224e706a", "FAPPLY"), ("8107facf", "thunk_op'"),
            ("be73a930", "tenv_val_ok_nsEmpty"), ("be73a930", "tenv_ctor_ok_nsEmpty"), ("be73a930", "tenv_abbrev_ok_nsEmpty"), ("7ddc7cb6", "type_env_conv_thm"), ("83e55f56", "fix_clock_do_eval_res")],
    "duplicate root": [("f6841e8b", "instInhabitedChar")],
    # V-C recheck (27 Nov): the Lean equation holds in every model of the HOL4 theory (TFL fills missing patterns with ARB); vc_recheck/RECHECK.md
    "holds in HOL4": ([] if s.PRE else [("24717e82", "termsem0")]) + s.DROPPED,
    "tier 2": [("7a70c894", "instance_"), ("24717e82", "instance'"), ("7ae93bc8", "fresh"), ("430741ce", "OUTL"), ("e1b2254a", "LEAST"), ("53ea580b", "ARB"), ("53ea580b", "select")],
    "disputed": [("f21925dc", "word"), ("f21925dc", "dimindex"), ("f6841e8b", "word"), ("340d433a", "word_join"), ("340d433a", "word_concat")],
    "false": [("8107facf", "store_ffi")],
}
CAT = {x: n for n, l in CATS.items() for x in l}
CANON = {("53ea580b", "select"): "ARB"}
ALIAS = {("28fb71c3", "do_arith"): "do_app"}  # the key named do_app; the division is in do_arith, which do_app calls
hits, extra, left = collections.defaultdict(set), collections.defaultdict(lambda: collections.defaultdict(set)), []
for k in s.K:
    u = k["unit"]
    for a in ("S1", "S3a", "S3b"):
        rv = {v["id"]: v["verdict"] for v in (s.load(u, s.REV[a]) or {"verdicts": []})["verdicts"]} if a in s.REV else {}
        for f in s.load(u, a)["findings"]:
            nm = s.names(f["declaration"])
            arms = [a] + ([s.REV[a]] if rv.get(f["id"]) == "accept" else [])
            used = False
            for i, e in enumerate(k["errors"]):
                dup = sum(x["declaration"] == e["declaration"] for x in k["errors"]) > 1
                if any(n == e["declaration"] or ALIAS.get((u, n)) == e["declaration"] for n in nm) and (f["class"] == e["class"] or not dup):
                    used = True
                    for x in arms:
                        hits[x].add((u, i))
            if used:
                continue
            m = [n for n in sorted(nm) if (u, n) in CAT]
            if m:
                for x in arms:
                    extra[x][CAT[(u, m[0])]].add((u, CANON.get((u, m[0]), m[0])))
            elif k["translation"] == "study1":
                for x in arms:
                    extra[x]["study1, not adjudicated"].add((u, f["declaration"]))
            else:
                left.append((a, u, f["declaration"]))
G = ["open value fixed", "type specialised", "type specialised (statement)", "study"]
g = lambda e: "study" if e["kind"].startswith("study") else e["kind"]
key = {(k["unit"], i): (k, e) for k in s.K for i, e in enumerate(k["errors"])}
ARMS = {"S1 Astra": hits["S1"], "S3a Opus": hits["S3a"], "S3b Opus": hits["S3b"], "S4 Astra+Neon": hits["S4"], "S6 Opus+Opus": hits["S6"],
        "S8 Opus a or b": hits["S3a"] | hits["S3b"], "Astra or Opus a": hits["S1"] | hits["S3a"]}
if __name__ == "__main__":
    tot = collections.Counter(g(e) for k, e in key.values())
    print(dict(tot), sum(tot.values()), "unassigned:", left)
    for n, h in ARMS.items():
        c = collections.Counter(g(key[x][1]) for x in h)
        print(n, len(h), [c[q] for q in G], {q: len(v) for q, v in extra[n.split()[0]].items()} if n.split()[0] in extra else "")
    for tr in sorted({k["translation"] for k in s.K}):
        t = {x for x, (k, e) in key.items() if k["translation"] == tr}
        print(tr, len(t), {n: len(h & t) for n, h in ARMS.items()})
    op = hits["S3a"] | hits["S3b"]
    nm = lambda xs: [(key[x][0]["translation"], key[x][1]["declaration"], key[x][1]["class"]) for x in sorted(xs)]
    print("Astra only:", len(hits["S1"] - op), "Opus only:", nm(op - hits["S1"]))
    print("missed by all:", nm(set(key) - op - hits["S1"]))
    print("controls:", sum(k["kind"] == "control" for k in s.K))
    for a in ("S1", "S3a", "S3b"):
        print(a, [(k["unit"], k["translation"], f["declaration"]) for k in s.K if k["kind"] == "control" for f in s.load(k["unit"], a)["findings"]])
    print("new found by:", {d: [a for a in ("S1", "S3a", "S3b") if (u, d) in extra[a]["new"]] for u, d in CATS["new"]})
    print("tier2 found by:", {u + d: [a for a in ("S1", "S3a", "S3b") if (u, d) in extra[a]["tier 2"]] for u, d in CATS["tier 2"]})
    for st in ("S1", "S3a", "S3b", "S4", "S6"):
        sec, n, cost, tk = 0, 0, 0, collections.Counter()
        for f in glob.glob(s.HERE + "runs/*/%s.meta" % st):
            m = json.load(open(f, encoding="utf-8"))
            n += 1
            sec += m.get("seconds") or 0
            cost += m.get("total_cost_usd") or 0
            for q, v in (m.get("usage") or {}).items():
                if isinstance(v, (int, float)):
                    tk[q] += v
        print(st, n, "runs", sec, "s", round(cost, 2), dict(tk))
