"""Turn export_statements.sml output into statements.jsonl and statements_pretty.txt, and check it."""
import hashlib, json, sys

def ty_args(t):
    assert t["ty"] == "min$fun"; return t["args"]

def typeof(t):
    if "v" in t: return t["t"]
    if "c" in t: return t["t"]
    if "f" in t:
        f, x = typeof(t["f"]), typeof(t["x"])
        dom, rng = ty_args(f)
        assert dom == x, "ill-typed application"
        return rng
    a = t["abs"]
    return {"ty": "min$fun", "args": [a["t"], typeof(t["body"])]}

def tvs(t, acc):
    if "tv" in t: acc.add(t["tv"])
    else:
        for a in t["args"]: tvs(a, acc)

def walk(t, consts, tv):
    if "v" in t: tvs(t["t"], tv)
    elif "c" in t: consts.add(t["c"]); tvs(t["t"], tv)
    elif "f" in t: walk(t["f"], consts, tv); walk(t["x"], consts, tv)
    else: tvs(t["abs"]["t"], tv); walk(t["body"], consts, tv)

raw = open("out/export.raw", encoding="latin-1").read()
rows = [json.loads(l[len("@@JSON "):]) for l in raw.splitlines() if l.startswith("@@JSON ")]
fix = lambda s: s.encode("latin-1").decode("utf-8")
def fixall(o):
    if isinstance(o, str): return fix(o)
    if isinstance(o, list): return [fixall(x) for x in o]
    if isinstance(o, dict): return {k: fixall(v) for k, v in o.items()}
    return o
rows = fixall(rows)
bool_ = {"ty": "min$bool", "args": []}
allc, n_hyp, bad = set(), 0, []
with open("out/statements.jsonl", "w", encoding="utf-8", newline="\n") as f, open("out/statements_pretty.txt", "w", encoding="utf-8", newline="\n") as g:
    for r in rows:
        c, tv = set(), set()
        for t in r["hyps"] + [r["concl"]]:
            try: assert typeof(t) == bool_
            except AssertionError as e: bad.append((r["thy"], r["name"], str(e)))
            walk(t, c, tv)
        n_hyp += bool(r["hyps"]); allc |= c
        f.write(json.dumps({"thy": r["thy"], "name": r["name"], "type_vars": sorted(tv), "constants": sorted(c),
                            "hyps": r["hyps"], "concl": r["concl"]}, ensure_ascii=False, sort_keys=True) + "\n")
        g.write("=== %s.%s\n%s\n\n" % (r["thy"], r["name"], r["pretty"]))
print("statements", len(rows), "distinct names", len({(r["thy"], r["name"]) for r in rows}),
      "with hyps", n_hyp, "ill-typed", len(bad), "distinct constants", len(allc))
print("sha256 statements.jsonl", hashlib.sha256(open("out/statements.jsonl", "rb").read()).hexdigest())
