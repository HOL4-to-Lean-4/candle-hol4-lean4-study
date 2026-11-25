"""Score findings against the known errors. A finding hits a known error if the last name component of its declaration equals the key declaration (ctor/record suffix dropped) and the class matches.
Findings that match nothing are listed for adjudication."""
import collections, io, json, os, re, sys
HERE = os.path.dirname(os.path.abspath(__file__)).replace("\\", "/") + "/"
K = json.load(io.open(HERE + "key.json", encoding="utf-8"))
STEPS = ["S1", "S3a", "S3b"]
REV = {"S1": "S4", "S3a": "S6"}


def names(d):
    out = set()
    for x in re.split(r"[,/;\s]+|\band\b", d):
        x = x.strip("`()*,.:")
        if x:
            out.add(x.split(".")[-1])
            out.add(x)
            if len(x.split(".")) > 1:
                out.add(x.split(".")[-2])
    return out


def load(u, s):
    p = HERE + "runs/%s/%s.json" % (u, s)
    return json.load(io.open(p, encoding="utf-8")) if os.path.exists(p) else None


hit, tot, unm = collections.Counter(), collections.Counter(), collections.defaultdict(list)
bykind = collections.Counter()
ctl = collections.Counter()
res = {}
for k in K:
    for s in STEPS:
        d = load(k["unit"], s)
        if d is None:
            continue
        rv = {v["id"]: v["verdict"] for v in (load(k["unit"], REV[s]) or {"verdicts": []})["verdicts"]} if s in REV else {}
        used = set()
        for e in k["errors"]:
            ok = [f for f in d["findings"] if e["declaration"] in names(f["declaration"]) and (f["class"] == e["class"] or e["declaration"] not in {x["declaration"] for x in k["errors"] if x is not e})]
            res[(s, k["unit"], e["declaration"], e["class"])] = bool(ok)
            if s in REV:
                res[(REV[s], k["unit"], e["declaration"], e["class"])] = any(rv.get(f["id"]) == "accept" for f in ok)
            used |= {f["id"] for f in ok}
        for f in d["findings"]:
            if f["id"] not in used:
                unm[s].append((k, f, rv.get(f["id"])))
done = {s: {k["unit"] for k in K if load(k["unit"], s)} for s in STEPS + ["S4", "S6"]}
common = set.intersection(*done.values())
if __name__ == "__main__":
    print({s: len(v) for s, v in done.items()}, "units done in all arms:", len(common))
    for s in ["S1", "S3a", "S3b", "S4", "S6"]:
        for lab in ["open value fixed", "type specialised", "type specialised (statement)", "study"]:
            ks = [(k, e) for k in K for e in k["errors"] if e["kind"].startswith(lab) and (lab != "type specialised" or e["kind"] == lab) and (lab != "study" or 1) and k["unit"] in common]
            n = len(ks)
            h = sum(res[(s, k["unit"], e["declaration"], e["class"])] for k, e in ks)
            print(s, lab, h, "/", n)
    for s in STEPS:
        c = [x for x in unm[s] if x[0]["kind"] == "control"]
        print(s, "unmatched findings:", len(unm[s]), "on controls:", len(c), "control units flagged:", len({x[0]["unit"] for x in c}))
