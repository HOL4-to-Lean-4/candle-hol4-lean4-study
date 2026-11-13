"""Compute the kernel-level dependency closure of a main theorem.

Input: deps.tsv from deps.sml. Seeds: the main theorem plus every theorem
marked [simp] in the source scripts (removing those would change simp sets).
Closure rules, iterated to a fixpoint, restricted to the listed theories:
  1. kernel-recorded proof dependencies of a kept entry;
  2. for each constant in a kept statement, the definition entries that define it;
  3. for each type operator in a kept statement, the entries of its datatype.
Output: keep.json (kept thy.name list) and a summary on stdout.
"""
import json, os, re, sys
from collections import defaultdict

tsv, root, cakemldir = sys.argv[1], sys.argv[2], sys.argv[3]
E = {}
for line in open(tsv):
    f = line.rstrip("\n").split("\t")
    f += [""] * (10 - len(f))
    thy, nm, cls, priv, path, ln, deps, consts, types, defd = f
    E[f"{thy}.{nm}"] = dict(thy=thy, name=nm, cls=cls, private=priv == "true",
        path=path.replace("$(CAKEMLDIR)", cakemldir), line=int(ln or 0),
        deps=deps.split(), consts=consts.split(), types=types.split(), defines=defd.split())
THYS = {e["thy"] for e in E.values()}

definers = defaultdict(list)
for k, e in E.items():
    if e["cls"] == "Def":
        for c in e["defines"]:
            definers[c].append(k)
# datatype entries: definitions whose name mentions the type (TY_DEF, repfns, case)
type_entries = defaultdict(list)
for k, e in E.items():
    for ty in e["types"]:
        pass
for k, e in E.items():
    m = re.match(r"(.*)_TY_DEF$", e["name"])
    if m:
        type_entries[f'{e["thy"]}${m.group(1)}'].append(k)

# [simp] seeds
simp = set()
for path in {e["path"] for e in E.values() if e["path"] != "?"}:
    if not os.path.exists(path):
        continue
    thy = [e["thy"] for e in E.values() if e["path"] == path][0]
    src = open(path, errors="ignore").read()
    for m in re.finditer(r"^(?:Theorem|Triviality|Definition)\s+([\w']+)\[([^\]]*)\]", src, re.M):
        if "simp" in m.group(2).split(","):
            simp.add(f"{thy}.{m.group(1)}")
    for m in re.finditer(r"export_rewrites\s*\[([^\]]*)\]", src):
        for n in re.findall(r'"([\w\']+)"', m.group(1)):
            simp.add(f"{thy}.{n}")
simp &= set(E)

keep, todo = set(), [root] + sorted(simp)
while todo:
    k = todo.pop()
    if k in keep or k not in E:
        continue
    keep.add(k)
    e = E[k]
    todo += [d for d in e["deps"] if d.split(".")[0] in THYS]
    for c in e["consts"]:
        if c.split("$")[0] in THYS:
            todo += definers.get(c, [])
    for t in e["types"]:
        if t.split("$")[0] in THYS:
            todo += type_entries.get(t, [])

json.dump(sorted(keep), open("keep.json", "w"), indent=0)
by = defaultdict(lambda: [0, 0, 0, 0])
for k, e in E.items():
    i = 0 if e["cls"] == "Def" else 2
    by[e["thy"]][i + 1] += 1
    if k in keep:
        by[e["thy"]][i] += 1
print(f"{'theory':20} defs kept/all   thms kept/all")
tot = [0, 0, 0, 0]
for t in sorted(by):
    d = by[t]; tot = [a + b for a, b in zip(tot, d)]
    print(f"{t:20} {d[0]:4}/{d[1]:<4}        {d[2]:4}/{d[3]:<4}")
print(f"{'TOTAL':20} {tot[0]:4}/{tot[1]:<4}        {tot[2]:4}/{tot[3]:<4}")
print("simp seeds:", len(simp), " of which needed by root alone:",
      len(simp & keep))
