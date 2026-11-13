"""Prune theory scripts to the dependency closure.

Usage: prune.py deps.tsv keep.json CAKEMLDIR [--extra extra.json] [--dry]

Splits each script into top-level blocks. A block that stores at least one
database entry (by source line) is removable. It is kept when
  - it stores a kept entry (keep.json, from closure.py), or
  - its name is referenced textually by a kept block (proof scripts name
    theorems in tactics even when the final proof does not use them), or
  - it is listed in extra.json (names restored after a failed build).
The text-reference rule is iterated to a fixpoint. All other blocks
(open, Overload, val, ML code) stay. Writes pruned scripts in place and
prune_report.json.
"""
import json, re, sys, os
from collections import defaultdict

tsv, keepf, cakemldir = sys.argv[1:4]
extra = set()
if "--extra" in sys.argv:
    extra = set(json.load(open(sys.argv[sys.argv.index("--extra") + 1])))
dry = "--dry" in sys.argv
keep = set(json.load(open(keepf)))

entries = defaultdict(list)  # path -> [(line, key)]
unlocated = set()
defines = {}  # key -> defined constant names
for line in open(tsv):
    f = line.rstrip("\n").split("\t")
    thy, nm, path, ln = f[0], f[1], f[4], int(f[5] or 0)
    if path == "?":
        unlocated.add(f"{thy}.{nm}")
        continue
    entries[path.replace("$(CAKEMLDIR)", cakemldir)].append((ln, f"{thy}.{nm}"))
    defines[f"{thy}.{nm}"] = [c.split("$", 1)[1] for c in (f[9].split() if len(f) > 9 else [])]

START = re.compile(r"^(Theorem|Triviality|Definition|Datatype|Inductive|CoInductive|"
                   r"Type|Overload|Quote|val|fun|open|local|in|end|structure|"
                   r"Libs|Ancestors|Theory|\(\*|Termination|QED|End|Proof)\b")
REMOVABLE = re.compile(r"^(Theorem|Triviality|Definition|Inductive|CoInductive)\s+([\w']+)")

def blocks_of(lines):
    """Top-level blocks: start at a column-0 keyword (not a terminator)."""
    starts = []
    depth, depths = 0, []
    for l in lines:
        depths.append(depth)
        j = 0
        while j < len(l) - 1:
            if l[j:j+2] == "(*": depth += 1; j += 2
            elif l[j:j+2] == "*)" and depth > 0: depth -= 1; j += 2
            else: j += 1
    for i, l in enumerate(lines):
        if depths[i] > 0:
            continue
        if REMOVABLE.match(l) or re.match(r"^(Datatype|Type|Overload|Quote|val|fun|open|local|"
                                          r"structure|Libs|Ancestors|Theory|\(\*)\b", l):
            starts.append(i)
    if not starts or starts[0] != 0:
        starts.insert(0, 0)
    starts.append(len(lines))
    return [(starts[j], starts[j + 1]) for j in range(len(starts) - 1)]

files = {}
for path in entries:
    lines = open(path, errors="ignore").read().split("\n")
    bl = blocks_of(lines)
    info = []
    for (a, b) in bl:
        m = REMOVABLE.match(lines[a])
        keys = [k for (ln, k) in entries[path] if a < ln <= b]  # DB lines are 1-based
        if m and entries[path]:
            # generated entries without a source location belong to their block
            thy = entries[path][0][1].split(".")[0]
            base = re.sub(r"_def$", "", m.group(2))
            keys += [f"{thy}.{base}{suf}" for suf in
                     ("_ind", "_rules", "_cases", "_strongind", "_def", "_aux_def")
                     if f"{thy}.{base}{suf}" in unlocated]
        info.append(dict(a=a, b=b, name=m.group(2) if m else None, keys=keys,
                         removable=bool(m) and bool(keys)))
    files[path] = (lines, info)

# names of all removable blocks (for reference scanning)
name_to_blocks = defaultdict(list)
for path, (lines, info) in files.items():
    for i, bi in enumerate(info):
        if bi["removable"]:
            for k in bi["keys"]:
                name_to_blocks[k.split(".", 1)[1]].append((path, i))
                for c in defines.get(k, []):
                    name_to_blocks[c].append((path, i))
            name_to_blocks[bi["name"]].append((path, i))

kept = set()
todo = []
seeded = set()
for path, (lines, info) in files.items():
    for i, bi in enumerate(info):
        if not bi["removable"] or any(k in keep for k in bi["keys"]) or bi["name"] in extra \
                or any(k.split(".", 1)[1] in extra for k in bi["keys"]) \
                or any(c in extra for k in bi["keys"] for c in defines.get(k, [])):
            todo.append((path, i))
            if not (bi["name"] in extra or any(k.split(".", 1)[1] in extra for k in bi["keys"])
                    or any(c in extra for k in bi["keys"] for c in defines.get(k, []))):
                seeded.add((path, i))
TOK = re.compile(r"[A-Za-z][\w']*")
while todo:
    path, i = todo.pop()
    if (path, i) in kept:
        continue
    kept.add((path, i))
    lines, info = files[path]
    text = "\n".join(lines[info[i]["a"]:info[i]["b"]])
    text = re.sub(r"\(\*.*?\*\)", " ", text, flags=re.S)
    if "--no-text" in sys.argv and (path, i) in seeded:
        continue
    for tok in set(TOK.findall(text)):
        for ref in name_to_blocks.get(tok, []):
            if ref not in kept:
                todo.append(ref)

report = {}
for path, (lines, info) in files.items():
    out, removed = [], []
    for i, bi in enumerate(info):
        if (path, i) in kept:
            out += lines[bi["a"]:bi["b"]]
        else:
            removed.append(bi["name"])
    report[os.path.relpath(path, cakemldir)] = dict(
        lines_before=len(lines), lines_after=len(out), removed=removed)
    if not dry:
        open(path, "w").write("\n".join(out))
json.dump(report, open("prune_report.json", "w"), indent=1)
tb = sum(r["lines_before"] for r in report.values()); ta = sum(r["lines_after"] for r in report.values())
print(f"lines {tb} -> {ta}; removed blocks: {sum(len(r['removed']) for r in report.values())}")
for p, r in sorted(report.items()):
    print(f"  {p}: {r['lines_before']} -> {r['lines_after']} ({len(r['removed'])} blocks removed)")
