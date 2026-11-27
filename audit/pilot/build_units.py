"""Build the 10 pilot units. Key (secret) stays here; unit folders go to E:/auditwork/<hex>/."""
# Paths: set STUDY_ROOT (this repository), WORK_ROOT (folder holding ts_ws/, auditreal/, ...)
# and DISS_ROOT to override. Defaults: the repo root; E:/ on Windows, ~/work/ elsewhere; parent of the repo.
import os as _os
def _repo_root():
    d = _os.path.dirname(_os.path.abspath(__file__))
    while not _os.path.exists(_os.path.join(d, "CLOUD.md")) and _os.path.dirname(d) != d:
        d = _os.path.dirname(d)
    return d
_STUDY = _os.environ.get("STUDY_ROOT", _repo_root()).replace("\\", "/").rstrip("/")
_WR = _os.environ.get("WORK_ROOT", "E:/" if _os.name == "nt" else _os.path.expanduser("~/work")).replace("\\", "/").rstrip("/") + "/"
_DISS = _os.environ.get("DISS_ROOT", _os.path.dirname(_STUDY)).replace("\\", "/").rstrip("/") + "/"
import hashlib, io, json, os, random, shutil

A = _STUDY + "/audit/"
ST = _WR + "ts_ws/mut_work/stripped/"
OUT = _WR + "auditwork/"
HERE = os.path.dirname(os.path.abspath(__file__)).replace("\\", "/") + "/"
rng = random.Random("pilot-20261124")

pool = {}
for l in io.open(A + "mutants/pool.jsonl", encoding="utf-8"):
    p = json.loads(l)
    pool[p["id"]] = p
acc = [l.split("\t") for l in io.open(A + "mutants/accepted.tsv", encoding="utf-8").read().split("\n")[1:] if l]
acc = [pool[r[0]] for r in acc if r[7] == "witness"]
decoys = [json.loads(l) for l in io.open(A + "mutants/decoys.jsonl", encoding="utf-8")]


def pick(pred, k, used):
    c = sorted([p for p in acc if pred(p) and p["declaration"] not in used], key=lambda p: p["id"])
    rng.shuffle(c)
    out = []
    for p in c:
        if len(out) < k and p["module"] not in {q["module"] for q in out}:
            out.append(p)
    used |= {p["declaration"] for p in out}
    return out


used = set()
U = []
U += [(p, "mutant") for p in pick(lambda p: p["family"].startswith("held-out"), 1, used)]
U += [(p, "mutant") for p in pick(lambda p: p["label"] == "V-C", 1, used)]
U += [(p, "mutant") for p in pick(lambda p: p["scope"] == "statement" and not p["family"].startswith("held-out"), 1, used)]
U += [(p, "mutant") for p in pick(lambda p: p["scope"] == "prelude" and p["label"] == "V-P" and not p["family"].startswith("held-out"), 1, used)]
U += [(p, "mutant") for p in pick(lambda p: p["scope"] == "definition" and p["label"] == "V-P" and not p["family"].startswith("held-out"), 2, used)]
d = sorted(decoys, key=lambda p: p["id"])
rng.shuffle(d)
dd = [next(p for p in d if p["scope"] == "definition"), next(p for p in d if p["scope"] == "statement")]
U += [(p, "decoy") for p in dd]
mods = sorted({p["module"] for p in acc})
rng.shuffle(mods)
U += [({"id": "CLEAN-" + m, "module": m, "file": m.replace(".", "/") + ".lean"}, "clean") for m in mods[:2]]
rng.shuffle(U)

conv = io.open(_WR + "ts_ws/audit_base/lean/CONVENTIONS.md", encoding="utf-8").read()
conv = conv[:conv.index("## 5. Encodings")] + (
    "## 5. Unspecified values\n\nConstants that HOL4 leaves partly unspecified are `opaque` in Lean, packed with the defining theorem HOL4 gives them.\n")
key = []
shutil.rmtree(OUT, ignore_errors=True)
for n, (p, kind) in enumerate(U, 1):
    uid = hashlib.sha256(f"pilot{n}{p['id']}".encode()).hexdigest()[:8]
    w = OUT + uid + "/"
    os.makedirs(w + "lean")
    for x in ["CandleLean", "CandleLean.lean", "lakefile.lean", "lean-toolchain", "lake-manifest.json"]:
        s = ST + x
        shutil.copytree(s, w + "lean/" + x) if os.path.isdir(s) else shutil.copy(s, w + "lean/" + x)
    io.open(w + "lean/CONVENTIONS.md", "w", encoding="utf-8", newline="\n").write(conv)
    if kind != "clean":
        f = w + "lean/" + p["file"]
        t = io.open(f, encoding="utf-8").read()
        assert t.count(p["old_decl"]) == 1
        io.open(f, "w", encoding="utf-8", newline="\n").write(t.replace(p["old_decl"], p["new_decl"]))
    shutil.copytree(_STUDY + "/package", w + "hol4/package")
    shutil.copytree(_WR + "ts_ws/hol4src", w + "hol4/HOL4-src")
    key.append({"unit": uid, "kind": kind, "id": p["id"], "module": p["module"], "file": p["file"], "declaration": p.get("declaration"),
                "label": p.get("label"), "family": p.get("family"), "operator": p.get("operator"), "scope": p.get("scope"), "diff": p.get("diff")})
json.dump(key, io.open(HERE + "key.json", "w", encoding="utf-8"), ensure_ascii=False, indent=1)
for k in key:
    print(k["unit"], k["kind"], k["id"], k["module"], k["declaration"], k["family"], k["operator"])
