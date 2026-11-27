"""Independent check of the witness files (run by the main session).
usage: python verify_witnesses.py [ids...]   writes witnesses/verify.tsv
Checks per MUT-xxxx.lean: compiles against the base with no error; no forbidden token; the text of the mutated declaration
(new_decl, whitespace-normalised, attributes and `private` ignored) occurs in the file (definition scopes); `witness` has only the
standard axioms; the statement mentions something outside `Mut` (reported as a note when not).
"""
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
import io, json, os, re, subprocess, sys
from concurrent.futures import ThreadPoolExecutor

HERE = os.path.dirname(os.path.abspath(__file__))
W = os.path.join(HERE, "witnesses")
BASE = _WR + "ts_ws/audit_base/lean"
P = {}
for l in io.open(os.path.join(HERE, "pool.jsonl"), encoding="utf-8"):
    p = json.loads(l)
    P[p["id"]] = p
ids = sys.argv[1:] or sorted(f[:-5] for f in os.listdir(W) if re.fullmatch(r"MUT-\d+\.lean", f))
BAD = re.compile(r"\bsorry\b|\badmit\b|\baxiom\b|native_decide|\bunsafe\b|implemented_by|\bopaque\b.*:=\s*sorry|debug\.skipKernelTC")


def strip_comments(t):
    t = re.sub(r"/-.*?-/", " ", t, flags=re.S)
    return re.sub(r"--[^\n]*", " ", t)


def norm(t):
    t = re.sub(r"@\[[^\]]*\]|\bprivate\b|\bnoncomputable\b|\bprotected\b", " ", t)
    return re.sub(r"\s+", " ", t).strip()


def check(i):
    f = os.path.join(W, i + ".lean")
    src = io.open(f, encoding="utf-8").read()
    body = strip_comments(src)
    notes = []
    if BAD.search(body):
        notes.append("FORBIDDEN:" + BAD.search(body).group(0)[:20])
    p = P[i]
    r = subprocess.run(["lake", "env", "lean", f.replace("\\", "/")], cwd=BASE, capture_output=True, text=True, encoding="utf-8", errors="replace")
    out = (r.stdout or "") + (r.stderr or "")
    if r.returncode != 0 or re.search(r"\berror\b", out):
        notes.append("COMPILE_ERROR")
    m = re.search(r"witness' depends on axioms: \[([^\]]*)\]|witness' does not depend on any axioms", out)
    if not m:
        notes.append("NO_AXIOM_REPORT")
    elif m.group(1):
        bad = [a.strip() for a in m.group(1).split(",") if a.strip() not in ("propext", "Classical.choice", "Quot.sound")]
        if bad:
            notes.append("AXIOMS:" + ",".join(bad))
    if p["scope"] != "statement":
        nd = norm(strip_comments(p["new_decl"]))
        if nd not in norm(body):
            notes.append("NEW_DECL_NOT_VERBATIM")
    if not re.search(r"theorem witness\b", body):
        notes.append("NO_WITNESS_THEOREM")
    hard = [n for n in notes if n.split(":")[0] in ("FORBIDDEN", "COMPILE_ERROR", "NO_AXIOM_REPORT", "AXIOMS", "NO_WITNESS_THEOREM")]
    return i, "FAIL" if hard else ("CHECK" if notes else "OK"), ";".join(notes)


with ThreadPoolExecutor(4) as ex:
    rows = list(ex.map(check, ids))
with io.open(os.path.join(W, "verify.tsv"), "w", encoding="utf-8", newline="\n") as o:
    o.write("id\tstatus\tnotes\n" + "".join("\t".join(r) + "\n" for r in rows))
from collections import Counter
print(Counter(r[1] for r in rows))
for r in rows:
    if r[1] != "OK":
        print(*r)
