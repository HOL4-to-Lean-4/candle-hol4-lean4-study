"""Type-variable count of every package constant: HOL4 vs the four Candle translations."""
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
import io
P = _STUDY + "/audit/pilot/"
R = _WR + "ts_ws/real/tv_%s.tsv"
REN = {"true": ["true_"], "false": ["false_"], "instance": ["instance_"]}
for r in ["opus55_direct_translation", "opus55_nolessons", "sonnet55_direct_translation", "fable52_direct_translation"]:
    L = {}
    for l in io.open(R % r, encoding="utf-8"):
        c = l.rstrip("\n").split("\t")
        if c[0] == "L":
            L.setdefault(c[2].split(".")[-1], []).append(c)
    n = 0
    print("==", r)
    for l in io.open(P + "consts.tsv", encoding="utf-8", errors="replace"):
        c = l.rstrip("\n").split("\t")
        if c[0] != "CONST":
            continue
        for nm in REN.get(c[2], [c[2]]):
            if nm in L:
                n += 1
                ks = {int(x[3]) for x in L[nm]}
                if int(c[3]) not in ks:
                    print("  ", c[1], nm, "HOL", c[3], "LEAN", sorted(ks), L[nm][0][1], L[nm][0][4][:120].encode("ascii", "replace").decode())
    print("compared", n)
