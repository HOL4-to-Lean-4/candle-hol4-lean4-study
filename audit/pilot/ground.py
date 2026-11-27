"""Scripted grounding: run each finding's lean_check / hol4_check.  python ground.py <step> [unit ...]
Writes runs/<unit>/<step>.ground.json : id -> {lean, lean_out, hol4, hol4_out}. Failure is recorded, never counted as a refutation by itself."""
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
import io, json, os, re, shutil, subprocess, sys

HERE = os.path.dirname(os.path.abspath(__file__)).replace("\\", "/") + "/"
ST = _WR + "ts_ws/mut_work/stripped/"
G = _WR + "ts_ws/ground/"
step = sys.argv[1]
units = sys.argv[2:] or [k["unit"] for k in json.load(io.open(HERE + "key.json", encoding="utf-8"))]
env = dict(os.environ)
env["PATH"] = os.path.expanduser("~/.elan/bin") + os.pathsep + env["PATH"]


def project(u):
    p = G + u + "/"
    if not os.path.exists(p + "done"):
        shutil.rmtree(p, ignore_errors=True)
        shutil.copytree(_WR + "auditwork/" + u + "/lean", p)
        shutil.copytree(ST + ".lake", p + ".lake")
        r = subprocess.run(["lake", "build"], cwd=p, env=env, capture_output=True, timeout=1800)
        assert r.returncode == 0, r.stdout[-2000:]
        open(p + "done", "w").write("ok")
    return p


def lean(u, code):
    if re.search(r"\b(sorry|admit|native_decide|unsafe|implemented_by)\b|^\s*axiom\b|IO\.|run_cmd|#eval|initialize|elab|macro", code, re.M):
        return "refused", "forbidden token in the check"
    p = project(u)
    f = p + "_chk.lean"
    io.open(f, "w", encoding="utf-8", newline="\n").write(code)
    try:
        r = subprocess.run(["lake", "env", "lean", "_chk.lean"], cwd=p, env=env, capture_output=True, timeout=60)
    except subprocess.TimeoutExpired:
        return "timeout", ""
    out = (r.stdout + r.stderr).decode("utf-8", "replace")
    if r.returncode == 0 and "declaration uses" not in out:
        return "compiles", out[:800]
    return "fails", out[:800]


def hol(code):
    r = subprocess.run([sys.executable, _STUDY + "/tools/hol4_query/hol4q.py", "prove", code],
                       capture_output=True, timeout=200)
    out = r.stdout.decode("utf-8", "replace")
    return ("proved" if "PROVED:" in out else "not proved"), out[-800:]


for u in units:
    f = HERE + f"runs/{u}/{step}.json"
    if not os.path.exists(f):
        continue
    res = {}
    for x in json.load(io.open(f, encoding="utf-8")).get("findings", []):
        r = {"declaration": x["declaration"], "lean": "none", "hol4": "none"}
        if x.get("lean_check"):
            r["lean"], r["lean_out"] = lean(u, x["lean_check"])
        if x.get("hol4_check"):
            try:
                r["hol4"], r["hol4_out"] = hol(x["hol4_check"])
            except Exception as e:
                r["hol4"], r["hol4_out"] = "error", str(e)[:200]
        res[x["id"]] = r
        print(u, step, x["id"], x["declaration"], r["lean"], r["hol4"], flush=True)
    json.dump(res, io.open(HERE + f"runs/{u}/{step}.ground.json", "w", encoding="utf-8"), ensure_ascii=False, indent=1)
