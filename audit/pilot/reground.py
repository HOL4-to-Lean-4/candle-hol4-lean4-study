"""Second HOL4 grounding pass (post hoc, after the default tactic proved 0 of 19): generic tactics with evaluation and rule inversion."""
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
import glob, io, json, os, subprocess, sys
Q = _STUDY + "/tools/hol4_query/hol4q.py"
TACS = ["(rpt strip_tac \\\\ EVAL_TAC)", "(EVAL_TAC \\\\ simp[] \\\\ metis_tac[])",
        "(rw[Once holSyntaxTheory.RACONV_cases, Once holSyntaxTheory.ACONV_def] \\\\ TRY (rw[Once holSyntaxTheory.RACONV_cases]) \\\\ EVAL_TAC)",
        "(rw[holSemanticsTheory.is_term_valuation0_def] \\\\ qexists_tac `implode \"a\"` \\\\ qexists_tac `Tyvar (implode \"a\")` \\\\ EVAL_TAC)"]
# the generic ones only; definition-specific tactics are recorded as such
for f in sorted(glob.glob("runs/*/S*.ground.json")):
    s = os.path.basename(f)[:-12]
    src = json.load(io.open(f.replace(".ground", ""), encoding="utf-8"))
    h = {x["id"]: x["hol4_check"] for x in src["findings"]}
    d = json.load(io.open(f, encoding="utf-8"))
    for k, v in d.items():
        v["hol4_2"] = "not proved"
        for i, t in enumerate(TACS[:2]):
            r = subprocess.run([sys.executable, Q, "prove", h[k], t.replace("\\\\", ">>")], capture_output=True, timeout=200)
            if "PROVED:" in r.stdout.decode("utf-8", "replace"):
                v["hol4_2"] = "proved by tactic %d" % i
                break
        print(s, v["declaration"], v["hol4_2"], flush=True)
    json.dump(d, io.open(f, "w", encoding="utf-8"), ensure_ascii=False, indent=1)
