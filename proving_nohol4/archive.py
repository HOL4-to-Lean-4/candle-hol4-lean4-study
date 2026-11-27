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
import csv, glob, io, json, os, shutil
S = _STUDY + "/"
D = S + "proving_nohol4/"
C = _WR + "ts_ws/prove2_ctl/ts/"
W = _WR + "prove2/ts/ws/lean/"
for n in ["BRIEF.md", "settings.json", "drive.sh", "PINS.txt", "Frozen.lean", "frozen_base.tsv", "frozen_end.tsv", "Ax267.lean", "cmp2.py", "starts.txt"]:
    shutil.copy(C + n, D + "ts/" + n)
os.makedirs(D + "ts/lean", exist_ok=True)
shutil.copytree(W + "CmlTS", D + "ts/lean/CmlTS", dirs_exist_ok=True)
for n in ["CmlTS.lean", "CONVENTIONS.md", "PROGRESS.tsv", "lakefile.lean", "lake-manifest.json", "lean-toolchain"]:
    shutil.copy(W + n, D + "ts/lean/" + n)
rows = []
for k, name, note in (("candle", "candle-proving-nohol4-opus55-repaired-base", "278 of 278 proved; no HOL4 sources or proof text"), ("ts", "ts-proving-nohol4-opus55-repaired-opus-lessons", "267 of 267 proved; no HOL4 sources or proof text")):
    st = io.open(_WR + "ts_ws/prove2_ctl/%s/starts.txt" % k).read().split()
    for l in io.open(_WR + "ts_ws/prove2_ctl/%s/run_1.jsonl" % k, encoding="utf-8"):
        o = json.loads(l) if l.startswith("{") else {}
        if o.get("type") == "result":
            u = o["usage"]
            rows.append(["baseline", "proving", "", name, 1, "claude-cli", "claude-opus-5-5", st[0], st[-1], u["input_tokens"], u["output_tokens"], u["cache_read_input_tokens"], u["cache_creation_input_tokens"],
                         (u.get("output_tokens_details") or {}).get("thinking_tokens", ""), "", round(o["total_cost_usd"], 2), "", "", 0, "my-pc", note])
            print(k, o["num_turns"], o["duration_ms"] / 60000, rows[-1])
p = S + "ledger/costs.csv"
t = io.open(p, encoding="utf-8", newline="").read()
assert "nohol4" not in t
nl = "\r\n" if "\r\n" in t else "\n"
with io.open(p, "a", encoding="utf-8", newline="") as f:
    csv.writer(f, lineterminator=nl).writerows(rows)
