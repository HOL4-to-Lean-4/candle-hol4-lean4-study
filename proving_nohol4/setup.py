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
import io, json, os
_abs = lambda p: "//" + (p[0].lower() + p[2:] if p[1:2] == ":" else p.lstrip("/")).rstrip("/")
_deny = [_abs(_DISS)] + [_abs(_WR + d) for d in ["ts_ws", "auditreal", "auditwork"]]
C = _WR + "ts_ws/prove2_ctl/"
for k, old, n, mod, other in [("candle", "prove", 278, "CandleLean", "ts"), ("ts", "prove_ts", 267, "CmlTS", "candle")]:
    os.makedirs(C + k, exist_ok=True)
    t = io.open(_WR + "ts_ws/%s/BRIEF.md" % old, encoding="utf-8").read()
    i = t.index("They are translations of")
    j = t.index("Your task: prove")
    t = t[:i] + "They are translations of\nHOL4 theorems. The HOL4 sources and proofs are deliberately not available in this task; comments quote only HOL4 statements and definitions. Do not look for HOL4 scripts,\nHOL4 proofs or earlier Lean proofs of these theorems anywhere. " + t[j:]
    assert "hol4/" not in t and "with their proofs" not in t and "%d theorems whose proof" % n in t, t[:600]
    io.open(C + k + "/BRIEF.md", "w", encoding="utf-8", newline="\n").write(t)
    s = {"permissions": {"allow": ["Read(./**)", "Edit(./**)", "Write(./**)", "Read(~/.elan/toolchains/leanprover--lean4---v4.28.0/**)",
                                   "Bash(lake build:*)", "Bash(lake env lean:*)", "Bash(cd lean)", "Bash(date -u:*)", "Bash(ls:*)"],
                         "deny": ["Read(%s/**)" % d for d in _deny + [_abs(_WR + "prove2/" + other)]]
                         + ["Edit(%s/**)" % d for d in _deny + [_abs(_WR + "prove2/" + other)]]
                         + ["Read(~/.claude/**)", "Read(~/.codex/**)", "Read(//wsl.localhost/**)", "Read(//wsl$/**)", "WebFetch", "WebSearch", "Task", "Agent",
                            "Bash(git:*)", "Bash(curl:*)", "Bash(wget:*)", "Bash(gh:*)", "Bash(wsl:*)"]}}
    io.open(C + k + "/settings.json", "w", encoding="utf-8", newline="\n").write(json.dumps(s, indent=1))
    d = io.open(_WR + "ts_ws/prove/drive.sh", encoding="utf-8", newline="").read()
    d = d.replace("P=$W/ts_ws/prove; cd $P/ws || exit 1", "P=$W/ts_ws/prove2_ctl/%s; cd $W/prove2/%s/ws || exit 1" % (k, k))
    assert "$W/prove2/%s/ws" % k in d
    io.open(C + k + "/drive.sh", "w", encoding="utf-8", newline="").write(d)
    f = io.open(_WR + "ts_ws/%s/Frozen.lean" % old, encoding="utf-8").read()
    io.open(C + k + "/Frozen.lean", "w", encoding="utf-8", newline="\n").write(f)
    print(k, t[:900])
