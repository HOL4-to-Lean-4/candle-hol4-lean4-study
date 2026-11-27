"""Scan every pilot transcript for access outside the unit folder and for tools other than reading."""
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
import collections, glob, io, json, os, re
HERE = os.path.dirname(os.path.abspath(__file__)).replace("\\", "/") + "/"
BS = chr(92)
tools = collections.Counter()
n = 0
for f in sorted(glob.glob(HERE + "runs/*/*.raw")):
    u = os.path.basename(os.path.dirname(f))
    step = os.path.basename(f)[:-4]
    for l in io.open(f, encoding="utf-8"):
        try:
            o = json.loads(l)
        except Exception:
            continue
        calls = []
        if o.get("type") == "assistant":
            calls = [(c["name"], json.dumps(c["input"], ensure_ascii=False)) for c in o["message"]["content"] if c.get("type") == "tool_use"]
        elif o.get("type") == "item.completed" and o.get("item", {}).get("type") not in ("agent_message", "reasoning", "error"):
            calls = [(o["item"]["type"], o["item"].get("command") or json.dumps(o["item"], ensure_ascii=False)[:400])]
        elif o.get("event") == "step_update" and o["step_update"].get("step_type") == "tool" and o["step_update"].get("state") == "DONE":
            calls = [(o["step_update"]["tool_name"], json.dumps(o["step_update"]["tool_info"]["parameters"], ensure_ascii=False))]
        for name, s in calls:
            tools[(step, name)] += 1
            s2 = re.sub(BS + BS + "+", "/", s)
            for q in re.findall(r"([A-Za-z]:/[^\s\"'`,)]+|(?<![\w./])/[a-z]/[^\s\"'`,)]+|~/[^\s\"'`]+|\.\./[^\s\"'`]*|/home/[^\s\"'`]+)", s2):
                if "powershell.exe" in q.lower() or q.lower().startswith(("e:/auditwork/" + u, "/e/auditwork/" + u, (_WR + "auditwork/" + u).lower())):
                    continue
                n += 1
                print("OUTSIDE", u, step, name, q[:150])
            if re.search(r"\blake\b|\blean(\.exe)? |Holmake|curl|Invoke-Web|git ", s2) and name in ("command_execution", "run_command", "Bash"):
                print("EXEC?", u, step, s2[:200])
print(n, "outside accesses")
for k, v in sorted(tools.items()):
    print(k, v)
