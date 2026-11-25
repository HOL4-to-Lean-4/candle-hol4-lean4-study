"""Scan a proving transcript: tool counts, paths outside the workspace, Lean programs that read files, any sight of HOL4 proof text."""
import collections, glob, io, json, re, sys
sys.path.insert(0, "E:/ts_ws/prove2_ctl")
from prooftext import N, regions
k, scripts = sys.argv[1], sys.argv[2]
H = set()
for p in glob.glob(scripts + "/**/*Script.sml", recursive=True):
    for r in regions(io.open(p, encoding="utf-8").read()):
        H |= {N(l) for l in r.split("\n") if len(N(l)) >= 25}
tools, flags, seen, res, denied = collections.Counter(), collections.Counter(), collections.Counter(), {}, []
WS = "e:/prove2/%s/ws" % k
for f in sorted(glob.glob("E:/ts_ws/prove2_ctl/%s/run_*.jsonl" % k)):
    for l in io.open(f, encoding="utf-8"):
        try:
            o = json.loads(l)
        except Exception:
            continue
        c = o.get("message", {}).get("content") if isinstance(o.get("message"), dict) else None
        if not isinstance(c, list):
            continue
        for p in c:
            if p.get("type") == "tool_use":
                tools[p["name"]] += 1
                i = p["input"]
                s = " ".join(str(v) for q, v in i.items() if not (p["name"] in ("Write", "Edit") and q not in ("file_path",))).replace("\\", "/")
                for q in re.findall(r"([A-Za-z]:/[^\s\"'`,;)]+|(?<![\w./])/[a-z]/[^\s\"'`,;)]+|~/[^\s\"'`]+|\.\./[^\s\"'`]+|//wsl[^\s]*)", s):
                    if not q.lower().startswith((WS, "/" + WS.replace(":", ""))):
                        flags[(p["name"], q[:120])] += 1
                body = json.dumps(i, ensure_ascii=False)
                if re.search(r"IO\.FS|IO\.Process|readFile|FilePath|include_str|readDir|#eval|run_cmd", body):
                    flags[("LEAN IO?", body[:200])] += 1
                if re.search(r"Script\.sml|\bQED\b|hol4", s, re.I):
                    flags[("HOL4?", p["name"] + " " + s[:160])] += 1
                res[p["id"]] = p
            if p.get("type") == "tool_result":
                t = p["content"] if isinstance(p["content"], str) else json.dumps(p["content"], ensure_ascii=False)
                if "denied" in t[:200]:
                    denied.append((res.get(p["tool_use_id"], {}).get("name"), json.dumps(res.get(p["tool_use_id"], {}).get("input"))[:160]))
                for ln in t.split("\n"):
                    x = N(re.sub(r"^\s*\d+\t", "", ln))
                    if x in H:
                        seen[ln.strip()[:120]] += 1
                if "QED" in t:
                    seen["QED in result of " + json.dumps(res[p["tool_use_id"]]["input"])[:120]] += 1
print(dict(tools))
print("outside / suspicious:")
for q, n in flags.items():
    print("  ", n, q)
print("denied:", denied)
print("HOL4 proof lines seen in results:", len(seen))
for q, n in list(seen.items())[:15]:
    print("  ", n, q)
