"""usage: stage2.py make RUN | merge RUN | scan RUN"""
import io, json, os, re, shutil, sys

C = "E:/ts_ws/common/"
cmd, run = sys.argv[1:3]
D = f"E:/ts_ws/runs/{run}/"
arm = "nolessons" if "nolessons" in run else "lessons"


def make():
    brief = io.open(C + f"briefs/{arm}_stage2.md", encoding="utf-8").read().replace("## Your workspace: WORKSPACE", "## Your workspace: the current directory")
    io.open(D + "stage2_brief.md", "w", encoding="utf-8", newline="\n").write(brief)
    for a in "ABCD":
        w = D + f"ws2{a}"
        assert not os.path.exists(w), w
        shutil.copytree(D + "ws1", w, ignore=shutil.ignore_patterns("PROGRESS.tsv", "scratch"))
        shutil.copy(C + f"ASSIGNMENT_{a}.tsv", w + "/ASSIGNMENT.tsv")
        shutil.copy(C + "TARGETS.tsv", w)
        print(w)


def merge():
    m = D + "merged"
    assert not os.path.exists(m)
    shutil.copytree(D + "ws1/lean", m, ignore=shutil.ignore_patterns("scratch"))
    for a in "ABCD":
        files = {l.split("\t")[4].strip() for l in io.open(C + f"ASSIGNMENT_{a}.tsv", encoding="utf-8").read().split("\n")[1:] if l}
        for f in sorted(files):
            shutil.copy(D + f"ws2{a}/lean/" + f, m + "/" + f)
            print(a, f)


def scan():
    allowed = (f"e:/ts_ws/runs/{run}/".lower(), "/e/ts_ws/runs/" + run.lower() + "/")
    for k in ["stage1"] + ["stage2" + a for a in "ABCD"]:
        p = D + k + ".jsonl"
        if not os.path.exists(p):
            continue
        flags, tools, res = set(), {}, None
        for l in io.open(p, encoding="utf-8", errors="replace"):
            o = json.loads(l)
            if o["type"] == "result":
                res = o
            if o["type"] != "assistant":
                continue
            for c in o["message"]["content"]:
                if c.get("type") != "tool_use":
                    continue
                tools[c["name"]] = tools.get(c["name"], 0) + 1
                s = " ".join(v for v in c["input"].values() if isinstance(v, str))
                if c["name"] in ("Write", "Edit"):
                    s2 = c["input"].get("file_path", "")
                else:
                    s2 = s
                for q in re.findall(r"([A-Za-z]:[\/][^\s\"'`]+|/[a-z]/[^\s\"'`]+|~/[^\s\"'`]+|\.\./[^\s\"'`]+)", s2):
                    n = q.replace("\\", "/").lower()
                    if n.startswith(allowed) or ".elan/toolchains" in n:
                        continue
                    flags.add((c["name"], q[:140]))
                if re.search(r"IO\.FS|IO\.Process|readFile|System\.FilePath|\bcurl\b|\bwget\b|\bgit\b", s):
                    flags.add((c["name"], "IO/net? " + s[:200]))
        print(k, tools, "denials:", len(res.get("permission_denials", [])) if res else None,
              "cost", res and res.get("total_cost_usd"), "turns", res and res.get("num_turns"), "ms", res and res.get("duration_ms"), "subtype", res and res.get("subtype"))
        for d in (res or {}).get("permission_denials", [])[:15]:
            print("   denied", d["tool_name"], json.dumps(d["tool_input"])[:160])
        for f in sorted(flags):
            print("   flag", f)


{"make": make, "merge": merge, "scan": scan}[cmd]()
