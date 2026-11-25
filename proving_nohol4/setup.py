import io, json, os
C = "E:/ts_ws/prove2_ctl/"
for k, old, n, mod, other in [("candle", "prove", 278, "CandleLean", "ts"), ("ts", "prove_ts", 267, "CmlTS", "candle")]:
    os.makedirs(C + k, exist_ok=True)
    t = io.open("E:/ts_ws/%s/BRIEF.md" % old, encoding="utf-8").read()
    i = t.index("They are translations of")
    j = t.index("Your task: prove")
    t = t[:i] + "They are translations of\nHOL4 theorems. The HOL4 sources and proofs are deliberately not available in this task; comments quote only HOL4 statements and definitions. Do not look for HOL4 scripts,\nHOL4 proofs or earlier Lean proofs of these theorems anywhere. " + t[j:]
    assert "hol4/" not in t and "with their proofs" not in t and "%d theorems whose proof" % n in t, t[:600]
    io.open(C + k + "/BRIEF.md", "w", encoding="utf-8", newline="\n").write(t)
    s = {"permissions": {"allow": ["Read(./**)", "Edit(./**)", "Write(./**)", "Read(~/.elan/toolchains/leanprover--lean4---v4.28.0/**)",
                                   "Bash(lake build:*)", "Bash(lake env lean:*)", "Bash(cd lean)", "Bash(date -u:*)", "Bash(ls:*)"],
                         "deny": ["Read(//e/%s/**)" % d for d in ["NUS", "ts_ws", "auditreal", "auditwork", "prove2/" + other]]
                         + ["Edit(//e/%s/**)" % d for d in ["NUS", "ts_ws", "auditreal", "auditwork", "prove2/" + other]]
                         + ["Read(~/.claude/**)", "Read(~/.codex/**)", "Read(//wsl.localhost/**)", "Read(//wsl$/**)", "WebFetch", "WebSearch", "Task", "Agent",
                            "Bash(git:*)", "Bash(curl:*)", "Bash(wget:*)", "Bash(gh:*)", "Bash(wsl:*)"]}}
    io.open(C + k + "/settings.json", "w", encoding="utf-8", newline="\n").write(json.dumps(s, indent=1))
    d = io.open("E:/ts_ws/prove/drive.sh", encoding="utf-8", newline="").read()
    d = d.replace("P=/e/ts_ws/prove; cd $P/ws || exit 1", "P=/e/ts_ws/prove2_ctl/%s; cd /e/prove2/%s/ws || exit 1" % (k, k))
    assert "/e/prove2/%s/ws" % k in d
    io.open(C + k + "/drive.sh", "w", encoding="utf-8", newline="").write(d)
    f = io.open("E:/ts_ws/%s/Frozen.lean" % old, encoding="utf-8").read()
    io.open(C + k + "/Frozen.lean", "w", encoding="utf-8", newline="\n").write(f)
    print(k, t[:900])
