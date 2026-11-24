"""Append one ledger row per arm step for the pilot (run once)."""
import collections, csv, glob, io, json
L = "E:/NUS/mcomp/Dissertation/candle_study/ledger/costs.csv"
assert "audit-pilot" not in io.open(L, encoding="utf-8").read()
A = collections.defaultdict(lambda: [0] * 7)
for f in glob.glob("runs/*/*.meta"):
    m = json.load(open(f))
    u, a = m.get("usage", {}), A[m["step"]]
    a[0] += 1
    if m["step"] == "S4":
        a[1] += u["input_tokens"]; a[2] += u["output_tokens"]; a[3] += u["cache_read_tokens"]; a[4] += u["thinking_tokens"]
    elif m["step"] == "S1":
        a[1] += u["input_tokens"] - u["cached_input_tokens"]; a[2] += u["output_tokens"]; a[3] += u["cached_input_tokens"]; a[4] += u["reasoning_output_tokens"]
    else:
        a[1] += u["input_tokens"]; a[2] += u["output_tokens"]; a[3] += u["cache_read_input_tokens"]; a[5] += u["cache_creation_input_tokens"]; a[6] += m["total_cost_usd"]
TOOL = {"S1": ("codex-cli", "gpt-6.2-astra"), "S4": ("agy", "gemini-4-neon-high")}
with io.open(L, "a", encoding="utf-8", newline="") as f:
    w = csv.writer(f, lineterminator="\n")
    for s in sorted(A):
        a = A[s]
        t = TOOL.get(s, ("claude-cli", "claude-opus-5-5"))
        w.writerow(["pilot", "audit", "", "audit-pilot-" + s, 1, t[0], t[1], "2026-11-24T09:13:15Z", "2026-11-24T09:26:44Z", a[1], a[2], a[3], a[5] or 0, a[4],
                    "", round(a[6], 2) if a[6] else "", "", "", 0, "my-pc", "%d units; pilot audit; model name as requested, codex and agy on subscription quota" % a[0]])
