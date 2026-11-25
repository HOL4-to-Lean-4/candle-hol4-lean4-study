import collections, csv, datetime, glob, io, json, os
R = []
for st, tool, model in (("S1", "codex", "gpt-6.2-astra"), ("S3a", "claude-cli", "claude-opus-5-5"), ("S3b", "claude-cli", "claude-opus-5-5"), ("S4", "agy", "gemini-4-neon-high"), ("S6", "claude-cli", "claude-opus-5-5")):
    tk, n, cost, t = collections.Counter(), 0, 0, []
    for f in glob.glob("audit/real/runs/*/%s.meta" % st):
        m = json.load(open(f, encoding="utf-8"))
        n += 1
        cost += m.get("total_cost_usd") or 0
        t.append(os.path.getmtime(f))
        for q, v in (m.get("usage") or {}).items():
            if isinstance(v, (int, float)):
                tk[q] += v
    z = lambda x: datetime.datetime.fromtimestamp(x, datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")
    cache = tk.get("cache_read_input_tokens") or tk.get("cached_input_tokens") or tk.get("cache_read_tokens") or 0
    inp = tk["input_tokens"] - (tk.get("cached_input_tokens") or 0)
    R.append(["baseline", "audit", "", "audit-real-" + st, 1, tool, model, z(min(t)), z(max(t)), inp, tk["output_tokens"], cache, tk.get("cache_creation_input_tokens", 0),
              tk.get("reasoning_output_tokens", tk.get("thinking_tokens", "")), "", round(cost, 2) if cost else "", "", "", 0, "my-pc", "%d units; audit on real errors; start and end are file times of the first and last result" % n])
p = "ledger/costs.csv"
t = io.open(p, encoding="utf-8", newline="").read()
assert "audit-real" not in t
nl = "\r\n" if "\r\n" in t else "\n"
with io.open(p, "a", encoding="utf-8", newline="") as f:
    if not t.endswith("\n"):
        f.write(nl)
    csv.writer(f, lineterminator=nl).writerows(R)
for r in R:
    print(r)
