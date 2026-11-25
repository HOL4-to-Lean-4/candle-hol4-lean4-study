"""Append rows for the type-soundness runs to candle_study/ledger/costs.csv (idempotent by workflow+run)."""
import csv, io, json, os, sys, glob, datetime

LED = "E:/NUS/mcomp/Dissertation/candle_study/ledger/costs.csv"
rows = list(csv.reader(io.open(LED, encoding="utf-8", newline="")))
H = rows[0]
have = {(r[3], r[4]) for r in rows[1:]}
new = []
for run in ["opus_lessons", "opus_nolessons", "sonnet_lessons"]:
    for base, tag in [("E:/ts_ws/runs_run0_incomplete_src/" + run, "run0"), ("E:/ts_ws/runs/" + run + "_v2", "v2")]:
        for k in ["stage1"] + ["stage2" + a for a in "ABCD"]:
            p = f"{base}/{k}.jsonl"
            if not os.path.exists(p):
                continue
            res, ts, model = None, [], None
            for l in io.open(p, encoding="utf-8", errors="replace"):
                o = json.loads(l)
                if o.get("timestamp"):
                    ts.append(o["timestamp"])
                if o["type"] == "result":
                    u0 = (res or {}).get("usage", {})
                    d0 = (res or {}).get("duration_ms", 0)
                    for f in ("input_tokens", "output_tokens", "cache_read_input_tokens", "cache_creation_input_tokens"):
                        o["usage"][f] = o["usage"].get(f, 0) + u0.get(f, 0)
                    o["duration_ms"] += d0
                    res = o
                if o["type"] == "assistant":
                    model = model or o["message"].get("model")
            if not res:
                print("no result", p)
                continue
            u = res.get("usage", {})
            mt = os.path.getmtime(p)
            end = datetime.datetime.utcfromtimestamp(mt).strftime("%Y-%m-%dT%H:%M:%SZ")
            start = datetime.datetime.utcfromtimestamp(mt - res["duration_ms"] / 1000).strftime("%Y-%m-%dT%H:%M:%SZ")
            wf = f"ts-{run}-{tag}-{k}"
            if (wf, "1") in have:
                continue
            note = "type-soundness translation; isolated claude -p; times from file mtime and duration"
            if tag == "run0":
                note += "; discarded before scoring (incomplete HOL4 sources)"
            new.append(["ablation", "translation", "", wf, "1", "claude-cli", model or "", start, end,
                        u.get("input_tokens", ""), u.get("output_tokens", ""), u.get("cache_read_input_tokens", ""),
                        u.get("cache_creation_input_tokens", ""), "", "", round(res.get("total_cost_usd", 0), 2), "", "", 0, "my-pc", note])
for r in new:
    print(r[3], r[6], r[7], r[15])
print(len(H), {len(r) for r in new}, "rows", len(new), "sum", sum(r[15] for r in new))
if "--write" in sys.argv:
    with io.open(LED, "a", encoding="utf-8", newline="") as f:
        csv.writer(f, lineterminator="\n").writerows(new)
