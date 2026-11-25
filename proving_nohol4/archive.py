import csv, glob, io, json, os, shutil
S = "E:/NUS/mcomp/Dissertation/candle_study/"
D = S + "proving_nohol4/"
C = "E:/ts_ws/prove2_ctl/ts/"
W = "E:/prove2/ts/ws/lean/"
for n in ["BRIEF.md", "settings.json", "drive.sh", "PINS.txt", "Frozen.lean", "frozen_base.tsv", "frozen_end.tsv", "Ax267.lean", "cmp2.py", "starts.txt"]:
    shutil.copy(C + n, D + "ts/" + n)
os.makedirs(D + "ts/lean", exist_ok=True)
shutil.copytree(W + "CmlTS", D + "ts/lean/CmlTS", dirs_exist_ok=True)
for n in ["CmlTS.lean", "CONVENTIONS.md", "PROGRESS.tsv", "lakefile.lean", "lake-manifest.json", "lean-toolchain"]:
    shutil.copy(W + n, D + "ts/lean/" + n)
rows = []
for k, name, note in (("candle", "candle-proving-nohol4-opus55-repaired-base", "278 of 278 proved; no HOL4 sources or proof text"), ("ts", "ts-proving-nohol4-opus55-repaired-opus-lessons", "267 of 267 proved; no HOL4 sources or proof text")):
    st = io.open("E:/ts_ws/prove2_ctl/%s/starts.txt" % k).read().split()
    for l in io.open("E:/ts_ws/prove2_ctl/%s/run_1.jsonl" % k, encoding="utf-8"):
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
