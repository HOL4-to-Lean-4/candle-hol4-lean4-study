import json,glob,sys
for f in sorted(glob.glob(sys.argv[1]+"/run_*.jsonl")):
    for l in open(f,encoding="utf-8"):
        try:o=json.loads(l)
        except Exception: continue
        if o.get("type")=="result": print(f,o.get("subtype"),o.get("num_turns"),o.get("total_cost_usd"),o.get("usage",{}).get("output_tokens"),json.dumps(o.get("permission_denials"))[:1500]); print(o.get("result","")[-3000:])
