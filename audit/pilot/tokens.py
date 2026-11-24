"""Where do the input tokens of each audit run come from?  Per model call: context size; per run: calls, first context, last context, sum, text read by tool."""
import collections, glob, io, json, os, re
R = collections.defaultdict(list)
reads = collections.defaultdict(collections.Counter)
for f in sorted(glob.glob("runs/*/S[136]*.raw")):
    u, s = os.path.basename(os.path.dirname(f)), os.path.basename(f)[:-4]
    calls, seen, out = [], set(), collections.Counter()
    name = {}
    for l in io.open(f, encoding="utf-8"):
        try:
            o = json.loads(l)
        except Exception:
            continue
        if o.get("type") == "assistant":
            m = o["message"]
            if m["id"] not in seen:
                seen.add(m["id"])
                x = m["usage"]
                calls.append(x["input_tokens"] + x.get("cache_read_input_tokens", 0) + x.get("cache_creation_input_tokens", 0))
            for c in m["content"]:
                if c.get("type") == "tool_use":
                    name[c["id"]] = (c["name"], json.dumps(c["input"]))
        if o.get("type") == "user":
            for c in o["message"]["content"]:
                if isinstance(c, dict) and c.get("type") == "tool_result":
                    t = c["content"] if isinstance(c["content"], str) else json.dumps(c["content"], ensure_ascii=False)
                    n, i = name.get(c["tool_use_id"], ("?", ""))
                    k = "CONVENTIONS" if "CONVENTIONS" in i else "HOL4-src" if "HOL4-src" in i else "hol4/package" if "package" in i else "lean module" if "CandleLean" in i else "other " + n
                    out[k] += len(t)
        if o.get("type") == "item.completed" and o["item"].get("type") == "command_execution":
            i, t = o["item"]["command"], o["item"].get("aggregated_output", "")
            k = "CONVENTIONS" if "CONVENTIONS" in i else "HOL4-src" if "HOL4-src" in i else "hol4/package" if "package" in i else "lean module" if "CandleLean" in i else "other"
            out[k] += len(t)
    R[s].append((u, len(calls), calls[:1], calls[-1:], sum(calls), dict(out)))
for s in R:
    print("==", s)
    for r in R[s]:
        print(r)
