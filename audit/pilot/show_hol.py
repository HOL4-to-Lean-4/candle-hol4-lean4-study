import glob, io, json, os
for f in sorted(glob.glob("runs/*/S*.ground.json")):
    s = os.path.basename(f)[:-12]
    src = json.load(io.open(f.replace(".ground", ""), encoding="utf-8"))
    h = {x["id"]: x["hol4_check"] for x in src["findings"]}
    for k, v in json.load(io.open(f, encoding="utf-8")).items():
        print(s, v["declaration"], "|", h[k][:130].replace("\n", " "), "|", v["hol4_out"][-230:].replace("\n", " ").strip())
