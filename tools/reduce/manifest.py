"""Write manifest.json for the reduced package: every top-level declaration in
the pruned scripts (comments excluded), with kind, name, script and line, and
whether HOL4's kernel dependency closure of the main theorem contains it."""
import json, re, sys, os
cakemldir, keepf, depsf, out = sys.argv[1:5]
keep = set(json.load(open(keepf)))
thy_of = {}
for line in open(depsf):
    f = line.split("\t")
    if f[4] != "?":
        thy_of[f[4].replace("$(CAKEMLDIR)", cakemldir)] = f[0]
KINDS = [("theorem", r"^(?:Theorem|Triviality)\s+([\w']+)"),
         ("definition", r"^Definition\s+([\w']+)"),
         ("inductive", r"^(?:Inductive|CoInductive)\s+([\w']+)"),
         ("type_abbrev", r"^Type\s+([\w']+)"),
         ("overload", r'^Overload\s+([^\s=]+)')]
decls, files = [], []
for path, thy in sorted(thy_of.items()):
    src = open(path, errors="ignore").read()
    lines = src.split("\n")
    depth, rel = 0, os.path.relpath(path, cakemldir)
    files.append(dict(script=rel, theory=thy, lines=len(lines)))
    in_dt = False
    for i, l in enumerate(lines):
        d0 = depth
        j = 0
        while j < len(l) - 1:
            if l[j:j+2] == "(*": depth += 1; j += 2
            elif l[j:j+2] == "*)" and depth > 0: depth -= 1; j += 2
            else: j += 1
        if d0 > 0:
            continue
        if re.match(r"^Datatype\s*:", l):
            in_dt = True; continue
        if in_dt:
            if re.match(r"^End\b", l): in_dt = False; continue
            for m in re.finditer(r"(?:^|;)\s*([\w']+)\s*=", l):
                decls.append(dict(kind="datatype", name=m.group(1), theory=thy, script=rel, line=i + 1))
            continue
        for kind, rx in KINDS:
            m = re.match(rx, l)
            if m:
                nm = re.sub(r"\[.*", "", m.group(1)).rstrip(":")
                key = f"{thy}.{nm}"
                decls.append(dict(kind=kind, name=nm, theory=thy, script=rel, line=i + 1,
                                  simp=bool(re.search(r"\[[^\]]*simp", l)),
                                  kernel_closure=key in keep or (kind == "inductive" and f"{key}_ind" in keep)))
counts = {}
for d in decls:
    counts[d["kind"]] = counts.get(d["kind"], 0) + 1
json.dump(dict(main_theorem="holSoundness.proves_sound", files=files, counts=counts,
               total_lines=sum(f["lines"] for f in files), declarations=decls),
          open(out, "w"), indent=1)
print(json.dumps(counts), "lines", sum(f["lines"] for f in files))
print("theorems in kernel closure:", sum(1 for d in decls if d["kind"] == "theorem" and d.get("kernel_closure")))
