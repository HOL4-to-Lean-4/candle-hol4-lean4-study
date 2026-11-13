#!/bin/bash
# Prune, rebuild in HOL4, restore names that the build reports missing, repeat.
# Needs: S (scratch root), cakeml clone at $S/cakeml on a branch, HOL in PATH.
set -u
R=$S/reduce; C=$S/cakeml
FILES=$(python3 -c "import json;print(' '.join(json.load(open('$R/prune_report.json'))))" 2>/dev/null)
[ -f $R/extra.json ] || echo '[]' > $R/extra.json
for it in $(seq 1 30); do
  (cd $C && git checkout -q 48ee98a76be82e08a3a5613e34a1b8ec3c24c835 -- basis/pure misc candle)
  (cd $R && python3 prune.py deps.tsv keep.json $C --extra extra.json $PRUNE_FLAGS | head -1)
  (cd $C/candle/standard/semantics && Holmake -j4 holSoundnessTheory > $R/build_$it.log 2>&1)
  rc=$?
  echo "iteration $it: build rc=$rc"
  [ $rc -eq 0 ] && { echo BUILD_OK; exit 0; }
  # names reported missing by the build
  python3 - "$R/build_$it.log" "$R/extra.json" <<'EOF' || exit 2
import json, re, sys, glob, os
log = open(sys.argv[1], errors="ignore").read()
for f in re.findall(r"Full log: (\S+)", log):
    try: log += open(f, errors="ignore").read()
    except: pass
names = set(re.findall(r"[Vv]alue or constructor \(([\w']+)\) has not been declared", log))
names |= set(re.findall(r"Couldn't find theorem named ([\w']+)", log))
names |= set(re.findall(r"No theorem named ([\w']+)", log))
names |= set(re.findall(r"theorem (?:\w+\$)?([\w']+) not found", log))
for v in re.findall(r'free in the\s+right hand side of the proposed definition: (.*)', log):
    for n in re.findall(r'"([\w\']+)"', v):
        names |= {n, n + "_def"}
names |= set(re.findall(r"[Vv]alue or constructor \((?:\w+\.)?([\w']+)\) has not been declared", log))
for v in re.findall(r'Free variables in rhs of definition: (.*)', log):
    for n in re.findall(r'"([\w\']+)"', v):
        names |= {n, n + "_def"}
names |= set(re.findall(r'Unbound (?:value|structure)\s+([\w\']+)', log))
# generic fallback: identifiers on the failing source line(s)
if not names:
    m = re.search(r"\*\*\* (\w+)Theory in \$\(CAKEMLDIR\)/(\S+)", log)
    if m:
        script = os.path.join(os.environ["S"], "cakeml", m.group(2), m.group(1) + "Script.sml")
        lines = open(script, errors="ignore").read().split("\n")
        lns = set(int(x) + d for x in re.findall(r"LocA \((\d+),", log) for d in (0, 1))
        lns |= set(int(x) for x in re.findall(r"on line (\d+)", log))
        lns |= set(int(x) for x in re.findall(re.escape(m.group(1)) + r"Script\.sml:(\d+):", log))
        for ln in lns:
            if 0 < ln <= len(lines):
                toks = set(re.findall(r"[A-Za-z][\w']*", lines[ln - 1]))
                names |= toks
                # an overloaded name needs the constants its Overload declarations name (transitively)
                frontier = set(toks)
                seen = set()
                while frontier:
                    t = frontier.pop(); seen.add(t)
                    for ol in lines:
                        if re.match(r"^Overload\s+" + re.escape(t) + r"\b", ol):
                            more = set(re.findall(r"[A-Za-z][\w']*", ol))
                            names |= more
                            frontier |= more - seen
ex = set(json.load(open(sys.argv[2])))
new = names - ex
print("restoring:", sorted(new))
if not new:
    sys.exit(1)
json.dump(sorted(ex | new), open(sys.argv[2], "w"))
EOF
  [ $? -ne 0 ] && { echo "NO_PROGRESS: see $R/build_$it.log"; exit 1; }
done
