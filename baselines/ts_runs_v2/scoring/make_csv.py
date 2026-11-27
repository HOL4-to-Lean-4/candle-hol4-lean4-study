"""Build the blinded scoring sheet for the type-soundness translations.
scoring_sheet.csv : one row per distinct (HOL4 item, Lean text); the translator is not shown.
key.csv           : item -> runs (do not open before scoring)."""
# Paths: set STUDY_ROOT (this repository), WORK_ROOT (folder holding ts_ws/, auditreal/, ...)
# and DISS_ROOT to override. Defaults: the repo root; E:/ on Windows, ~/work/ elsewhere; parent of the repo.
import os as _os
def _repo_root():
    d = _os.path.dirname(_os.path.abspath(__file__))
    while not _os.path.exists(_os.path.join(d, "CLOUD.md")) and _os.path.dirname(d) != d:
        d = _os.path.dirname(d)
    return d
_STUDY = _os.environ.get("STUDY_ROOT", _repo_root()).replace("\\", "/").rstrip("/")
_WR = _os.environ.get("WORK_ROOT", "E:/" if _os.name == "nt" else _os.path.expanduser("~/work")).replace("\\", "/").rstrip("/") + "/"
_DISS = _os.environ.get("DISS_ROOT", _os.path.dirname(_STUDY)).replace("\\", "/").rstrip("/") + "/"
import csv, io, json, os, random, re

HERE = os.path.dirname(os.path.abspath(__file__))
RUNS = ["opus_lessons", "opus_nolessons", "sonnet_lessons"]
R = _WR + "ts_ws/runs/"
STUDY = _STUDY + "/"
T = {}
for l in io.open(_WR + "ts_ws/common/TARGETS.tsv", encoding="utf-8").read().split("\n")[1:]:
    if l:
        c = l.split("\t")
        T.setdefault(c[2], []).append(c)
pretty = {}
for blk in re.split(r"\n(?==== )", io.open(STUDY + "tools/hol4_query/out_ts/statements_pretty.txt", encoding="utf-8").read()):
    m = re.match(r"=== (\S+)\n(.*)", blk, re.S)
    if m:
        pretty[m.group(1)] = m.group(2).strip()
SCRIPTS = {}
for root, _, fs in os.walk(R + "opus_lessons_v2/ws1/hol4"):
    for f in fs:
        if f.endswith("Script.sml"):
            SCRIPTS[f] = io.open(os.path.join(root, f), encoding="utf-8", errors="replace").read().split("\n")


def hol_source(name):
    c = T.get(name, [None])[0]
    if not c:
        return ""
    L = SCRIPTS.get(c[3])
    if not L:
        return ""
    i = int(c[4]) - 1
    out = []
    for x in L[i:i + 400]:
        if re.match(r"\s*Proof\b", x):
            break
        out.append(x)
        if re.match(r"\s*(End|QED)\b", x):
            break
    return "\n".join(out).strip()


def lean_map(run):
    d = R + run + "_v2/merged/CmlTS"
    out = {}
    for root, _, fs in os.walk(d):
        for f in fs:
            if f.endswith(".lean"):
                t = io.open(os.path.join(root, f), encoding="utf-8").read()
                for m in re.finditer(r"^(?:@\[[^\]]*\]\s*)?theorem\s+([^\s({\[:]+)(.*?):=\s*by\s+sorry", t, re.M | re.S):
                    out[m.group(1).split(".")[-1]] = "theorem " + m.group(1) + m.group(2).rstrip()
    return out


def abbrevs(run):
    d = R + run + "_v2/merged/CmlTS"
    out = {}
    for root, _, fs in os.walk(d):
        for f in fs:
            if f.endswith(".lean"):
                s = io.open(os.path.join(root, f), encoding="utf-8").read()
                for m in re.finditer(r"^(?:@\[[^\]]*\]\s*)?abbrev\s+(\S+)(.*?)(?=\n\s*\n|\n/-|\n[a-z@])", s, re.M | re.S):
                    out.setdefault(m.group(1).split(".")[-1], re.sub(r"\s+", " ", "abbrev " + m.group(1) + m.group(2)).replace("CmlTS.", ""))
    return out


AB = {r: abbrevs(r) for r in RUNS}


def glossary(run, text):
    A, todo, out = AB[run], list(dict.fromkeys(re.findall(r"[A-Za-z_][\w']*", text))), []
    seen = set()
    while todo:
        n = todo.pop(0)
        if n in A and n not in seen and len(out) < 25:
            seen.add(n)
            out.append(A[n])
            todo += re.findall(r"[A-Za-z_][\w']*", A[n])
    return chr(10).join(out)


ALIAS = {"EVERY_LIST_REL": ["EVERY_LIST_REL", "EVERY_LIST_REL_2", "EVERY_LIST_REL_lem", "EVERY_LIST_REL'"],
         "concrete_v_list": ["concrete_v_list_thm", "concrete_v_list_eq"]}
CTX = {
    "binder-types": "The HOL4 theorem has type variables ('a, 'b, ...: it holds for every type). Look at whether the Lean statement keeps them as type parameters or fixes a concrete type (for example mlstring or Nat). Question: is the Lean statement the same theorem, or only a special case? Is the fixed type variable used by the statement?",
    "instances": "The Lean statement has an extra instance hypothesis (for example [Nonempty e]) for a type that HOL4 always assumes non-empty. Question: is it harmless?",
    "shape": "Compare the Lean statement with the HOL4 statement (quantifiers, types, hypotheses, conclusion, case expressions). Question: do they say the same thing? Some rows were not flagged by the scan.",
}
items = {}
for run in RUNS:
    rep = json.load(io.open(STUDY + f"baselines/ts_runs_v2/s0/results/{run}/report.json", encoding="utf-8"))
    it = rep if isinstance(rep, list) else rep.get("theorems") or rep.get("statements") or rep.get("results")
    if isinstance(it, dict):
        it = [dict(v, name=k) for k, v in it.items()]
    lm = lean_map(run)
    for x in it:
        fl = x.get("reasons") or x.get("flags")
        if not fl:
            continue
        nm = (x.get("name") or x.get("hol4")).split(".")[-1].split("$")[-1]
        lean = next((lm[a] for a in ALIAS.get(nm, [nm]) + [nm + "'", nm + "_thm", nm + "_2", nm + "_lem"] if a in lm), "")
        lean = re.sub(r"\bCmlTS\.", "", lean)
        classes = {f["class"] for f in fl}
        kind = "binder-types" if "binder-types" in classes else "instances" if "instances" in classes else "shape"
        if not lean:
            print("no Lean text:", run, nm)
        key = (nm, re.sub(r"\s+", " ", lean))
        items.setdefault(key, {"name": nm, "lean": lean, "kind": kind, "runs": []})["runs"].append(run)
        if "instances" in classes and kind == "binder-types":
            items[key]["kind"] = "binder-types+instances"
random.seed(20261124)
flagged = {k[0] for k in items}
ctl = [n for n in sorted(T) if T[n][0][0] == "theorem" and n not in flagged and n not in ALIAS and len(T[n]) == 1]
for nm in random.sample(ctl, 14):
    run = random.choice(RUNS)
    lean = lean_map(run).get(nm, "")
    if lean:
        items[(nm, "control")] = {"name": nm, "lean": re.sub(r"CmlTS\.", "", lean), "kind": "shape", "runs": [run + "(control)"]}
L = list(items.values())
random.shuffle(L)
th = {k.split(".")[-1]: v for k, v in pretty.items()}
_sheet = os.path.join(HERE, "scoring_sheet.csv")
if os.path.exists(_sheet):
    with io.open(_sheet, encoding="utf-8-sig", newline="") as f:
        for r in csv.DictReader(f):
            if any((v or "").strip() for c, v in r.items() if c and (c.startswith("verdict") or c == "reason")):
                raise SystemExit("scoring_sheet.csv has answers; copy it away first")
with io.open(os.path.join(HERE, "scoring_sheet.csv"), "w", encoding="utf-8-sig", newline="") as f:
    w = csv.writer(f)
    w.writerow(["item", "hol4_theory.theorem", "where", "context_and_question", "hol4_original_source", "hol4_statement_with_types",
                "lean_translation", "lean_type_abbreviations_used", "verdict (same / weaker / stronger / different / note / unsure)", "reason"])
    for n, x in enumerate(L, 1):
        c = T[x["name"]][0]
        ctx = " ".join(CTX[k] for k in x["kind"].split("+"))
        full = next((k for k in pretty if k.endswith("." + x["name"])), "")
        w.writerow([f"S{n:02d}", full or x["name"], f"{c[3]} line {c[4]}", ctx, hol_source(x["name"]), th.get(x["name"], ""), x["lean"], glossary(x["runs"][0].split("(")[0], x["lean"]), "", ""])
with io.open(os.path.join(HERE, "key.csv"), "w", encoding="utf-8-sig", newline="") as f:
    w = csv.writer(f)
    w.writerow(["item", "theorem", "runs"])
    for n, x in enumerate(L, 1):
        w.writerow([f"S{n:02d}", x["name"], " ".join(x["runs"])])
print(len(L), "items", {k: sum(x["kind"] == k for x in L) for k in {x["kind"] for x in L}})
print("empty:", [x["name"] for x in L if not x["lean"] or not hol_source(x["name"]) or x["name"] not in th])
