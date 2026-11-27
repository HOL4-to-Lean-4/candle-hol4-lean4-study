"""Build the blinded sheet on which the author checks the reasons of audit findings.  python audit/real/check/make_sheet.py
check_sheet.csv : one row per finding, arm, reviewer verdict, translation and status hidden.   check_key.csv : row -> source (do not open before scoring; not in git).
Needs E:/auditreal (build_units.py). Selection and seed are fixed here; analyse.py holds the analysis. Never overwrites a sheet that has answers."""
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
import collections, csv, io, os, random, re, sys

HERE = os.path.dirname(os.path.abspath(__file__)).replace("\\", "/") + "/"
sys.path.insert(0, HERE + "..")
import final as F
import score as s

U = _WR + "auditreal/"
rng = random.Random("check-20261126")
ANS = ["q1_difference_real (yes / no / unsure)", "q2_kind (too specific / open value fixed / needs choice term / other meaning / harmless / none)",
       "q3_reason (right / partly / wrong / cannot tell)", "minutes", "comment"]
SHEET, KEY = HERE + "check_sheet.csv", HERE + "check_key.csv"
if os.path.exists(SHEET):
    for r in csv.DictReader(io.open(SHEET, encoding="utf-8-sig", newline="")):
        if any((r.get(a) or "").strip() for a in ANS):
            sys.exit("check_sheet.csv has answers; copy it away first")
UNIT = {k["unit"]: k for k in s.K}
FIND = {a: {k["unit"]: s.load(k["unit"], a)["findings"] for k in s.K} for a in ("S1", "S3a", "S3b")}


def find_hits():
    """(unit, error index) -> {arm: [finding]}, same matching as final.py."""
    out = collections.defaultdict(lambda: collections.defaultdict(list))
    for k in s.K:
        for a in FIND:
            for f in FIND[a][k["unit"]]:
                nm = s.names(f["declaration"])
                for i, e in enumerate(k["errors"]):
                    dup = sum(x["declaration"] == e["declaration"] for x in k["errors"]) > 1
                    if any(n == e["declaration"] or F.ALIAS.get((k["unit"], n)) == e["declaration"] for n in nm) and (f["class"] == e["class"] or not dup):
                        out[(k["unit"], i)][a].append(f)
    return out


H = {x: dict(v) for x, v in find_hits().items()}
H.update({x: {} for x in F.key if x not in H})
assert {x for x in H if H[x]} == F.hits["S1"] | F.hits["S3a"] | F.hits["S3b"]
ROWS, have = [], set()


def add(u, a, f, stratum, err=""):
    if (u, a, f["id"]) not in have:
        have.add((u, a, f["id"]))
        ROWS.append({"unit": u, "arm": a, "f": f, "stratum": stratum, "error": err})


# 1. known errors that some but not all of the three audit runs found: every finding that names them
for x in sorted(F.key):
    if H[x] and len(H[x]) < 3:
        for a in sorted(H[x]):
            for f in H[x][a]:
                add(x[0], a, f, "discordant", F.key[x][1]["declaration"])
# 2. every finding outside the key, except study 1
for a in FIND:
    for u in FIND[a]:
        for f in FIND[a][u]:
            m = [n for n in sorted(s.names(f["declaration"])) if (u, n) in F.CAT]
            if m and (u, a, f["id"]) not in have and not any(f in fs.get(a, []) for (v, i), fs in H.items() if v == u):
                add(u, a, f, "outside key: " + F.CAT[(u, m[0])])
# 3. sample of the known errors that all three found: one finding each, from a random run
agree = sorted(x for x in F.key if len(H[x]) == 3)
for x in rng.sample(agree, 12):
    a = rng.choice(sorted(H[x]))
    add(x[0], a, H[x][a][0], "agreement sample", F.key[x][1]["declaration"])
# 4. known errors that nobody found
for x in sorted(F.key):
    if not H[x]:
        u, d = x[0], F.key[x][1]["declaration"]
        ROWS.append({"unit": u, "arm": "key", "stratum": "missed by all", "error": d,
                     "f": {"id": "K", "declaration": d, "lean": "", "hol4": "", "class": "V-P", "lean_check": None,
                           "explanation": "The HOL4 constant has more type variables than the Lean one. Lean fixes some of these types, so the Lean definition covers fewer instances than HOL4's."}})
# 5. controls: findings about one translation, shown with the same declaration of another translation where the scripts see no type difference
TO = [k for k in s.K if k["translation"] == "ts_opus_nolessons"]
src = [(k["unit"], f) for k in s.K if k["translation"] == "ts_sonnet" for f in FIND["S1"][k["unit"]]
       if f["class"] == "V-P" and any(f["declaration"].split(".")[-1] == e["declaration"] and e["kind"].startswith("type specialised") for e in k["errors"])]
LEANFILES = {}


def lean_files(u):
    if u not in LEANFILES:
        LEANFILES[u] = {}
        for r, _, fs in os.walk(U + u + "/lean"):
            for f in fs:
                if f.endswith(".lean") and f != "lakefile.lean":
                    p = os.path.join(r, f).replace("\\", "/")
                    LEANFILES[u][p[len(U + u) + 1:]] = io.open(p, encoding="utf-8").read().split("\n")
    return LEANFILES[u]


DEF = r"^(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+|unsafe\s+|partial\s+)*(?:def|opaque|abbrev|theorem|lemma|instance|structure|inductive|axiom|class|mutual)\b"
top = re.compile(DEF)


def locate(u, name):
    pat = re.compile(DEF[:-2] + r"\s+(?:[\w.']+\.)?%s(?![\w'!?])" % re.escape(name))
    return [(p, i) for p, L in lean_files(u).items() for i, l in enumerate(L) if pat.search(l)]


def lean_block(u, path, line):
    L = lean_files(u).get(path)
    if L is None:
        return ""
    i = min(max(line - 1, 0), len(L) - 1)
    while i > 0 and not top.match(L[i]):
        i -= 1
    if i and L[i - 1].startswith("@["):
        i -= 1
    j = i + 1
    while j < len(L) and not (top.match(L[j]) or re.match(r"^(end|namespace|section|open|variable|@\[|set_option|attribute|notation|infix)", L[j])):
        j += 1
    return "\n".join(L[i:j]).strip()


START = re.compile(r"^\s*(Definition|Theorem|Datatype|Inductive|CoInductive|Triviality|Type|Overload|Quote|val|fun|Theory|[A-Z_]+ ::)\b|new_(specification|definition|recursive_definition|constant)")


def hol_block(u, path, line):
    p = U + u + "/" + path
    if not os.path.isfile(p):
        return ""
    L = io.open(p, encoding="utf-8", errors="replace").read().split("\n")
    i = min(max(line - 1, 0), len(L) - 1)
    k = i
    while k > 0 and i - k < 60 and not START.search(L[k]):
        k -= 1
    if not START.search(L[k]):
        k = max(0, i - 8)
    out = []
    for n, x in enumerate(L[k:k + 90]):
        if re.match(r"\s*Proof\b", x) or (n and k + n > i and START.match(x)):
            break
        out.append(x)
        if re.match(r"\s*(End|QED)\b", x) or (n and re.search(r";\s*$", x) and k + n >= i and L[k].lstrip().startswith(("val", "fun"))):
            break
    return "\n".join(out).strip()


HT = collections.defaultdict(set)
for fn in ("consts.tsv", "consts_ts.tsv"):
    for l in io.open(HERE + "../../pilot/" + fn, encoding="utf-8", errors="replace"):
        c = l.rstrip("\n").split("\t")
        if c[0] == "CONST":
            HT[(fn, {"true": "true_", "false": "false_", "instance": "instance_"}.get(c[2], c[2]))].add("%s$%s %s" % (c[1], c[2], c[4]))


def related(u, text, own):
    """Lean type abbreviations and structures that the excerpt mentions (two levels)."""
    ab = {}
    for p, L in lean_files(u).items():
        for i, l in enumerate(L):
            m = re.match(r"^(?:@\[[^\]]*\]\s*)?(?:noncomputable\s+)?abbrev\s+([\w.']+)", l)
            if m:
                ab.setdefault(m.group(1).split(".")[-1], (p, i + 1))
    out, seen, todo = [], {own}, re.findall(r"[A-Za-z_][\w']*", text)
    for _ in range(2):
        nxt = []
        for n in dict.fromkeys(todo):
            if n in ab and n not in seen and len(out) < 14:
                seen.add(n)
                b = "\n".join(lean_block(u, *ab[n]).split("\n")[:8])
                out.append(b)
                nxt += re.findall(r"[A-Za-z_][\w']*", b)
        todo = nxt
    return "\n".join(out)


def base(d):
    return d.split(",")[0].split()[0].strip("`()").split(".")[-1]


ctl = []
for u, f in src:
    for k in TO:
        g = [(p, i) for p, i in locate(k["unit"], base(f["declaration"])) if p.split("/")[-1] == f["lean"].split("/")[-1].split(":")[0]]
        if len(g) == 1:
            ctl.append((k["unit"], f, "%s:%d" % (g[0][0], g[0][1] + 1)))
            break
ctl.sort(key=lambda x: x[1]["declaration"])
seen = set()
ctl = [c for c in ctl if not (c[1]["declaration"] in seen or seen.add(c[1]["declaration"]))]
for u, f, loc in rng.sample(ctl, 8):
    g = dict(f, lean=loc, lean_check=None)
    ROWS.append({"unit": u, "arm": "control", "stratum": "control", "error": "", "f": g})

by = collections.defaultdict(list)
for r in ROWS:
    by[(r["unit"], base(r["f"]["declaration"]))].append(r)
G = sorted(by)
rng.shuffle(G)
bad, sheet, key, n = [], [], [], 0
for gi, g in enumerate(G, 1):
    rng.shuffle(by[g])
    for r in by[g]:
        n += 1
        u, f = r["unit"], r["f"]
        d = base(f["declaration"])
        m = re.match(r"(.+?):(\d+)", f["lean"])
        if m:
            lp, ll = m.group(1), int(m.group(2))
        else:
            c = locate(u, d)
            own = [x for x in c if x[0] == "lean/" + UNIT[u]["file"]] or c
            lp, ll = (own[0][0], own[0][1] + 1) if own else ("", 0)
        lb = lean_block(u, lp, ll)
        if not re.search(r"(?<![\w'])%s(?![\w'])" % re.escape(d), lb):
            c = locate(u, d)
            c = [x for x in c if x[0] == lp] or c
            if c:
                lp, ll = c[0][0], c[0][1] + 1
                lb = lean_block(u, lp, ll)
        h = re.match(r"(.+?):(\d+)", f["hol4"] or "")
        hp, hl = (h.group(1), int(h.group(2))) if h else ("", 0)
        hb = hol_block(u, hp, hl) if h else ""
        if not hb:  # no usable location: look the name up in the package
            for rt, _, fs in os.walk(U + u + "/hol4/package"):
                for x in fs:
                    if x.endswith("Script.sml") and not hb:
                        for i, l in enumerate(io.open(os.path.join(rt, x), encoding="utf-8", errors="replace").read().split("\n")):
                            if re.search(r"^\s*((Definition|Theorem|Triviality)\s+%s(_def)?\b|%s\s.*⇔)" % ((re.escape(d.rstrip("_")),) * 2), l):
                                hp, hl = os.path.join(rt, x).replace("\\", "/")[len(U + u) + 1:], i + 1
                                hb = hol_block(u, hp, hl)
                                break
        ty = "\n".join(sorted(HT.get(("consts_ts.tsv" if UNIT[u]["translation"].startswith("ts_") else "consts.tsv", d.rstrip("'")), ())))
        if not lb or not hb:
            bad.append((n, u, r["arm"], f["declaration"], f["lean"], f["hol4"], bool(lb), bool(hb)))
        sheet.append([f"C{n:03d}", f"G{gi:03d}", d, f["class"], f["explanation"], hp + (":%d" % hl if hp else ""), hb[:9000], ty[:2000], lp + (":%d" % ll if lp else ""),
                      lb[:9000], related(u, lb, d)[:6000], (f.get("lean_check") or "")[:4000]] + [""] * len(ANS))
        key.append([f"C{n:03d}", u, UNIT[u]["translation"], r["arm"], f["id"], d, r["stratum"], r["error"]])
with io.open(SHEET, "w", encoding="utf-8-sig", newline="") as o:
    w = csv.writer(o)
    w.writerow(["row", "group", "declaration", "claimed_class", "claim", "hol4_where", "hol4_source", "hol4_type", "lean_where", "lean_text", "lean_abbreviations_used", "check_offered_with_the_claim"] + ANS)
    w.writerows(sheet)
with io.open(KEY, "w", encoding="utf-8-sig", newline="") as o:
    w = csv.writer(o)
    w.writerow(["row", "unit", "translation", "arm", "finding", "declaration", "stratum", "error"])
    w.writerows(key)
print(len(sheet), "rows,", len(G), "groups", dict(collections.Counter(k[6] for k in key)), dict(collections.Counter(k[3] for k in key)))
print("without excerpt:", bad)
