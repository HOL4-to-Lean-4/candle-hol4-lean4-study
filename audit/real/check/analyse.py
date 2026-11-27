"""Analysis of the author's check, fixed before any answer was given.  python audit/real/check/analyse.py FILLED_SHEET.csv [FILLED_SCORING_SHEET.csv]
Needs check_key.csv (rebuild with make_sheet.py in a copy of the repository if it is lost). The optional second file is the filled 51-row sheet of
baselines/ts_runs_v2/scoring (needs key.csv next to make_csv.py); it decides the 15 provisional statement errors. Writes CHECK_RESULTS.md next to this file with AUDIT_KEY=pre_recheck (the key as run: the fixed analysis), and CHECK_RESULTS_recheck.md with the key after the V-C recheck of 27 November."""
import collections, csv, io, math, os, random, re, sys

HERE = os.path.dirname(os.path.abspath(__file__)).replace("\\", "/") + "/"
sys.path.insert(0, HERE + "..")
import final as F

rd = lambda p: list(csv.DictReader(io.open(p, encoding="utf-8-sig", newline="")))
SHEET = {r["row"]: r for r in rd(sys.argv[1])}
KEY = {r["row"]: r for r in rd(HERE + "check_key.csv")}
assert set(SHEET) == set(KEY), "the sheet and check_key.csv have different rows"
for x in KEY:
    assert SHEET[x]["declaration"] == KEY[x]["declaration"], x
col = lambda r, p: next((r[c] or "").strip().lower() for c in r if c.startswith(p))
A = {x: {"q1": col(r, "q1"), "q2": col(r, "q2"), "q3": col(r, "q3")} for x, r in SHEET.items()}
Q1, Q3 = ("yes", "no", "unsure"), ("right", "partly", "wrong", "cannot tell")
bad = [x for x in A if A[x]["q1"] not in Q1 + ("",) or A[x]["q3"] not in Q3 + ("",)]
empty = [x for x in A if not A[x]["q1"]]
ARMS = ("S1", "S3a", "S3b")
out = []
w = out.append


def wilson(k, n):
    if not n:
        return "-"
    z, p = 1.96, k / n
    c, h = p + z * z / (2 * n), z * math.sqrt(p * (1 - p) / n + z * z / (4 * n * n))
    return "%d of %d (%.0f%% to %.0f%%)" % (k, n, 100 * (c - h) / (1 + z * z / n), 100 * (c + h) / (1 + z * z / n))


w("# Author's check of the audit findings\n\nWritten by `analyse.py`. %d of %d rows answered; %.0f minutes logged." % (
    len(A) - len(empty), len(A), sum(float(m) for m in (col(r, "minutes") for r in SHEET.values()) if re.fullmatch(r"[\d.]+", m))))
if bad:
    w("\nRows with an answer outside the allowed words (counted as unanswered): " + ", ".join(bad))
    for x in bad:
        A[x] = {"q1": "", "q2": "", "q3": ""}

w("\n## Controls (claim is not true of the shown declaration)\n")
c = [x for x in KEY if KEY[x]["stratum"] == "control" and A[x]["q1"]]
w("Answered \"no\" (correct): %s. Answered \"unsure\": %d." % (wilson(sum(A[x]["q1"] == "no" for x in c), len(c)), sum(A[x]["q1"] == "unsure" for x in c)))

w("\n## Answers by stratum and arm\n")
w("| Stratum | Arm | Rows | Difference real: yes | no | unsure | Reason (of yes): right | partly | wrong | cannot tell |\n|---|---|---|---|---|---|---|---|---|---|")
for st in sorted({k["stratum"] for k in KEY.values()}):
    for a in ARMS + ("control", "key"):
        X = [x for x in KEY if KEY[x]["stratum"] == st and KEY[x]["arm"] == a and A[x]["q1"]]
        if X:
            y = [x for x in X if A[x]["q1"] == "yes"]
            w("| %s | %s | %d | %s | %s |" % (st, a, len(X), " | ".join(str(sum(A[x]["q1"] == q for x in X)) for q in Q1),
                                             " | ".join(str(sum(A[x]["q3"] == q for x in y)) for q in Q3)))
y = [x for x in KEY if KEY[x]["stratum"] == "agreement sample" and A[x]["q1"]]
w("\nAgreement sample, difference real and reason right: " + wilson(sum(A[x]["q1"] == "yes" and A[x]["q3"] == "right" for x in y), len(y)))

g = collections.defaultdict(set)
for x in KEY:
    if A[x]["q1"] and KEY[x]["stratum"] != "control":
        g[SHEET[x]["group"]].add(A[x]["q1"])
w("\nGroups (same declaration, several claims) with both \"yes\" and \"no\" for q1: " + (", ".join(sorted(x for x in g if {"yes", "no"} <= g[x])) or "none") + ". The claims may differ, so this is listed, not counted.")


def err(x):
    k = KEY[x]
    c = [i for (u, i), (_, e) in F.key.items() if u == k["unit"] and e["declaration"] == k["error"]]
    c = [i for i in c if F.key[(k["unit"], i)][1]["class"] == SHEET[x]["claimed_class"]] if len(c) > 1 else c
    return (k["unit"], c[0]) if c else None


E = collections.defaultdict(list)
for x in KEY:
    if KEY[x]["error"]:
        E[err(x)].append(x)
refuted, open_ = set(), set()
for e, X in E.items():
    q = {A[x]["q1"] for x in X} - {""}
    if q == {"no"}:
        refuted.add(e)
    elif "yes" not in q:
        open_.add(e)
w("\n## Key corrections\n")
nm = lambda S: ", ".join(sorted("%s (%s)" % (F.key[e][1]["declaration"], F.key[e][0]["translation"]) for e in S)) or "none"
w("Known errors whose every checked claim was answered \"no\": %d: %s." % (len(refuted), nm(refuted)))
w("\nKnown errors in the sheet with no \"yes\" and not refuted (unsure or unanswered): %d: %s." % (len(open_), nm(open_)))
prov = {e for e in F.key if F.key[e][1]["kind"] == "type specialised (statement)"}
drop = set(refuted)
if len(sys.argv) > 2:
    T = {"opus_lessons": "ts_opus", "opus_nolessons": "ts_opus_nolessons", "sonnet_lessons": "ts_sonnet"}
    sk = {r["item"]: r for r in rd(HERE + "../../../baselines/ts_runs_v2/scoring/key.csv")}
    ver = {}
    for r in rd(sys.argv[2]):
        for t in sk[r["item"]]["runs"].split():
            if "(control)" not in t:
                ver[(T[t], sk[r["item"]]["theorem"])] = col(r, "verdict")
    P = {e: ver.get((F.key[e][0]["translation"], F.key[e][1]["declaration"]), "") for e in prov}
    d = {e for e in prov if P[e] in ("same", "note")}
    dis = {e for e in prov if (e in d) != (e in refuted) and e in E and P[e]}
    drop = (refuted - {e for e in prov if P[e] and e not in d}) | d
    w("\nProvisional statement errors by the 51-row sheet (it decides, because it is scored first and shows more): %s. Dropped (\"same\" or \"note\"): %s. The two sheets disagree on: %s." % (
        dict(collections.Counter(v or "no row" for v in P.values())), nm(d), nm(dis)))

w("\n## Recall after the check\n")
w("A hit in the checked strata counts only if the author found the difference real (q1 yes); \"right reason\" also needs q3 right. Hits that were not in the sheet (found by all three runs, outside the sample of 12) stay as they were.")
keep = set(F.key) - drop


def hit(a, need):
    r = set()
    for e in F.hits[a] & keep:
        if e not in E:
            r.add(e)
            continue
        X = [x for x in E[e] if KEY[x]["arm"] == a]
        if not X or any(A[x]["q1"] == "yes" and (not need or A[x]["q3"] == "right") for x in X):
            r.add(e)
    return r


H = {}
for need in (False, True):
    for a in ARMS:
        H[a, need] = hit(a, need)
    H["S8", need] = H["S3a", need] | H["S3b", need]
w("\n| Arm | Known errors found before the check (" + str(len(F.key)) + ") | Kept errors (%d): found, difference real | found, reason also right |\n|---|---|---|---|" % len(keep))
for a in ARMS + ("S8",):
    b = F.hits["S3a"] | F.hits["S3b"] if a == "S8" else F.hits[a]
    w("| %s | %d | %d | %d |" % (a, len(b), len(H[a, False]), len(H[a, True])))
w("\nS1 against S8, difference in recall on the kept errors, interval from 10000 resamples of modules:\n")
for need in (False, True):
    by = collections.defaultdict(list)
    for e in keep:
        by[e[0]].append((e in H["S1", need]) - (e in H["S8", need]))
    M, rng, bs = sorted(by), random.Random("analyse-20261126"), []
    for _ in range(10000):
        s = [by[rng.choice(M)] for _ in M]
        bs.append(sum(map(sum, s)) / sum(map(len, s)))
    bs.sort()
    w("- %s: %+.2f [%+.2f, %+.2f]" % ("reason also right" if need else "difference real", sum(map(sum, by.values())) / len(keep), bs[250], bs[9749]))
w("\n## Findings outside the key\n")
w("| Category before the check | Declarations checked | confirmed (q1 yes) | refuted (all no) | open |\n|---|---|---|---|---|")
D = collections.defaultdict(lambda: collections.defaultdict(list))
for x in KEY:
    if KEY[x]["stratum"].startswith("outside key"):
        D[KEY[x]["stratum"]][(KEY[x]["unit"], F.CANON.get((KEY[x]["unit"], KEY[x]["declaration"]), KEY[x]["declaration"]))].append(A[x]["q1"])
for st in sorted(D):
    v = list(D[st].values())
    y, n = sum("yes" in q for q in v), sum(set(q) == {"no"} for q in v)
    w("| %s | %d | %d | %d | %d |" % (st[13:], len(v), y, n, len(v) - y - n))
w("\nStudy-1 findings outside the key are not in the sheet and are counted neither way.")
if not F.s.PRE:
    hh = set(F.s.DROPPED) | {("24717e82", "termsem0")}
    rows = sorted(x for x in KEY if (KEY[x]["unit"], KEY[x]["declaration"].split(".")[-1]) in hh and SHEET[x]["claimed_class"] == "V-C")
    w("\n## V-C recheck (27 November)\n")
    w("This file uses the key after the V-C recheck (`../vc_recheck/RECHECK.md`). %d known error(s) and the new error `termsem0` (candle_fable) stay unsure under the test of plan v3.4, section 3 (saved-theorem reading): "
      "the saved theorems that mention `termsem0` were not all checked against a counterexample. They count as unresolved. Their rows: %s. Answers q1: %s. The fixed analysis with the key as run is `CHECK_RESULTS.md`."
      % (len(F.s.DROPPED), ", ".join(rows), dict(collections.Counter(A[x]["q1"] for x in rows))))
io.open(HERE + ("CHECK_RESULTS.md" if F.s.PRE else "CHECK_RESULTS_recheck.md"), "w", encoding="utf-8", newline="\n").write("\n".join(out) + "\n")
print("\n".join(out))
