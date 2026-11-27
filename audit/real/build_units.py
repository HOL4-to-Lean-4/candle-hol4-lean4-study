"""Units for the audit on real errors: modules of our own, unrepaired translations (comments stripped) that hold at least one known error, plus modules with none known.
key.json (secret): unit -> translation, module, known errors (declaration, class, kind, evidence)."""
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
import glob, hashlib, io, json, os, random, re, shutil, sys
sys.path.insert(0, _WR + "ts_ws/mut_work")
from stripper_test import strip_comments

HERE = os.path.dirname(os.path.abspath(__file__)).replace("\\", "/") + "/"
OUT = _WR + "auditreal/"
P = HERE + "../pilot/"
rng = random.Random("real-20261124")
CAN = {_STUDY + "/package": "package"}
T = {  # translation -> (lean dir, root lib, hol4 package, hol4 src)
    "candle_opus": (_WR + "ts_ws/real/opus55_direct_translation", "CandleLean", _STUDY + "/package", _WR + "ts_ws/hol4src"),
    "candle_opus_nolessons": (_WR + "ts_ws/real/opus55_nolessons", "CandleLean", _STUDY + "/package", _WR + "ts_ws/hol4src"),
    "candle_sonnet": (_WR + "ts_ws/real/sonnet55_direct_translation", "CandleLean", _STUDY + "/package", _WR + "ts_ws/hol4src"),
    "candle_fable": (_WR + "ts_ws/real/fable52_direct_translation", "CandleLean", _STUDY + "/package", _WR + "ts_ws/hol4src"),
    "ts_opus": (_WR + "ts_ws/runs/opus_lessons_v2/merged", "CmlTS", _WR + "ts_ws/runs/opus_lessons_v2/ws1/hol4/package", _WR + "ts_ws/runs/opus_lessons_v2/ws1/hol4/HOL4-src"),
    "ts_opus_nolessons": (_WR + "ts_ws/runs/opus_nolessons_v2/merged", "CmlTS", _WR + "ts_ws/runs/opus_lessons_v2/ws1/hol4/package", _WR + "ts_ws/runs/opus_lessons_v2/ws1/hol4/HOL4-src"),
    "ts_sonnet": (_WR + "ts_ws/runs/sonnet_lessons_v2/merged", "CmlTS", _WR + "ts_ws/runs/opus_lessons_v2/ws1/hol4/package", _WR + "ts_ws/runs/opus_lessons_v2/ws1/hol4/HOL4-src"),
    "study1": (_DISS + "r1check/0d1173557/lean_type_sound", "LeanTypeSound", _WR + "ts_ws/runs/opus_lessons_v2/ws1/hol4/package", _WR + "ts_ws/runs/opus_lessons_v2/ws1/hol4/HOL4-src"),
}
VC_TS = "HD CHR FAPPLY int_div int_mod MAP3 type_def_to_ctMap locnrow locncol locn_rowupdate locn_colupdate dest_Refv FV_dec".split()
ERR = []  # translation, declaration, class, kind


def add(t, names, cls, kind):
    for n in (names.split() if isinstance(names, str) else names):
        ERR.append((t, n, cls, kind))


add("candle_opus", "HD LAST dest_var RESULT CLASH CHR FAPPLY termsem0", "V-C", "open value fixed")
add("candle_opus", "interprets0", "V-P", "type specialised")
add("candle_opus_nolessons", "HD LAST dest_var RESULT CLASH", "V-C", "open value fixed")
add("candle_sonnet", "ARB HD LAST SEG CHR RESULT CLASH FUN_FMAP", "V-C", "open value fixed")
add("candle_sonnet", "collate", "V-P", "type specialised")  # mllist
add("candle_fable", "interprets0", "V-P", "type specialised")
add("ts_opus", VC_TS + ["THE"], "V-C", "open value fixed")
add("ts_opus", "build_ctor_tenv ctMap_has_exns ctMap_has_bools check_ctor_tenv_ok", "V-P", "type specialised")
add("ts_opus_nolessons", VC_TS + ["THE"], "V-C", "open value fixed")
add("ts_sonnet", VC_TS + ["CARD"], "V-C", "open value fixed")
add("ts_sonnet", "fix_clock do_eval_res nsSub_compute do_if build_constrs build_ctor_tenv type_ctor tenv_val_ok tenv_ctor_ok tenv_abbrev_ok ctMap_has_exns ctMap_has_bools consistent_ctMap "
    "add_tenvE weakS weakCT store_type_extension", "V-P", "type specialised")  # type_def_to_ctMap: also V-C above
add("ts_sonnet", "type_def_to_ctMap", "V-P", "type specialised")
add("ts_sonnet", "type_tenv_ctor_weakening type_tenv_val_weakening_lemma tenv_abbrev_ok_lookup tenv_ctor_ok_merge tenv_ctor_ok_lookup mem_type_def_to_ctMap type_def_to_ctMap_mem "
    "nsLookup_add_tenvE1 nsLookup_add_tenvE2 nsLookup_add_tenvE3 add_tenvE_bvl check_ctor_tenv_ok store_type_extension_weakS store_type_extension_refl store_type_extension_trans",
    "V-P", "type specialised (statement)")
add("study1", "CARD", "V-P", "study-1: list may have duplicates")
add("study1", "do_app", "V-P", "study-1: Euclidean instead of floored division")


def _ntfs_glob(root):
    """glob(root/**/*.lean) in the order Windows (NTFS) lists it, so the unit sample is the same on every OS."""
    ls = lambda p: sorted(os.listdir(p), key=str.upper)
    dirs = []
    def rec(p):
        for n in ls(p):
            q = os.path.join(p, n)
            if os.path.isdir(q):
                dirs.append(q)
                rec(q)
    dirs.append(root)
    rec(root)
    return [os.path.join(p, n) for p in dirs for n in ls(p) if n.endswith(".lean") and os.path.isfile(os.path.join(p, n))]


def modules(t):
    d, lib, _, _ = T[t]
    out = {}
    for f in _ntfs_glob(d + "/" + lib):
        f = f.replace("\\", "/")
        out[f[len(d) + 1:]] = io.open(f, encoding="utf-8").read()
    return out


MODS = {t: modules(t) for t in T}
key = {}
miss = []
for t, n, cls, kind in ERR:
    pat = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:private\s+)?(?:noncomputable\s+)?(?:def|opaque|abbrev|theorem)\s+(?:[\w.]+\.)?%s(?![\w'!?])" % re.escape(n), re.M)
    hits = [f for f, s in MODS[t].items() if pat.search(strip_comments(s))]
    if t == "candle_sonnet" and n == "collate":
        hits = [f for f in hits if f.endswith("Mllist.lean")]
    if len(hits) != 1:
        miss.append((t, n, hits))
        continue
    key.setdefault((t, hits[0]), []).append({"declaration": n, "class": cls, "kind": kind})
print("not located exactly once:", miss)
bad = set(key)
cand = [(t, f) for t in T if t != "study1" for f, s in MODS[t].items() if (t, f) not in bad and 40 <= strip_comments(s).count("\n") and not f.endswith("Prelude.lean")]
rng.shuffle(cand)
seen, controls = {}, []
for c in cand:
    if seen.get(c[0], 0) < 2 and len(controls) < 12:
        seen[c[0]] = seen.get(c[0], 0) + 1
        controls.append(c)
units = [(c, "error") for c in key] + [(c, "control") for c in controls]
units.sort()
rng.shuffle(units)
print(len(units), "units", sum(k == "error" for _, k in units), "with known errors", sum(len(v) for v in key.values()), "known errors")
if "--dry" in sys.argv:
    for (t, f), k in sorted(units):
        print(k, t, f, [e["declaration"] for e in key.get((t, f), [])])
    sys.exit()
shutil.rmtree(OUT, ignore_errors=True)
K = []
for n, ((t, f), k) in enumerate(units, 1):
    uid = hashlib.sha256(("real%d%s%s" % (n, t, f)).encode()).hexdigest()[:8]
    d, lib, pkg, src = T[t]
    w = OUT + uid + "/"
    os.makedirs(w + "lean")
    for g, s in MODS[t].items():
        os.makedirs(os.path.dirname(w + "lean/" + g), exist_ok=True)
        io.open(w + "lean/" + g, "w", encoding="utf-8", newline="\n").write(strip_comments(s))
    shutil.copytree(pkg, w + "hol4/package", ignore=shutil.ignore_patterns(".hol", "*.md"))
    shutil.copytree(src, w + "hol4/HOL4-src")
    K.append({"unit": uid, "kind": k, "translation": t, "file": f, "module": f[:-5].replace("/", "."), "errors": key.get((t, f), [])})
json.dump(K, io.open(HERE + "key.json", "w", encoding="utf-8"), ensure_ascii=False, indent=1)
print("built", len(K))
