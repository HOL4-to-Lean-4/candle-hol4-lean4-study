"""Recreate the work folders that the scripts expect outside the repository (Windows).

    python scripts/setup_pc.py [--study1]

The scripts use the fixed paths E:/ts_ws, E:/auditreal, E:/auditwork, E:/prove2 and
E:/NUS/mcomp/Dissertation/candle_study. Clone this repository to the last one.
Without an E: drive, first run:  subst E: C:\\some\\folder
Existing folders are kept. --study1 also fetches the study-1 Lean project from the
public CakeML fork (audit/real/build_units.py needs it). --work is for testing only.
"""
import argparse
import io
import os
import shutil
import subprocess
import sys

S = os.path.dirname(os.path.dirname(os.path.abspath(__file__))).replace("\\", "/") + "/"
ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
ap.add_argument("--study1", action="store_true")
ap.add_argument("--work", default="E:/")
a = ap.parse_args()
E = a.work.rstrip("/") + "/"
T = E + "ts_ws/"
B = S + "baselines/"


def tree(src, dst):
    if os.path.exists(dst):
        print("kept   ", dst)
        return False
    shutil.copytree(src, dst, ignore=shutil.ignore_patterns(".lake", "__pycache__"))
    print("created", dst)
    return True


def hol(dst):
    """The HOL4 library sources the auditors and translators read."""
    if os.path.exists(dst):
        print("kept   ", dst)
        return
    root, n = S + "vendor/HOL/", 0
    for d, _, fs in os.walk(root + "src"):
        for f in fs:
            if f.endswith((".sml", ".sig", ".ML")) or f == "Holmakefile":
                o = os.path.join(dst, os.path.relpath(d, root))
                os.makedirs(o, exist_ok=True)
                shutil.copy(os.path.join(d, f), o)
                n += 1
    print("created", dst, n, "files")


if (E + "NUS/mcomp/Dissertation/candle_study/").lower() != S.lower():
    print("NOTE: this clone is in %s; the scripts expect %sNUS/mcomp/Dissertation/candle_study/" % (S, E))
hol(T + "hol4src")
tree(S + "audit_base/lean", T + "audit_base/lean")
for x in ("opus55_direct_translation", "opus55_nolessons", "sonnet55_direct_translation", "fable52_direct_translation"):
    tree(B + x + "/lean", T + "real/" + x)
for x in ("opus_lessons", "opus_nolessons", "sonnet_lessons"):
    tree(B + "ts_runs_v2/" + x + "/lean", T + "runs/" + x + "_v2/merged")
W = T + "runs/opus_lessons_v2/ws1/hol4/"
tree(S + "package_ts", W + "package")
hol(W + "HOL4-src")
tree(B + "ts_runs_v2/run", T + "common")
tree(S + "proving_ts/base", T + "prove_ts/base_copy")
os.makedirs(T + "mut_work", exist_ok=True)
shutil.copy(S + "audit/real/stripper_test.py", T + "mut_work/")
sys.path.insert(0, S + "audit/real")
from stripper_test import strip_comments  # noqa: E402

ST = T + "mut_work/stripped"
if tree(S + "audit_base/lean", ST):
    for d, _, fs in os.walk(ST + "/CandleLean"):
        for f in fs:
            p = os.path.join(d, f)
            t = io.open(p, encoding="utf-8").read()
            io.open(p, "w", encoding="utf-8", newline="\n").write(strip_comments(t))
if a.study1:
    r = E + "NUS/mcomp/Dissertation/r1check/0d1173557"
    if os.path.exists(r):
        print("kept   ", r)
    else:
        def git(*c):
            subprocess.run(["git", "-c", "core.autocrlf=false"] + list(c), check=True)

        git("clone", "-q", "--filter=blob:none", "--no-checkout", "https://github.com/HOL4-to-Lean-4/cakeml.git", r)
        git("-C", r, "sparse-checkout", "set", "--cone", "lean_type_sound")
        git("-C", r, "checkout", "-q", "0d1173557a23554a11ee9f168e7fa9a045c23da6")
        print("created", r)
