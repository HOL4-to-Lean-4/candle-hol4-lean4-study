"""Remove HOL4 proof text (termination tactics, tactic proofs, derivations by conversions) from the comments of a Lean base.
Only lines inside Lean comments are touched; the result is checked by prooftext.py and by the frozen-constant dump."""
import glob, io, re, sys
from prooftext import comments

MARK = "  [HOL4 proof text removed]"
# explicit line ranges (1-based, inclusive), read by hand
R = {
    "candle": {"HolSyntax.lean": [(371, 374)], "HolSyntaxExtra.lean": [(243, 248), (581, 582), (591, 592), (602, 603), (618, 619), (652, 653)], "Misc.lean": [(246, 247), (317, 317)]},
    "ts": {"SemanticPrimitivesProps.lean": [(240, 242)], "TypeSysProps.lean": [(829, 831)]},
}[sys.argv[2]]
base = sys.argv[1]
for f in sorted(glob.glob(base + "/**/*.lean", recursive=True)):
    t = io.open(f, encoding="utf-8", newline="").read()
    assert "\r" not in t, f
    L = t.split("\n")
    incom = {ln for ln, _ in comments(t)}
    kill = set()
    for a, b in R.get(f.replace("\\", "/").split("/")[-1], []):
        kill |= set(range(a, b + 1))
    i = 1
    while i <= len(L):
        if i in incom and re.match(r"\s*Termination\s*$", L[i - 1]):
            j = i
            while not re.match(r"\s*End\b", L[j - 1]):
                assert j in incom and j - i < 20, (f, i, j)
                kill.add(j)
                j += 1
            i = j
        i += 1
    if not kill:
        continue
    out = []
    for n, l in enumerate(L, 1):
        if n in kill:
            assert n in incom, (f, n, l)
            print(f.replace("\\", "/").split("/")[-1], n, l)
            assert "-/" not in l and "/-" not in l, (f, n, l)
            if n - 1 not in kill:
                out.append(MARK)
        else:
            out.append(l)
    io.open(f, "w", encoding="utf-8", newline="").write("\n".join(out))
