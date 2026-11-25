"""Derive brief, review prompt, settings and runner from the pilot."""
import io
P = "E:/NUS/mcomp/Dissertation/candle_study/audit/"
rd = lambda f: io.open(P + f, encoding="utf-8").read()


def wr(f, t):
    io.open(P + f, "w", encoding="utf-8", newline="\n").write(t)


def rep(t, a, b):
    assert a in t, a[:60]
    return t.replace(a, b)


t = rd("pilot/BRIEF_audit.md")
t = rep(t, t[t.index("A reduced HOL4 development"):t.index("**Your scope")],
        "Part of a HOL4 development (CakeML) was translated to Lean 4.28.0 (core and Batteries, no Mathlib): definitions, datatypes, inductive relations, the HOL4 library\n"
        "constants they use, and theorem statements whose proofs may be `sorry`. It compiles. Names are HOL4's where possible.\n\n")
t = rep(t, "under the type mapping in `lean/CONVENTIONS.md`", "under the type mapping visible in the Lean library modules")
t = rep(t, "a Lean encoding choice recorded in the conventions", "a faithful choice of representation")
t = rep(t, "- `lean/CandleLean/`: the translation (comments removed); `lean/CONVENTIONS.md`: type mapping and names.", "- `lean/`: the translation (comments removed).")
wr("real/BRIEF_audit.md", t)
r = rd("pilot/REVIEW.md")
r = rep(r, "under the type mapping in `lean/CONVENTIONS.md`", "under the type mapping visible in the Lean library modules")
r = rep(r, "a Lean encoding choice recorded in the conventions", "a faithful choice of representation")
r = rep(r, "`lean/CandleLean/`, `lean/CONVENTIONS.md`, ", "`lean/`, ")
wr("real/REVIEW.md", r)
wr("real/settings_audit.json", rd("pilot/settings_audit.json"))
u = rd("pilot/run.py")
u = rep(u, '"E:/auditwork/"', '"E:/auditreal/"')
u = rep(u, 'assert d and ("findings" in d or "verdicts" in d), "no JSON"', 'if not (d and ("findings" in d or "verdicts" in d)):\n    sys.exit(3)')
u = rep(u, "d = parse(final)", "try:\n    d = parse(final)\nexcept Exception:\n    d = None")
wr("real/run.py", u)
d = rd("pilot/run.py")
