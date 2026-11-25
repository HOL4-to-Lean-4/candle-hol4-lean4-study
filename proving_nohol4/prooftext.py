"""Find HOL4 proof text in the Lean base (comments) and in CONVENTIONS.md.
(1) REGION: a line that occurs inside a proof region of the HOL4 scripts; (2) VOC: tactic vocabulary.
python prooftext.py BASE SCRIPTDIR..."""
import glob, io, os, re, sys

N = lambda s: re.sub(r"\s+", "", s)


def regions(t):
    out = [m.group(1) for m in re.finditer(r"^(?:Proof\b|Termination\b)(.*?)^(?:QED|End)\b", t, re.S | re.M)]
    for m in re.finditer(r"(?:store_thm|Q\.prove|\bprove|tprove|save_thm)\s*\(.*?(?=^(?:Theorem|Definition|Triviality|val |Datatype|Inductive|End|QED|Overload))", t, re.S | re.M):
        s = m.group(0)
        k = max(s.rfind("`,"), s.rfind("”,"))
        out.append(s[k + 2:] if k > 0 else "")
    return out


def comments(t):
    out, i, depth, ln, cur, instr = [], 0, 0, 1, "", False
    while i < len(t):
        two = t[i:i + 2]
        if depth == 0 and instr:
            if t[i] == "\\":
                i += 2
                continue
            if t[i] == '"':
                instr = False
            if t[i] == "\n":
                ln += 1
            i += 1
            continue
        if depth == 0 and t[i] == "'":
            m = re.match(r"'(?:\\.[^']*|[^\\'])'", t[i:])
            if m and not (i and (t[i - 1].isalnum() or t[i - 1] in "_'")):
                i += m.end()
                continue
        if depth == 0 and two == "--":
            j = t.find("\n", i)
            j = len(t) if j < 0 else j
            out.append((ln, t[i + 2:j]))
            i = j
            continue
        if two == "/-":
            depth += 1
            i += 2
            continue
        if depth and two == "-/":
            depth -= 1
            i += 2
            if depth == 0:
                out.append((ln, cur))
                cur = ""
            continue
        if depth == 0 and t[i] == '"':
            instr = True
        if t[i] == "\n":
            if depth:
                out.append((ln, cur))
                cur = ""
            ln += 1
        elif depth:
            cur += t[i]
        i += 1
    return out


VOC = re.compile(r">>|>-|\|>|<<|\\\\|_tac\b|_TAC\b|\bQED\b|^\s*(?:Proof|Termination)\b|\b(?:rw|simp|fs|gvs|gs|rfs|srw_tac|metis|match_mp|drule|irule|Induct|Cases|rpt|strip|qexists|first_x|imp_res|WF_REL|ho_match|recInduct|CONV_RULE|REWRITE|SIMP|MESON|METIS|EVAL)\w*\s*(?:\[|`|‘|“)")

if __name__ == "__main__":
    base = sys.argv[1]
    H = set()
    for d in sys.argv[2:]:
        for p in glob.glob(d + "/**/*Script.sml", recursive=True):
            for r in regions(io.open(p, encoding="utf-8").read()):
                H |= {N(l) for l in r.split("\n") if len(N(l)) >= 12}
    n = 0
    for f in sorted(glob.glob(base + "/**/*.lean", recursive=True)) + sorted(glob.glob(base + "/*.md")):
        if ".lake" in f:
            continue
        t = io.open(f, encoding="utf-8").read()
        L = list(enumerate(t.split("\n"), 1)) if f.endswith(".md") else comments(t)
        for ln, l in L:
            a, b = N(l) in H, VOC.search(l)
            if a or b:
                n += 1
                print("REGION" if a else "VOC   ", os.path.relpath(f, base), ln, l.strip()[:150])
    print(n, "lines flagged;", len(H), "HOL4 proof lines known")
