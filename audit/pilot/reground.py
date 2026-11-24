"""Second HOL4 grounding pass (post hoc, after the default tactic proved 0 of 19): generic tactics with evaluation and rule inversion."""
import glob, io, json, os, subprocess, sys
Q = "E:/NUS/mcomp/Dissertation/candle_study/tools/hol4_query/hol4q.py"
TACS = ["(rpt strip_tac \\\\ EVAL_TAC)", "(EVAL_TAC \\\\ simp[] \\\\ metis_tac[])",
        "(rw[Once holSyntaxTheory.RACONV_cases, Once holSyntaxTheory.ACONV_def] \\\\ TRY (rw[Once holSyntaxTheory.RACONV_cases]) \\\\ EVAL_TAC)",
        "(rw[holSemanticsTheory.is_term_valuation0_def] \\\\ qexists_tac `implode \"a\"` \\\\ qexists_tac `Tyvar (implode \"a\")` \\\\ EVAL_TAC)"]
# the generic ones only; definition-specific tactics are recorded as such
for f in sorted(glob.glob("runs/*/S*.ground.json")):
    s = os.path.basename(f)[:-12]
    src = json.load(io.open(f.replace(".ground", ""), encoding="utf-8"))
    h = {x["id"]: x["hol4_check"] for x in src["findings"]}
    d = json.load(io.open(f, encoding="utf-8"))
    for k, v in d.items():
        v["hol4_2"] = "not proved"
        for i, t in enumerate(TACS[:2]):
            r = subprocess.run([sys.executable, Q, "prove", h[k], t.replace("\\\\", ">>")], capture_output=True, timeout=200)
            if "PROVED:" in r.stdout.decode("utf-8", "replace"):
                v["hol4_2"] = "proved by tactic %d" % i
                break
        print(s, v["declaration"], v["hol4_2"], flush=True)
    json.dump(d, io.open(f, "w", encoding="utf-8"), ensure_ascii=False, indent=1)
