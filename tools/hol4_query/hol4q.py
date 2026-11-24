#!/usr/bin/env python3
"""HOL4 query tool for the Candle package (run on Windows; HOL4 runs in WSL).

  hol4q.py print THY NAME          the theorem as HOL4 stores it, with all types
  hol4q.py parse 'TERM'            how HOL4 parses TERM: types and the constants it resolves to
  hol4q.py eval  'TERM'            EVAL_CONV on a ground term (theorem printed)
  hol4q.py prove 'TERM' [TACTIC]   try TACTIC (default: simp[] then metis) with a 90 s limit;
                                   prints PROVED or FAILED. FAILED IS NOT A REFUTATION.
  options before the subcommand: --open THY[,THY..] adds theories to open (default: holSoundness
  ancestors as loaded). Every run is appended to out/query_log.jsonl (query, SML, output, time).
Needs the package built in WSL at ~/candle_build/repo (scripts/build.sh native).
"""
import json, os, subprocess, sys, tempfile, time

HERE = os.path.dirname(os.path.abspath(__file__))
PRE = 'val _ = load "holSoundnessTheory"; open HolKernel boolLib bossLib; val _ = new_theory "hol4q_scratch"; val _ = show_types := true;\n'
OPENS = ["holSyntax", "holSyntaxLib", "holSyntaxExtra", "holSemantics", "holSemanticsExtra", "holSoundness", "setSpec", "mlstring", "misc"]


def sml_str(s):
    return '"' + s.replace("\\", "\\\\").replace('"', '\\"') + '"'


def body(kind, args, opens):
    op = 'val _ = load "pairLib";\n' + "".join("open %sTheory;\n" % o for o in opens)
    if kind == "print":
        thy, name = args
        return 'val th = DB.fetch %s %s;\nval _ = print (thm_to_string th ^ "\n");\n' % (sml_str(thy), sml_str(name))
    term = sml_str(args[0])
    if kind == "parse":
        return op + 'val t = Parse.Term [QUOTE %s];\nval _ = print (term_to_string t ^ "\ntype: " ^ type_to_string (type_of t) ^ "\n");\nval _ = app (fn c => let val {Thy,Name,Ty} = dest_thy_const c in print (Thy ^ "$" ^ Name ^ " : " ^ type_to_string Ty ^ "\n") end) (find_terms is_const t);\n' % term
    if kind == "eval":
        return op + 'val _ = print (thm_to_string (EVAL (Parse.Term [QUOTE %s])) ^ "\n");\n' % term
    if kind == "prove":
        tac = args[1] if len(args) > 1 else "(simp[] THEN TRY (metis_tac[]))"
        return op + 'val t = Parse.Term [QUOTE %s];\nval r = (print ("PROVED: " ^ thm_to_string (Tactical.TAC_PROOF (([], t), %s)) ^ "\n")) handle e => print ("FAILED (not a refutation): " ^ exn_to_string e ^ "\n");\n' % (term, tac)
    sys.exit(__doc__)


def main():
    argv = sys.argv[1:]
    opens = list(OPENS)
    if argv and argv[0] == "--open":
        opens += argv[1].split(","); argv = argv[2:]
    if not argv:
        sys.exit(__doc__)
    kind, args = argv[0], argv[1:]
    sml = PRE + body(kind, args, opens)
    d = "~/hq"
    t0 = time.time()
    script = os.path.join(tempfile.gettempdir(), "hol4q_%d.sml" % os.getpid())
    open(script, "w", encoding="utf-8", newline="\n").write(sml)
    wsl_script = subprocess.run(["wsl.exe", "-e", "wslpath", "-a", script.replace("\\", "/")], capture_output=True).stdout.decode().replace("\0", "").strip()
    sh = ('cd ~/candle_build/repo; B=$PWD/_build; export PATH=$B/polyml/bin:$B/HOL/bin:$PATH LD_LIBRARY_PATH=$B/polyml/lib HOLDIR=$B/HOL CAKEMLDIR=$PWD/package; '
          'cp "%s" package/candle/standard/semantics/_hol4q_PID.sml; cd package/candle/standard/semantics; timeout 90 hol run _hol4q_PID.sml; echo "exit=$?"; rm -f _hol4q_PID.sml' % wsl_script).replace('_PID', '_%d' % os.getpid())
    r = subprocess.run(["wsl.exe", "-e", "sh", "-c", sh], capture_output=True)
    out = (r.stdout + r.stderr).decode("utf-8", "replace").replace("\0", "")
    rec = dict(time=time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()), kind=kind, args=args, sml=sml, output=out, seconds=round(time.time() - t0, 1))
    os.makedirs(os.path.join(HERE, "out"), exist_ok=True)
    open(os.path.join(HERE, "out", "query_log.jsonl"), "a", encoding="utf-8").write(json.dumps(rec, ensure_ascii=False) + "\n")
    print(out)


if __name__ == "__main__":
    main()
