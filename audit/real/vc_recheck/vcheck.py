"""Stricter V-C test (plan v3.4, section 3): check a counterexample interpretation against every saved theorem that mentions the constant.

  python vcheck.py SPEC.json [KEY_DECL[/FAMILY] ...]      (default: all entries)

For each entry the constant c (Theory$name, n curried arguments) is replaced by
    c' = \\x1 .. xn. if P x1 .. xn then g x1 .. xn else c x1 .. xn        (g a fresh variable: an arbitrary function)
in every theorem, definition and axiom of the loaded theories (the package and all its HOL4 ancestors) whose conclusion or
hypotheses mention c at any type. For each such theorem T, HOL4 tries to prove the closure of T[c'/c] (so for every g) with a
few fixed tactics and the original T as a lemma, each with a time limit. Theorems that do not mention c keep their truth
value, because only c changes. If every theorem is proved, any equation that fixes c inside P to one value (or relates two
points of P, or a point of P to another constant) is not a consequence of the saved theorems: label V-C. If any theorem is
not proved, the label is "unsure" (a failed proof is not a refutation). Results go to results/<entry>.json and the HOL4 log
to logs/. Needs HOL4 in WSL: ~/candle_build/repo (Candle) and ~/ts_build/hol4-ultramin (type soundness).
"""
import json, os, re, subprocess, sys, tempfile, time

HERE = os.path.dirname(os.path.abspath(__file__))
ENV = 'B=$HOME/candle_build/repo/_build; export PATH=$B/polyml/bin:$B/HOL/bin:$PATH LD_LIBRARY_PATH=$B/polyml/lib HOLDIR=$B/HOL CAKEMLDIR=$HOME/candle_build/repo/package; '
CTX = {
    "candle": ("$HOME/candle_build/repo/package/candle/standard/semantics", ["holSoundnessTheory"]),
    "ts": ("$HOME/ts_build/hol4-ultramin", ["typeSoundTheory", "weakeningTheory", "typeSysPropsTheory", "evaluatePropsTheory", "semantics_minTheory",
                                             "semanticPrimitivesPropsTheory", "namespacePropsTheory", "typeSoundInvariantsTheory"]),
}
TIME = 15.0


def sml_str(s):
    return '"' + s.replace("\\", "\\\\").replace('"', '\\"') + '"'


def sml(e):
    _, loads = CTX[e["family"]]
    thy, name = e["hol_const"].split("$")
    args = e["args"]
    lam = "\\" + " ".join("(%s:%s)" % (a, t) for a, t in args) + ". " + e["P"] if args else ""
    return r'''
val _ = List.app load ("smlTimeout" :: %(loads)s);
open HolKernel boolLib bossLib;
val _ = new_theory "vcheck_scratch";
val c0 = prim_mk_const {Thy = %(thy)s, Name = %(name)s};
val n = %(n)d;
val (dom, rng) = strip_fun (type_of c0);
val dom = List.take (dom, n);
val rng = List.foldr (op -->) rng (List.drop (#1 (strip_fun (type_of c0)), n)) handle _ => rng;
val xs = List.tabulate (n, fn i => mk_var ("vcx" ^ Int.toString i, List.nth (dom, i)));
val g = mk_var ("vc_g", List.foldr (op -->) rng dom);
val cprime =
  if n = 0 then g else
  let val P0 = Parse.Term [QUOTE %(lam)s]
      val theta = match_type (type_of P0) (List.foldr (op -->) bool dom)
      val P = inst theta P0
      val body = mk_cond (rhs (concl (QCONV (DEPTH_CONV BETA_CONV) (list_mk_comb (P, xs)))),list_mk_comb (g, xs), list_mk_comb (c0, xs))
  in list_mk_abs (xs, body) end;
val _ = print ("CPRIME " ^ term_to_string cprime ^ " : " ^ type_to_string (type_of cprime) ^ "\n");
fun same a b = is_const b andalso let val x = dest_thy_const a val y = dest_thy_const b in #Thy x = #Thy y andalso #Name x = #Name y end;
fun repl_with subs t =
  case List.find (fn (k, _) => same k t) subs of
    SOME (k, v) => inst (match_type (type_of k) (type_of t)) v
  | NONE =>
    if is_comb t then mk_comb (repl_with subs (rator t), repl_with subs (rand t))
    else if is_abs t then let val (v, b) = dest_abs t in mk_abs (v, repl_with subs b) end
    else t;
(* constants that must change together with c (their definitions use c): replacement given in closed form, with c inside *)
val cov = map (fn (cthy, cname, s) =>
  let val d0 = prim_mk_const {Thy = cthy, Name = cname}
      val t0 = Parse.Term [QUOTE s]
      val t1 = inst (match_type (type_of t0) (type_of d0)) t0
  in (d0, repl_with [(c0, cprime)] t1) end) %(cov)s;
val subs = (c0, cprime) :: cov;
val _ = List.app (fn (k, v) => print ("COVARY " ^ term_to_string k ^ " := " ^ term_to_string v ^ "\n")) cov;
val repl = repl_with subs;
fun is_c t = List.exists (fn (k, _) => same k t) subs;
fun mentions th = List.exists (fn t => can (find_term is_c) t) (concl th :: hyp th);
val thys = ancestry "-";
val all = List.filter (fn ((th, _), _) => List.exists (fn x => x = th) thys) (DB.listDB ());
val rel = List.filter (fn (_, (th, _)) => mentions th) all;
val _ = print ("RELEVANT " ^ Int.toString (length rel) ^ "\n");
fun cls DB.Thm = "thm" | cls DB.Axm = "axiom" | cls DB.Def = "def";
fun try_tacs goal th =
  let val tacs = [("rw", rw [] THEN gvs [] THEN NO_TAC),
                  ("rw_metis", rw [] THEN gvs [] THEN metis_tac [th]),
                  ("metis", metis_tac [th]),
                  ("rw_simp_th", rw [] THEN gvs [th] THEN NO_TAC),
                  ("split_metis", rpt strip_tac THEN rpt (COND_CASES_TAC THEN gvs []) THEN metis_tac [th])]
      fun go [] = "FAILED"
        | go ((nm, tac) :: rest) =
            ((smlTimeout.timeout %(time)s (fn () => Tactical.TAC_PROOF (([], goal), tac)) (); nm)
             handle _ => go rest)
  in go tacs end;
fun check ((thy, nm), (th, {class = cl, private = pv, loc = _} : DB.thminfo)) =
  let val goal = gen_all (list_mk_imp (map repl (hyp th), repl (concl th)))
      val r = if aconv goal (gen_all (list_mk_imp (hyp th, concl th))) then "unchanged" else try_tacs goal th
  in print ("RESULT\t" ^ thy ^ "\t" ^ nm ^ "\t" ^ cls cl ^ (if pv then "/local" else "") ^ "\t" ^ r ^ "\n") end
  handle e => print ("RESULT\t" ^ thy ^ "\t" ^ nm ^ "\t" ^ cls cl ^ (if pv then "/local" else "") ^ "\tERROR " ^ String.translate (fn #"\n" => " " | c => str c) (exn_to_string e) ^ "\n");
val _ = List.app check rel;
val _ = print "DONE\n";
''' % dict(loads="[" + ",".join(sml_str(l) for l in loads) + "]", thy=sml_str(thy), name=sml_str(name), n=len(args), lam=sml_str(lam or "T"), time=repr(TIME),
           cov="[" + ",".join("(%s, %s, %s)" % (sml_str(c["const"].split("$")[0]), sml_str(c["const"].split("$")[1]), sml_str(c["term"])) for c in e.get("covary", [])) + "]")


def run(e):
    tag = re.sub(r"\W", "_", "%s_%s_%s" % (e["key_decl"], e["family"], "_".join(e.get("translations", [])) or "all"))[:90]
    src = sml(e)
    os.makedirs(HERE + "/logs", exist_ok=True)
    os.makedirs(HERE + "/results", exist_ok=True)
    p = os.path.join(tempfile.gettempdir(), "vcheck_%s.sml" % tag)
    open(p, "w", encoding="utf-8", newline="\n").write(src)
    wp = subprocess.run(["wsl.exe", "-e", "wslpath", "-a", p.replace("\\", "/")], capture_output=True).stdout.decode().replace("\0", "").strip()
    d, _ = CTX[e["family"]]
    sh = ENV + 'cd %s; cp "%s" _vcheck_%s.sml; timeout 7200 hol run _vcheck_%s.sml; echo "exit=$?"; rm -f _vcheck_%s.sml' % (d, wp, tag, tag, tag)
    t0 = time.time()
    r = subprocess.run(["wsl.exe", "-e", "sh", "-c", sh], capture_output=True)
    out = (r.stdout + r.stderr).decode("utf-8", "replace").replace("\0", "")
    open(HERE + "/logs/%s.log" % tag, "w", encoding="utf-8", newline="\n").write(src + "\n==== OUTPUT ====\n" + out)
    res = [l.split("\t")[1:] for l in out.split("\n") if l.startswith("RESULT\t")]
    rel = re.search(r"RELEVANT (\d+)", out)
    cp = re.search(r"CPRIME (.*)", out)
    ok = bool(re.search(r"^DONE$", out, re.M)) and rel is not None and len(res) == int(rel.group(1))
    bad = [x for x in res if x[3] not in ("rw", "rw_metis", "metis", "rw_simp_th", "split_metis", "unchanged")]
    verdict = "error" if not ok else ("V-C" if not bad else "unsure")
    rec = dict(entry=e, cprime=cp.group(1) if cp else None, relevant=int(rel.group(1)) if rel else None, checked=len(res),
               proved=len(res) - len(bad), not_proved=[x[:3] + [x[3]] for x in bad], results=res, verdict=verdict,
               seconds=round(time.time() - t0), log="logs/%s.log" % tag)
    json.dump(rec, open(HERE + "/results/%s.json" % tag, "w", encoding="utf-8"), ensure_ascii=False, indent=1)
    print("%-60s %-7s relevant=%s proved=%d not=%d %ds" % (tag, verdict, rec["relevant"], rec["proved"], len(bad), rec["seconds"]))
    return rec


if __name__ == "__main__":
    from concurrent.futures import ThreadPoolExecutor
    a = sys.argv[1:]
    jobs = 1
    if a[0] == "--jobs":
        jobs, a = int(a[1]), a[2:]
    spec = json.load(open(a[0], encoding="utf-8"))
    want = a[1:]
    sel = [e for e in spec if not want or e["key_decl"] in want or e["key_decl"] + "/" + e["family"] in want]
    with ThreadPoolExecutor(jobs) as ex:
        list(ex.map(run, sel))
