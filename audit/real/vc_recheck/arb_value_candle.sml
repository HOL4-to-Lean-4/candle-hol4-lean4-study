open HolKernel boolLib bossLib;
val _ = new_theory "arbprobe";
(* Redefine a copy of the constant from its stored equations, then read the primitive (kernel) definition HOL4 makes for it. *)
fun copy_def (thy, cname, defname, newname) =
  let val th = DB.fetch thy defname
      val c = prim_mk_const {Thy = thy, Name = cname}
      val v = mk_var (newname, type_of c)
      fun sub t = if is_const t andalso #Name (dest_thy_const t) = cname andalso #Thy (dest_thy_const t) = thy then inst (match_type (type_of c) (type_of t)) v
                  else if is_comb t then mk_comb (sub (rator t), sub (rand t)) else if is_abs t then let val (x, b) = dest_abs t in mk_abs (x, sub b) end else t
      val eqs = list_mk_conj (map (fn t => #2 (strip_forall (sub t))) (strip_conj (concl (SPEC_ALL th))))
      val _ = print ("EQS " ^ term_to_string eqs ^ "\n")
      val d = Define [ANTIQUOTE eqs]
      val prim = CONJ (DB.fetch "-" (newname ^ "_def_curried")) (DB.fetch "-" (newname ^ "_def_tupled_primitive"))
  in print ("PRIM " ^ thm_to_string prim ^ "\n"); (d, prim) end
  handle e => (print ("COPYFAIL " ^ newname ^ " " ^ exn_to_string e ^ "\n"); (TRUTH, TRUTH));
val _ = List.app (fn ((t, n), _) => if String.isPrefix "my" n then print ("NAME " ^ n ^ "\n") else ()) [];
val (tm, tmp) = copy_def ("holSemantics", "termsem0", "termsem_def", "mytermsem");
fun tryp nm q tac = (TAC_PROOF (([], Parse.Term q), tac); print ("PROVED " ^ nm ^ "\n")) handle e => print ("FAILED " ^ nm ^ "\n");
val tacp = fn p => (rpt gen_tac >> ONCE_REWRITE_TAC [CONJUNCT1 p] >> ONCE_REWRITE_TAC [CONJUNCT2 p] >> simp [relationTheory.WFREC_DEF]);
val _ = tryp "termsem" `!mem tmsig i v a b. (!x ty. a <> Var x ty) ==> mytermsem mem tmsig i v (Abs a b) = ARB` (tacp tmp >> Cases_on `a` >> fs []);
