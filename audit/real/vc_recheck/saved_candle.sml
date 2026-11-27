(* Saved-theorem reading (author, 27 Nov): a counterexample for termsem0 (Abs of a non-variable) that satisfies every saved theorem
   mentioning termsem0 or a constant defined from it (satisfies0, models0, entails0): 25 theorems up to holSoundness.
   termsemg g is defined by the saved clauses of termsem_def plus an arbitrary value g for the other cases; satisfies, models and entails
   are redefined from it by their saved definitions. *)
open HolKernel boolLib bossLib listTheory holSyntaxTheory holSyntaxExtraTheory holSemanticsTheory holSemanticsExtraTheory holSoundnessTheory;
val _ = new_theory "savedcandle";
val _ = load "smlTimeout";
(* try each tactic with a time limit; print the first that proves the goal, or the goals left by the first tactic *)
fun tryl nm t (tacs : tactic list) secs =
  let fun go [] k = (print ("FAILED " ^ nm ^ "\n");
                     (proofManagerLib.set_goal ([], t);
                      smlTimeout.timeout secs (fn () => proofManagerLib.expand (hd tacs)) ();
                      List.app (fn (asl, g) => print ("  GOAL " ^ term_to_string g ^ "\n     ASMS " ^ String.concatWith " ;; " (map term_to_string asl) ^ "\n")) (proofManagerLib.top_goals ())) handle _ => ();
                     NONE)
        | go (tac :: rest) k = (let val th = smlTimeout.timeout secs (fn () => prove (t, tac)) () in print ("PROVED " ^ nm ^ " (tactic " ^ Int.toString k ^ ")\n"); SOME th end
                                handle _ => go rest (k + 1))
  in go tacs 1 end;
fun tryp nm t tac = tryl nm t [tac] 120.0;

fun cst thy n = prim_mk_const {Thy = thy, Name = n};
val T0 = cst "holSemantics" "termsem0" and S0 = cst "holSemantics" "satisfies0" and M0 = cst "holSemantics" "models0" and E0 = cst "holSemantics" "entails0";
val gty = type_of T0;
val g = mk_var ("g", gty);
fun gv n c = mk_var (n, gty --> type_of c);
val TG = gv "termsemg" T0 and SG = gv "satg" S0 and MG = gv "modelsg" M0 and EG = gv "entailsg" E0;
fun same a b = is_const b andalso let val x = dest_thy_const a val y = dest_thy_const b in #Thy x = #Thy y andalso #Name x = #Name y end;
fun subst_c subs t =
  case List.find (fn (k, _) => same k t) subs of
    SOME (k, v) => inst (match_type (type_of k) (type_of t)) v
  | NONE => if is_comb t then mk_comb (subst_c subs (rator t), subst_c subs (rand t))
            else if is_abs t then let val (x, b) = dest_abs t in mk_abs (x, subst_c subs b) end else t;
val subs = [(T0, mk_comb (TG, g)), (S0, mk_comb (SG, g)), (M0, mk_comb (MG, g)), (E0, mk_comb (EG, g))];
val R = subst_c subs;
fun eqs th = list_mk_conj (map (fn t => #2 (strip_forall (R t))) (strip_conj (#2 (strip_forall (concl th)))));

(* termsemg: the four saved clauses, then g for every other term *)
val catch = let val (dom, _) = strip_fun gty val xs = ListPair.map (fn (n, ty) => mk_var (n, ty)) (["mem", "tmsig", "i", "v", "t"], dom)
            in mk_eq (list_mk_comb (TG, g :: xs), list_mk_comb (g, xs)) end;
val _ = print ("DEFT " ^ term_to_string (list_mk_conj (strip_conj (eqs termsem_def) @ [catch])) ^ "\n");
val termsemg_def = Define [ANTIQUOTE (list_mk_conj (strip_conj (eqs termsem_def) @ [catch]))];
val termsemg_c = prim_mk_const {Thy = "savedcandle", Name = "termsemg"};
fun fix t = subst [TG |-> termsemg_c] t handle _ => t;
val satg_def = Define [ANTIQUOTE (fix (eqs satisfies_def))];
val satg_c = prim_mk_const {Thy = "savedcandle", Name = "satg"};
val modelsg_def = Define [ANTIQUOTE (subst [SG |-> satg_c] (fix (eqs models_def)))];
val modelsg_c = prim_mk_const {Thy = "savedcandle", Name = "modelsg"};
val entailsg_def = Define [ANTIQUOTE (subst [MG |-> modelsg_c, SG |-> satg_c] (fix (eqs entails_def)))];
val entailsg_c = prim_mk_const {Thy = "savedcandle", Name = "entailsg"};
fun RR t = subst [TG |-> termsemg_c, SG |-> satg_c, MG |-> modelsg_c, EG |-> entailsg_c] (R t);
fun goal_of th = let val t = list_mk_imp (hyp th, concl th) in mk_forall (g, gen_all (RR t)) end;

(* the open value: on the whole region P (Abs a b with a not a variable), termsemg is g *)
val _ = tryp "open_value" ``!g mem tmsig i v a b. (!x ty. a <> Var x ty) ==> termsemg g mem tmsig i v (Abs a b) = g mem tmsig i v (Abs a b)``
  (Cases_on `a` >> rw [termsemg_def]);
(* on well-typed terms termsemg is termsem0 *)
val WT = Option.valOf (tryp "welltyped_agree" ``!t g mem tmsig i v. welltyped t ==> termsemg g mem tmsig i v t = termsem0 mem tmsig i v t``
  (Induct >> rw [WELLTYPED_CLAUSES] >> rw [termsemg_def, termsem_def] >> rw [FUN_EQ_THM]));
val SAT = Option.valOf (tryp "satisfies_agree" ``!g mem i sig h c. EVERY welltyped (c::h) ==> (satg g mem i (sig,h,c) <=> satisfies0 mem i (sig,h,c))``
  (rw [satg_def, satisfies_def] >> fs [EVERY_MEM] >> metis_tac [WT]));
val MOD = Option.valOf (tryp "models_agree" ``!g mem i thy. theory_ok thy ==> (modelsg g mem i thy <=> models0 mem i thy)``
  (rw [modelsg_def, models_def, theory_ok_def] >> metis_tac [SAT, EVERY_DEF, term_ok_welltyped]));
val ENT = Option.valOf (tryp "entails_agree" ``!g mem. entailsg g mem = entails0 mem``
  (rw [FUN_EQ_THM, pairTheory.FORALL_PROD, entailsg_def, entails_def] >> EQ_TAC >> rw [] >> fs [EVERY_MEM] >>
   metis_tac [SAT, MOD, EVERY_MEM, MEM, term_ok_welltyped]));

val MAPWT = Option.valOf (tryp "map_agree" ``!g mem G i v ilist.
    (!s s'. MEM (s',s) ilist ==> ?x ty. s = Var x ty /\ s' has_type ty) ==>
    MAP ((dest_var ## termsemg g mem G i v) o (\(s',s). (s,s'))) (REVERSE ilist) =
    MAP ((dest_var ## termsem0 mem G i v) o (\(s',s). (s,s'))) (REVERSE ilist)``
  (rw [listTheory.MAP_EQ_f, listTheory.MEM_REVERSE] >> PairCases_on `e` >> rw [] >> res_tac >> metis_tac [WT, welltyped_def]));

val names = [("holSemantics", "entails_def"), ("holSemantics", "models_def"), ("holSemantics", "satisfies_def"), ("holSemantics", "termsem_def"),
  ("holSemanticsExtra", "termsem_aconv"), ("holSemanticsExtra", "termsem_Equal"), ("holSemanticsExtra", "termsem_equation"), ("holSemanticsExtra", "termsem_frees"),
  ("holSemanticsExtra", "termsem_INST"), ("holSemanticsExtra", "termsem_raconv"), ("holSemanticsExtra", "termsem_simple_inst"), ("holSemanticsExtra", "termsem_simple_subst"),
  ("holSemanticsExtra", "termsem_typesem"), ("holSemanticsExtra", "termsem_VSUBST"), ("holSoundness", "ABS_correct"), ("holSoundness", "ASSUME_correct"),
  ("holSoundness", "BETA_correct"), ("holSoundness", "binary_inference_rule"), ("holSoundness", "DEDUCT_ANTISYM_correct"), ("holSoundness", "EQ_MP_correct"),
  ("holSoundness", "INST_correct"), ("holSoundness", "INST_TYPE_correct"), ("holSoundness", "MK_COMB_correct"), ("holSoundness", "proves_sound"), ("holSoundness", "REFL_correct")];
val WTS = [WT, SAT, MOD, ENT, MAPWT, term_ok_welltyped, VSUBST_WELLTYPED, INST_WELLTYPED, welltyped_def, simple_inst_has_type, simple_subst_has_type, VSUBST_HAS_TYPE, INST_HAS_TYPE, welltyped_equation];
fun tacs orig =
  [rw [termsemg_def, satg_def, modelsg_def, entailsg_def] >> NO_TAC,
         rw [ENT] >> metis_tac [orig],
         rpt strip_tac >> fs [ENT] >> imp_res_tac term_ok_welltyped >> rfs [WT, MAPWT, VSUBST_WELLTYPED, INST_WELLTYPED, termsemg_def] >> metis_tac [orig],
         rpt strip_tac >> fs [ENT] >> rfs [entails_def] >> imp_res_tac term_ok_welltyped >> rfs [WT] >> metis_tac [orig, WT, term_ok_welltyped],
         rpt strip_tac >> imp_res_tac term_ok_welltyped >> rfs [WT, termsemg_def] >> metis_tac (orig :: WTS)];
(* targeted tactics: each shows the terms involved are well typed, rewrites termsemg to termsem0 there, then uses the original theorem *)
fun showg (asl, w) = (print ("  GOAL " ^ term_to_string w ^ "\n     ASMS " ^ String.concatWith " ;; " (map term_to_string asl) ^ "\n"); ALL_TAC (asl, w));
(* WT at the type 'U of the theorems, so that imp_res_tac gives usable assumptions *)
val WTU = INST_TYPE [alpha |-> mk_vartype "'U"] WT;
fun ent orig = rpt gen_tac >> PURE_REWRITE_TAC [ENT] >> MATCH_ACCEPT_TAC orig;
fun extra n orig =
  case n of
    "termsem_Equal" => let val pre = rpt strip_tac >> `welltyped (Equal ty)` by simp [] >> imp_res_tac WTU >> ASM_REWRITE_TAC []
                       in [pre >> irule orig >> rw [] >> qexistsl_tac [`p1`, `p2`] >> fs [],
          pre >> irule orig >> rw [] >> qexistsl_tac [`p1`, `p2`] >> rfs [] >> metis_tac [],
          pre >> irule orig >> metis_tac [], pre >> metis_tac [orig], pre >> showg >> NO_TAC] end
  | "termsem_equation" => [rpt strip_tac >> imp_res_tac term_ok_welltyped >>
        `welltyped s /\ welltyped t` by (qpat_x_assum `welltyped (_ === _)` mp_tac >> rw [equation_def, WELLTYPED_CLAUSES]) >>
        simp [WT] >> metis_tac [orig]]
  | "termsem_INST" => let val pre = rpt strip_tac >> imp_res_tac term_ok_welltyped >> `welltyped (INST tyin tm)` by metis_tac [INST_WELLTYPED] >>
                                    imp_res_tac WTU >> ASM_REWRITE_TAC []
                      in [pre >> irule orig >> rw [] >> qexistsl_tac [`p1`, `p2`] >> fs [],
          pre >> irule orig >> rw [] >> qexistsl_tac [`p1`, `p2`] >> rfs [] >> metis_tac [],
          pre >> irule orig >> metis_tac [], pre >> metis_tac [orig], pre >> showg >> NO_TAC] end
  | "termsem_simple_inst" => let val pre = rpt strip_tac >> `welltyped (simple_inst tyin tm)` by metis_tac [simple_inst_has_type, welltyped_def] >>
                                    imp_res_tac WTU >> ASM_REWRITE_TAC []
                      in [pre >> irule orig >> rw [] >> qexistsl_tac [`p1`, `p2`] >> fs [],
          pre >> irule orig >> rw [] >> qexistsl_tac [`p1`, `p2`] >> rfs [] >> metis_tac [],
          pre >> irule orig >> metis_tac [], pre >> metis_tac [orig], pre >> showg >> NO_TAC] end
  | "termsem_simple_subst" => [rpt strip_tac >>
        `welltyped (simple_subst ilist tm)` by (fs [welltyped_def] >> qexists_tac `ty` >> irule simple_subst_has_type >> rw [EVERY_MEM, pairTheory.FORALL_PROD] >>
           res_tac >> rw [typeof_def]) >>
        simp [WT, MAPWT] >> metis_tac [orig]]
  | "binary_inference_rule" => let val pre0 = rpt strip_tac >> fs [ENT]
                                   val pre = pre0 >> `welltyped p1 /\ welltyped p2 /\ welltyped q` by (fs [entails_def] >> metis_tac [welltyped_def, term_ok_welltyped]) >>
                                             imp_res_tac WTU >> fs []
      in [pre >> irule orig >> rw [] >> qexistsl_tac [`p1`, `p2`] >> fs [],
          pre >> irule orig >> rw [] >> qexistsl_tac [`p1`, `p2`] >> rfs [] >> metis_tac [],
          pre >> irule orig >> metis_tac [],
          pre >> mp_tac orig >> asm_rewrite_tac [] >> disch_then (qspecl_then [`thy`, `h1`, `h2`, `p1`, `p2`, `q`] mp_tac) >> asm_rewrite_tac [],
          pre0 >> fs [entails_def] >> showg >> NO_TAC, pre >> showg >> NO_TAC] end
  | _ => [ent orig];
val failing = ["termsem_Equal", "termsem_equation", "termsem_INST", "termsem_simple_inst", "termsem_simple_subst", "ABS_correct", "BETA_correct",
               "binary_inference_rule", "INST_TYPE_correct", "MK_COMB_correct"];
val failing2 = ["binary_inference_rule"];
val run = case OS.Process.getEnv "ONLY_FAILING" of SOME _ => List.filter (fn (_, n) => List.exists (fn x => x = n) failing2) names | NONE => names;
val _ = List.app (fn (t, n) => let val th = DB.fetch t n
                                   val ts = (if List.exists (fn x => x = n) failing then extra n th else []) @ tacs th
                               in ignore (tryl (t ^ "$" ^ n) (goal_of th) (ts @ [showg >> NO_TAC]) 30.0) end) run;
