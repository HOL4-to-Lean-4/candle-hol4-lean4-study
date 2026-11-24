val _ = load "typeSoundTheory";
open HolKernel boolLib bossLib;
val _ = new_theory "scratchq";
val prim = DB.fetch "semanticPrimitives" "the_Litv_IntLit_def_primitive";
val _ = (let val wf = prove(``WF (@R:'a->'a->bool. WF R)``, SELECT_ELIM_TAC >> metis_tac [relationTheory.WF_EMPTY_REL])
  val th = prove(``the_Litv_IntLit (Litv (Char #"a")) = ARB``,
    simp [prim, MATCH_MP relationTheory.WFREC_THM (INST_TYPE [alpha |-> fst (dom_rng (type_of (lhs (concl prim))))] wf)])
  in print ("@@PROVED "^thm_to_string th^"\n") end) handle e => print ("@@FAIL "^General.exnMessage e^"\n");
