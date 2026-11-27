open HolKernel boolLib bossLib;
fun pr (n, th) = print ("F " ^ n ^ " : " ^ thm_to_string th ^ "\n");
fun look s = List.app (fn ((t, n), (th, _, _)) => pr (t ^ "$" ^ n, th)) (List.filter (fn ((_, n), _) => n = s) (DB.find s));
val _ = List.app look ["WELLTYPED_CLAUSES", "term_ok_welltyped", "VSUBST_WELLTYPED", "INST_WELLTYPED", "simple_inst_has_type", "simple_subst_has_type", "VSUBST_HAS_TYPE", "INST_HAS_TYPE", "welltyped_equation", "theory_ok_def", "entails_def", "models_def", "is_structure_def"];
