open HolKernel boolLib bossLib;
fun mentions (thy, nm) th = can (find_term (fn t => is_const t andalso #Thy (dest_thy_const t) = thy andalso #Name (dest_thy_const t) = nm)) (list_mk_conj (concl th :: hyp th));
val all = List.filter (fn ((t, _), _) => List.exists (fn x => x = t) (ancestry "-")) (DB.listDB ());
fun show c = List.app (fn ((t, n), (th, _)) => if mentions c th then print ("REL " ^ #2 c ^ "\t" ^ t ^ "$" ^ n ^ "\n" ^ thm_to_string th ^ "\n") else ()) all;
val _ = show ("misc", "MAP3");
val _ = show ("typeSysProps", "type_def_to_ctMap");
