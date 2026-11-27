open HolKernel boolLib bossLib;
fun is_c (thy, nm) t = is_const t andalso #Thy (dest_thy_const t) = thy andalso #Name (dest_thy_const t) = nm;
fun mentions c th = can (find_term (is_c c)) (list_mk_conj (concl th :: hyp th));
val all = List.filter (fn ((t, _), _) => List.exists (fn x => x = t) (ancestry "-")) (DB.listDB ());
val _ = show_types := false;
val _ = List.app (fn ((t, n), (th, _)) => if mentions ("holSemantics", "termsem0") th then print ("REL " ^ t ^ "$" ^ n ^ "\n" ^ thm_to_string th ^ "\n") else ()) all;
(* which constants are defined from termsem0: constants on the left of saved definitions whose right side mentions it *)
val sat = DB.fetch "holSemantics" "satisfies_def";
val _ = print ("SATCONST " ^ String.concatWith " " (map (fn c => let val {Thy, Name, ...} = dest_thy_const c in Thy ^ "$" ^ Name end)
  (HOLset.listItems (List.foldl (fn (t, s) => HOLset.addList (s, find_terms is_const t)) empty_tmset [concl sat]))) ^ "\n");
