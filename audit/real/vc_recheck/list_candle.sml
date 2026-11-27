open HolKernel boolLib bossLib;
fun mentions (thy, nm) th = can (find_term (fn t => is_const t andalso #Thy (dest_thy_const t) = thy andalso #Name (dest_thy_const t) = nm)) (list_mk_conj (concl th :: hyp th));
val all = List.filter (fn ((t, _), _) => List.exists (fn x => x = t) (ancestry "-")) (DB.listDB ());
fun count c = print ("COUNT " ^ #2 c ^ " " ^ Int.toString (length (List.filter (fn (_, (th, _)) => mentions c th) all)) ^ "\n");
val _ = List.app count [("holSemantics", "termsem0"), ("holSemantics", "satisfies"), ("holSemantics", "termsem"), ("holSemantics", "is_model"), ("holSemantics", "entails")];
val _ = List.app (fn ((t, n), (th, _)) => if mentions ("holSemantics", "termsem0") th then print ("REL " ^ t ^ "$" ^ n ^ "\n") else ()) all;
val _ = print ("SAT " ^ thm_to_string (DB.fetch "holSemantics" "satisfies_def") ^ "\n");
