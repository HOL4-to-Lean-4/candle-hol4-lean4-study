open HolKernel boolLib bossLib;
(* Constants defined (by a saved definition) from termsem0, transitively, and the saved theorems that mention any of them. *)
val all = List.filter (fn ((t, _), _) => List.exists (fn x => x = t) (ancestry "-")) (DB.listDB ());
fun cid c = let val {Thy, Name, ...} = dest_thy_const c in Thy ^ "$" ^ Name end;
fun consts th = map cid (HOLset.listItems (List.foldl (fn (t, s) => HOLset.addList (s, find_terms is_const t)) empty_tmset (concl th :: hyp th)));
(* the constant a definition defines: head constant of the left side of its first conjunct *)
fun defined th =
  let val c = hd (strip_conj (#2 (strip_forall (concl th))))
      val c = #2 (strip_forall c)
      val l = if is_eq c then lhs c else if is_imp c then (let val r = #2 (dest_imp c) in if is_eq r then lhs r else r end) else c
      val l = if is_neg l then dest_neg l else l
      val (f, _) = strip_comb l
  in if is_const f then SOME (cid f) else NONE end handle _ => NONE;
val defs = List.mapPartial (fn ((t, n), (th, {class = DB.Def, ...} : DB.thminfo)) => (case defined th of SOME d => SOME (d, consts th) | NONE => NONE) | _ => NONE) all;
fun grow C = let val C' = List.foldl (fn ((d, cs), acc) => if List.exists (fn x => List.exists (fn y => x = y) acc) cs andalso not (List.exists (fn y => y = d) acc) then d :: acc else acc) C defs
             in if length C' = length C then C else grow C' end;
val C = grow ["holSemantics$termsem0"];
val _ = print ("CLOSURE " ^ Int.toString (length C) ^ ": " ^ String.concatWith " " C ^ "\n");
val rel = List.filter (fn (_, (th, _)) => List.exists (fn x => List.exists (fn y => x = y) C) (consts th)) all;
val _ = print ("RELEVANT " ^ Int.toString (length rel) ^ "\n");
val _ = List.app (fn ((t, n), _) => print ("R " ^ t ^ "$" ^ n ^ "\n")) rel;
