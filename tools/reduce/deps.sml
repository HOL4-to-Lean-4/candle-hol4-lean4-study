(* Dependency extraction for the closure reduction.
   Usage: hol < deps.sml, with env THYS (space-separated theory names),
   ROOT (thy.name of the main theorem), OUT (output file).
   Writes one line per stored theorem/definition of the listed theories:
     thy <TAB> name <TAB> class <TAB> private <TAB> script <TAB> line <TAB> deps <TAB> consts <TAB> types
   deps: thy.name list of the theorems it depends on (kernel-recorded);
   consts/types: constants and type operators in its statement. *)
val thys = String.tokens Char.isSpace (valOf (OS.Process.getEnv "THYS"));
val _ = app (fn t => load (t ^ "Theory")) thys;
val out = TextIO.openOut (valOf (OS.Process.getEnv "OUT"));

(* depid -> thy.name over all loaded theories *)
val idmap = ref (Redblackmap.mkDict Dep.depid_compare : (Dep.depid, string) Redblackmap.dict);
fun add_thy t =
  List.app (fn ((th_, nm), (th, _)) =>
      case Tag.dep_of (Thm.tag th) of
          Dep.DEP_SAVED (id, _) => idmap := Redblackmap.insert (!idmap, id, th_ ^ "." ^ nm)
        | _ => ())
    (DB.thy t) handle _ => ();
val _ = app add_thy (ancestry "-");

fun depnames th =
  List.mapPartial (fn id => Redblackmap.peek (!idmap, id))
    (Dep.depidl_of (Tag.dep_of (Thm.tag th)));

fun consts_of th =
  let val tms = concl th :: hyp th
      val cs = List.concat (map (find_terms is_const) tms)
      fun nm c = let val {Thy, Name, ...} = dest_thy_const c in Thy ^ "$" ^ Name end
  in Lib.mk_set (map nm cs) end;

fun types_of th =
  let val tms = concl th :: hyp th
      val tys = List.concat (map (fn t => map type_of (find_terms (K true) t)) tms)
      fun ops ty = if is_vartype ty then []
                   else let val {Thy, Tyop, Args} = dest_thy_type ty
                        in (Thy ^ "$" ^ Tyop) :: List.concat (map ops Args) end
  in Lib.mk_set (List.concat (map ops tys)) end;

fun defined_of th =
  let fun heads t = List.concat (map (fn c =>
            let val c' = snd (strip_forall c)
                val c'' = if is_imp c' then snd (dest_imp c') else c'
            in if is_eq c'' then
                 let val (f, _) = strip_comb (lhs c'')
                 in if is_const f then
                      let val {Thy, Name, ...} = dest_thy_const f in [Thy ^ "$" ^ Name] end
                    else [] end
               else [] end) (strip_conj t))
  in Lib.mk_set (heads (concl th)) handle _ => [] end;
fun class_str c = case c of DB.Thm => "Thm" | DB.Axm => "Axm" | DB.Def => "Def";
fun loc_str l = case l of
    DB.Located {scriptpath, linenum, ...} => scriptpath ^ "\t" ^ Int.toString linenum
  | _ => "?\t0";

fun emit t =
  List.app (fn ((th_, nm), (th, info : DB.thminfo)) =>
     TextIO.output (out, String.concatWith "\t"
       [th_, nm, class_str (#class info), Bool.toString (#private info), loc_str (#loc info),
        String.concatWith " " (depnames th),
        String.concatWith " " (consts_of th),
        String.concatWith " " (types_of th),
        String.concatWith " " (defined_of th)] ^ "\n"))
    (DB.thy t);
val _ = app emit thys;
val _ = TextIO.closeOut out;
