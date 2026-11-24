(* Typed kernel export of theorem statements.
   Usage (Linux, from the directory holding the built theories, with HOLDIR/CAKEMLDIR set):
     hol run export_statements.sml   (targets.sml must define  val targets = [(thy,name),...])
   For each target prints one JSON object per line on stdout, prefixed by "@@JSON ".
   Terms are raw: Var / Const (theory, name, type) / Comb / Abs with fully explicit types,
   so no parser, overload or pretty-printer setting affects the result. *)
val _ = load "holSoundnessTheory";
val _ = use "targets.sml";
open HolKernel boolLib;

val buf = TextIO.stdOut;
fun out s = TextIO.output (buf, s);
fun q s =
  let fun c #"\"" = "\\\"" | c #"\\" = "\\\\"
        | c x = if Char.ord x < 32 orelse Char.ord x > 126 then str (Char.chr 92) ^ "u" ^ StringCvt.padLeft #"0" 4 (Int.fmt StringCvt.HEX (Char.ord x)) else str x
  in "\"" ^ String.translate c s ^ "\"" end;

fun ty t =
  if is_vartype t then "{\"tv\":" ^ q (dest_vartype t) ^ "}"
  else let val {Thy, Tyop, Args} = dest_thy_type t
       in "{\"ty\":" ^ q (Thy ^ "$" ^ Tyop) ^ ",\"args\":[" ^ String.concatWith "," (map ty Args) ^ "]}" end;

fun tm t =
  if is_var t then let val (n, y) = dest_var t in "{\"v\":" ^ q n ^ ",\"t\":" ^ ty y ^ "}" end
  else if is_const t then let val {Thy, Name, Ty} = dest_thy_const t
       in "{\"c\":" ^ q (Thy ^ "$" ^ Name) ^ ",\"t\":" ^ ty Ty ^ "}" end
  else if is_comb t then let val (f, x) = dest_comb t in "{\"f\":" ^ tm f ^ ",\"x\":" ^ tm x ^ "}" end
  else let val (b, body) = dest_abs t
       in let val (n, y) = dest_var b in "{\"abs\":{\"v\":" ^ q n ^ ",\"t\":" ^ ty y ^ "},\"body\":" ^ tm body ^ "}" end end;

val _ = show_types := true;
fun one (thy, name) =
  let val th = DB.fetch thy name
      val _ = Globals.linewidth := 120
      val pp = thm_to_string th
  in
    out ("@@JSON {\"thy\":" ^ q thy ^ ",\"name\":" ^ q name
       ^ ",\"hyps\":[" ^ String.concatWith "," (map tm (hyp th))
       ^ "],\"concl\":" ^ tm (concl th) ^ ",\"pretty\":" ^ q pp ^ "}\n")
  end handle e => out ("@@MISSING {\"thy\":" ^ q thy ^ ",\"name\":" ^ q name ^ ",\"err\":" ^ q (exnMessage e) ^ "}\n");
val _ = app one targets;
val _ = TextIO.flushOut buf;
