val _ = load "typeSoundTheory";
open HolKernel boolLib bossLib;
val _ = Globals.linewidth := 150;
fun pr (thy,c) = List.app (fn (n,th) =>
    if can (find_term (fn t => is_const t andalso #Name (dest_thy_const t) = c andalso #Thy (dest_thy_const t) = thy)) (concl th)
    then print ("@@ "^thy^"."^n^" : "^(thm_to_string th)^"\n") else ()) (DB.definitions thy);
val L = [("location","locnrow"),("location","locn_rowupdate"),("misc","MAP3"),("semanticPrimitivesProps","dest_Refv"),
 ("semanticPrimitivesProps","FV_dec"),("typeSysProps","type_def_to_ctMap"),("semanticPrimitives","the_Litv_IntLit"),("semanticPrimitives","the_Litv_Char"),
 ("list","HD"),("option","THE"),("list","EL"),("pred_set","CARD"),("integer","int_div"),("string","CHR")];
val _ = List.app pr L;
val _ = List.app (fn (n,q,ths) => (print ("@@P "^n^" ");
   (TextIO.flushOut TextIO.stdOut; ignore (prove(q, ths)); print "PROVED\n") handle e => print ("failed\n"))) [
  ("the_Litv", ``the_Litv_IntLit (Litv (Char #"a")) = ARB``, REWRITE_TAC [DB.fetch "semanticPrimitives" "the_Litv_IntLit_def_primitive"] >>
      CONV_TAC (LAND_CONV (RATOR_CONV (REWR_CONV relationTheory.WFREC_THM))) >> simp[]) ];
