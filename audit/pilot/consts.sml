val _ = load "holSoundnessTheory"; open HolKernel boolLib bossLib;
val thys = ["misc","mllist","mlstring","setSpec","holSyntaxLib","holSyntax","holSyntaxExtra","holSemantics","holSemanticsExtra","holSoundness"];
val _ = app (fn t => app (fn c => let val {Thy,Name,Ty} = dest_thy_const c in print ("CONST\t" ^ Thy ^ "\t" ^ Name ^ "\t" ^ Int.toString (length (type_vars Ty)) ^ "\t" ^ String.translate (fn #"\n" => " " | c => str c) (type_to_string Ty) ^ "\n") end) (constants t)) thys;
