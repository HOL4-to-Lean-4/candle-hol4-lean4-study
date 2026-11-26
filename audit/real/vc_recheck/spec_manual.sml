open HolKernel boolLib bossLib;
val _ = new_theory "specprobe";
fun tryp nm q (tac : tactic) =
  (let val th = prove (Parse.Term q, tac) in print ("PROVED " ^ nm ^ " : " ^ thm_to_string th ^ "\n") end)
  handle ex => (print ("FAILED " ^ nm ^ " " ^ exn_to_string ex ^ "\n");
               (proofManagerLib.set_goal ([], Parse.Term q); proofManagerLib.expand tac;
                List.app (fn (_, g) => print ("  GOAL " ^ term_to_string g ^ "\n")) (proofManagerLib.top_goals ())) handle e => print ("  TACERR " ^ exn_to_string e ^ "\n"));
(* CHR: specification char_BIJ with CHR varied at n in P (CHR' n = if P n then g n else CHR n). *)
fun chr nm P =
  tryp nm [QUOTE ("!g. let C = \\n. if " ^ P ^ " then g n else CHR n in (!a. C (ORD a) = a) /\\ (!r. r < 256 <=> ORD (C r) = r)")]
    (simp [LET_THM] >> rpt strip_tac >> rpt COND_CASES_TAC
     >> gvs [stringTheory.CHR_ORD, stringTheory.ORD_CHR_RWT]
     >> TRY (qspec_then `a` assume_tac stringTheory.ORD_BOUND >> gvs [] >> NO_TAC)
     >> TRY (qspec_then `g r` assume_tac stringTheory.ORD_BOUND >> gvs [] >> NO_TAC)
     >> TRY (qspec_then `g 256` assume_tac stringTheory.ORD_BOUND >> qspec_then `g 257` assume_tac stringTheory.ORD_BOUND
             >> qspec_then `g 300` assume_tac stringTheory.ORD_BOUND >> qspec_then `g 301` assume_tac stringTheory.ORD_BOUND >> gvs [] >> NO_TAC)
     >> metis_tac [stringTheory.ORD_CHR, stringTheory.ORD_BOUND]);
val _ = chr "CHR_256" "n = 256";
val _ = chr "CHR_256_257" "(n = 256 \\/ n = 257)";
val _ = chr "CHR_300_301" "(n = 300 \\/ n = 301)";
(* SEG: specification with SEG' m k l = TAKE m (DROP k l) ++ REPLICATE (m - (LENGTH l - k)) a, and SEG' 1 0 [] <> []. *)
val _ = tryp "SEG_spec" `!a:'a. let S = \m k (l:'a list). TAKE m (DROP k l) ++ REPLICATE (m - (LENGTH l - k)) a in
     (!k l. S 0 k l = []) /\ (!m x l. S (SUC m) 0 (x::l) = x :: S m 0 l) /\ (!m k x l. S (SUC m) (SUC k) (x::l) = S (SUC m) k l)`
  (simp [LET_THM]);
val _ = tryp "SEG_witness_fails" `!a:num. TAKE 1 (DROP 0 ([]:num list)) ++ REPLICATE (1 - (LENGTH ([]:num list) - 0)) a <> []` (EVAL_TAC >> simp []);
(* HD: specification HD (h::t) = h with HD' l = if l = [] then g l else HD l. *)
val _ = tryp "HD_spec" `!g. let H = \(l:'a list). if l = [] then g l else HD l in !h t. H (h::t) = h` (simp [LET_THM]);
