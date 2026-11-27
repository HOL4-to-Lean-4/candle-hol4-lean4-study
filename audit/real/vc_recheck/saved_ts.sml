(* Saved-theorem reading (author, 27 Nov): a counterexample for MAP3 and type_def_to_ctMap that satisfies every saved theorem mentioning them.
   The replacement is defined by the saved clauses plus a catch-all clause with an arbitrary function g. *)
open HolKernel boolLib bossLib;
val _ = new_theory "savedts";
fun tryp nm q (tac : tactic) =
  (let val th = prove (Parse.Term q, tac) in print ("PROVED " ^ nm ^ " : " ^ thm_to_string th ^ "\n") end)
  handle ex => print ("FAILED " ^ nm ^ " " ^ exn_to_string ex ^ "\n");

val MAP3g_def = Define `
  (MAP3g g f [] [] [] = []) /\
  (MAP3g g f (h1::t1) (h2::t2) (h3::t3) = f h1 h2 h3 :: MAP3g g f t1 t2 t3) /\
  (MAP3g g f l1 l2 l3 = g f l1 l2 l3)`;
(* saved theorem misc$MAP3_def with MAP3 := MAP3g g *)
val _ = tryp "MAP3_def" `!g. (!f. MAP3g g f [] [] [] = []) /\
    !t3 t2 t1 h3 h2 h1 f. MAP3g g f (h1::t1) (h2::t2) (h3::t3) = f h1 h2 h3 :: MAP3g g f t1 t2 t3` (rw [MAP3g_def]);
(* the open values are g: so MAP3 f [] [x] [] and MAP3 f [x] [] [] can be anything, in particular different from ARB and from each other *)
val _ = tryp "MAP3_open_a" `!g f h t. MAP3g g f [] (h::t) [] = g f [] (h::t) []` (rw [MAP3g_def]);
val _ = tryp "MAP3_open_b" `!g f h t. MAP3g g f (h::t) [] [] = g f (h::t) [] []` (rw [MAP3g_def]);

val tdcg_def = Define `
  (tdcg g tenvT next_stamp [] [] = []) /\
  (tdcg g tenvT next_stamp ((tvs,tn,ctors)::tds) (id::ids) =
     tdcg g tenvT (next_stamp + 1) tds ids ++
     REVERSE (MAP (\(cn,ts). (TypeStamp cn next_stamp,tvs,MAP (type_name_subst tenvT) ts,id)) ctors)) /\
  (tdcg g tenvT next_stamp tds ids = g tenvT next_stamp tds ids)`;
val _ = tryp "type_def_to_ctMap_def" `!g. (!tenvT next_stamp. tdcg g tenvT next_stamp [] [] = []) /\
    !tvs tn tenvT tds next_stamp ids id ctors.
      tdcg g tenvT next_stamp ((tvs,tn,ctors)::tds) (id::ids) =
      tdcg g tenvT (next_stamp + 1) tds ids ++
      REVERSE (MAP (\(cn,ts). (TypeStamp cn next_stamp,tvs,MAP (type_name_subst tenvT) ts,id)) ctors)` (rw [tdcg_def]);
(* on equal lengths the replacement is the HOL4 constant, so the three saved theorems with LENGTH tds = LENGTH ids carry over *)
val eq_len = prove (``!tds ids g tenvT n. LENGTH tds = LENGTH ids ==> tdcg g tenvT n tds ids = type_def_to_ctMap tenvT n tds ids``,
  Induct >- (Cases >> rw [tdcg_def, typeSysPropsTheory.type_def_to_ctMap_def]) >>
  qx_gen_tac `p` >> PairCases_on `p` >> Cases >> rw [tdcg_def, typeSysPropsTheory.type_def_to_ctMap_def]);
val _ = print ("PROVED eq_len : " ^ thm_to_string eq_len ^ "\n");
val _ = tryp "ctMap_ok_type_defs" `!g tenvT next tds tids.
    ALL_DISTINCT tids /\ DISJOINT (set tids) (set prim_type_nums) /\ LENGTH tds = LENGTH tids /\ check_ctor_tenv tenvT tds /\ tenv_abbrev_ok tenvT ==>
    ctMap_ok (FEMPTY |++ REVERSE (tdcg g tenvT next tds tids))` (metis_tac [eq_len, typeSysPropsTheory.ctMap_ok_type_defs]);
val _ = tryp "mem_type_def_to_ctMap" `!g tenvT next tds ids stamp x.
    MEM (stamp,x) (tdcg g tenvT next tds ids) /\ LENGTH tds = LENGTH ids ==> ?cn i. stamp = TypeStamp cn i /\ next <= i /\ i < next + LENGTH tds`
  (metis_tac [eq_len, typeSysPropsTheory.mem_type_def_to_ctMap]);
val _ = tryp "type_def_to_ctMap_mem" `!g tenvT next tds tids k x.
    ALOOKUP (tdcg g tenvT next tds tids) k = SOME x /\ LENGTH tds = LENGTH tids ==> MEM (SND (SND x)) tids`
  (metis_tac [eq_len, typeSysPropsTheory.type_def_to_ctMap_mem]);
val _ = tryp "tdc_open" `!g tenvT n i is. tdcg g tenvT n [] (i::is) = g tenvT n [] (i::is)` (rw [tdcg_def]);
