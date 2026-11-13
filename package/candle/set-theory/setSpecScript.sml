(*
  Specification of (roughly) Zermelo's set theory.
  Two main definitions:
    is_set_theory (mem : 'U -> 'U -> bool), and
    is_model (mem, indset, ch)
*)
Theory setSpec
Ancestors
  cardinal
Libs
  preamble

val _ = Parse.remove_type_abbrev "reln";
val _ = Parse.remove_type_abbrev "inf";

(* http://www.lemma-one.com/ProofPower/specs/spc002.pdf *)

val _ = Parse.hide "mem";

val mem = ``mem:'U->'U->bool``

val _ = Parse.add_infix("<:",425,Parse.NONASSOC)
Overload "<:" = ``mem:'U->'U->bool``

Definition extensional_def:
  extensional ^mem ⇔ ∀x y. x = y ⇔ ∀a. mem a x ⇔ mem a y
End

Definition is_separation_def:
  is_separation ^mem sub ⇔ ∀x P. ∀a. mem a (sub x P) ⇔ mem a x ∧ P a
End

Definition is_power_def:
  is_power ^mem power ⇔ ∀x. ∀a. mem a (power x) ⇔ ∀b. mem b a ⇒ mem b x
End

Definition is_union_def:
  is_union ^mem union ⇔ ∀x. ∀a. mem a (union x) ⇔ ∃b. mem a b ∧ mem b x
End

Definition is_upair_def:
  is_upair ^mem upair ⇔ ∀x y. ∀a. mem a (upair x y) ⇔ a = x ∨ a = y
End

Definition is_set_theory_def:
  is_set_theory ^mem ⇔
    extensional mem ∧
    (∃sub. is_separation mem sub) ∧
    (∃power. is_power mem power) ∧
    (∃union. is_union mem union) ∧
    (∃upair. is_upair mem upair)
End

Definition sub_def:
  sub ^mem = @sub. is_separation mem sub
End

Definition power_def:
  power ^mem = @power. is_power mem power
End

Definition union_def:
  union ^mem = @union. is_union mem union
End

Definition upair_def:
  upair ^mem = @upair. is_upair mem upair
End

Theorem is_extensional:
   is_set_theory ^mem ⇒ extensional mem
Proof
  rw[is_set_theory_def]
QED

Theorem is_separation_sub:
   is_set_theory ^mem ⇒ is_separation mem (sub mem)
Proof
  rw[sub_def] >> SELECT_ELIM_TAC >> fsrw_tac[SATISFY_ss][is_set_theory_def]
QED

Theorem is_power_power:
   is_set_theory ^mem ⇒ is_power mem (power mem)
Proof
  rw[power_def] >> SELECT_ELIM_TAC >> fsrw_tac[SATISFY_ss][is_set_theory_def]
QED

Theorem is_union_union:
   is_set_theory ^mem ⇒ is_union mem (union mem)
Proof
  rw[union_def] >> SELECT_ELIM_TAC >> fsrw_tac[SATISFY_ss][is_set_theory_def]
QED

Theorem is_upair_upair:
   is_set_theory ^mem ⇒ is_upair mem (upair mem)
Proof
  rw[upair_def] >> SELECT_ELIM_TAC >> fsrw_tac[SATISFY_ss][is_set_theory_def]
QED

val _ = Parse.add_infix("suchthat",9,Parse.LEFT)
Overload suchthat = ``sub ^mem``
Overload Pow = ``power ^mem``
Overload "+" = ``upair ^mem``

Theorem mem_sub:
   is_set_theory ^mem ⇒ ∀x s P. x <: (s suchthat P) ⇔ x <: s ∧ P x
Proof
  strip_tac >> imp_res_tac is_separation_sub >> fs[is_separation_def]
QED

Theorem mem_power:
   is_set_theory ^mem ⇒
    ∀x y. x <: (Pow y) ⇔ (∀b. b <: x ⇒ b <: y)
Proof
  strip_tac >> imp_res_tac is_power_power >> fs[is_power_def]
QED

Theorem mem_union:
   is_set_theory ^mem ⇒
    ∀x s. x <: (union mem s) ⇔ ∃a. x <: a ∧ a <: s
Proof
  strip_tac >> imp_res_tac is_union_union >> fs[is_union_def]
QED

Theorem mem_upair:
   is_set_theory ^mem ⇒ ∀a x y. a <: (x + y) ⇔ a = x ∨ a = y
Proof
  strip_tac >> imp_res_tac is_upair_upair >> fs[is_upair_def]
QED

Definition empty_def:
  empty ^mem = sub mem ARB (K F)
End

Overload "∅" = ``empty ^mem``

Theorem mem_empty:
   is_set_theory ^mem ⇒ ∀x. ¬(x <: ∅)
Proof
  strip_tac >> imp_res_tac is_separation_sub >>
  fs[empty_def,is_separation_def]
QED

Definition unit_def:
  unit ^mem x = x + x
End

Overload Unit = ``unit ^mem``

Theorem mem_unit:
   is_set_theory ^mem ⇒
    ∀x y. x <: (Unit y) ⇔ x = y
Proof
  strip_tac >> imp_res_tac is_upair_upair >>
  fs[is_upair_def,unit_def]
QED

Theorem unit_inj:
   is_set_theory ^mem ⇒
    ∀x y. Unit x = Unit y ⇔ x = y
Proof
  strip_tac >>
  imp_res_tac is_extensional >>
  fs[extensional_def,mem_unit] >>
  metis_tac[]
QED

Definition one_def:
  one ^mem = Unit ∅
End

Overload One = ``one ^mem``

Theorem mem_one:
   is_set_theory ^mem ⇒
    ∀x. x <: One ⇔ x = ∅
Proof
  strip_tac >> simp[mem_unit,one_def]
QED

Definition two_def:
  two ^mem = ∅ + One
End

Overload Two = ``two ^mem``

Theorem mem_two:
   is_set_theory ^mem ⇒
    ∀x. x <: Two ⇔ x = ∅ ∨ x = One
Proof
  strip_tac >> simp[mem_upair,mem_one,two_def]
QED

Definition pair_def:
  pair ^mem x y = (Unit x) + (x + y)
End

Overload "," = ``pair ^mem``

Theorem upair_inj:
   is_set_theory ^mem ⇒
    ∀a b c d. a + b = c + d ⇔ a = c ∧ b = d ∨ a = d ∧ b = c
Proof
  strip_tac >>
  imp_res_tac is_extensional >>
  fs[extensional_def,mem_upair] >>
  metis_tac[]
QED

Theorem unit_eq_upair:
   is_set_theory ^mem ⇒
    ∀x y z. Unit x = y + z ⇔ x = y ∧ y = z
Proof
  strip_tac >>
  imp_res_tac is_extensional >>
  fs[extensional_def,mem_unit,mem_upair] >>
  metis_tac[]
QED

Theorem pair_inj:
   is_set_theory ^mem ⇒
    ∀a b c d. (a,b) = (c,d) ⇔ a = c ∧ b = d
Proof
  strip_tac >> fs[pair_def] >> rw[] >>
  simp[upair_inj,unit_inj,unit_eq_upair] >>
  metis_tac[]
QED

Definition binary_union_def:
  binary_union ^mem x y = union mem (upair mem x y)
End

Overload UNION = ``binary_union ^mem``

Theorem mem_binary_union:
   is_set_theory ^mem ⇒
    ∀a x y. a <: (x ∪ y) ⇔ a <: x ∨ a <: y
Proof
  strip_tac >> fs[binary_union_def,mem_union,mem_upair] >>
  metis_tac[]
QED

Definition product_def:
  product ^mem x y =
    (Pow (Pow (x ∪ y)) suchthat
     λa. ∃b c. b <: x ∧ c <: y ∧ a = (b,c))
End

Overload CROSS = ``product ^mem``

Theorem mem_product:
   is_set_theory ^mem ⇒
    ∀a x y. a <: (x × y) ⇔ ∃b c. a = (b,c) ∧ b <: x ∧ c <: y
Proof
  strip_tac >> fs[product_def] >>
  simp[mem_sub,mem_power,mem_binary_union] >>
  rw[EQ_IMP_THM] >> TRY(metis_tac[]) >>
  rfs[pair_def,mem_upair] >> rw[] >>
  rfs[mem_unit,mem_upair]
QED

Definition relspace_def:
  relspace ^mem x y = Pow (x × y)
End

Overload Relspace = ``relspace ^mem``

Definition funspace_def:
  funspace ^mem x y =
    (Relspace x y suchthat
     λf. ∀a. a <: x ⇒ ∃!b. (a,b) <: f)
End

Overload Funspace = ``funspace ^mem``

Definition apply_def:
  apply ^mem x y = @a. (y,a) <: x
End

val _ = Parse.add_infix("'",2000,Parse.LEFT);
Overload "'" = ``apply ^mem``

Overload boolset = ``Two``

Definition true_def:
  true ^mem = ∅
End

Definition false_def:
  false ^mem = One
End

Overload True = ``true ^mem``
Overload False = ``false ^mem``

Theorem true_neq_false:
   is_set_theory ^mem ⇒ True ≠ False
Proof
  strip_tac >>
  imp_res_tac mem_one >>
  imp_res_tac mem_empty >>
  fs[true_def,false_def,is_set_theory_def,extensional_def,one_def] >>
  metis_tac[]
QED

Theorem mem_boolset:
   is_set_theory ^mem ⇒
    ∀x. x <: boolset ⇔ ((x = True) ∨ (x = False))
Proof
  strip_tac >> fs[mem_two,true_def,false_def]
QED

Definition boolean_def:
  boolean ^mem b = if b then True else False
End

Overload Boolean = ``boolean ^mem``

Theorem boolean_in_boolset:
   is_set_theory ^mem ⇒
    ∀b. Boolean b <: boolset
Proof
  strip_tac >> imp_res_tac mem_boolset >>
  Cases >> simp[boolean_def]
QED

Theorem boolean_eq_true:
   is_set_theory ^mem ⇒ ∀b. Boolean b = True ⇔ b
Proof
  strip_tac >> rw[boolean_def,true_neq_false]
QED

Overload Holds = ``holds ^mem``

Definition abstract_def:
  abstract ^mem dom rng f = (dom × rng suchthat λx. ∃a. x = (a,f a))
End

Overload Abstract = ``abstract ^mem``

Theorem apply_abstract:
   is_set_theory ^mem ⇒
    ∀f x s t. x <: s ∧ f x <: t ⇒ (Abstract s t f) ' x = f x
Proof
  strip_tac >>
  rw[apply_def,abstract_def] >>
  SELECT_ELIM_TAC >>
  simp[mem_sub,mem_product,pair_inj]
QED

Theorem apply_in_rng:
   is_set_theory ^mem ⇒
    ∀f x s t. x <: s ∧ f <: Funspace s t ⇒
    f ' x <: t
Proof
  strip_tac >>
  simp[funspace_def,mem_sub,relspace_def,
       mem_power,apply_def,mem_product,EXISTS_UNIQUE_THM] >>
  rw[] >> res_tac >> SELECT_ELIM_TAC >> res_tac >> rfs[pair_inj] >> metis_tac[]
QED

Theorem abstract_in_funspace:
   is_set_theory ^mem ⇒
    ∀f s t. (∀x. x <: s ⇒ f x <: t) ⇒ Abstract s t f <: Funspace s t
Proof
  strip_tac >>
  simp[funspace_def,relspace_def,abstract_def,mem_power,mem_product,mem_sub] >>
  simp[EXISTS_UNIQUE_THM,pair_inj]
QED

Theorem abstract_eq:
   is_set_theory ^mem ⇒
    ∀s t1 t2 f g.
    (∀x. x <: s ⇒ f x <: t1 ∧ g x <: t2 ∧ f x = g x)
    ⇒ Abstract s t1 f = Abstract s t2 g
Proof
  rw[] >>
  imp_res_tac is_extensional >>
  pop_assum mp_tac >>
  simp[extensional_def] >>
  disch_then kall_tac >>
  simp[abstract_def,mem_sub,mem_product] >>
  metis_tac[pair_inj]
QED

val indset = ``indset:'U``
val ch = ``ch:'U->'U``
val s = ``(^mem,^indset,^ch)``

Overload M = ``(^mem,^indset,^ch)``

Overload tuple = ``tuple0 ^mem``

Overload bigcross = ``bigcross0 ^mem``
