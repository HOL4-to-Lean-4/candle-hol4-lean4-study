import CmlTS.Misc
import CmlTS.Ast
import CmlTS.Namespace
import CmlTS.Ffi
import CmlTS.FpSem
import CmlTS.Mlstring
import CmlTS.Prelude.Float

/-!
# semanticPrimitives (HOL4 theory `semanticPrimitives`)

Values, stores, and the primitive operations of the semantics.

Renamed types (HOL4 -> Lean): `v` -> `Value`.  The function `thunk_op` is `thunk_op'` (the
datatype `thunk_op` of `ast` keeps its name).  Record field accessors `sem_env_v env`, `sem_env_c env`
are `env.v`, `env.c`.  HOL4 `bool` data (e.g. `Boolv`, `Eq_val`, `Loc`) is `Prop`.
-/

universe u v w

noncomputable section

open Classical

set_option linter.unusedVariables false

/- HOL4:
   (* Constructors and exceptions need unique identities, which we represent by stamps. *)
   Datatype:
    stamp =
     (* Each type gets a unique number, and the constructor name must be unique
        inside of the type *)
       TypeStamp conN num
     | ExnStamp num
   End -/
inductive stamp : Type where
  | TypeStamp (c : conN) (n : Nat) : stamp
  | ExnStamp (n : Nat) : stamp
  deriving DecidableEq

instance : Inhabited stamp := ⟨.ExnStamp 0⟩

/- HOL4:
   Datatype:
     sem_env =
     <| v : (modN, varN, 'v) namespace
      (* Lexical mapping of constructor idents to arity, stamp pairs *)
      ; c : (modN, conN, (num # stamp)) namespace
      |>
   End -/
structure sem_env (V : Type) : Type where
  v : Namespace modN varN V
  c : Namespace modN conN (Nat × stamp)

/- HOL4:
   (* Value forms *)
   Datatype:
    v =
       Litv lit
     (* Constructor application. Can be a tuple or a given constructor of a given type *)
     | Conv (stamp option) (v list)
     (* Function closures
        The environment is used for the free variables in the function *)
     | Closure (v sem_env) varN exp
     (* Function closure for recursive functions
      * See Closure and Letrec above
      * The last variable name indicates which function from the mutually
      * recursive bundle this closure value represents *)
     | Recclosure (v sem_env) ((varN # varN # exp) list) varN
     | Loc bool (* = is allowed *) num (* address *)
     | Vectorv (v list)
     (* Environment value for Eval, and its numeric identifier *)
     | Env (v sem_env) (num # num)
   End -/
inductive Value : Type where
  | Litv (l : lit) : Value
  | Conv (s : Option stamp) (vs : List Value) : Value
  | Closure (env : sem_env Value) (x : varN) (e : exp) : Value
  | Recclosure (env : sem_env Value) (funs : List (varN × varN × exp)) (f : varN) : Value
  | Loc (b : Prop) (n : Nat) : Value
  | Vectorv (vs : List Value) : Value
  | Env (env : sem_env Value) (id : Nat × Nat) : Value

instance : Inhabited Value := ⟨.Litv default⟩

/- HOL4:
   Type env_ctor = ``: (modN, conN, (num # stamp)) namespace``
   Type env_val = ``: (modN, varN, v) namespace`` -/
abbrev env_ctor : Type := Namespace modN conN (Nat × stamp)
abbrev env_val : Type := Namespace modN varN Value

/- HOL4:
   Definition bind_stamp_def:  bind_stamp = ExnStamp 0
   Definition chr_stamp_def:  chr_stamp = ExnStamp 1
   Definition div_stamp_def:  div_stamp = ExnStamp 2
   Definition subscript_stamp_def:  subscript_stamp = ExnStamp 3 -/
def bind_stamp : stamp := .ExnStamp 0
def chr_stamp : stamp := .ExnStamp 1
def div_stamp : stamp := .ExnStamp 2
def subscript_stamp : stamp := .ExnStamp 3

/- HOL4:
   Definition bind_exn_v_def:  bind_exn_v = Conv (SOME bind_stamp) []
   Definition chr_exn_v_def:  chr_exn_v = Conv (SOME chr_stamp) []
   Definition div_exn_v_def:  div_exn_v = Conv (SOME div_stamp) []
   Definition sub_exn_v_def:  sub_exn_v = Conv (SOME subscript_stamp) [] -/
def bind_exn_v : Value := .Conv (some bind_stamp) []
def chr_exn_v : Value := .Conv (some chr_stamp) []
def div_exn_v : Value := .Conv (some div_stamp) []
def sub_exn_v : Value := .Conv (some subscript_stamp) []

/- HOL4:
   Definition bool_type_num_def:  bool_type_num   = 0
   Definition list_type_num_def:  list_type_num   = 1 -/
def bool_type_num : Nat := 0
def list_type_num : Nat := 1

/- HOL4:
   (* The result of evaluation *)
   Datatype:
     abort =
        Rtype_error
      | Rtimeout_error
      | Rffi_error final_event
   End -/
inductive abort : Type where
  | Rtype_error : abort
  | Rtimeout_error : abort
  | Rffi_error (e : final_event) : abort

/- HOL4:
   Datatype:
     error_result =
        Rraise 'a (* Should only be a value of type exn *)
      | Rabort abort
   End -/
inductive error_result (α : Type u) : Type u where
  | Rraise (a : α) : error_result α
  | Rabort (a : abort) : error_result α

/- HOL4:
   Datatype:
     result =
        Rval 'a
      | Rerr ('b error_result)
   End -/
inductive result (α : Type u) (β : Type v) : Type (max u v) where
  | Rval (a : α) : result α β
  | Rerr (e : error_result β) : result α β

/- HOL4:
   (* Stores *)
   Datatype:
    store_v =
     (* A ref cell *)
       Refv 'a
     (* A byte array *)
     | W8array (word8 list)
     (* An array of values *)
     | Varray ('a list)
     (* Thunk *)
     | Thunk thunk_mode 'a
   End -/
inductive store_v (α : Type u) : Type u where
  | Refv (a : α) : store_v α
  | W8array (ws : List word8) : store_v α
  | Varray (vs : List α) : store_v α
  | Thunk (m : thunk_mode) (a : α) : store_v α

instance {α : Type u} : Inhabited (store_v α) := ⟨.W8array []⟩

/- HOL4:
   Definition store_v_same_type_def:
     store_v_same_type v1 v2 =
       case (v1:'a store_v, v2:'a store_v) of
       | (Refv _,    Refv _   ) => T
       | (W8array _, W8array _) => T
       | (Varray _,  Varray _ ) => T
       | (Thunk NotEvaluated _, Thunk _ _) => T
       | _ => F
   End -/
def store_v_same_type {α : Type u} (v1 v2 : store_v α) : Prop :=
  match v1, v2 with
  | .Refv _, .Refv _ => True
  | .W8array _, .W8array _ => True
  | .Varray _, .Varray _ => True
  | .Thunk .NotEvaluated _, .Thunk _ _ => True
  | _, _ => False

/- HOL4:
   (* The nth item in the list is the value at location n *)
   Type store = “:('a store_v) list” -/
abbrev store (α : Type u) : Type u := List (store_v α)

/- HOL4:
   Definition store_lookup_def:
     store_lookup l (st:('a store_v) list) =
       if l < LENGTH st then SOME (EL l st) else NONE
   End -/
def store_lookup {α : Type u} (l : Nat) (st : List (store_v α)) : Option (store_v α) :=
  if l < LENGTH st then some (EL l st) else none

/- HOL4:
   Definition store_alloc_def:
     store_alloc (v:'a store_v) st = (st ++ [v],LENGTH st)
   End -/
def store_alloc {α : Type u} (v : store_v α) (st : List (store_v α)) :
    List (store_v α) × Nat := (st ++ [v], LENGTH st)

/- HOL4:
   Definition store_assign_def:
     store_assign n (v:'a store_v) st =
       if n < LENGTH st ∧ store_v_same_type (EL n st) v then
         SOME (LUPDATE v n st)
       else NONE
   End -/
def store_assign {α : Type u} (n : Nat) (v : store_v α) (st : List (store_v α)) :
    Option (List (store_v α)) :=
  if n < LENGTH st ∧ store_v_same_type (EL n st) v then some (LUPDATE v n st) else none

/- HOL4:
   Type compiler_args = ``: ((num # num) # v # dec list)``
   Type compiler_fun = ``: compiler_args -> (v # word8 list # word64 list)option`` -/
abbrev compiler_args : Type := (Nat × Nat) × Value × List dec
abbrev compiler_fun : Type := compiler_args → Option (Value × List word8 × List word64)

/- HOL4:
   Datatype:
    eval_decs_state =
     <|
       compiler : compiler_fun ;
       (* state must be encoded as v somehow *)
       compiler_state : v ;
       env_id_counter : (num # num # num) ;
       (* decs must also be encoded as v *)
       decode_decs : v ->  ( dec list)option
     |>
   End -/
structure eval_decs_state : Type where
  compiler : compiler_fun
  compiler_state : Value
  env_id_counter : Nat × Nat × Nat
  decode_decs : Value → Option (List dec)

/- HOL4:
   (* Alternative mode for Eval including an oracle.
      This is only for use in the compiler proof. *)
   Type eval_oracle_fun = ``: num -> compiler_args``

   Datatype:
    eval_oracle_state =
     <|
       oracle : eval_oracle_fun ;
       custom_do_eval : v list -> eval_oracle_fun ->
            ((num # num) # eval_oracle_fun # dec list)option ;
       envs : ( ( v sem_env)list) list ;
       generation : num
     |>
   End -/
abbrev eval_oracle_fun : Type := Nat → compiler_args

structure eval_oracle_state : Type where
  oracle : eval_oracle_fun
  custom_do_eval : List Value → eval_oracle_fun → Option ((Nat × Nat) × eval_oracle_fun × List dec)
  envs : List (List (sem_env Value))
  generation : Nat

/- HOL4:
   Datatype:
     eval_state =
        EvalDecs eval_decs_state
      | EvalOracle eval_oracle_state
   End -/
inductive eval_state : Type where
  | EvalDecs (s : eval_decs_state) : eval_state
  | EvalOracle (s : eval_oracle_state) : eval_state

/- HOL4:
   Datatype:
     state =
     <| clock : num
      ; refs  : v store
      ; ffi : 'ffi ffi_state
      ; next_type_stamp : num
      ; next_exn_stamp : num
      ; eval_state :  eval_state option
      |>
   End -/
structure state (α : Type u) : Type u where
  clock : Nat
  refs : List (store_v Value)
  ffi : ffi_state α
  next_type_stamp : Nat
  next_exn_stamp : Nat
  eval_state : Option eval_state

/- HOL4:
   (* Other primitives *)
   (* Check that a constructor is properly applied *)
   Definition do_con_check_def:
     do_con_check (cenv:((mlstring),(mlstring),(num#stamp))namespace) n_opt l ⇔
       case n_opt of
         NONE => T
       | SOME n => case nsLookup cenv n of NONE => F | SOME (l',v2) => l = l'
   End -/
def do_con_check (cenv : Namespace modN conN (Nat × stamp)) (n_opt : Option (Ident modN conN))
    (l : Nat) : Prop :=
  match n_opt with
  | none => True
  | some n =>
    match nsLookup cenv n with
    | none => False
    | some (l', _) => l = l'

/- HOL4:
   Definition one_con_check_def[simp]:
     one_con_check envc (Con cn es) = do_con_check envc cn (LENGTH es) ∧
     one_con_check envc _ = T
   End -/
def one_con_check (envc : Namespace modN conN (Nat × stamp)) : exp → Prop
  | .Con cn es => do_con_check envc cn (LENGTH es)
  | _ => True

/- HOL4:
   Definition build_conv_def:
     build_conv (envC:((mlstring),(mlstring),(num#stamp))namespace) cn vs =
     case cn of
       NONE => SOME (Conv NONE vs)
     | SOME id =>
         case nsLookup envC id of
           NONE => NONE
         | SOME (len,stamp) => SOME (Conv (SOME stamp) vs)
   End -/
def build_conv (envC : Namespace modN conN (Nat × stamp)) (cn : Option (Ident modN conN))
    (vs : List Value) : Option Value :=
  match cn with
  | none => some (.Conv none vs)
  | some i =>
    match nsLookup envC i with
    | none => none
    | some (_, stamp) => some (.Conv (some stamp) vs)

/- HOL4:
   Definition lit_same_type_def:
     lit_same_type l1 l2 ⇔
        case (l1,l2) of
        | (IntLit _, IntLit _) => T
        | (Char   _, Char   _) => T
        | (StrLit _, StrLit _) => T
        | (Word8  _, Word8  _) => T
        | (Word64 _, Word64 _) => T
        | (Float64 _, Float64 _) => T
        | _ => F
   End -/
def lit_same_type (l1 l2 : lit) : Prop :=
  match l1, l2 with
  | .IntLit _, .IntLit _ => True
  | .Char _, .Char _ => True
  | .StrLit _, .StrLit _ => True
  | .Word8 _, .Word8 _ => True
  | .Word64 _, .Word64 _ => True
  | .Float64 _, .Float64 _ => True
  | _, _ => False

/- HOL4:
   Datatype:
     match_result =
        No_match
      | Match_type_error
      | Match 'a
   End -/
inductive match_result (α : Type u) : Type u where
  | No_match : match_result α
  | Match_type_error : match_result α
  | Match (a : α) : match_result α

/- HOL4:
   Definition same_type_def:
     (same_type (TypeStamp v0 n1) (TypeStamp v1 n2) ⇔ n1 = n2) ∧
     (same_type (ExnStamp v2) (ExnStamp v3) ⇔ T) ∧
     (same_type _ _ ⇔ F)
   End -/
def same_type : stamp → stamp → Prop
  | .TypeStamp _ n1, .TypeStamp _ n2 => n1 = n2
  | .ExnStamp _, .ExnStamp _ => True
  | _, _ => False

/- HOL4:
   Definition same_ctor_def:
     same_ctor stamp1 stamp2 ⇔ stamp1 = (stamp2:stamp)
   End -/
def same_ctor (stamp1 stamp2 : stamp) : Prop := stamp1 = stamp2

/- HOL4:
   Definition ctor_same_type_def:
     ctor_same_type c1 c2 ⇔
      case (c1,c2) of
        (NONE,NONE) => T
      | (SOME stamp1,SOME stamp2) => same_type stamp1 stamp2
      | _ => F
   End -/
def ctor_same_type (c1 c2 : Option stamp) : Prop :=
  match c1, c2 with
  | none, none => True
  | some stamp1, some stamp2 => same_type stamp1 stamp2
  | _, _ => False

/- HOL4:
   Definition Boolv_def:
     Boolv b =
       if b then Conv (SOME (TypeStamp «True» bool_type_num)) []
            else Conv (SOME (TypeStamp «False» bool_type_num)) []
   End -/
def Boolv (b : Prop) : Value :=
  if b then .Conv (some (.TypeStamp (mlstr "True") bool_type_num)) []
  else .Conv (some (.TypeStamp (mlstr "False") bool_type_num)) []

/- HOL4:
   (* A big-step pattern matcher.  If the value matches the pattern, return an
    * environment with the pattern variables bound to the corresponding sub-terms
    * of the value; this environment extends the environment given as an argument.
    * No_match is returned when there is no match, but any constructors
    * encountered in determining the match failure are applied to the correct
    * number of arguments, and constructors in corresponding positions in the
    * pattern and value come from the same type.  Match_type_error is returned
    * when one of these conditions is violated *)
   Definition pmatch_def:
     pmatch envC s Pany v' env = Match env ∧
     pmatch envC s (Pvar x) v' env = Match ((x,v')::env) ∧
     pmatch envC s (Plit l) (Litv l') env =
     (if l = l' then Match env
      else if lit_same_type l l' then No_match
      else Match_type_error) ∧
     pmatch envC s (Pcon (SOME n) ps) (Conv (SOME stamp') vs) env =
     (case nsLookup envC n of
        NONE => Match_type_error
      | SOME (l,stamp) =>
          if same_type stamp stamp' ∧ LENGTH ps = l then
            if same_ctor stamp stamp' then
              if LENGTH vs = l then pmatch_list envC s ps vs env
              else Match_type_error
            else No_match
          else Match_type_error) ∧
     pmatch envC s (Pcon NONE ps) (Conv NONE vs) env =
     (if LENGTH ps = LENGTH vs then pmatch_list envC s ps vs env
      else Match_type_error) ∧
     pmatch envC s (Pref p) (Loc _ lnum) env =
     (case store_lookup lnum s of
        NONE => Match_type_error
      | SOME (Refv v) => pmatch envC s p v env
      | SOME _ => Match_type_error) ∧
     pmatch envC s (Pas p i) v env = pmatch envC s p v ((i,v)::env) ∧
     pmatch envC s (Ptannot p t) v env = pmatch envC s p v env ∧
     pmatch envC s _ _ env = Match_type_error ∧
     pmatch_list envC s [] [] env = Match env ∧
     pmatch_list envC s (p::ps) (v::vs) env =
     (case pmatch envC s p v env of
        No_match =>
          (case pmatch_list envC s ps vs env of
             No_match => No_match
           | Match_type_error => Match_type_error
           | Match v1 => No_match)
      | Match_type_error => Match_type_error
      | Match env' => pmatch_list envC s ps vs env') ∧
     pmatch_list envC s _ _ env = Match_type_error
   Termination
     WF_REL_TAC
     `inv_image $< (λx. case x of INL (s,a,p,b,c) => pat_size p
                               | INR (s,a,ps,b,c) => list_size pat_size ps)`
   End -/
mutual
def pmatch (envC : Namespace modN conN (Nat × stamp)) (s : List (store_v Value)) :
    pat → Value → List (varN × Value) → match_result (List (varN × Value))
  | .Pany, _, env => .Match env
  | .Pvar x, v', env => .Match ((x, v') :: env)
  | .Plit l, .Litv l', env =>
    if l = l' then .Match env
    else if lit_same_type l l' then .No_match
    else .Match_type_error
  | .Pcon (some n) ps, .Conv (some stamp') vs, env =>
    match nsLookup envC n with
    | none => .Match_type_error
    | some (l, stamp) =>
      if same_type stamp stamp' ∧ LENGTH ps = l then
        if same_ctor stamp stamp' then
          if LENGTH vs = l then pmatch_list envC s ps vs env
          else .Match_type_error
        else .No_match
      else .Match_type_error
  | .Pcon none ps, .Conv none vs, env =>
    if LENGTH ps = LENGTH vs then pmatch_list envC s ps vs env
    else .Match_type_error
  | .Pref p, .Loc _ lnum, env =>
    match store_lookup lnum s with
    | none => .Match_type_error
    | some (.Refv v) => pmatch envC s p v env
    | some _ => .Match_type_error
  | .Pas p i, v, env => pmatch envC s p v ((i, v) :: env)
  | .Ptannot p _, v, env => pmatch envC s p v env
  | _, _, env => .Match_type_error
def pmatch_list (envC : Namespace modN conN (Nat × stamp)) (s : List (store_v Value)) :
    List pat → List Value → List (varN × Value) → match_result (List (varN × Value))
  | [], [], env => .Match env
  | p :: ps, v :: vs, env =>
    match pmatch envC s p v env with
    | .No_match =>
      match pmatch_list envC s ps vs env with
      | .No_match => .No_match
      | .Match_type_error => .Match_type_error
      | .Match _ => .No_match
    | .Match_type_error => .Match_type_error
    | .Match env' => pmatch_list envC s ps vs env'
  | _, _, env => .Match_type_error
end

/- HOL4:
   Definition can_pmatch_all_def:
     (can_pmatch_all envC refs [] v ⇔ T) ∧
     (can_pmatch_all envC refs (p::ps) v ⇔
        if pmatch envC refs p v [] = Match_type_error then F
        else can_pmatch_all envC refs ps v)
   End -/
def can_pmatch_all (envC : Namespace modN conN (Nat × stamp)) (refs : List (store_v Value)) :
    List pat → Value → Prop
  | [], _ => True
  | p :: ps, v =>
    if pmatch envC refs p v [] = .Match_type_error then False
    else can_pmatch_all envC refs ps v

/- HOL4:
   (* Bind each function of a mutually recursive set of functions to its closure *)
   Definition build_rec_env_def:
     (build_rec_env:(varN#varN#exp)list ->(v)sem_env ->((mlstring),(mlstring),(v))namespace
                    ->((mlstring),(mlstring),(v))namespace) funs cl_env add_to_env =
     FOLDR (λ(f,x,e) env'. nsBind f (Recclosure cl_env funs f) env')
           add_to_env funs
   End -/
def build_rec_env (funs : List (varN × varN × exp)) (cl_env : sem_env Value)
    (add_to_env : Namespace modN varN Value) : Namespace modN varN Value :=
  FOLDR (fun fxe env' => nsBind fxe.1 (.Recclosure cl_env funs fxe.1) env') add_to_env funs

/- HOL4:
   (* Lookup in the list of mutually recursive functions *)
   Definition find_recfun_def:
     (find_recfun:mlstring ->(mlstring#'a#'b)list ->('a#'b)option) n funs =
     case funs of
       [] => NONE
     | (f,x,e)::funs' => if f = n then SOME (x,e) else find_recfun n funs'
   End -/
def find_recfun {α : Type u} {β : Type v} (n : mlstring) :
    List (mlstring × α × β) → Option (α × β)
  | [] => none
  | (f, x, e) :: funs' => if f = n then some (x, e) else find_recfun n funs'

/- HOL4:
   Datatype:
     eq_result =
        Eq_val bool
      | Eq_type_error
   End -/
inductive eq_result : Type where
  | Eq_val (b : Prop) : eq_result
  | Eq_type_error : eq_result

/- HOL4:
   Definition do_eq_def:
     do_eq (Litv l1) (Litv l2) =
       (if lit_same_type l1 l2 then Eq_val (l1 = l2) else Eq_type_error) ∧
     do_eq (Loc b1 l1) (Loc b2 l2) =
       (if b1 ∧ b2 then Eq_val (l1 = l2) else Eq_type_error) ∧
     do_eq (Conv cn1 vs1) (Conv cn2 vs2) =
       (if cn1 = cn2 ∧ LENGTH vs1 = LENGTH vs2 then do_eq_list vs1 vs2
        else if ctor_same_type cn1 cn2 then Eq_val F
        else Eq_type_error) ∧
     do_eq (Vectorv vs1) (Vectorv vs2) =
       (if LENGTH vs1 = LENGTH vs2 then do_eq_list vs1 vs2 else Eq_val F) ∧
     do_eq (Closure v0 v3 v4) (Closure v5 v6 v7) = Eq_val T ∧
     do_eq (Closure v8 v9 v10) (Recclosure v11 v12 v13) = Eq_val T ∧
     do_eq (Recclosure v14 v15 v16) (Closure v17 v18 v19) = Eq_val T ∧
     do_eq (Recclosure v20 v21 v22) (Recclosure v23 v24 v25) = Eq_val T ∧
     do_eq (Env v26 (gen1,id1)) (Env v27 (gen2,id2)) =
       Eq_val (gen1 = gen2 ∧ id1 = id2) ∧
     do_eq _ _ = Eq_type_error ∧
     do_eq_list [] [] = Eq_val T ∧
     do_eq_list (v1::vs1) (v2::vs2) =
       (case do_eq v1 v2 of
          Eq_val r => if ¬r then Eq_val F else do_eq_list vs1 vs2
        | Eq_type_error => Eq_type_error) ∧
     do_eq_list _ _ = Eq_val F
   Termination
     WF_REL_TAC `inv_image $< (λx. case x of INL (v1,v2) => v_size v1
                                           | INR (vs1,vs2) => list_size v_size vs1)`
     >> Cases_on ‘compress_bool v1’ >> gs[Boolv_def, listTheory.list_size_def]
   End -/
mutual
def do_eq : Value → Value → eq_result
  | .Litv l1, .Litv l2 => if lit_same_type l1 l2 then .Eq_val (l1 = l2) else .Eq_type_error
  | .Loc b1 l1, .Loc b2 l2 => if b1 ∧ b2 then .Eq_val (l1 = l2) else .Eq_type_error
  | .Conv cn1 vs1, .Conv cn2 vs2 =>
    if cn1 = cn2 ∧ LENGTH vs1 = LENGTH vs2 then do_eq_list vs1 vs2
    else if ctor_same_type cn1 cn2 then .Eq_val False
    else .Eq_type_error
  | .Vectorv vs1, .Vectorv vs2 =>
    if LENGTH vs1 = LENGTH vs2 then do_eq_list vs1 vs2 else .Eq_val False
  | .Closure _ _ _, .Closure _ _ _ => .Eq_val True
  | .Closure _ _ _, .Recclosure _ _ _ => .Eq_val True
  | .Recclosure _ _ _, .Closure _ _ _ => .Eq_val True
  | .Recclosure _ _ _, .Recclosure _ _ _ => .Eq_val True
  | .Env _ (gen1, id1), .Env _ (gen2, id2) => .Eq_val (gen1 = gen2 ∧ id1 = id2)
  | _, _ => .Eq_type_error
def do_eq_list : List Value → List Value → eq_result
  | [], [] => .Eq_val True
  | v1 :: vs1, v2 :: vs2 =>
    match do_eq v1 v2 with
    | .Eq_val r => if ¬ r then .Eq_val False else do_eq_list vs1 vs2
    | .Eq_type_error => .Eq_type_error
  | _, _ => .Eq_val False
end

/- HOL4:
   (* Do an application *)
   Definition do_opapp_def:
     do_opapp vs =
        case vs of
        | [Closure env n e; v] => SOME (env with v := nsBind n v env.v,e)
        | [Recclosure env' funs n'; v] =>
          if ALL_DISTINCT (MAP (λ(f,x,e). f) funs) then
            case find_recfun n' funs of
              NONE => NONE
            | SOME (n,e) =>
              SOME
                (env' with v := nsBind n v (build_rec_env funs env' env'.v),e)
          else NONE
        | _ => NONE
   End -/
def do_opapp (vs : List Value) : Option (sem_env Value × exp) :=
  match vs with
  | [.Closure env n e, v] => some ({ env with v := nsBind n v env.v }, e)
  | [.Recclosure env' funs n', v] =>
    if ALL_DISTINCT (MAP (fun fxe => fxe.1) funs) then
      match find_recfun n' funs with
      | none => none
      | some (n, e) =>
        some ({ env' with v := nsBind n v (build_rec_env funs env' env'.v) }, e)
    else none
  | _ => none

/- HOL4:
   (* If a value represents a list, get that list. Otherwise return Nothing *)
   Definition v_to_list_def:
     v_to_list (Conv (SOME stamp) []) =
       (if stamp = TypeStamp «[]» list_type_num then SOME [] else NONE) ∧
     v_to_list (Conv (SOME stamp) [v1; v2]) =
       (if stamp = TypeStamp «::» list_type_num then
          case v_to_list v2 of NONE => NONE | SOME vs => SOME (v1::vs)
        else NONE) ∧
     v_to_list _ = NONE
   End -/
def v_to_list : Value → Option (List Value)
  | .Conv (some stamp) [] =>
    if stamp = .TypeStamp (mlstr "[]") list_type_num then some [] else none
  | .Conv (some stamp) [v1, v2] =>
    if stamp = .TypeStamp (mlstr "::") list_type_num then
      match v_to_list v2 with
      | none => none
      | some vs => some (v1 :: vs)
    else none
  | _ => none

/- HOL4:
   Definition list_to_v_def:
     list_to_v [] = Conv (SOME (TypeStamp «[]» list_type_num)) [] ∧
     list_to_v (x::xs) = Conv (SOME (TypeStamp «::» list_type_num)) [x; list_to_v xs]
   End -/
def list_to_v : List Value → Value
  | [] => .Conv (some (.TypeStamp (mlstr "[]") list_type_num)) []
  | x :: xs => .Conv (some (.TypeStamp (mlstr "::") list_type_num)) [x, list_to_v xs]

/- HOL4:
   Definition v_to_char_list_def:
     v_to_char_list (Conv (SOME stamp) []) =
       (if stamp = TypeStamp «[]» list_type_num then SOME "" else NONE) ∧
     v_to_char_list (Conv (SOME stamp) [Litv (Char c); v]) =
       (if stamp = TypeStamp «::» list_type_num then
          case v_to_char_list v of NONE => NONE | SOME cs => SOME (STRING c cs)
        else NONE) ∧
     v_to_char_list _ = NONE
   End -/
def v_to_char_list : Value → Option string
  | .Conv (some stamp) [] =>
    if stamp = .TypeStamp (mlstr "[]") list_type_num then some [] else none
  | .Conv (some stamp) [.Litv (.Char c), v] =>
    if stamp = .TypeStamp (mlstr "::") list_type_num then
      match v_to_char_list v with
      | none => none
      | some cs => some (STRING c cs)
    else none
  | _ => none

/- HOL4:
   Definition vs_to_string_def:
     vs_to_string [] = SOME «»  ∧
     vs_to_string (Litv (StrLit s1)::vs) =
       (case vs_to_string vs of NONE => NONE | SOME s2 => SOME (strcat s1 s2)) ∧
     vs_to_string (_::v1) = NONE
   End -/
def vs_to_string : List Value → Option mlstring
  | [] => some (mlstr "")
  | .Litv (.StrLit s1) :: vs =>
    match vs_to_string vs with
    | none => none
    | some s2 => some (strcat s1 s2)
  | _ :: _ => none

/- HOL4:
   Definition nat_to_v_def:
     nat_to_v n = Litv (IntLit (&n))
   End -/
def nat_to_v (n : Nat) : Value := .Litv (.IntLit (int_of_num n))

/- HOL4:
   Definition maybe_all_list_def:
     maybe_all_list v =
       case v of
         [] => SOME []
       | NONE::vs => NONE
       | SOME x::vs =>
           case maybe_all_list vs of NONE => NONE | SOME xs => SOME (x::xs)
   End -/
def maybe_all_list {α : Type u} : List (Option α) → Option (List α)
  | [] => some []
  | none :: _ => none
  | some x :: vs =>
    match maybe_all_list vs with
    | none => none
    | some xs => some (x :: xs)

/- HOL4:
   Definition v_to_word8_def:
     v_to_word8 v =
       case v of
       | Litv (Word8 w) => SOME w
       | _ => NONE
   End -/
def v_to_word8 (v : Value) : Option word8 :=
  match v with
  | .Litv (.Word8 w) => some w
  | _ => none

/- HOL4:
   Definition v_to_word8_list_def:
     v_to_word8_list v =
       case v_to_list v of
       | NONE => NONE
       | SOME xs => maybe_all_list (MAP v_to_word8 xs)
   End -/
def v_to_word8_list (v : Value) : Option (List word8) :=
  match v_to_list v with
  | none => none
  | some xs => maybe_all_list (MAP v_to_word8 xs)

/- HOL4:
   Definition v_to_word64_def:
     v_to_word64 v =
       case v of
       | Litv (Word64 w) => SOME w
       | _ => NONE
   End -/
def v_to_word64 (v : Value) : Option word64 :=
  match v with
  | .Litv (.Word64 w) => some w
  | _ => none

/- HOL4:
   Definition v_to_word64_list_def:
     v_to_word64_list v =
       case v_to_list v of
       | NONE => NONE
       | SOME xs => maybe_all_list (MAP v_to_word64 xs)
   End -/
def v_to_word64_list (v : Value) : Option (List word64) :=
  match v_to_list v with
  | none => none
  | some xs => maybe_all_list (MAP v_to_word64 xs)

/- HOL4:
   Definition lookup_env_def:
     lookup_env s (i,j) =
       case oEL i s.envs of NONE => NONE | SOME gen_envs => oEL j gen_envs
   End -/
def lookup_env (s : eval_oracle_state) (p : Nat × Nat) : Option (sem_env Value) :=
  match oEL p.1 s.envs with
  | none => none
  | some gen_envs => oEL p.2 gen_envs

/- HOL4:
   Definition add_decs_generation_def:
     add_decs_generation s =
       case s.env_id_counter of
         (cur_gen,next_id,next_gen) =>
           s with env_id_counter := (next_gen,0,next_gen + 1)
   End -/
def add_decs_generation (s : eval_decs_state) : eval_decs_state :=
  match s.env_id_counter with
  | (_, _, next_gen) => { s with env_id_counter := (next_gen, 0, next_gen + 1) }

/- HOL4:
   Definition add_env_generation_def:
     add_env_generation s =
       s with <|generation := LENGTH s.envs; envs := s.envs ⧺ [[]]|>
   End -/
def add_env_generation (s : eval_oracle_state) : eval_oracle_state :=
  { s with generation := LENGTH s.envs, envs := s.envs ++ [[]] }

/- HOL4:
   Definition declare_env_def:
     declare_env es env =
       case es of
       | NONE => NONE
       | SOME (EvalDecs s) =>
         (case s.env_id_counter of
            (cur_gen,next_id,next_gen) =>
              SOME
                (Env env (cur_gen,next_id),
                 SOME
                   (EvalDecs
                      (s with
                       env_id_counter := (cur_gen,next_id + 1,next_gen)))))
       | SOME (EvalOracle s') =>
         case oEL s'.generation s'.envs of
         | NONE => NONE
         | SOME gen_envs =>
           SOME
             (Conv NONE [nat_to_v s'.generation; nat_to_v (LENGTH gen_envs)],
              SOME
                (EvalOracle
                   (s' with
                    envs := LUPDATE (gen_envs ⧺ [env]) s'.generation s'.envs)))
   End -/
def declare_env (es : Option eval_state) (env : sem_env Value) :
    Option (Value × Option eval_state) :=
  match es with
  | none => none
  | some (.EvalDecs s) =>
    match s.env_id_counter with
    | (cur_gen, next_id, next_gen) =>
      some (.Env env (cur_gen, next_id),
        some (.EvalDecs { s with env_id_counter := (cur_gen, next_id + 1, next_gen) }))
  | some (.EvalOracle s') =>
    match oEL s'.generation s'.envs with
    | none => none
    | some gen_envs =>
      some (.Conv none [nat_to_v s'.generation, nat_to_v (LENGTH gen_envs)],
        some (.EvalOracle
          { s' with envs := LUPDATE (gen_envs ++ [env]) s'.generation s'.envs }))

/- HOL4:
   (* Concrete, or first-order values, which do not contain code closures and
      are unchanged by many compiler phases. *)
   Definition concrete_v_def:
     (concrete_v v ⇔
        case v of
        | Loc _ _ => T
        | Litv _ => T
        | Conv v_ vs => concrete_v_list vs
        | Vectorv vs => concrete_v_list vs
        | _ => F) ∧
     (concrete_v_list [] ⇔ T) ∧
     (concrete_v_list (v::vs) ⇔ concrete_v v ∧ concrete_v_list vs)
   Termination
     WF_REL_TAC `measure (λx. case x of INL v => v_size v
                                      | INR vs => list_size v_size vs)`
   End -/
mutual
def concrete_v : Value → Prop
  | .Loc _ _ => True
  | .Litv _ => True
  | .Conv _ vs => concrete_v_list vs
  | .Vectorv vs => concrete_v_list vs
  | _ => False
def concrete_v_list : List Value → Prop
  | [] => True
  | v :: vs => concrete_v v ∧ concrete_v_list vs
end

/- HOL4:
   Definition compiler_agrees_def:
     compiler_agrees (f:((num#num)#v#(dec)list ->(v#(word8)list#(word64)list)option))
         args (st_v,bs_v,ws_v) ⇔
       case (f args,args,v_to_word8_list bs_v,v_to_word64_list ws_v) of
       | (SOME (st,c_bs,c_ws),(v16,prev_st_v,_),SOME bs,SOME ws) =>
           st = st_v ∧ c_bs = bs ∧ c_ws = ws ∧ concrete_v st_v ∧
           concrete_v prev_st_v
       | _ => F
   End -/
def compiler_agrees (f : (Nat × Nat) × Value × List dec → Option (Value × List word8 × List word64))
    (args : (Nat × Nat) × Value × List dec) (r : Value × Value × Value) : Prop :=
  match r with
  | (st_v, bs_v, ws_v) =>
    match f args, args, v_to_word8_list bs_v, v_to_word64_list ws_v with
    | some (st, c_bs, c_ws), (_, prev_st_v, _), some bs, some ws =>
      st = st_v ∧ c_bs = bs ∧ c_ws = ws ∧ concrete_v st_v ∧ concrete_v prev_st_v
    | _, _, _, _ => False

/- HOL4:
   (* get the declarations to be evaluated in the various Eval semantics *)
   Definition do_eval_def:
     do_eval vs es =
       case (es,vs) of
       | (SOME (EvalDecs s),[Env env id; st_v; decs_v; st_v2; bs_v; ws_v]) =>
         (case s.decode_decs decs_v of
            NONE => NONE
          | SOME decs =>
            if
              st_v = s.compiler_state ∧ concrete_v decs_v ∧
              compiler_agrees s.compiler (id,st_v,decs) (st_v2,bs_v,ws_v)
            then
              SOME
                (env,decs,
                 SOME
                   (EvalDecs
                      (add_decs_generation (s with compiler_state := st_v2))))
            else NONE)
       | (SOME (EvalOracle s'),vs) =>
         (case s'.custom_do_eval vs s'.oracle of
            NONE => NONE
          | SOME (env_id,oracle,decs) =>
              case lookup_env s' env_id of
                NONE => NONE
              | SOME env =>
                  SOME
                  (env,decs,
                   SOME
                   (EvalOracle (add_env_generation (s' with oracle := oracle)))))
       | _ => NONE
   End -/
def do_eval (vs : List Value) (es : Option eval_state) :
    Option (sem_env Value × List dec × Option eval_state) :=
  match es, vs with
  | some (.EvalDecs s), [.Env env id, st_v, decs_v, st_v2, bs_v, ws_v] =>
    match s.decode_decs decs_v with
    | none => none
    | some decs =>
      if st_v = s.compiler_state ∧ concrete_v decs_v ∧
          compiler_agrees s.compiler (id, st_v, decs) (st_v2, bs_v, ws_v) then
        some (env, decs,
          some (.EvalDecs (add_decs_generation { s with compiler_state := st_v2 })))
      else none
  | some (.EvalOracle s'), vs =>
    match s'.custom_do_eval vs s'.oracle with
    | none => none
    | some (env_id, oracle, decs) =>
      match lookup_env s' env_id with
      | none => none
      | some env =>
        some (env, decs, some (.EvalOracle (add_env_generation { s' with oracle := oracle })))
  | _, _ => none

/- HOL4:
   (* conclude an Eval generation *)

   Definition reset_env_generation_def:
     reset_env_generation prior_es es =
       case (prior_es,es) of
       | (SOME (EvalDecs prior_s'),SOME (EvalDecs s')) =>
         (case (prior_s'.env_id_counter,s'.env_id_counter) of
            ((cur_gen,next_id,v5),v6,v8,next_gen) =>
              SOME
                (EvalDecs
                   (s' with env_id_counter := (cur_gen,next_id,next_gen))))
       | (SOME (EvalOracle prior_s),SOME (EvalOracle s)) =>
         SOME (EvalOracle (s with generation := prior_s.generation))
       | _ => es
   End -/
def reset_env_generation (prior_es es : Option eval_state) : Option eval_state :=
  match prior_es, es with
  | some (.EvalDecs prior_s'), some (.EvalDecs s') =>
    match prior_s'.env_id_counter, s'.env_id_counter with
    | (cur_gen, next_id, _), (_, _, next_gen) =>
      some (.EvalDecs { s' with env_id_counter := (cur_gen, next_id, next_gen) })
  | some (.EvalOracle prior_s), some (.EvalOracle s) =>
    some (.EvalOracle { s with generation := prior_s.generation })
  | _, _ => es

/- HOL4:
   Definition copy_array_def:
     copy_array (src,srcoff) len d =
       if
         srcoff < 0 ∨ len < 0 ∨ LENGTH src < Num (ABS (I (srcoff + len)))
       then
         NONE
       else
         (let
            copied =
              TAKE (Num (ABS (I len))) (DROP (Num (ABS (I srcoff))) src)
          in
            case d of
              NONE => SOME copied
            | SOME (dst,dstoff) =>
              if dstoff < 0 ∨ LENGTH dst < Num (ABS (I (dstoff + len))) then
                NONE
              else
                SOME
                  (TAKE (Num (ABS (I dstoff))) dst ⧺ copied ⧺
                   DROP (Num (ABS (I (dstoff + len)))) dst))
   End -/
def copy_array {α : Type u} (src : List α × Int) (len : Int) (d : Option (List α × Int)) :
    Option (List α) :=
  if src.2 < 0 ∨ len < 0 ∨ LENGTH src.1 < Num (ABS (id (src.2 + len))) then none
  else
    let copied := TAKE (Num (ABS (id len))) (DROP (Num (ABS (id src.2))) src.1)
    match d with
    | none => some copied
    | some (dst, dstoff) =>
      if dstoff < 0 ∨ LENGTH dst < Num (ABS (id (dstoff + len))) then none
      else
        some (TAKE (Num (ABS (id dstoff))) dst ++ copied ++
          DROP (Num (ABS (id (dstoff + len)))) dst)

/- HOL4:
   Definition ws_to_chars_def:
     ws_to_chars (ws:word8 list) = MAP (λw. CHR (w2n w)) ws
   End -/
def ws_to_chars (ws : List word8) : List char := MAP (fun w => CHR (w2n w)) ws

/- HOL4:
   Definition chars_to_ws_def:
     chars_to_ws cs = MAP (λc. i2w (&ORD c)) cs :word8 list
   End -/
def chars_to_ws (cs : List char) : List word8 := MAP (fun c => i2w (int_of_num (ORD c))) cs

/- HOL4:
   Definition shift8_lookup_def:
     shift8_lookup sh =
       case sh of
       |  Lsl => word_lsl
       | Lsr => word_lsr
       | Asr => word_asr
       | Ror => word_ror : word8 -> num -> word8
   End -/
def shift8_lookup (sh : shift) : word8 → Nat → word8 :=
  match sh with
  | .Lsl => word_lsl
  | .Lsr => word_lsr
  | .Asr => word_asr
  | .Ror => word_ror

/- HOL4:
   Definition shift64_lookup_def:
     shift64_lookup sh =
       case sh of
       | Lsl => word_lsl
       | Lsr => word_lsr
       | Asr => word_asr
       | Ror => word_ror : word64 -> num -> word64
   End -/
def shift64_lookup (sh : shift) : word64 → Nat → word64 :=
  match sh with
  | .Lsl => word_lsl
  | .Lsr => word_lsr
  | .Asr => word_asr
  | .Ror => word_ror

/- HOL4:
   Datatype:
     exp_or_val = Exp exp | Val v
   End -/
inductive exp_or_val : Type where
  | Exp (e : exp) : exp_or_val
  | Val (v : Value) : exp_or_val

/- HOL4:
   Type store_ffi = “: 'v store # 'ffi ffi_state” -/
abbrev store_ffi (V : Type u) (α : Type v) : Type (max u v) := List (store_v V) × ffi_state α

/- HOL4:
   Definition xor_bytes_def:
     xor_bytes [] bs2 = SOME (bs2:word8 list) ∧
     xor_bytes bs1 [] = NONE ∧
     xor_bytes (b1::bs1) (b2::bs2) =
       case xor_bytes bs1 bs2 of
       | NONE => NONE
       | SOME rest => SOME (word_xor b1 b2 :: rest)
   End -/
def xor_bytes : List word8 → List word8 → Option (List word8)
  | [], bs2 => some bs2
  | _ :: _, [] => none
  | b1 :: bs1, b2 :: bs2 =>
    match xor_bytes bs1 bs2 with
    | none => none
    | some rest => some (word_xor b1 b2 :: rest)

/- HOL4:
   Definition thunk_op_def:
     thunk_op (s: v store_v list, t: 'ffi ffi_state) th_op vs =
       case (th_op,vs) of
       | (AllocThunk m, [v]) =>
           (let (s',n) = store_alloc (Thunk m v) s in
              SOME ((s',t), Rval (Loc F n)))
       | (UpdateThunk m, [Loc _ lnum; v]) =>
           (case store_assign lnum (Thunk m v) s of
            | SOME s' => SOME ((s',t), Rval (Conv NONE []))
            | NONE => NONE)
       | _ => NONE
   End
   (Lean name `thunk_op'`, because `thunk_op` is the datatype of `ast`) -/
def thunk_op' {α : Type u} (st : List (store_v Value) × ffi_state α) (th_op : thunk_op)
    (vs : List Value) :
    Option ((List (store_v Value) × ffi_state α) × result Value Value) :=
  match st with
  | (s, t) =>
    match th_op, vs with
    | .AllocThunk m, [v] =>
      match store_alloc (.Thunk m v) s with
      | (s', n) => some ((s', t), .Rval (.Loc False n))
    | .UpdateThunk m, [.Loc _ lnum, v] =>
      match store_assign lnum (.Thunk m v) s with
      | some s' => some ((s', t), .Rval (.Conv none []))
      | none => none
    | _, _ => none

/- HOL4:
   Definition check_type_def:
     check_type BoolT v = (v = Boolv T ∨ v = Boolv F) ∧
     check_type IntT v = (∃i. v = Litv (IntLit i)) ∧
     check_type CharT v = (∃c. v = Litv (Char c)) ∧
     check_type StrT v = (∃s. v = Litv (StrLit s)) ∧
     check_type (WordT W8) v = (∃w. v = Litv (Word8 w)) ∧
     check_type (WordT W64) v = (∃w. v = Litv (Word64 w)) ∧
     check_type Float64T v = (∃w. v = Litv (Float64 w))
   End -/
def check_type : prim_type → Value → Prop
  | .BoolT, v => v = Boolv True ∨ v = Boolv False
  | .IntT, v => ∃ i, v = .Litv (.IntLit i)
  | .CharT, v => ∃ c, v = .Litv (.Char c)
  | .StrT, v => ∃ s, v = .Litv (.StrLit s)
  | .WordT .W8, v => ∃ w, v = .Litv (.Word8 w)
  | .WordT .W64, v => ∃ w, v = .Litv (.Word64 w)
  | .Float64T, v => ∃ w, v = .Litv (.Float64 w)

/- HOL4:
   Definition dest_Litv_def[simp]:
     dest_Litv (Litv v) = SOME v ∧
     dest_Litv _ = NONE
   End -/
def dest_Litv : Value → Option lit
  | .Litv v => some v
  | _ => none

/- HOL4:
   Definition the_Litv_IntLit_def[simp]:
     the_Litv_IntLit (Litv (IntLit i)) = i
   End
   (other values: unspecified, `ARB`) -/
def the_Litv_IntLit : Value → Int
  | .Litv (.IntLit i) => i
  | _ => ARB

/- HOL4:
   Definition the_Litv_Word8_def[simp]:
     the_Litv_Word8 (Litv (Word8 w)) = w
   End -/
def the_Litv_Word8 : Value → word8
  | .Litv (.Word8 w) => w
  | _ => ARB

/- HOL4:
   Definition the_Litv_Word64_def[simp]:
     the_Litv_Word64 (Litv (Word64 w)) = w
   End -/
def the_Litv_Word64 : Value → word64
  | .Litv (.Word64 w) => w
  | _ => ARB

/- HOL4:
   Definition the_Litv_Float64_def[simp]:
     the_Litv_Float64 (Litv (Float64 w)) = w
   End -/
def the_Litv_Float64 : Value → word64
  | .Litv (.Float64 w) => w
  | _ => ARB

/- HOL4:
   Definition the_Litv_Char_def[simp]:
     the_Litv_Char (Litv (Char c)) = c
   End -/
def the_Litv_Char : Value → char
  | .Litv (.Char c) => c
  | _ => ARB

/- HOL4:
   Definition the_Boolv_def[simp]:
     the_Boolv v = (v = Boolv T)
   End -/
def the_Boolv (v : Value) : Prop := v = Boolv True

/- HOL4:
   Definition num_cmp_def[simp]:
     num_cmp Lt  i j = (i <  j:num) ∧
     num_cmp Leq i j = (i <= j) ∧
     num_cmp Gt  i j = (i >  j) ∧
     num_cmp Geq i j = (i >= j)
   End -/
def num_cmp : opb → Nat → Nat → Prop
  | .Lt, i, j => i < j
  | .Leq, i, j => i ≤ j
  | .Gt, i, j => i > j
  | .Geq, i, j => i ≥ j

/- HOL4:
   Definition int_cmp_def[simp]:
     int_cmp Lt  i j = (i <  j:int) ∧
     int_cmp Leq i j = (i <= j) ∧
     int_cmp Gt  i j = (i >  j) ∧
     int_cmp Geq i j = (i >= j)
   End -/
def int_cmp : opb → Int → Int → Prop
  | .Lt, i, j => i < j
  | .Leq, i, j => i ≤ j
  | .Gt, i, j => i > j
  | .Geq, i, j => i ≥ j

/- HOL4:
   Definition do_test_def: (* TODO: extend with more cases *)
     do_test Equal ty v1 v2 =
       (if check_type ty v1 ∧ check_type ty v2 then
          (if ty = Float64T
           then Eq_val (fp64_equal (the_Litv_Float64 v1) (the_Litv_Float64 v2))
           else do_eq v1 v2)
        else Eq_type_error) ∧
     do_test (Compare cmp) ty v1 v2 =
       (case (ty, dest_Litv v1, dest_Litv v2) of
        | (IntT,     SOME (IntLit i),  SOME (IntLit j))  => Eq_val (int_cmp cmp i j)
        | (CharT,    SOME (Char c),    SOME (Char d))    => Eq_val (num_cmp cmp (ORD c) (ORD d))
        | (WordT W8, SOME (Word8 w),   SOME (Word8 v))   => Eq_val (num_cmp cmp (w2n w) (w2n v))
        | (Float64T, SOME (Float64 w), SOME (Float64 v)) => Eq_val (fp_cmp cmp w v)
        | _ => Eq_type_error) ∧
     do_test _ ty v1 v2 = Eq_type_error
   End -/
def do_test : test → prim_type → Value → Value → eq_result
  | .Equal, ty, v1, v2 =>
    if check_type ty v1 ∧ check_type ty v2 then
      (if ty = .Float64T then .Eq_val (fp64_equal (the_Litv_Float64 v1) (the_Litv_Float64 v2))
       else do_eq v1 v2)
    else .Eq_type_error
  | .Compare cmp, ty, v1, v2 =>
    match ty, dest_Litv v1, dest_Litv v2 with
    | .IntT, some (.IntLit i), some (.IntLit j) => .Eq_val (int_cmp cmp i j)
    | .CharT, some (.Char c), some (.Char d) => .Eq_val (num_cmp cmp (ORD c) (ORD d))
    | .WordT .W8, some (.Word8 w), some (.Word8 v) => .Eq_val (num_cmp cmp (w2n w) (w2n v))
    | .Float64T, some (.Float64 w), some (.Float64 v) => .Eq_val (fp_cmp cmp w v)
    | _, _, _ => .Eq_type_error
  | _, _, _, _ => .Eq_type_error

/- HOL4:
   Definition do_arith_def:
     (do_arith a Float64T vals =
        case (a, MAP the_Litv_Float64 vals) of
        | (Abs,  [v1])       => SOME (INR $ Litv $ Float64 $ fp64_abs v1)
        | (Neg,  [v1])       => SOME (INR $ Litv $ Float64 $ fp64_negate v1)
        | (Sqrt, [v1])       => SOME (INR $ Litv $ Float64 $ fp64_sqrt roundTiesToEven v1)
        | (Add,  [v1;v2])    => SOME (INR $ Litv $ Float64 $ fp64_add roundTiesToEven v1 v2)
        | (Sub,  [v1;v2])    => SOME (INR $ Litv $ Float64 $ fp64_sub roundTiesToEven v1 v2)
        | (Mul,  [v1;v2])    => SOME (INR $ Litv $ Float64 $ fp64_mul roundTiesToEven v1 v2)
        | (Div,  [v1;v2])    => SOME (INR $ Litv $ Float64 $ fp64_div roundTiesToEven v1 v2)
        | (FMA,  [v1;v2;v3]) => SOME (INR $ Litv $ Float64 $ fp64_mul_add roundTiesToEven v2 v3 v1)
        | _ => NONE) ∧
     (do_arith a IntT vals =
        case (a, MAP the_Litv_IntLit vals) of
        | (Add,  [v1;v2]) => SOME (INR $ Litv $ IntLit $ v1 + v2)
        | (Sub,  [v1;v2]) => SOME (INR $ Litv $ IntLit $ v1 - v2)
        | (Mul,  [v1;v2]) => SOME (INR $ Litv $ IntLit $ v1 * v2)
        | (Div,  [v1;v2]) => SOME (if v2 = 0 then INL div_exn_v else
                                     INR (Litv $ IntLit $ v1 / v2))
        | (Mod,  [v1;v2]) => SOME (if v2 = 0 then INL div_exn_v else
                                     INR (Litv $ IntLit $ v1 % v2))
        | _ => NONE) ∧
     (do_arith a (WordT W8) vals =
        case (a, MAP the_Litv_Word8 vals) of
        | (Add, [v1;v2]) => SOME (INR $ Litv $ Word8 $ word_add v1 v2)
        | (Sub, [v1;v2]) => SOME (INR $ Litv $ Word8 $ word_sub v1 v2)
        | (And, [v1;v2]) => SOME (INR $ Litv $ Word8 $ word_and v1 v2)
        | (Or,  [v1;v2]) => SOME (INR $ Litv $ Word8 $ word_or v1 v2)
        | (Xor, [v1;v2]) => SOME (INR $ Litv $ Word8 $ word_xor v1 v2)
        | _ => NONE) ∧
     (do_arith a (WordT W64) vals =
        case (a, MAP the_Litv_Word64 vals) of
        | (Add, [v1;v2]) => SOME (INR $ Litv $ Word64 $ word_add v1 v2)
        | (Sub, [v1;v2]) => SOME (INR $ Litv $ Word64 $ word_sub v1 v2)
        | (And, [v1;v2]) => SOME (INR $ Litv $ Word64 $ word_and v1 v2)
        | (Or,  [v1;v2]) => SOME (INR $ Litv $ Word64 $ word_or v1 v2)
        | (Xor, [v1;v2]) => SOME (INR $ Litv $ Word64 $ word_xor v1 v2)
        | _ => NONE) ∧
     (do_arith a BoolT vals =
        case (a, vals) of
        | (Not, [v1]) => SOME (INR $ Boolv (¬ (the_Boolv v1)))
        | _ => NONE) ∧
     (do_arith a _ vals = NONE)
   End
   (`INL`/`INR` are `Sum.inl`/`Sum.inr`) -/
def do_arith : arith → prim_type → List Value → Option (Sum Value Value)
  | a, .Float64T, vals =>
    match a, MAP the_Litv_Float64 vals with
    | .Abs, [v1] => some (.inr (.Litv (.Float64 (fp64_abs v1))))
    | .Neg, [v1] => some (.inr (.Litv (.Float64 (fp64_negate v1))))
    | .Sqrt, [v1] => some (.inr (.Litv (.Float64 (fp64_sqrt .roundTiesToEven v1))))
    | .Add, [v1, v2] => some (.inr (.Litv (.Float64 (fp64_add .roundTiesToEven v1 v2))))
    | .Sub, [v1, v2] => some (.inr (.Litv (.Float64 (fp64_sub .roundTiesToEven v1 v2))))
    | .Mul, [v1, v2] => some (.inr (.Litv (.Float64 (fp64_mul .roundTiesToEven v1 v2))))
    | .Div, [v1, v2] => some (.inr (.Litv (.Float64 (fp64_div .roundTiesToEven v1 v2))))
    | .FMA, [v1, v2, v3] =>
      some (.inr (.Litv (.Float64 (fp64_mul_add .roundTiesToEven v2 v3 v1))))
    | _, _ => none
  | a, .IntT, vals =>
    match a, MAP the_Litv_IntLit vals with
    | .Add, [v1, v2] => some (.inr (.Litv (.IntLit (v1 + v2))))
    | .Sub, [v1, v2] => some (.inr (.Litv (.IntLit (v1 - v2))))
    | .Mul, [v1, v2] => some (.inr (.Litv (.IntLit (v1 * v2))))
    | .Div, [v1, v2] =>
      some (if v2 = 0 then .inl div_exn_v else .inr (.Litv (.IntLit (int_div v1 v2))))
    | .Mod, [v1, v2] =>
      some (if v2 = 0 then .inl div_exn_v else .inr (.Litv (.IntLit (int_mod v1 v2))))
    | _, _ => none
  | a, .WordT .W8, vals =>
    match a, MAP the_Litv_Word8 vals with
    | .Add, [v1, v2] => some (.inr (.Litv (.Word8 (word_add v1 v2))))
    | .Sub, [v1, v2] => some (.inr (.Litv (.Word8 (word_sub v1 v2))))
    | .And, [v1, v2] => some (.inr (.Litv (.Word8 (word_and v1 v2))))
    | .Or, [v1, v2] => some (.inr (.Litv (.Word8 (word_or v1 v2))))
    | .Xor, [v1, v2] => some (.inr (.Litv (.Word8 (word_xor v1 v2))))
    | _, _ => none
  | a, .WordT .W64, vals =>
    match a, MAP the_Litv_Word64 vals with
    | .Add, [v1, v2] => some (.inr (.Litv (.Word64 (word_add v1 v2))))
    | .Sub, [v1, v2] => some (.inr (.Litv (.Word64 (word_sub v1 v2))))
    | .And, [v1, v2] => some (.inr (.Litv (.Word64 (word_and v1 v2))))
    | .Or, [v1, v2] => some (.inr (.Litv (.Word64 (word_or v1 v2))))
    | .Xor, [v1, v2] => some (.inr (.Litv (.Word64 (word_xor v1 v2))))
    | _, _ => none
  | a, .BoolT, vals =>
    match a, vals with
    | .Not, [v1] => some (.inr (Boolv (¬ (the_Boolv v1))))
    | _, _ => none
  | _, _, _ => none

/- HOL4:
   Definition do_conversion_def:
     (* Word to Int conversions *)
     (do_conversion v (WordT W8) IntT =
        SOME (INR $ Litv $ IntLit $ & (w2n (the_Litv_Word8 v)))) ∧
     (do_conversion v (WordT W64) IntT =
        SOME (INR $ Litv $ IntLit $ & (w2n (the_Litv_Word64 v)))) ∧
     (* Int to Word conversions *)
     (do_conversion v IntT (WordT W8) =
        SOME (INR $ Litv $ Word8 $ i2w (the_Litv_IntLit v))) ∧
     (do_conversion v IntT (WordT W64) =
        SOME (INR $ Litv $ Word64 $ i2w (the_Litv_IntLit v))) ∧
     (* Char/Int conversions *)
     (do_conversion v CharT IntT =
        SOME (INR $ Litv $ IntLit $ & (ORD (the_Litv_Char v)))) ∧
     (do_conversion v IntT CharT =
        let i = the_Litv_IntLit v in
          if i < 0 ∨ i > 255 then SOME (INL chr_exn_v)
          else SOME (INR $ Litv $ Char $ CHR (Num (ABS i)))) ∧
     (* Char/Word8 conversions *)
     (do_conversion v CharT (WordT W8) =
        SOME (INR $ Litv $ Word8 $ char_to_word8 (the_Litv_Char v))) ∧
     (do_conversion v (WordT W8) CharT =
        SOME (INR $ Litv $ Char $ word8_to_char (the_Litv_Word8 v))) ∧
     (* Float64/Word64 conversions (bit reinterpretation) *)
     (do_conversion v Float64T (WordT W64) =
        SOME (INR $ Litv $ Word64 $ the_Litv_Float64 v)) ∧
     (do_conversion v (WordT W64) Float64T =
        SOME (INR $ Litv $ Float64 $ the_Litv_Word64 v)) ∧
     (do_conversion _ _ _ = NONE)
   End -/
def do_conversion : Value → prim_type → prim_type → Option (Sum Value Value)
  | v, .WordT .W8, .IntT => some (.inr (.Litv (.IntLit (int_of_num (w2n (the_Litv_Word8 v))))))
  | v, .WordT .W64, .IntT => some (.inr (.Litv (.IntLit (int_of_num (w2n (the_Litv_Word64 v))))))
  | v, .IntT, .WordT .W8 => some (.inr (.Litv (.Word8 (i2w (the_Litv_IntLit v)))))
  | v, .IntT, .WordT .W64 => some (.inr (.Litv (.Word64 (i2w (the_Litv_IntLit v)))))
  | v, .CharT, .IntT => some (.inr (.Litv (.IntLit (int_of_num (ORD (the_Litv_Char v))))))
  | v, .IntT, .CharT =>
    let i := the_Litv_IntLit v
    if i < 0 ∨ i > 255 then some (.inl chr_exn_v)
    else some (.inr (.Litv (.Char (CHR (Num (ABS i))))))
  | v, .CharT, .WordT .W8 => some (.inr (.Litv (.Word8 (char_to_word8 (the_Litv_Char v)))))
  | v, .WordT .W8, .CharT => some (.inr (.Litv (.Char (word8_to_char (the_Litv_Word8 v)))))
  | v, .Float64T, .WordT .W64 => some (.inr (.Litv (.Word64 (the_Litv_Float64 v))))
  | v, .WordT .W64, .Float64T => some (.inr (.Litv (.Float64 (the_Litv_Word64 v))))
  | _, _, _ => none

/- HOL4:
   Definition do_app_def:
     do_app (s: v store_v list, t: 'ffi ffi_state) op vs =
       case (op, vs) of
         (ListAppend, [x1; x2]) =>
         (case (v_to_list x1, v_to_list x2) of
             (SOME xs, SOME ys) => SOME ((s,t), Rval (list_to_v (xs ++ ys)))
           | _ => NONE
         )
       | (Shift W8 op n, [Litv (Word8 w)]) =>
           SOME ((s,t), Rval (Litv (Word8 (shift8_lookup op w n))))
       | (Shift W64 op n, [Litv (Word64 w)]) =>
           SOME ((s,t), Rval (Litv (Word64 (shift64_lookup op w n))))
       | (Equality, [v1; v2]) =>
           (case do_eq v1 v2 of
               Eq_type_error => NONE
             | Eq_val b => SOME ((s,t), Rval (Boolv b))
           )
       | (Opassign, [Loc b lnum; v]) =>
           (case store_assign lnum (Refv v) s of
               SOME s' => SOME ((s',t), Rval (Conv NONE []))
             | NONE => NONE
           )
       | (Opref, [v]) =>
           let (s',n) = (store_alloc (Refv v) s) in
             SOME ((s',t), Rval (Loc T n))
       | (Opderef, [Loc b n]) =>
           (case store_lookup n s of
               SOME (Refv v) => SOME ((s,t),Rval v)
             | _ => NONE
           )
       | (Aw8alloc, [Litv (IntLit n); Litv (Word8 w)]) =>
           if n <( 0 : int) then
             SOME ((s,t), Rerr (Rraise sub_exn_v))
           else
             let (s',lnum) =
               (store_alloc (W8array (REPLICATE (Num (ABS (I n))) w)) s)
             in
               SOME ((s',t), Rval (Loc T lnum))
       | (Aw8sub, [Loc _ lnum; Litv (IntLit i)]) =>
           (case store_lookup lnum s of
               SOME (W8array ws) =>
                 if i <( 0 : int) then
                   SOME ((s,t), Rerr (Rraise sub_exn_v))
                 else
                   let n = (Num (ABS (I i))) in
                     if n >= LENGTH ws then
                       SOME ((s,t), Rerr (Rraise sub_exn_v))
                     else
                       SOME ((s,t), Rval (Litv (Word8 (EL n ws))))
             | _ => NONE
           )
       | (Aw8sub_unsafe, [Loc _ lnum; Litv (IntLit i)]) =>
           (case store_lookup lnum s of
               SOME (W8array ws) =>
                 if i <( 0 : int) then
                   NONE
                 else
                   let n = (Num (ABS (I i))) in
                     if n >= LENGTH ws then
                       NONE
                     else
                       SOME ((s,t), Rval (Litv (Word8 (EL n ws))))
             | _ => NONE
           )
       | (Aw8length, [Loc _ n]) =>
           (case store_lookup n s of
               SOME (W8array ws) =>
                 SOME ((s,t),Rval (Litv(IntLit(int_of_num(LENGTH ws)))))
             | _ => NONE
            )
       | (Aw8update, [Loc _ lnum; Litv(IntLit i); Litv(Word8 w)]) =>
           (case store_lookup lnum s of
             SOME (W8array ws) =>
               if i <( 0 : int) then
                 SOME ((s,t), Rerr (Rraise sub_exn_v))
               else
                 let n = (Num (ABS (I i))) in
                   if n >= LENGTH ws then
                     SOME ((s,t), Rerr (Rraise sub_exn_v))
                   else
                     (case store_assign lnum (W8array (LUPDATE w n ws)) s of
                         NONE => NONE
                       | SOME s' => SOME ((s',t), Rval (Conv NONE []))
                     )
           | _ => NONE
         )
       | (Aw8update_unsafe, [Loc _ lnum; Litv(IntLit i); Litv(Word8 w)]) =>
           (case store_lookup lnum s of
             SOME (W8array ws) =>
               if i <( 0 : int) then
                 NONE
               else
                 let n = (Num (ABS (I i))) in
                   if n >= LENGTH ws then
                     NONE
                   else
                     (case store_assign lnum (W8array (LUPDATE w n ws)) s of
                         NONE => NONE
                       | SOME s' => SOME ((s',t), Rval (Conv NONE []))
                     )
           | _ => NONE
         )
       | (CopyStrStr, [Litv(StrLit strng);Litv(IntLit off);Litv(IntLit len)]) =>
           SOME ((s,t),
           (case copy_array (explode strng,off) len NONE of
             NONE => Rerr (Rraise sub_exn_v)
           | SOME cs => Rval (Litv(StrLit(implode(cs))))
           ))
       | (CopyStrAw8, [Litv(StrLit strng);Litv(IntLit off);Litv(IntLit len);
                       Loc _ dst;Litv(IntLit dstoff)]) =>
           (case store_lookup dst s of
             SOME (W8array ws) =>
               (case copy_array (explode strng,off) len (SOME(ws_to_chars ws,dstoff)) of
                 NONE => SOME ((s,t), Rerr (Rraise sub_exn_v))
               | SOME cs =>
                 (case store_assign dst (W8array (chars_to_ws cs)) s of
                   SOME s' =>  SOME ((s',t), Rval (Conv NONE []))
                 | _ => NONE
                 )
               )
           | _ => NONE
           )
       | (CopyAw8Str, [Loc _ src;Litv(IntLit off);Litv(IntLit len)]) =>
         (case store_lookup src s of
           SOME (W8array ws) =>
           SOME ((s,t),
                 (case copy_array (ws,off) len NONE of
                    NONE => Rerr (Rraise sub_exn_v)
                  | SOME ws => Rval (Litv(StrLit(implode(ws_to_chars ws))))
                 ))
          | _ => NONE
         )
       | (CopyAw8Aw8, [Loc _ src;Litv(IntLit off);Litv(IntLit len);
                       Loc _ dst;Litv(IntLit dstoff)]) =>
         (case (store_lookup src s, store_lookup dst s) of
           (SOME (W8array ws), SOME (W8array ds)) =>
             (case copy_array (ws,off) len (SOME(ds,dstoff)) of
               NONE => SOME ((s,t), Rerr (Rraise sub_exn_v))
             | SOME ws =>
                 (case store_assign dst (W8array ws) s of
                   SOME s' => SOME ((s',t), Rval (Conv NONE []))
                 | _ => NONE
                 )
             )
         | _ => NONE
         )
       | (XorAw8Str_unsafe, [Loc _ dst; Litv (StrLit str_arg)]) =>
           (case store_lookup dst s of
             SOME (W8array bs) =>
               (case xor_bytes (MAP (n2w o ORD) (explode str_arg)) bs of
                | NONE => NONE
                | SOME new_bs =>
                   case store_assign dst (W8array new_bs) s of
                   | NONE => NONE
                   | SOME s' => SOME ((s',t), Rval (Conv NONE [])))
           | _ => NONE
           )
       | (Implode, [v]) =>
             (case v_to_char_list v of
               SOME ls =>
                 SOME ((s,t), Rval (Litv (StrLit (implode ls))))
             | NONE => NONE
             )
       | (Explode, [v]) =>
             (case v of
               Litv (StrLit strng) =>
                 SOME ((s,t), Rval (list_to_v (MAP (\ c .  Litv (Char c)) (explode strng))))
             | _ => NONE
             )
       | (Strsub, [Litv (StrLit strng); Litv (IntLit i)]) =>
           if i <( 0 : int) then
             SOME ((s,t), Rerr (Rraise sub_exn_v))
           else
             let n = (Num (ABS (I i))) in
               if n >= strlen strng then
                 SOME ((s,t), Rerr (Rraise sub_exn_v))
               else
                 SOME ((s,t), Rval (Litv (Char (EL n (explode strng)))))
       | (Strlen, [Litv (StrLit strng)]) =>
           SOME ((s,t), Rval (Litv(IntLit(int_of_num(strlen strng)))))
       | (Strcat, [v]) =>
           (case v_to_list v of
             SOME vs =>
               (case vs_to_string vs of
                 SOME strng =>
                   SOME ((s,t), Rval (Litv(StrLit strng)))
               | _ => NONE
               )
           | _ => NONE
           )
       | (VfromList, [v]) =>
             (case v_to_list v of
                 SOME vs =>
                   SOME ((s,t), Rval (Vectorv vs))
               | NONE => NONE
             )
       | (Vsub_unsafe, [Vectorv vs; Litv (IntLit i)]) =>
           if (0:int) ≤ i ∧ Num i < LENGTH vs then
             SOME ((s,t), Rval (EL (Num i) vs))
           else
             NONE
       | (Vsub, [Vectorv vs; Litv (IntLit i)]) =>
           if i <( 0 : int) then
             SOME ((s,t), Rerr (Rraise sub_exn_v))
           else
             let n = (Num (ABS (I i))) in
               if n >= LENGTH vs then
                 SOME ((s,t), Rerr (Rraise sub_exn_v))
               else
                 SOME ((s,t), Rval (EL n vs))
       | (Vlength, [Vectorv vs]) =>
           SOME ((s,t), Rval (Litv (IntLit (int_of_num (LENGTH vs)))))
       | (Aalloc, [Litv (IntLit n); v]) =>
           if n <( 0 : int) then
             SOME ((s,t), Rerr (Rraise sub_exn_v))
           else
             let (s',lnum) =
               (store_alloc (Varray (REPLICATE (Num (ABS (I n))) v)) s)
             in
               SOME ((s',t), Rval (Loc T lnum))
       | (AallocEmpty, [Conv NONE []]) =>
           let (s',lnum) = (store_alloc (Varray []) s) in
             SOME ((s',t), Rval (Loc T lnum))
       | (AallocFixed, vs) =>
           let (s',lnum) =
             (store_alloc (Varray vs) s)
           in
             SOME ((s',t), Rval (Loc T lnum))
       | (Asub, [Loc _ lnum; Litv (IntLit i)]) =>
           (case store_lookup lnum s of
               SOME (Varray vs) =>
                 if i <( 0 : int) then
                   SOME ((s,t), Rerr (Rraise sub_exn_v))
                 else
                   let n = (Num (ABS (I i))) in
                     if n >= LENGTH vs then
                       SOME ((s,t), Rerr (Rraise sub_exn_v))
                     else
                       SOME ((s,t), Rval (EL n vs))
             | _ => NONE
           )
       | (Asub_unsafe, [Loc _ lnum; Litv (IntLit i)]) =>
           (case store_lookup lnum s of
               SOME (Varray vs) =>
                 if i <( 0 : int) then
                   NONE
                 else
                   let n = (Num (ABS (I i))) in
                     if n >= LENGTH vs then
                       NONE
                     else
                       SOME ((s,t), Rval (EL n vs))
             | _ => NONE
           )
       | (Alength, [Loc _ n]) =>
           (case store_lookup n s of
               SOME (Varray ws) =>
                 SOME ((s,t),Rval (Litv(IntLit(int_of_num(LENGTH ws)))))
             | _ => NONE
            )
       | (Aupdate, [Loc _ lnum; Litv (IntLit i); v]) =>
           (case store_lookup lnum s of
             SOME (Varray vs) =>
               if i <( 0 : int) then
                 SOME ((s,t), Rerr (Rraise sub_exn_v))
               else
                 let n = (Num (ABS (I i))) in
                   if n >= LENGTH vs then
                     SOME ((s,t), Rerr (Rraise sub_exn_v))
                   else
                     (case store_assign lnum (Varray (LUPDATE v n vs)) s of
                         NONE => NONE
                       | SOME s' => SOME ((s',t), Rval (Conv NONE []))
                     )
           | _ => NONE
         )
       | (Aupdate_unsafe, [Loc _ lnum; Litv (IntLit i); v]) =>
           (case store_lookup lnum s of
             SOME (Varray vs) =>
               if i <( 0 : int) then
                 NONE
               else
                 let n = (Num (ABS (I i))) in
                   if n >= LENGTH vs then
                     NONE
                   else
                     (case store_assign lnum (Varray (LUPDATE v n vs)) s of
                         NONE => NONE
                       | SOME s' => SOME ((s',t), Rval (Conv NONE []))
                     )
           | _ => NONE
         )
       | (ConfigGC, [Litv (IntLit i); Litv (IntLit j)]) =>
           SOME ((s,t), Rval (Conv NONE []))
       | (FFI n, [Litv(StrLit conf); Loc _ lnum]) =>
           (case store_lookup lnum s of
             SOME (W8array ws) =>
               (case call_FFI t (ExtCall n) (MAP (n2w o ORD) (explode conf)) ws of
                 FFI_return t' ws' =>
                  (case store_assign lnum (W8array ws') s of
                    SOME s' => SOME ((s', t'), Rval (Conv NONE []))
                  | NONE => NONE
                  )
               | FFI_final outcome =>
                  SOME ((s, t), Rerr (Rabort (Rffi_error outcome)))
               )
           | _ => NONE
           )
       | (Env_id, [Env env (gen, id)]) => SOME ((s, t),
               Rval (Conv NONE [nat_to_v gen; nat_to_v id]))
       | (Env_id, [Conv NONE [gen; id]]) => SOME ((s, t),
               Rval (Conv NONE [gen; id]))
       | (ThunkOp th_op, vs) => thunk_op (s,t) th_op vs
       | (Arith a ty, vs) =>
           (if EVERY (check_type ty) vs then
              (case do_arith a ty vs of
               | SOME (INR res) => SOME ((s, t), Rval res)
               | SOME (INL exn) => SOME ((s, t), Rerr (Rraise exn))
               | NONE           => NONE)
            else NONE)
       | (FromTo ty1 ty2, [v]) =>
           (if check_type ty1 v then
              (case do_conversion v ty1 ty2 of
               | SOME (INR res) => SOME ((s, t), Rval res)
               | SOME (INL exn) => SOME ((s, t), Rerr (Rraise exn))
               | NONE           => NONE)
            else NONE)
       | (Test test test_ty, [v1; v2]) =>
           (case do_test test test_ty v1 v2 of
               Eq_type_error => NONE
             | Eq_val b => SOME ((s,t), Rval (Boolv b))
           )
       | _ => NONE
   End -/
def do_app {α : Type u} (st : List (store_v Value) × ffi_state α) (o : op) (vs : List Value) :
    Option ((List (store_v Value) × ffi_state α) × result Value Value) :=
  match st with
  | (s, t) =>
  match o, vs with
  | .ListAppend, [x1, x2] =>
    (match v_to_list x1, v_to_list x2 with
     | some xs, some ys => some ((s, t), .Rval (list_to_v (xs ++ ys)))
     | _, _ => none)
  | .Shift .W8 sop n, [.Litv (.Word8 w)] =>
    some ((s, t), .Rval (.Litv (.Word8 (shift8_lookup sop w n))))
  | .Shift .W64 sop n, [.Litv (.Word64 w)] =>
    some ((s, t), .Rval (.Litv (.Word64 (shift64_lookup sop w n))))
  | .Equality, [v1, v2] =>
    (match do_eq v1 v2 with
     | .Eq_type_error => none
     | .Eq_val b => some ((s, t), .Rval (Boolv b)))
  | .Opassign, [.Loc _ lnum, v] =>
    (match store_assign lnum (.Refv v) s with
     | some s' => some ((s', t), .Rval (.Conv none []))
     | none => none)
  | .Opref, [v] =>
    (match store_alloc (.Refv v) s with
     | (s', n) => some ((s', t), .Rval (.Loc True n)))
  | .Opderef, [.Loc _ n] =>
    (match store_lookup n s with
     | some (.Refv v) => some ((s, t), .Rval v)
     | _ => none)
  | .Aw8alloc, [.Litv (.IntLit n), .Litv (.Word8 w)] =>
    if n < 0 then some ((s, t), .Rerr (.Rraise sub_exn_v))
    else
      (match store_alloc (.W8array (REPLICATE (Num (ABS (id n))) w)) s with
       | (s', lnum) => some ((s', t), .Rval (.Loc True lnum)))
  | .Aw8sub, [.Loc _ lnum, .Litv (.IntLit i)] =>
    (match store_lookup lnum s with
     | some (.W8array ws) =>
       if i < 0 then some ((s, t), .Rerr (.Rraise sub_exn_v))
       else
         let n := Num (ABS (id i))
         if n ≥ LENGTH ws then some ((s, t), .Rerr (.Rraise sub_exn_v))
         else some ((s, t), .Rval (.Litv (.Word8 (EL n ws))))
     | _ => none)
  | .Aw8sub_unsafe, [.Loc _ lnum, .Litv (.IntLit i)] =>
    (match store_lookup lnum s with
     | some (.W8array ws) =>
       if i < 0 then none
       else
         let n := Num (ABS (id i))
         if n ≥ LENGTH ws then none
         else some ((s, t), .Rval (.Litv (.Word8 (EL n ws))))
     | _ => none)
  | .Aw8length, [.Loc _ n] =>
    (match store_lookup n s with
     | some (.W8array ws) => some ((s, t), .Rval (.Litv (.IntLit (int_of_num (LENGTH ws)))))
     | _ => none)
  | .Aw8update, [.Loc _ lnum, .Litv (.IntLit i), .Litv (.Word8 w)] =>
    (match store_lookup lnum s with
     | some (.W8array ws) =>
       if i < 0 then some ((s, t), .Rerr (.Rraise sub_exn_v))
       else
         let n := Num (ABS (id i))
         if n ≥ LENGTH ws then some ((s, t), .Rerr (.Rraise sub_exn_v))
         else
           (match store_assign lnum (.W8array (LUPDATE w n ws)) s with
            | none => none
            | some s' => some ((s', t), .Rval (.Conv none [])))
     | _ => none)
  | .Aw8update_unsafe, [.Loc _ lnum, .Litv (.IntLit i), .Litv (.Word8 w)] =>
    (match store_lookup lnum s with
     | some (.W8array ws) =>
       if i < 0 then none
       else
         let n := Num (ABS (id i))
         if n ≥ LENGTH ws then none
         else
           (match store_assign lnum (.W8array (LUPDATE w n ws)) s with
            | none => none
            | some s' => some ((s', t), .Rval (.Conv none [])))
     | _ => none)
  | .CopyStrStr, [.Litv (.StrLit strng), .Litv (.IntLit off), .Litv (.IntLit len)] =>
    some ((s, t),
      (match copy_array (explode strng, off) len none with
       | none => .Rerr (.Rraise sub_exn_v)
       | some cs => .Rval (.Litv (.StrLit (implode cs)))))
  | .CopyStrAw8, [.Litv (.StrLit strng), .Litv (.IntLit off), .Litv (.IntLit len),
      .Loc _ dst, .Litv (.IntLit dstoff)] =>
    (match store_lookup dst s with
     | some (.W8array ws) =>
       (match copy_array (explode strng, off) len (some (ws_to_chars ws, dstoff)) with
        | none => some ((s, t), .Rerr (.Rraise sub_exn_v))
        | some cs =>
          (match store_assign dst (.W8array (chars_to_ws cs)) s with
           | some s' => some ((s', t), .Rval (.Conv none []))
           | _ => none))
     | _ => none)
  | .CopyAw8Str, [.Loc _ src, .Litv (.IntLit off), .Litv (.IntLit len)] =>
    (match store_lookup src s with
     | some (.W8array ws) =>
       some ((s, t),
         (match copy_array (ws, off) len none with
          | none => .Rerr (.Rraise sub_exn_v)
          | some ws => .Rval (.Litv (.StrLit (implode (ws_to_chars ws))))))
     | _ => none)
  | .CopyAw8Aw8, [.Loc _ src, .Litv (.IntLit off), .Litv (.IntLit len),
      .Loc _ dst, .Litv (.IntLit dstoff)] =>
    (match store_lookup src s, store_lookup dst s with
     | some (.W8array ws), some (.W8array ds) =>
       (match copy_array (ws, off) len (some (ds, dstoff)) with
        | none => some ((s, t), .Rerr (.Rraise sub_exn_v))
        | some ws =>
          (match store_assign dst (.W8array ws) s with
           | some s' => some ((s', t), .Rval (.Conv none []))
           | _ => none))
     | _, _ => none)
  | .XorAw8Str_unsafe, [.Loc _ dst, .Litv (.StrLit str_arg)] =>
    (match store_lookup dst s with
     | some (.W8array bs) =>
       (match xor_bytes (MAP (n2w ∘ ORD) (explode str_arg)) bs with
        | none => none
        | some new_bs =>
          (match store_assign dst (.W8array new_bs) s with
           | none => none
           | some s' => some ((s', t), .Rval (.Conv none []))))
     | _ => none)
  | .Implode, [v] =>
    (match v_to_char_list v with
     | some ls => some ((s, t), .Rval (.Litv (.StrLit (implode ls))))
     | none => none)
  | .Explode, [v] =>
    (match v with
     | .Litv (.StrLit strng) =>
       some ((s, t), .Rval (list_to_v (MAP (fun c => .Litv (.Char c)) (explode strng))))
     | _ => none)
  | .Strsub, [.Litv (.StrLit strng), .Litv (.IntLit i)] =>
    if i < 0 then some ((s, t), .Rerr (.Rraise sub_exn_v))
    else
      let n := Num (ABS (id i))
      if n ≥ strlen strng then some ((s, t), .Rerr (.Rraise sub_exn_v))
      else some ((s, t), .Rval (.Litv (.Char (EL n (explode strng)))))
  | .Strlen, [.Litv (.StrLit strng)] =>
    some ((s, t), .Rval (.Litv (.IntLit (int_of_num (strlen strng)))))
  | .Strcat, [v] =>
    (match v_to_list v with
     | some vs =>
       (match vs_to_string vs with
        | some strng => some ((s, t), .Rval (.Litv (.StrLit strng)))
        | _ => none)
     | _ => none)
  | .VfromList, [v] =>
    (match v_to_list v with
     | some vs => some ((s, t), .Rval (.Vectorv vs))
     | none => none)
  | .Vsub_unsafe, [.Vectorv vs, .Litv (.IntLit i)] =>
    if (0 : Int) ≤ i ∧ Num i < LENGTH vs then some ((s, t), .Rval (EL (Num i) vs))
    else none
  | .Vsub, [.Vectorv vs, .Litv (.IntLit i)] =>
    if i < 0 then some ((s, t), .Rerr (.Rraise sub_exn_v))
    else
      let n := Num (ABS (id i))
      if n ≥ LENGTH vs then some ((s, t), .Rerr (.Rraise sub_exn_v))
      else some ((s, t), .Rval (EL n vs))
  | .Vlength, [.Vectorv vs] =>
    some ((s, t), .Rval (.Litv (.IntLit (int_of_num (LENGTH vs)))))
  | .Aalloc, [.Litv (.IntLit n), v] =>
    if n < 0 then some ((s, t), .Rerr (.Rraise sub_exn_v))
    else
      (match store_alloc (.Varray (REPLICATE (Num (ABS (id n))) v)) s with
       | (s', lnum) => some ((s', t), .Rval (.Loc True lnum)))
  | .AallocEmpty, [.Conv none []] =>
    (match store_alloc (.Varray []) s with
     | (s', lnum) => some ((s', t), .Rval (.Loc True lnum)))
  | .AallocFixed, vs =>
    (match store_alloc (.Varray vs) s with
     | (s', lnum) => some ((s', t), .Rval (.Loc True lnum)))
  | .Asub, [.Loc _ lnum, .Litv (.IntLit i)] =>
    (match store_lookup lnum s with
     | some (.Varray vs) =>
       if i < 0 then some ((s, t), .Rerr (.Rraise sub_exn_v))
       else
         let n := Num (ABS (id i))
         if n ≥ LENGTH vs then some ((s, t), .Rerr (.Rraise sub_exn_v))
         else some ((s, t), .Rval (EL n vs))
     | _ => none)
  | .Asub_unsafe, [.Loc _ lnum, .Litv (.IntLit i)] =>
    (match store_lookup lnum s with
     | some (.Varray vs) =>
       if i < 0 then none
       else
         let n := Num (ABS (id i))
         if n ≥ LENGTH vs then none
         else some ((s, t), .Rval (EL n vs))
     | _ => none)
  | .Alength, [.Loc _ n] =>
    (match store_lookup n s with
     | some (.Varray ws) => some ((s, t), .Rval (.Litv (.IntLit (int_of_num (LENGTH ws)))))
     | _ => none)
  | .Aupdate, [.Loc _ lnum, .Litv (.IntLit i), v] =>
    (match store_lookup lnum s with
     | some (.Varray vs) =>
       if i < 0 then some ((s, t), .Rerr (.Rraise sub_exn_v))
       else
         let n := Num (ABS (id i))
         if n ≥ LENGTH vs then some ((s, t), .Rerr (.Rraise sub_exn_v))
         else
           (match store_assign lnum (.Varray (LUPDATE v n vs)) s with
            | none => none
            | some s' => some ((s', t), .Rval (.Conv none [])))
     | _ => none)
  | .Aupdate_unsafe, [.Loc _ lnum, .Litv (.IntLit i), v] =>
    (match store_lookup lnum s with
     | some (.Varray vs) =>
       if i < 0 then none
       else
         let n := Num (ABS (id i))
         if n ≥ LENGTH vs then none
         else
           (match store_assign lnum (.Varray (LUPDATE v n vs)) s with
            | none => none
            | some s' => some ((s', t), .Rval (.Conv none [])))
     | _ => none)
  | .ConfigGC, [.Litv (.IntLit _), .Litv (.IntLit _)] =>
    some ((s, t), .Rval (.Conv none []))
  | .FFI n, [.Litv (.StrLit conf), .Loc _ lnum] =>
    (match store_lookup lnum s with
     | some (.W8array ws) =>
       (match call_FFI t (.ExtCall n) (MAP (n2w ∘ ORD) (explode conf)) ws with
        | .FFI_return t' ws' =>
          (match store_assign lnum (.W8array ws') s with
           | some s' => some ((s', t'), .Rval (.Conv none []))
           | none => none)
        | .FFI_final outcome => some ((s, t), .Rerr (.Rabort (.Rffi_error outcome))))
     | _ => none)
  | .Env_id, [.Env _ (gen, id)] =>
    some ((s, t), .Rval (.Conv none [nat_to_v gen, nat_to_v id]))
  | .Env_id, [.Conv none [gen, id]] =>
    some ((s, t), .Rval (.Conv none [gen, id]))
  | .ThunkOp th_op, vs => thunk_op' (s, t) th_op vs
  | .Arith a ty, vs =>
    (if EVERY (check_type ty) vs then
       (match do_arith a ty vs with
        | some (.inr res) => some ((s, t), .Rval res)
        | some (.inl exn) => some ((s, t), .Rerr (.Rraise exn))
        | none => none)
     else none)
  | .FromTo ty1 ty2, [v] =>
    (if check_type ty1 v then
       (match do_conversion v ty1 ty2 with
        | some (.inr res) => some ((s, t), .Rval res)
        | some (.inl exn) => some ((s, t), .Rerr (.Rraise exn))
        | none => none)
     else none)
  | .Test tst test_ty, [v1, v2] =>
    (match do_test tst test_ty v1 v2 with
     | .Eq_type_error => none
     | .Eq_val b => some ((s, t), .Rval (Boolv b)))
  | _, _ => none

/- HOL4:
   (* Do a logical operation *)
   Definition do_log_def:
     do_log l v e =
       if l = Andalso ∧ v = Boolv T ∨ l = Orelse ∧ v = Boolv F then SOME (Exp e)
       else if l = Andalso ∧ v = Boolv F ∨ l = Orelse ∧ v = Boolv T then SOME (Val v)
       else NONE
   End -/
def do_log (l : lop) (v : Value) (e : exp) : Option exp_or_val :=
  if l = .Andalso ∧ v = Boolv True ∨ l = .Orelse ∧ v = Boolv False then some (.Exp e)
  else if l = .Andalso ∧ v = Boolv False ∨ l = .Orelse ∧ v = Boolv True then some (.Val v)
  else none

/- HOL4:
   (* Do an if-then-else *)
   Definition do_if_def:
     do_if v e1 e2 =
       if v = Boolv T then SOME e1 else if v = Boolv F then SOME e2 else NONE
   End -/
def do_if (v : Value) (e1 e2 : exp) : Option exp :=
  if v = Boolv True then some e1 else if v = Boolv False then some e2 else none

/- HOL4:
   (* Semantic helpers for definitions *)

   Definition build_constrs_def:
     build_constrs stamp condefs =
       MAP (λ(conN,ts). (conN,LENGTH ts,TypeStamp conN stamp)) condefs
   End -/
def build_constrs (stamp_n : Nat) (condefs : List (conN × List ast_t)) :
    List (conN × Nat × stamp) :=
  MAP (fun cts => (cts.1, LENGTH cts.2, .TypeStamp cts.1 stamp_n)) condefs

/- HOL4:
   (* Build a constructor environment for the type definition tds *)
   Definition build_tdefs_def:
     build_tdefs next_stamp ([]:(tvarN list # mlstring # (mlstring # ast_t list) list) list) =
       ((alist_to_ns []):((mlstring),(mlstring),(num#stamp))namespace) ∧
     build_tdefs next_stamp ((tvs,tn,condefs)::tds) =
       nsAppend (build_tdefs (next_stamp + 1) tds)
         (alist_to_ns (REVERSE (build_constrs next_stamp condefs)))
   End -/
def build_tdefs :
    Nat → List (List tvarN × mlstring × List (mlstring × List ast_t)) →
      Namespace modN conN (Nat × stamp)
  | _, [] => alist_to_ns []
  | next_stamp, (_, _, condefs) :: tds =>
    nsAppend (build_tdefs (next_stamp + 1) tds)
      (alist_to_ns (REVERSE (build_constrs next_stamp condefs)))

/- HOL4:
   (* Checks that no constructor is defined twice in a type *)
   Definition check_dup_ctors_def:
     check_dup_ctors ((tvs,tn,condefs):(tvarN)list#mlstring#(mlstring#(ast_t)list)list) ⇔
       ALL_DISTINCT
         (let x2 = [] in
            FOLDR (λ(n,ts) x2. if T then n::x2 else x2) x2 condefs)
   End -/
def check_dup_ctors (tdef : List tvarN × mlstring × List (mlstring × List ast_t)) : Prop :=
  ALL_DISTINCT
    (let x2 : List mlstring := []
     FOLDR (fun nts x2 => if True then nts.1 :: x2 else x2) x2 tdef.2.2)

/- HOL4:
   Definition combine_dec_result_def:
     combine_dec_result env (r:((v sem_env),'a)result) =
       case r of
       | Rval env' => Rval <|v := nsAppend env'.v env.v; c := nsAppend env'.c env.c|>
       | Rerr e => Rerr e
   End -/
def combine_dec_result {α : Type u} (env : sem_env Value) (r : result (sem_env Value) α) :
    result (sem_env Value) α :=
  match r with
  | .Rval env' => .Rval ⟨nsAppend env'.v env.v, nsAppend env'.c env.c⟩
  | .Rerr e => .Rerr e

/- HOL4:
   Definition extend_dec_env_def:
     extend_dec_env new_env (env: v sem_env) =
       <|c := nsAppend new_env.c env.c; v := nsAppend new_env.v env.v|>
   End
   val _ = set_fixity "+++" (Infixl 480);
   Overload "+++" = “extend_dec_env” -/
def extend_dec_env (new_env env : sem_env Value) : sem_env Value :=
  ⟨nsAppend new_env.v env.v, nsAppend new_env.c env.c⟩

/-- HOL4 `new_env +++ env` is `extend_dec_env new_env env` -/
infixl:480 " +++ " => extend_dec_env

/- HOL4:
   (* With `dest_thunk` we check 3 things: ... *)
   Datatype:
     dest_thunk_ret
       = BadRef
       | NotThunk
       | IsThunk thunk_mode v
   End -/
inductive dest_thunk_ret : Type where
  | BadRef : dest_thunk_ret
  | NotThunk : dest_thunk_ret
  | IsThunk (m : thunk_mode) (v : Value) : dest_thunk_ret

/- HOL4:
   Definition dest_thunk_def:
     dest_thunk [Loc _ n] st =
       (case store_lookup n st of
        | NONE => BadRef
        | SOME (Thunk Evaluated v) => IsThunk Evaluated v
        | SOME (Thunk NotEvaluated v) => IsThunk NotEvaluated v
        | SOME _ => NotThunk) ∧
     dest_thunk vs st = NotThunk
   End -/
def dest_thunk : List Value → List (store_v Value) → dest_thunk_ret
  | [.Loc _ n], st =>
    (match store_lookup n st with
     | none => .BadRef
     | some (.Thunk .Evaluated v) => .IsThunk .Evaluated v
     | some (.Thunk .NotEvaluated v) => .IsThunk .NotEvaluated v
     | some _ => .NotThunk)
  | _, _ => .NotThunk

/- HOL4:
   Definition update_thunk_def:
     update_thunk [Loc _ n] st [v] =
       (case dest_thunk [v] st of
        | NotThunk => store_assign n (Thunk Evaluated v) st
        | _ => NONE) ∧
     update_thunk _ st _ = NONE
   End -/
def update_thunk : List Value → List (store_v Value) → List Value →
    Option (List (store_v Value))
  | [.Loc _ n], st, [v] =>
    (match dest_thunk [v] st with
     | .NotThunk => store_assign n (.Thunk .Evaluated v) st
     | _ => none)
  | _, _, _ => none

end
