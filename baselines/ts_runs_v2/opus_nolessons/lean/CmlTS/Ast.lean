import CmlTS.Prelude.String
import CmlTS.Mlstring
import CmlTS.Namespace
import CmlTS.Location
/-
  Translation of HOL4 theory `ast` (astScript.sml).
-/
set_option autoImplicit false

namespace CmlTS
open Classical

/- HOL4:
Datatype:
  lit =
    IntLit int
  | Char char
  | StrLit mlstring
  | Word8 word8
  | Word64 word64
  | Float64 word64
End -/
inductive lit
  | IntLit (i : Int)
  | Char (c : char)
  | StrLit (s : mlstring)
  | Word8 (w : word8)
  | Word64 (w : word64)
  | Float64 (w : word64)
  deriving DecidableEq, Inhabited

export lit (IntLit StrLit Word8 Word64 Float64)

/- HOL4:
Datatype:
  shift = Lsl | Lsr | Asr | Ror
End -/
inductive shift
  | Lsl | Lsr | Asr | Ror
  deriving DecidableEq, Inhabited

export shift (Lsl Lsr Asr Ror)

/- HOL4:
Datatype:
  arith = Add | Sub | Mul | Div | Mod | Neg | And | Xor | Or | Not | Abs | Sqrt | FMA
End -/
inductive arith
  | Add | Sub | Mul | Div | Mod | Neg | And | Xor | Or | Not | Abs | Sqrt | FMA
  deriving DecidableEq, Inhabited

/- HOL4:
Type modN = “:mlstring” -/
abbrev modN : Type := mlstring

/- HOL4:
Type varN = “:mlstring” -/
abbrev varN : Type := mlstring

/- HOL4:
Type conN = ``: mlstring`` -/
abbrev conN : Type := mlstring

/- HOL4:
Type typeN = ``: mlstring`` -/
abbrev typeN : Type := mlstring

/- HOL4:
Type tvarN = ``: mlstring`` -/
abbrev tvarN : Type := mlstring

/- HOL4:
Datatype:
  word_size = W8 | W64
End -/
inductive word_size
  | W8 | W64
  deriving DecidableEq, Inhabited

export word_size (W8 W64)

/- HOL4:
Datatype:
  thunk_mode = Evaluated | NotEvaluated
End -/
inductive thunk_mode
  | Evaluated | NotEvaluated
  deriving DecidableEq, Inhabited

export thunk_mode (Evaluated NotEvaluated)

/- HOL4:
Datatype:
  thunk_op =
    AllocThunk thunk_mode
  | UpdateThunk thunk_mode
  | ForceThunk
End -/
inductive thunk_op
  | AllocThunk (m : thunk_mode)
  | UpdateThunk (m : thunk_mode)
  | ForceThunk
  deriving DecidableEq, Inhabited

export thunk_op (AllocThunk UpdateThunk ForceThunk)

/- HOL4:
Datatype:
  opb = Lt | Gt | Leq | Geq
End -/
inductive opb
  | Lt | Gt | Leq | Geq
  deriving DecidableEq, Inhabited

export opb (Lt Gt Leq Geq)

/- HOL4:
Datatype:
  test = Equal | Compare opb | AltCompare opb
End -/
inductive test
  | Equal | Compare (o : opb) | AltCompare (o : opb)
  deriving DecidableEq, Inhabited

export test (Equal Compare AltCompare)

/- HOL4:
Datatype:
  prim_type = BoolT
            | IntT
            | CharT
            | StrT
            | WordT word_size
            | Float64T
End -/
inductive prim_type
  | BoolT
  | IntT
  | CharT
  | StrT
  | WordT (ws : word_size)
  | Float64T
  deriving DecidableEq, Inhabited

export prim_type (BoolT IntT CharT StrT WordT Float64T)

/- HOL4:
Datatype:
  op =
  (* primitive operations for the primitive types: +, -, and, sqrt, etc. *)
    Arith arith prim_type
  (* conversions between primitive types: char<->int, word<->double, word<->int *)
  | FromTo prim_type prim_type
  (* Operations on words *)
  | Shift word_size shift num
  | Equality
  | Test test prim_type
  (* Function application *)
  | Opapp
  (* Reference operations *)
  | Opassign
  | Opref
  | Opderef
  (* Word8Array operations *)
  | Aw8alloc
  | Aw8sub
  | Aw8length
  | Aw8update
  (* string/bytearray conversions *)
  | CopyStrStr
  | CopyStrAw8
  | CopyAw8Str
  | CopyAw8Aw8
  | XorAw8Str_unsafe
  (* String operations *)
  | Implode
  | Explode
  | Strsub
  | Strlen
  | Strcat
  (* Vector operations *)
  | VfromList
  | Vsub
  | Vlength
  (* Array operations *)
  | Aalloc
  | AallocEmpty
  | AallocFixed
  | Asub
  | Alength
  | Aupdate
  (* Unsafe vector/array accesses *)
  | Vsub_unsafe
  | Asub_unsafe
  | Aupdate_unsafe
  | Aw8sub_unsafe
  | Aw8update_unsafe
  (* thunk operations *)
  | ThunkOp thunk_op
  (* List operations *)
  | ListAppend
  (* Configure the GC *)
  | ConfigGC
  (* Call a given foreign function *)
  | FFI mlstring
  (* Evaluate new code in a given env *)
  | Eval
  (* Get the identifier of an env object *)
  | Env_id
End -/
inductive op
  | Arith (a : arith) (ty : prim_type)
  | FromTo (ty1 ty2 : prim_type)
  | Shift (ws : word_size) (sh : shift) (n : Nat)
  | Equality
  | Test (t : test) (ty : prim_type)
  | Opapp
  | Opassign
  | Opref
  | Opderef
  | Aw8alloc
  | Aw8sub
  | Aw8length
  | Aw8update
  | CopyStrStr
  | CopyStrAw8
  | CopyAw8Str
  | CopyAw8Aw8
  | XorAw8Str_unsafe
  | Implode
  | Explode
  | Strsub
  | Strlen
  | Strcat
  | VfromList
  | Vsub
  | Vlength
  | Aalloc
  | AallocEmpty
  | AallocFixed
  | Asub
  | Alength
  | Aupdate
  | Vsub_unsafe
  | Asub_unsafe
  | Aupdate_unsafe
  | Aw8sub_unsafe
  | Aw8update_unsafe
  | ThunkOp (t : thunk_op)
  | ListAppend
  | ConfigGC
  | FFI (s : mlstring)
  | Eval
  | Env_id
  deriving DecidableEq, Inhabited

export op (Arith FromTo Shift Equality Test Opapp Opassign Opref Opderef Aw8alloc Aw8sub Aw8length
  Aw8update CopyStrStr CopyStrAw8 CopyAw8Str CopyAw8Aw8 XorAw8Str_unsafe Implode Explode Strsub
  Strlen Strcat VfromList Vsub Vlength Aalloc AallocEmpty AallocFixed Asub Alength Aupdate
  Vsub_unsafe Asub_unsafe Aupdate_unsafe Aw8sub_unsafe Aw8update_unsafe ThunkOp ListAppend ConfigGC
  FFI Eval Env_id)

/- HOL4:
Datatype:
 op_class =
    EvalOp (* Eval primitive *)
  | FunApp (* function application *)
  | Force (* forcing a thunk *)
  | Simple (* arithmetic operation, no finite-precision/reals *)
End -/
inductive op_class
  | EvalOp | FunApp | Force | Simple
  deriving DecidableEq, Inhabited

export op_class (EvalOp FunApp Force Simple)

/- HOL4:
Definition getOpClass_def[simp]:
 getOpClass op =
 case op of
  | Opapp => FunApp
  | Eval => EvalOp
  | ThunkOp t => (if t = ForceThunk then Force else Simple)
  | _ => Simple
End -/
def getOpClass (o : op) : op_class :=
  match o with
  | .Opapp => .FunApp
  | .Eval => .EvalOp
  | .ThunkOp t => if t = .ForceThunk then .Force else .Simple
  | _ => .Simple

/- HOL4:
Datatype:
 ast_t =
  (* Type variables that the user writes down ('a, 'b, etc.) *)
    Atvar tvarN
  (* Function type *)
  | Atfun ast_t ast_t
  (* Tuple type *)
  | Attup (ast_t list)
  (* Type constructor applications.
    0-ary type applications represent unparameterised types (e.g., num or string) *)
  | Atapp (ast_t list) ((modN, typeN) id)
End -/
inductive ast_t
  | Atvar (tv : tvarN)
  | Atfun (t1 t2 : ast_t)
  | Attup (ts : List ast_t)
  | Atapp (ts : List ast_t) (tn : ident modN typeN)

export ast_t (Atvar Atfun Attup Atapp)

instance : Inhabited ast_t := ⟨.Attup []⟩

/- HOL4:
Datatype:
 pat =
    Pany
  | Pvar varN
  | Plit lit
  (* Constructor applications.
     A Nothing constructor indicates a tuple pattern. *)
  | Pcon (((modN, conN) id) option) (pat list)
  | Pref pat
  (* Pattern alias. *)
  | Pas pat varN
  | Ptannot pat ast_t
End -/
inductive pat
  | Pany
  | Pvar (x : varN)
  | Plit (l : lit)
  | Pcon (cn : Option (ident modN conN)) (ps : List pat)
  | Pref (p : pat)
  | Pas (p : pat) (x : varN)
  | Ptannot (p : pat) (t : ast_t)

export pat (Pany Pvar Plit Pcon Pref Pas Ptannot)

instance : Inhabited pat := ⟨.Pany⟩

/- HOL4:
Datatype:
  lop = Andalso | Orelse
End -/
inductive lop
  | Andalso | Orelse
  deriving DecidableEq, Inhabited

export lop (Andalso Orelse)

/- HOL4:
Datatype:
 exp =
    Raise exp
  | Handle exp ((pat # exp) list)
  | Lit lit
  (* Constructor application.
     A Nothing constructor indicates a tuple pattern. *)
  | Con (((modN, conN)id)option) (exp list)
  | Var ((modN, varN) id)
  | Fun varN exp
  (* Application a primitive operator to arguments.
     Includes function application. *)
  | App op (exp list)
  (* Logical operations (and, or) *)
  | Log lop exp exp
  | If exp exp exp
  (* Pattern matching *)
  | Mat exp ((pat # exp) list)
  (* A let expression
     A Nothing value for the binding indicates that this is a
     sequencing expression, that is: (e1; e2). *)
  | Let (varN option) exp exp
  (* Local definition (potentially) mutually recursive
     functions.
     The first varN is the function's name, and the second varN
     is its parameter. *)
  | Letrec ((varN # varN # exp) list) exp
  | Tannot exp ast_t
  (* Location annotated expressions, not expected in source programs *)
  | Lannot exp locs
End -/
inductive exp
  | Raise (e : exp)
  | Handle (e : exp) (pes : List (pat × exp))
  | Lit (l : lit)
  | Con (cn : Option (ident modN conN)) (es : List exp)
  | Var (x : ident modN varN)
  | Fun (x : varN) (e : exp)
  | App (o : op) (es : List exp)
  | Log (l : lop) (e1 e2 : exp)
  | If (e1 e2 e3 : exp)
  | Mat (e : exp) (pes : List (pat × exp))
  | Let (x : Option varN) (e1 e2 : exp)
  | Letrec (funs : List (varN × varN × exp)) (e : exp)
  | Tannot (e : exp) (t : ast_t)
  | Lannot (e : exp) (l : locs)

export exp (Raise Handle Lit Con Var Fun App Log If Mat Let Letrec Tannot Lannot)

instance : Inhabited exp := ⟨.Con none []⟩

/- HOL4:
Type type_def = ``: ( tvarN list # typeN # (conN # ast_t list) list) list`` -/
abbrev type_def : Type := List (List tvarN × typeN × List (conN × List ast_t))

/- HOL4:
Datatype:
 dec =
  (* Top-level bindings
   * The pattern allows several names to be bound at once *)
    Dlet locs pat exp
  (* Mutually recursive function definition *)
  | Dletrec locs ((varN # varN # exp) list)
  (* Type definition
     Defines several data types, each which has several
     named variants, which can in turn have several arguments.
   *)
  | Dtype locs type_def
  (* Type abbreviations *)
  | Dtabbrev locs (tvarN list) typeN ast_t
  (* New exceptions *)
  | Dexn locs conN (ast_t list)
  (* Module *)
  | Dmod modN (dec list)
  (* Local: local part, visible part *)
  | Dlocal (dec list) (dec list)
  (* Store current lexical env in an env value *)
  | Denv tvarN
End -/
inductive dec
  | Dlet (l : locs) (p : pat) (e : exp)
  | Dletrec (l : locs) (funs : List (varN × varN × exp))
  | Dtype (l : locs) (tds : type_def)
  | Dtabbrev (l : locs) (tvs : List tvarN) (tn : typeN) (t : ast_t)
  | Dexn (l : locs) (cn : conN) (ts : List ast_t)
  | Dmod (mn : modN) (ds : List dec)
  | Dlocal (lds ds : List dec)
  | Denv (n : tvarN)

export dec (Dlet Dletrec Dtype Dtabbrev Dexn Dmod Dlocal Denv)

instance : Inhabited dec := ⟨.Dlocal [] []⟩

/- HOL4:
Definition pat_bindings_def:
  pat_bindings Pany already_bound = already_bound ∧
  pat_bindings (Pvar n) already_bound = n::already_bound ∧
  pat_bindings (Plit l) already_bound = already_bound ∧
  pat_bindings (Pcon v0 ps) already_bound = pats_bindings ps already_bound ∧
  pat_bindings (Pref p) already_bound = pat_bindings p already_bound ∧
  pat_bindings (Pas p i) already_bound = pat_bindings p (i::already_bound) ∧
  pat_bindings (Ptannot p v1) already_bound = pat_bindings p already_bound ∧
  pats_bindings [] already_bound = already_bound ∧
  pats_bindings (p::ps) already_bound =
  pats_bindings ps (pat_bindings p already_bound)
End -/
mutual
def pat_bindings : pat → List varN → List varN
  | .Pany, already_bound => already_bound
  | .Pvar n, already_bound => n :: already_bound
  | .Plit _, already_bound => already_bound
  | .Pcon _ ps, already_bound => pats_bindings ps already_bound
  | .Pref p, already_bound => pat_bindings p already_bound
  | .Pas p i, already_bound => pat_bindings p (i :: already_bound)
  | .Ptannot p _, already_bound => pat_bindings p already_bound
termination_by structural p => p
def pats_bindings : List pat → List varN → List varN
  | [], already_bound => already_bound
  | p :: ps, already_bound => pats_bindings ps (pat_bindings p already_bound)
termination_by structural ps => ps
end

/- HOL4:
Definition every_exp_def[simp]:
  (every_exp p (Raise e) ⇔
             p (Raise e) ∧ every_exp p e) ∧
  (every_exp p (Handle e pes) ⇔
             p (Handle e pes) ∧ every_exp p e ∧ EVERY (λ(pat,e). every_exp p e) pes) ∧
  (every_exp p (ast$Lit l) ⇔
             p (ast$Lit l)) ∧
  (every_exp p (Con cn es) ⇔
             p (Con cn es) ∧ EVERY (every_exp p) es) ∧
  (every_exp p (Var v) ⇔
             p (Var v)) ∧
  (every_exp p (Fun x e) ⇔
             p (Fun x e) ∧ every_exp p e) ∧
  (every_exp p (App op es) ⇔
             p (App op es) ∧ EVERY (every_exp p) es) ∧
  (every_exp p (Log lop e1 e2) ⇔
             p (Log lop e1 e2) ∧ every_exp p e1 ∧ every_exp p e2) ∧
  (every_exp p (If e1 e2 e3) ⇔
             p (If e1 e2 e3) ∧ every_exp p e1 ∧ every_exp p e2 ∧ every_exp p e3) ∧
  (every_exp p (Mat e pes) ⇔
             p (Mat e pes) ∧ every_exp p e ∧ EVERY (λ(pat,e). every_exp p e) pes) ∧
  (every_exp p (Let x e1 e2) ⇔
             p (Let x e1 e2) ∧ every_exp p e1 ∧ every_exp p e2) ∧
  (every_exp p (Tannot e a) ⇔
             p (Tannot e a) ∧ every_exp p e) ∧
  (every_exp p (Lannot e a) ⇔
             p (Lannot e a) ∧ every_exp p e) ∧
  (every_exp p (Letrec funs e) ⇔
             p (Letrec funs e) ∧ every_exp p e ∧ EVERY (λ(n,v,e). every_exp p e) funs)
End
   (`λ(pat,e). every_exp p e` is written `fun pe => every_exp p pe.2`, and so on.) -/
def every_exp (p : exp → Prop) : exp → Prop
  | .Raise e => p (.Raise e) ∧ every_exp p e
  | .Handle e pes =>
    p (.Handle e pes) ∧ every_exp p e ∧ EVERY (fun pe => every_exp p pe.2) pes
  | .Lit l => p (.Lit l)
  | .Con cn es => p (.Con cn es) ∧ EVERY (fun e => every_exp p e) es
  | .Var x => p (.Var x)
  | .Fun x e => p (.Fun x e) ∧ every_exp p e
  | .App o es => p (.App o es) ∧ EVERY (fun e => every_exp p e) es
  | .Log l e1 e2 => p (.Log l e1 e2) ∧ every_exp p e1 ∧ every_exp p e2
  | .If e1 e2 e3 => p (.If e1 e2 e3) ∧ every_exp p e1 ∧ every_exp p e2 ∧ every_exp p e3
  | .Mat e pes =>
    p (.Mat e pes) ∧ every_exp p e ∧ EVERY (fun pe => every_exp p pe.2) pes
  | .Let x e1 e2 => p (.Let x e1 e2) ∧ every_exp p e1 ∧ every_exp p e2
  | .Tannot e a => p (.Tannot e a) ∧ every_exp p e
  | .Lannot e a => p (.Lannot e a) ∧ every_exp p e
  | .Letrec funs e =>
    p (.Letrec funs e) ∧ every_exp p e ∧ EVERY (fun f => every_exp p f.2.2) funs
termination_by e => e
decreasing_by
  all_goals simp_wf
  all_goals first
    | omega
    | (have := List.sizeOf_lt_of_mem (by assumption); omega)
    | (have := sizeOf_snd_lt_of_mem (by assumption); omega)
    | (have := sizeOf_snd_snd_lt_of_mem (by assumption); omega)

end CmlTS
