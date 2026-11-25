import CmlTS.Namespace
import CmlTS.Mlstring
import CmlTS.Location

/-!
# ast (HOL4 theory `ast`): CakeML abstract syntax

Constructors live in the namespace of their datatype (`lit.IntLit`, `arith.Add`, `exp.Lit`, ...).
-/

universe u v w

noncomputable section

open Classical

/- HOL4:
   (* Literal constants *)
   Datatype:
     lit =
       IntLit int
     | Char char
     | StrLit mlstring
     | Word8 word8
     | Word64 word64
     | Float64 word64
   End -/
inductive lit : Type where
  | IntLit (i : Int) : lit
  | Char (c : char) : lit
  | StrLit (s : mlstring) : lit
  | Word8 (w : word8) : lit
  | Word64 (w : word64) : lit
  | Float64 (w : word64) : lit

instance : Inhabited lit := ⟨.IntLit 0⟩

/- HOL4:
   Datatype:
     shift = Lsl | Lsr | Asr | Ror
   End -/
inductive shift : Type where
  | Lsl : shift
  | Lsr : shift
  | Asr : shift
  | Ror : shift

/- HOL4:
   Datatype:
     arith = Add | Sub | Mul | Div | Mod | Neg | And | Xor | Or | Not | Abs | Sqrt | FMA
   End -/
inductive arith : Type where
  | Add : arith
  | Sub : arith
  | Mul : arith
  | Div : arith
  | Mod : arith
  | Neg : arith
  | And : arith
  | Xor : arith
  | Or : arith
  | Not : arith
  | Abs : arith
  | Sqrt : arith
  | FMA : arith
  deriving DecidableEq

/- HOL4:
   (* Module names *)    Type modN = “:mlstring”
   (* Variable names *)  Type varN = “:mlstring”
   (* Constructor names (from datatype definitions) *)  Type conN = ``: mlstring``
   (* Type names *)      Type typeN = ``: mlstring``
   (* Type variable names *)  Type tvarN = ``: mlstring`` -/
abbrev modN : Type := mlstring
abbrev varN : Type := mlstring
abbrev conN : Type := mlstring
abbrev typeN : Type := mlstring
abbrev tvarN : Type := mlstring

/- HOL4:
   Datatype:
     word_size = W8 | W64
   End -/
inductive word_size : Type where
  | W8 : word_size
  | W64 : word_size
  deriving DecidableEq

/- HOL4:
   Datatype:
     thunk_mode = Evaluated | NotEvaluated
   End -/
inductive thunk_mode : Type where
  | Evaluated : thunk_mode
  | NotEvaluated : thunk_mode
  deriving DecidableEq

instance : Inhabited thunk_mode := ⟨.Evaluated⟩

/- HOL4:
   Datatype:
     thunk_op =
       AllocThunk thunk_mode
     | UpdateThunk thunk_mode
     | ForceThunk
   End -/
inductive thunk_op : Type where
  | AllocThunk (m : thunk_mode) : thunk_op
  | UpdateThunk (m : thunk_mode) : thunk_op
  | ForceThunk : thunk_op
  deriving DecidableEq

/- HOL4:
   Datatype:
     opb = Lt | Gt | Leq | Geq
   End -/
inductive opb : Type where
  | Lt : opb
  | Gt : opb
  | Leq : opb
  | Geq : opb
  deriving DecidableEq

/- HOL4:
   Datatype:
     test = Equal | Compare opb | AltCompare opb
   End -/
inductive test : Type where
  | Equal : test
  | Compare (o : opb) : test
  | AltCompare (o : opb) : test
  deriving DecidableEq

/- HOL4:
   Datatype:
     prim_type = BoolT
               | IntT
               | CharT
               | StrT
               | WordT word_size
               | Float64T
   End -/
inductive prim_type : Type where
  | BoolT : prim_type
  | IntT : prim_type
  | CharT : prim_type
  | StrT : prim_type
  | WordT (w : word_size) : prim_type
  | Float64T : prim_type
  deriving DecidableEq

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
inductive op : Type where
  | Arith (a : arith) (t : prim_type) : op
  | FromTo (t1 t2 : prim_type) : op
  | Shift (w : word_size) (s : shift) (n : Nat) : op
  | Equality : op
  | Test (t : test) (p : prim_type) : op
  | Opapp : op
  | Opassign : op
  | Opref : op
  | Opderef : op
  | Aw8alloc : op
  | Aw8sub : op
  | Aw8length : op
  | Aw8update : op
  | CopyStrStr : op
  | CopyStrAw8 : op
  | CopyAw8Str : op
  | CopyAw8Aw8 : op
  | XorAw8Str_unsafe : op
  | Implode : op
  | Explode : op
  | Strsub : op
  | Strlen : op
  | Strcat : op
  | VfromList : op
  | Vsub : op
  | Vlength : op
  | Aalloc : op
  | AallocEmpty : op
  | AallocFixed : op
  | Asub : op
  | Alength : op
  | Aupdate : op
  | Vsub_unsafe : op
  | Asub_unsafe : op
  | Aupdate_unsafe : op
  | Aw8sub_unsafe : op
  | Aw8update_unsafe : op
  | ThunkOp (t : thunk_op) : op
  | ListAppend : op
  | ConfigGC : op
  | FFI (s : mlstring) : op
  | Eval : op
  | Env_id : op

instance : Inhabited op := ⟨.Opapp⟩

/- HOL4:
   (* Define operator classes, that allow to group their behavior later *)
   Datatype:
    op_class =
       EvalOp (* Eval primitive *)
     | FunApp (* function application *)
     | Force (* forcing a thunk *)
     | Simple (* arithmetic operation, no finite-precision/reals *)
   End -/
inductive op_class : Type where
  | EvalOp : op_class
  | FunApp : op_class
  | Force : op_class
  | Simple : op_class
  deriving DecidableEq

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
  | .ThunkOp t => (if t = .ForceThunk then .Force else .Simple)
  | _ => .Simple

/- HOL4:
   (* Types used in type annotations *)
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
inductive ast_t : Type where
  | Atvar (tv : tvarN) : ast_t
  | Atfun (t1 t2 : ast_t) : ast_t
  | Attup (ts : List ast_t) : ast_t
  | Atapp (ts : List ast_t) (i : Ident modN typeN) : ast_t

instance : Inhabited ast_t := ⟨.Attup []⟩

/- HOL4:
   (* Patterns *)
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
inductive pat : Type where
  | Pany : pat
  | Pvar (n : varN) : pat
  | Plit (l : lit) : pat
  | Pcon (c : Option (Ident modN conN)) (ps : List pat) : pat
  | Pref (p : pat) : pat
  | Pas (p : pat) (n : varN) : pat
  | Ptannot (p : pat) (t : ast_t) : pat

instance : Inhabited pat := ⟨.Pany⟩

/- HOL4:
   (* Short circuiting logical operations *)
   Datatype:
     lop = Andalso | Orelse
   End -/
inductive lop : Type where
  | Andalso : lop
  | Orelse : lop
  deriving DecidableEq

/- HOL4:
   (* Expressions *)
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
inductive exp : Type where
  | Raise (e : exp) : exp
  | Handle (e : exp) (pes : List (pat × exp)) : exp
  | Lit (l : lit) : exp
  | Con (c : Option (Ident modN conN)) (es : List exp) : exp
  | Var (i : Ident modN varN) : exp
  | Fun (x : varN) (e : exp) : exp
  | App (o : op) (es : List exp) : exp
  | Log (l : lop) (e1 e2 : exp) : exp
  | If (e1 e2 e3 : exp) : exp
  | Mat (e : exp) (pes : List (pat × exp)) : exp
  | Let (x : Option varN) (e1 e2 : exp) : exp
  | Letrec (funs : List (varN × varN × exp)) (e : exp) : exp
  | Tannot (e : exp) (t : ast_t) : exp
  | Lannot (e : exp) (l : locs) : exp

instance : Inhabited exp := ⟨.Lit default⟩

/- HOL4:
   Type type_def = ``: ( tvarN list # typeN # (conN # ast_t list) list) list`` -/
abbrev type_def : Type := List (List tvarN × typeN × List (conN × List ast_t))

/- HOL4:
   (* Declarations *)
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
inductive dec : Type where
  | Dlet (l : locs) (p : pat) (e : exp) : dec
  | Dletrec (l : locs) (funs : List (varN × varN × exp)) : dec
  | Dtype (l : locs) (td : type_def) : dec
  | Dtabbrev (l : locs) (tvs : List tvarN) (tn : typeN) (t : ast_t) : dec
  | Dexn (l : locs) (cn : conN) (ts : List ast_t) : dec
  | Dmod (mn : modN) (ds : List dec) : dec
  | Dlocal (lds : List dec) (ds : List dec) : dec
  | Denv (n : tvarN) : dec

instance : Inhabited dec := ⟨.Denv default⟩

/- HOL4:
   (* Accumulates the bindings of a pattern *)
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
def pats_bindings : List pat → List varN → List varN
  | [], already_bound => already_bound
  | p :: ps, already_bound => pats_bindings ps (pat_bindings p already_bound)
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
   (Lean: structural recursion through the nested lists with the auxiliary functions
   `every_exp_list`, `every_exp_pes`, `every_exp_funs`; the HOL4 equations with `EVERY` are
   the theorems `every_exp_eq_*` below.) -/
mutual
def every_exp (p : exp → Prop) : exp → Prop
  | .Raise e => p (.Raise e) ∧ every_exp p e
  | .Handle e pes => p (.Handle e pes) ∧ every_exp p e ∧ every_exp_pes p pes
  | .Lit l => p (.Lit l)
  | .Con cn es => p (.Con cn es) ∧ every_exp_list p es
  | .Var v => p (.Var v)
  | .Fun x e => p (.Fun x e) ∧ every_exp p e
  | .App o es => p (.App o es) ∧ every_exp_list p es
  | .Log l e1 e2 => p (.Log l e1 e2) ∧ every_exp p e1 ∧ every_exp p e2
  | .If e1 e2 e3 => p (.If e1 e2 e3) ∧ every_exp p e1 ∧ every_exp p e2 ∧ every_exp p e3
  | .Mat e pes => p (.Mat e pes) ∧ every_exp p e ∧ every_exp_pes p pes
  | .Let x e1 e2 => p (.Let x e1 e2) ∧ every_exp p e1 ∧ every_exp p e2
  | .Tannot e a => p (.Tannot e a) ∧ every_exp p e
  | .Lannot e a => p (.Lannot e a) ∧ every_exp p e
  | .Letrec funs e => p (.Letrec funs e) ∧ every_exp p e ∧ every_exp_funs p funs
def every_exp_list (p : exp → Prop) : List exp → Prop
  | [] => True
  | e :: es => every_exp p e ∧ every_exp_list p es
def every_exp_pes (p : exp → Prop) : List (pat × exp) → Prop
  | [] => True
  | (_, e) :: pes => every_exp p e ∧ every_exp_pes p pes
def every_exp_funs (p : exp → Prop) : List (varN × varN × exp) → Prop
  | [] => True
  | (_, _, e) :: funs => every_exp p e ∧ every_exp_funs p funs
end

theorem every_exp_list_eq (p : exp → Prop) (es : List exp) :
    every_exp_list p es = EVERY (every_exp p) es := by
  induction es with
  | nil => rfl
  | cons e es ih => simp only [every_exp_list, EVERY, ih]

theorem every_exp_pes_eq (p : exp → Prop) (pes : List (pat × exp)) :
    every_exp_pes p pes = EVERY (fun pe => every_exp p pe.2) pes := by
  induction pes with
  | nil => rfl
  | cons pe pes ih => obtain ⟨_, e⟩ := pe; simp only [every_exp_pes, EVERY, ih]

theorem every_exp_funs_eq (p : exp → Prop) (funs : List (varN × varN × exp)) :
    every_exp_funs p funs = EVERY (fun f => every_exp p f.2.2) funs := by
  induction funs with
  | nil => rfl
  | cons f funs ih => obtain ⟨_, _, e⟩ := f; simp only [every_exp_funs, EVERY, ih]

end
