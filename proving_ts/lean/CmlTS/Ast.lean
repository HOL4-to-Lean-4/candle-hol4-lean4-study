import CmlTS.Namespace
import CmlTS.Location
import CmlTS.Mlstring

/-
HOL4 theory `ast` (astScript.sml).
-/

namespace CmlTS

noncomputable section

open scoped Classical

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
  deriving Inhabited

/- HOL4:
Datatype:
  shift = Lsl | Lsr | Asr | Ror
End -/
inductive shift
  | Lsl
  | Lsr
  | Asr
  | Ror

/- HOL4:
Datatype:
  arith = Add | Sub | Mul | Div | Mod | Neg | And | Xor | Or | Not | Abs | Sqrt | FMA
End -/
inductive arith
  | Add
  | Sub
  | Mul
  | Div
  | Mod
  | Neg
  | And
  | Xor
  | Or
  | Not
  | Abs
  | Sqrt
  | FMA

/- HOL4: Type modN = “:mlstring” -/
abbrev modN : Type := mlstring

/- HOL4: Type varN = “:mlstring” -/
abbrev varN : Type := mlstring

/- HOL4: Type conN = ``: mlstring`` -/
abbrev conN : Type := mlstring

/- HOL4: Type typeN = ``: mlstring`` -/
abbrev typeN : Type := mlstring

/- HOL4: Type tvarN = ``: mlstring`` -/
abbrev tvarN : Type := mlstring

/- HOL4:
Datatype:
  word_size = W8 | W64
End -/
inductive word_size
  | W8
  | W64

export word_size (W8 W64)

/- HOL4:
Datatype:
  thunk_mode = Evaluated | NotEvaluated
End -/
inductive thunk_mode
  | Evaluated
  | NotEvaluated

export thunk_mode (Evaluated NotEvaluated)

/- HOL4:
Datatype:
  thunk_op =
    AllocThunk thunk_mode
  | UpdateThunk thunk_mode
  | ForceThunk
End -/
inductive thunk_op_t
  | AllocThunk (m : thunk_mode)
  | UpdateThunk (m : thunk_mode)
  | ForceThunk

export thunk_op_t (AllocThunk UpdateThunk ForceThunk)

/- HOL4:
Datatype:
  opb = Lt | Gt | Leq | Geq
End -/
inductive opb
  | Lt
  | Gt
  | Leq
  | Geq

/- HOL4:
Datatype:
  test = Equal | Compare opb | AltCompare opb
End -/
inductive test
  | Equal
  | Compare (o : opb)
  | AltCompare (o : opb)

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
  | WordT (sz : word_size)
  | Float64T

export prim_type (BoolT IntT CharT StrT WordT Float64T)

/- HOL4:
Datatype:
  op =
    Arith arith prim_type
  | FromTo prim_type prim_type
  | Shift word_size shift num
  | Equality
  | Test test prim_type
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
  | ThunkOp thunk_op
  | ListAppend
  | ConfigGC
  | FFI mlstring
  | Eval
  | Env_id
End -/
inductive op
  | Arith (a : arith) (ty : prim_type)
  | FromTo (ty1 ty2 : prim_type)
  | Shift (sz : word_size) (sh : shift) (n : Nat)
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
  | ThunkOp (o : thunk_op_t)
  | ListAppend
  | ConfigGC
  | FFI (s : mlstring)
  | Eval
  | Env_id

export op (Arith FromTo Shift Equality Test Opapp Opassign Opref Opderef Aw8alloc Aw8sub
  Aw8length Aw8update CopyStrStr CopyStrAw8 CopyAw8Str CopyAw8Aw8 XorAw8Str_unsafe Implode
  Explode Strsub Strlen Strcat VfromList Vsub Vlength Aalloc AallocEmpty AallocFixed Asub
  Alength Aupdate Vsub_unsafe Asub_unsafe Aupdate_unsafe Aw8sub_unsafe Aw8update_unsafe
  ThunkOp ListAppend ConfigGC FFI Eval Env_id)

/- HOL4:
Datatype:
 op_class =
    EvalOp (* Eval primitive *)
  | FunApp (* function application *)
  | Force (* forcing a thunk *)
  | Simple (* arithmetic operation, no finite-precision/reals *)
End -/
inductive op_class
  | EvalOp
  | FunApp
  | Force
  | Simple

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
  | Opapp => FunApp
  | Eval => EvalOp
  | ThunkOp t => if t = ForceThunk then Force else Simple
  | _ => Simple

/- HOL4:
Datatype:
 ast_t =
    Atvar tvarN
  | Atfun ast_t ast_t
  | Attup (ast_t list)
  | Atapp (ast_t list) ((modN, typeN) id)
End -/
inductive ast_t
  | Atvar (tv : tvarN)
  | Atfun (t1 t2 : ast_t)
  | Attup (ts : List ast_t)
  | Atapp (ts : List ast_t) (tn : ident modN typeN)
  deriving Inhabited

export ast_t (Atvar Atfun Attup Atapp)

/- HOL4:
Datatype:
 pat =
    Pany
  | Pvar varN
  | Plit lit
  | Pcon (((modN, conN) id) option) (pat list)
  | Pref pat
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
  deriving Inhabited

export pat (Pany Pvar Plit Pcon Pref Pas Ptannot)

/- HOL4:
Datatype:
  lop = Andalso | Orelse
End -/
inductive lop
  | Andalso
  | Orelse

export lop (Andalso Orelse)

/- HOL4:
Datatype:
 exp =
    Raise exp
  | Handle exp ((pat # exp) list)
  | Lit lit
  | Con (((modN, conN)id)option) (exp list)
  | Var ((modN, varN) id)
  | Fun varN exp
  | App op (exp list)
  | Log lop exp exp
  | If exp exp exp
  | Mat exp ((pat # exp) list)
  | Let (varN option) exp exp
  | Letrec ((varN # varN # exp) list) exp
  | Tannot exp ast_t
  | Lannot exp locs
End -/
inductive exp
  | Raise (e : exp)
  | Handle (e : exp) (pes : List (pat × exp))
  | Lit (l : lit)
  | Con (cn : Option (ident modN conN)) (es : List exp)
  | Var (n : ident modN varN)
  | Fun (x : varN) (e : exp)
  | App (o : op) (es : List exp)
  | Log (l : lop) (e1 e2 : exp)
  | If (e1 e2 e3 : exp)
  | Mat (e : exp) (pes : List (pat × exp))
  | Let (xo : Option varN) (e1 e2 : exp)
  | Letrec (funs : List (varN × varN × exp)) (e : exp)
  | Tannot (e : exp) (t : ast_t)
  | Lannot (e : exp) (l : locs)
  deriving Inhabited

/- HOL4: Type type_def = ``: ( tvarN list # typeN # (conN # ast_t list) list) list`` -/
abbrev type_def : Type := List (List tvarN × typeN × List (conN × List ast_t))

/- HOL4:
Datatype:
 dec =
    Dlet locs pat exp
  | Dletrec locs ((varN # varN # exp) list)
  | Dtype locs type_def
  | Dtabbrev locs (tvarN list) typeN ast_t
  | Dexn locs conN (ast_t list)
  | Dmod modN (dec list)
  | Dlocal (dec list) (dec list)
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
  deriving Inhabited

export dec (Dlet Dletrec Dtype Dtabbrev Dexn Dmod Dlocal Denv)

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
  | Pany, already_bound => already_bound
  | Pvar n, already_bound => n :: already_bound
  | Plit _, already_bound => already_bound
  | Pcon _ ps, already_bound => pats_bindings ps already_bound
  | Pref p, already_bound => pat_bindings p already_bound
  | Pas p i, already_bound => pat_bindings p (i :: already_bound)
  | Ptannot p _, already_bound => pat_bindings p already_bound

def pats_bindings : List pat → List varN → List varN
  | [], already_bound => already_bound
  | p :: ps, already_bound => pats_bindings ps (pat_bindings p already_bound)

end

/-! Helper lemmas (not HOL4 constants) for termination proofs. -/

theorem sizeOf_snd_lt_aux {α β : Type} [SizeOf α] [SizeOf β] {p : α × β} {l : List (α × β)}
    (h : p ∈ l) : sizeOf p.2 < sizeOf l := by
  have h1 := List.sizeOf_lt_of_mem h
  cases p
  simp at h1 ⊢
  omega

theorem sizeOf_snd_snd_lt_aux {α β γ : Type} [SizeOf α] [SizeOf β] [SizeOf γ] {p : α × β × γ}
    {l : List (α × β × γ)} (h : p ∈ l) : sizeOf p.2.2 < sizeOf l := by
  have h1 := List.sizeOf_lt_of_mem h
  obtain ⟨a, b, c⟩ := p
  simp at h1 ⊢
  omega

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
(`λ(pat,e). every_exp p e` is written with projections: `fun pe => every_exp p pe.2`) -/
def every_exp (p : exp → Prop) : exp → Prop
  | exp.Raise e => p (exp.Raise e) ∧ every_exp p e
  | exp.Handle e pes =>
    p (exp.Handle e pes) ∧ every_exp p e ∧ EVERY (fun pe => every_exp p pe.2) pes
  | exp.Lit l => p (exp.Lit l)
  | exp.Con cn es => p (exp.Con cn es) ∧ EVERY (fun e => every_exp p e) es
  | exp.Var v => p (exp.Var v)
  | exp.Fun x e => p (exp.Fun x e) ∧ every_exp p e
  | exp.App o es => p (exp.App o es) ∧ EVERY (fun e => every_exp p e) es
  | exp.Log l e1 e2 => p (exp.Log l e1 e2) ∧ every_exp p e1 ∧ every_exp p e2
  | exp.If e1 e2 e3 =>
    p (exp.If e1 e2 e3) ∧ every_exp p e1 ∧ every_exp p e2 ∧ every_exp p e3
  | exp.Mat e pes =>
    p (exp.Mat e pes) ∧ every_exp p e ∧ EVERY (fun pe => every_exp p pe.2) pes
  | exp.Let x e1 e2 => p (exp.Let x e1 e2) ∧ every_exp p e1 ∧ every_exp p e2
  | exp.Tannot e a => p (exp.Tannot e a) ∧ every_exp p e
  | exp.Lannot e a => p (exp.Lannot e a) ∧ every_exp p e
  | exp.Letrec funs e =>
    p (exp.Letrec funs e) ∧ every_exp p e ∧ EVERY (fun f => every_exp p f.2.2) funs
termination_by e => sizeOf e
decreasing_by
  all_goals first
    | decreasing_tactic
    | (rename_i h
       have h1 := sizeOf_snd_lt_aux h
       simp only [exp.Handle.sizeOf_spec, exp.Mat.sizeOf_spec]
       omega)
    | (rename_i h
       have h1 := sizeOf_snd_snd_lt_aux h
       simp only [exp.Letrec.sizeOf_spec]
       omega)

end

end CmlTS
