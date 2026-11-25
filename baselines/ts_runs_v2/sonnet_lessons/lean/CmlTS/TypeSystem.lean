import CmlTS.Ast
import CmlTS.Namespace
import CmlTS.SemanticPrimitives

/-!
# typeSystem (HOL4 theory `typeSystem`): specification of CakeML's type system

Renamed types (HOL4 -> Lean): `t` -> `Ty`.

Functions defined by recursion through `EVERY`/`MAP` over `t`/`ast_t`/`exp` are defined by
structural recursion with an auxiliary function on lists (`*_list`); the theorems `*_list_eq`
state that the auxiliary function is the `EVERY`/`MAP` of the main function (these are exactly the
HOL4 defining equations).
-/

universe u v w

noncomputable section

open Classical

/- HOL4:
   Type type_ident = “:num” -/
abbrev type_ident : Type := Nat

/- HOL4:
   (* Types *)
   Datatype:
    t =
     (* Type variables that the user writes down ('a, 'b, etc.) *)
       Tvar tvarN
     (* deBruijn indexed type variables. *)
     | Tvar_db num
     (* The two numbers represent the identity of the type constructor. The first
        is the identity of the compilation unit that it was defined in, and the
        second is its identity inside of that unit *)
     | Tapp (t list) type_ident
   End -/
inductive Ty : Type where
  | Tvar (tv : tvarN) : Ty
  | Tvar_db (n : Nat) : Ty
  | Tapp (ts : List Ty) (tn : type_ident) : Ty

instance : Inhabited Ty := ⟨.Tvar_db 0⟩

/- HOL4:
   (* Some abbreviations *)
   Definition Tarray_num_def:   ((Tarray_num:num) : type_ident= (( 0 : num)))
   Definition Tbool_num_def:    Tbool_num = 1
   Definition Tchar_num_def:    Tchar_num = 2
   Definition Texn_num_def:     Texn_num = 3
   Definition Tfn_num_def:      Tfn_num = 4
   Definition Tint_num_def:     Tint_num = 5
   Definition Tlist_num_def:    Tlist_num = 6
   Definition Tref_num_def:     Tref_num = 7
   Definition Tstring_num_def:  Tstring_num = 8
   Definition Ttup_num_def:     Ttup_num = 9
   Definition Tvector_num_def:  Tvector_num = 10
   Definition Tword64_num_def:  Tword64_num = 11
   Definition Tword8_num_def:   Tword8_num = 12
   Definition Tword8array_num_def:  Tword8array_num = 13
   Definition Tdouble_num_def:  Tdouble_num = 14 -/
def Tarray_num : type_ident := 0
def Tbool_num : type_ident := 1
def Tchar_num : type_ident := 2
def Texn_num : type_ident := 3
def Tfn_num : type_ident := 4
def Tint_num : type_ident := 5
def Tlist_num : type_ident := 6
def Tref_num : type_ident := 7
def Tstring_num : type_ident := 8
def Ttup_num : type_ident := 9
def Tvector_num : type_ident := 10
def Tword64_num : type_ident := 11
def Tword8_num : type_ident := 12
def Tword8array_num : type_ident := 13
def Tdouble_num : type_ident := 14

/- HOL4:
   (* The numbers for the primitive types *)
   Definition prim_type_nums_def:
    prim_type_nums: num list =
    [Tarray_num; Tchar_num; Texn_num; Tfn_num; Tint_num; Tref_num; Tstring_num;
     Ttup_num; Tvector_num; Tword64_num; Tword8_num; Tword8array_num; Tdouble_num;
    ]
   End -/
def prim_type_nums : List Nat :=
  [Tarray_num, Tchar_num, Texn_num, Tfn_num, Tint_num, Tref_num, Tstring_num,
   Ttup_num, Tvector_num, Tword64_num, Tword8_num, Tword8array_num, Tdouble_num]

/- HOL4:
   Definition Tarray_def:   Tarray t = Tapp [t] Tarray_num
   Definition Tbool_def:    Tbool = Tapp [] Tbool_num
   Definition Tchar_def:    Tchar = Tapp [] Tchar_num
   Definition Texn_def:     Texn = Tapp [] Texn_num
   Definition Tfn_def:      Tfn t1 t2 = Tapp [t1;t2] Tfn_num
   Definition Tint_def:     Tint = Tapp [] Tint_num
   Definition Tlist_def:    Tlist t = Tapp [t] Tlist_num
   Definition Tref_def:     Tref t = Tapp [t] Tref_num
   Definition Tstring_def:  Tstring = Tapp [] Tstring_num
   Definition Ttup_def:     Ttup ts = Tapp ts Ttup_num
   Definition Tvector_def:  Tvector t = Tapp [t] Tvector_num
   Definition Tword64_def:  Tword64 = Tapp [] Tword64_num
   Definition Tword8_def:   Tword8 = Tapp [] Tword8_num
   Definition Tword8array_def:  Tword8array = Tapp [] Tword8array_num
   Definition Tdouble_def:  Tdouble = Tapp [] Tdouble_num -/
def Tarray (t : Ty) : Ty := .Tapp [t] Tarray_num
def Tbool : Ty := .Tapp [] Tbool_num
def Tchar : Ty := .Tapp [] Tchar_num
def Texn : Ty := .Tapp [] Texn_num
def Tfn (t1 t2 : Ty) : Ty := .Tapp [t1, t2] Tfn_num
def Tint : Ty := .Tapp [] Tint_num
def Tlist (t : Ty) : Ty := .Tapp [t] Tlist_num
def Tref (t : Ty) : Ty := .Tapp [t] Tref_num
def Tstring : Ty := .Tapp [] Tstring_num
def Ttup (ts : List Ty) : Ty := .Tapp ts Ttup_num
def Tvector (t : Ty) : Ty := .Tapp [t] Tvector_num
def Tword64 : Ty := .Tapp [] Tword64_num
def Tword8 : Ty := .Tapp [] Tword8_num
def Tword8array : Ty := .Tapp [] Tword8array_num
def Tdouble : Ty := .Tapp [] Tdouble_num

/- HOL4:
   (* Check that the free type variables are in the given list. Every deBruijn
    * variable must be smaller than the first argument. So if it is 0, no deBruijn
    * indices are permitted. *)
   Definition check_freevars_def:
   ((check_freevars:num ->(mlstring)list -> t -> bool) dbmax tvs (Tvar tv)=
      (MEM tv tvs))
   /\
   ((check_freevars:num ->(mlstring)list -> t -> bool) dbmax tvs (Tapp ts tn)=
      (EVERY (check_freevars dbmax tvs) ts))
   /\
   ((check_freevars:num ->(mlstring)list -> t -> bool) dbmax tvs (Tvar_db n)=  (n < dbmax))
   End -/
mutual
def check_freevars (dbmax : Nat) (tvs : List mlstring) : Ty → Prop
  | .Tvar tv => MEM tv tvs
  | .Tapp ts _ => check_freevars_list dbmax tvs ts
  | .Tvar_db n => n < dbmax
def check_freevars_list (dbmax : Nat) (tvs : List mlstring) : List Ty → Prop
  | [] => True
  | t :: ts => check_freevars dbmax tvs t ∧ check_freevars_list dbmax tvs ts
end

theorem check_freevars_list_eq (dbmax : Nat) (tvs : List mlstring) (ts : List Ty) :
    check_freevars_list dbmax tvs ts = EVERY (check_freevars dbmax tvs) ts := by
  induction ts with
  | nil => rfl
  | cons t ts ih => simp only [check_freevars_list, EVERY, ih]

/- HOL4:
   Definition check_freevars_ast_def:
   ((check_freevars_ast:(mlstring)list -> ast_t -> bool) tvs (Atvar tv)=
      (MEM tv tvs))
   /\
   ((check_freevars_ast:(mlstring)list -> ast_t -> bool) tvs (Attup ts)=
      (EVERY (check_freevars_ast tvs) ts))
   /\
   ((check_freevars_ast:(mlstring)list -> ast_t -> bool) tvs (Atfun t1 t2)=
      (check_freevars_ast tvs t1 /\ check_freevars_ast tvs t2))
   /\
   ((check_freevars_ast:(mlstring)list -> ast_t -> bool) tvs (Atapp ts tn)=
      (EVERY (check_freevars_ast tvs) ts))
   End -/
mutual
def check_freevars_ast (tvs : List mlstring) : ast_t → Prop
  | .Atvar tv => MEM tv tvs
  | .Attup ts => check_freevars_ast_list tvs ts
  | .Atfun t1 t2 => check_freevars_ast tvs t1 ∧ check_freevars_ast tvs t2
  | .Atapp ts _ => check_freevars_ast_list tvs ts
def check_freevars_ast_list (tvs : List mlstring) : List ast_t → Prop
  | [] => True
  | t :: ts => check_freevars_ast tvs t ∧ check_freevars_ast_list tvs ts
end

theorem check_freevars_ast_list_eq (tvs : List mlstring) (ts : List ast_t) :
    check_freevars_ast_list tvs ts = EVERY (check_freevars_ast tvs) ts := by
  induction ts with
  | nil => rfl
  | cons t ts ih => simp only [check_freevars_ast_list, EVERY, ih]

/- HOL4:
   (* Simultaneous substitution of types for type variables in a type *)
   Definition type_subst_def:
   ((type_subst:((mlstring),(t))fmap -> t -> t) s (Tvar tv)=
      ((case FLOOKUP s tv of
         NONE => Tvar tv
       | SOME(t) => t
     )))
   /\
   ((type_subst:((mlstring),(t))fmap -> t -> t) s (Tapp ts tn)=
      (Tapp (MAP (type_subst s) ts) tn))
   /\
   ((type_subst:((mlstring),(t))fmap -> t -> t) s (Tvar_db n)=  (Tvar_db n))
   End -/
mutual
def type_subst (s : FMap mlstring Ty) : Ty → Ty
  | .Tvar tv =>
    match FLOOKUP s tv with
    | none => .Tvar tv
    | some t => t
  | .Tapp ts tn => .Tapp (type_subst_list s ts) tn
  | .Tvar_db n => .Tvar_db n
def type_subst_list (s : FMap mlstring Ty) : List Ty → List Ty
  | [] => []
  | t :: ts => type_subst s t :: type_subst_list s ts
end

theorem type_subst_list_eq (s : FMap mlstring Ty) (ts : List Ty) :
    type_subst_list s ts = MAP (type_subst s) ts := by
  induction ts with
  | nil => rfl
  | cons t ts ih => simp only [type_subst_list, MAP, List.map_cons, ih]

/- HOL4:
   (* Increment the deBruijn indices in a type by n levels, skipping all levels
    * less than skip. *)
   Definition deBruijn_inc_def:
   ((deBruijn_inc:num -> num -> t -> t) skip n (Tvar tv)=  (Tvar tv))
   /\
   ((deBruijn_inc:num -> num -> t -> t) skip n (Tvar_db m)=
      (if m < skip then
       Tvar_db m
     else
       Tvar_db (m + n)))
   /\
   ((deBruijn_inc:num -> num -> t -> t) skip n (Tapp ts tn)=  (Tapp (MAP (deBruijn_inc skip n) ts) tn))
   End -/
mutual
def deBruijn_inc (skip n : Nat) : Ty → Ty
  | .Tvar tv => .Tvar tv
  | .Tvar_db m => if m < skip then .Tvar_db m else .Tvar_db (m + n)
  | .Tapp ts tn => .Tapp (deBruijn_inc_list skip n ts) tn
def deBruijn_inc_list (skip n : Nat) : List Ty → List Ty
  | [] => []
  | t :: ts => deBruijn_inc skip n t :: deBruijn_inc_list skip n ts
end

theorem deBruijn_inc_list_eq (skip n : Nat) (ts : List Ty) :
    deBruijn_inc_list skip n ts = MAP (deBruijn_inc skip n) ts := by
  induction ts with
  | nil => rfl
  | cons t ts ih => simp only [deBruijn_inc_list, MAP, List.map_cons, ih]

/- HOL4:
   (* skip the lowest given indices and replace the next (LENGTH ts) with the given types and reduce all the higher ones *)
   Definition deBruijn_subst_def:
   ((deBruijn_subst:num ->(t)list -> t -> t) skip ts (Tvar tv)=  (Tvar tv))
   /\
   ((deBruijn_subst:num ->(t)list -> t -> t) skip ts (Tvar_db n)=
      (if ~ (n < skip) /\ (n < (LENGTH ts + skip)) then
       EL (n - skip) ts
     else if ~ (n < skip) then
       Tvar_db (n - LENGTH ts)
     else
       Tvar_db n))
   /\
   ((deBruijn_subst:num ->(t)list -> t -> t) skip ts (Tapp ts' tn)=
      (Tapp (MAP (deBruijn_subst skip ts) ts') tn))
   End -/
mutual
def deBruijn_subst (skip : Nat) (ts : List Ty) : Ty → Ty
  | .Tvar tv => .Tvar tv
  | .Tvar_db n =>
    if ¬ (n < skip) ∧ (n < (LENGTH ts + skip)) then EL (n - skip) ts
    else if ¬ (n < skip) then .Tvar_db (n - LENGTH ts)
    else .Tvar_db n
  | .Tapp ts' tn => .Tapp (deBruijn_subst_list skip ts ts') tn
def deBruijn_subst_list (skip : Nat) (ts : List Ty) : List Ty → List Ty
  | [] => []
  | t :: ts' => deBruijn_subst skip ts t :: deBruijn_subst_list skip ts ts'
end

theorem deBruijn_subst_list_eq (skip : Nat) (ts ts' : List Ty) :
    deBruijn_subst_list skip ts ts' = MAP (deBruijn_subst skip ts) ts' := by
  induction ts' with
  | nil => rfl
  | cons t ts' ih => simp only [deBruijn_subst_list, MAP, List.map_cons, ih]

/- HOL4:
   (* Type environments *)
   Datatype:
    tenv_val_exp =
       Empty
     (* Binds several de Bruijn type variables *)
     | Bind_tvar num tenv_val_exp
     (* The number is how many de Bruijn type variables the typescheme binds *)
     | Bind_name varN num t tenv_val_exp
   End -/
inductive tenv_val_exp : Type where
  | Empty : tenv_val_exp
  | Bind_tvar (n : Nat) (tenvE : tenv_val_exp) : tenv_val_exp
  | Bind_name (n : varN) (tvs : Nat) (t : Ty) (tenvE : tenv_val_exp) : tenv_val_exp

instance : Inhabited tenv_val_exp := ⟨.Empty⟩

/- HOL4:
   Definition bind_tvar_def:
    ((bind_tvar:num -> tenv_val_exp -> tenv_val_exp) tvs tenvE=  (if tvs =( 0 : num) then tenvE else Bind_tvar tvs tenvE))
   End -/
def bind_tvar (tvs : Nat) (tenvE : tenv_val_exp) : tenv_val_exp :=
  if tvs = 0 then tenvE else .Bind_tvar tvs tenvE

/- HOL4:
   Definition opt_bind_name_def:
    ((opt_bind_name:(mlstring)option -> num -> t -> tenv_val_exp -> tenv_val_exp) n tvs t tenvE=
      ((case n of
         NONE => tenvE
       | SOME n' => Bind_name n' tvs t tenvE
     )))
   End -/
def opt_bind_name (n : Option mlstring) (tvs : Nat) (t : Ty) (tenvE : tenv_val_exp) :
    tenv_val_exp :=
  match n with
  | none => tenvE
  | some n' => .Bind_name n' tvs t tenvE

/- HOL4:
   Definition tveLookup_def:
   ((tveLookup:mlstring -> num -> tenv_val_exp ->(num#t)option) n inc Empty=  NONE)
   /\
   ((tveLookup:mlstring -> num -> tenv_val_exp ->(num#t)option) n inc (Bind_tvar tvs tenvE)=  (tveLookup n (inc + tvs) tenvE))
   /\
   ((tveLookup:mlstring -> num -> tenv_val_exp ->(num#t)option) n inc (Bind_name n' tvs t tenvE)=
      (if n' = n then
       SOME (tvs, deBruijn_inc tvs inc t)
     else
       tveLookup n inc tenvE))
   End -/
def tveLookup (n : mlstring) : Nat → tenv_val_exp → Option (Nat × Ty)
  | _, .Empty => none
  | inc, .Bind_tvar tvs tenvE => tveLookup n (inc + tvs) tenvE
  | inc, .Bind_name n' tvs t tenvE =>
    if n' = n then some (tvs, deBruijn_inc tvs inc t) else tveLookup n inc tenvE

/- HOL4:
   Type tenv_abbrev = ``: (modN, typeN, ( tvarN list # t)) namespace``
   Type tenv_ctor = ``: (modN, conN, ( tvarN list # t list # type_ident)) namespace``
   Type tenv_val = ``: (modN, varN, (num # t)) namespace`` -/
abbrev tenv_abbrev : Type := Namespace modN typeN (List tvarN × Ty)
abbrev tenv_ctor : Type := Namespace modN conN (List tvarN × List Ty × type_ident)
abbrev tenv_val : Type := Namespace modN varN (Nat × Ty)

/- HOL4:
   Datatype:
    type_env =
     <| v : tenv_val
      ; c : tenv_ctor
      ; t : tenv_abbrev
      |>
   End -/
structure type_env : Type where
  v : tenv_val
  c : tenv_ctor
  t : tenv_abbrev

/- HOL4:
   Definition extend_dec_tenv_def:
    ((extend_dec_tenv:type_env -> type_env -> type_env) tenv' tenv=
      (<| v := (nsAppend tenv'.v tenv.v);
        c := (nsAppend tenv'.c tenv.c);
        t := (nsAppend tenv'.t tenv.t) |>))
   End -/
def extend_dec_tenv (tenv' tenv : type_env) : type_env :=
  ⟨nsAppend tenv'.v tenv.v, nsAppend tenv'.c tenv.c, nsAppend tenv'.t tenv.t⟩

/- HOL4:
   Definition lookup_varE_def:
    ((lookup_varE:((mlstring),(mlstring))id -> tenv_val_exp ->(num#t)option) id tenvE=
      ((case id of
       Short x => tveLookup x(( 0 : num)) tenvE
     | _ => NONE
     )))
   End -/
def lookup_varE (i : Ident mlstring mlstring) (tenvE : tenv_val_exp) : Option (Nat × Ty) :=
  match i with
  | .Short x => tveLookup x 0 tenvE
  | _ => none

/- HOL4:
   Definition lookup_var_def:
    ((lookup_var:((modN),(varN))id -> tenv_val_exp -> type_env ->(num#t)option) id tenvE tenv=
      ((case lookup_varE id tenvE of
       SOME x => SOME x
     | NONE => nsLookup tenv.v id
     )))
   End -/
def lookup_var (i : Ident modN varN) (tenvE : tenv_val_exp) (tenv : type_env) :
    Option (Nat × Ty) :=
  match lookup_varE i tenvE with
  | some x => some x
  | none => nsLookup tenv.v i

/- HOL4:
   Definition num_tvs_def:
   ((num_tvs:tenv_val_exp -> num) Empty= (( 0 : num)))
   /\
   ((num_tvs:tenv_val_exp -> num) (Bind_tvar tvs tenvE)=  (tvs + num_tvs tenvE))
   /\
   ((num_tvs:tenv_val_exp -> num) (Bind_name n tvs t tenvE)=  (num_tvs tenvE))
   End -/
def num_tvs : tenv_val_exp → Nat
  | .Empty => 0
  | .Bind_tvar tvs tenvE => tvs + num_tvs tenvE
  | .Bind_name _ _ _ tenvE => num_tvs tenvE

/- HOL4:
   Definition bind_var_list_def:
   ((bind_var_list:num ->(mlstring#t)list -> tenv_val_exp -> tenv_val_exp) tvs [] tenvE=  tenvE)
   /\
   ((bind_var_list:num ->(mlstring#t)list -> tenv_val_exp -> tenv_val_exp) tvs ((n,t)::binds) tenvE=
    (Bind_name n tvs t (bind_var_list tvs binds tenvE)))
   End -/
def bind_var_list (tvs : Nat) : List (mlstring × Ty) → tenv_val_exp → tenv_val_exp
  | [], tenvE => tenvE
  | (n, t) :: binds, tenvE => .Bind_name n tvs t (bind_var_list tvs binds tenvE)

/- HOL4:
   Definition t_of_def[simp]:
     t_of BoolT       = Tbool   ∧
     t_of IntT        = Tint    ∧
     t_of CharT       = Tchar   ∧
     t_of StrT        = Tstring ∧
     t_of (WordT W8)  = Tword8  ∧
     t_of (WordT W64) = Tword64 ∧
     t_of Float64T    = Tdouble
   End -/
def t_of : prim_type → Ty
  | .BoolT => Tbool
  | .IntT => Tint
  | .CharT => Tchar
  | .StrT => Tstring
  | .WordT .W8 => Tword8
  | .WordT .W64 => Tword64
  | .Float64T => Tdouble

/- HOL4:
   Definition supported_test_def[simp]:
     supported_test Equal       ty = T ∧
     supported_test (Compare _) ty = MEM ty [IntT; CharT; WordT W8; Float64T] ∧
     supported_test _           ty = F
   End -/
def supported_test : test → prim_type → Prop
  | .Equal, _ => True
  | .Compare _, ty => MEM ty [.IntT, .CharT, .WordT .W8, .Float64T]
  | _, _ => False

/- HOL4:
   Definition supported_arith_def[simp]:
     (supported_arith a IntT =
        if MEM a [Add; Sub; Mul; Div; Mod] then SOME (2:num) else NONE) ∧
     (supported_arith a Float64T =
        if MEM a [Abs; Neg; Sqrt] then SOME 1 else
        if MEM a [Add; Sub; Mul; Div] then SOME 2 else
        if MEM a [FMA] then SOME 3 else NONE) ∧
     (supported_arith a (WordT _) =
        if MEM a [Add; Sub; And; Or; Xor] then SOME 2 else NONE) ∧
     (supported_arith a BoolT =
        if MEM a [Not] then SOME 1 else NONE) ∧
     (supported_arith a (ty:prim_type) = NONE)
   End -/
def supported_arith : arith → prim_type → Option Nat
  | a, .IntT => if MEM a [.Add, .Sub, .Mul, .Div, .Mod] then some 2 else none
  | a, .Float64T =>
    if MEM a [.Abs, .Neg, .Sqrt] then some 1
    else if MEM a [.Add, .Sub, .Mul, .Div] then some 2
    else if MEM a [.FMA] then some 3 else none
  | a, .WordT _ => if MEM a [.Add, .Sub, .And, .Or, .Xor] then some 2 else none
  | a, .BoolT => if MEM a [.Not] then some 1 else none
  | _, _ => none

/- HOL4:
   Definition supported_conversion_def[simp]:
     (* Word to Int conversions *)
     (supported_conversion (WordT W8) IntT = T) ∧
     (supported_conversion (WordT W64) IntT = T) ∧
     (* Int to Word conversions *)
     (supported_conversion IntT (WordT W8) = T) ∧
     (supported_conversion IntT (WordT W64) = T) ∧
     (* Char/Int conversions *)
     (supported_conversion CharT IntT = T) ∧
     (supported_conversion IntT CharT = T) ∧
     (* Char/Word8 conversions *)
     (supported_conversion CharT (WordT W8) = T) ∧
     (supported_conversion (WordT W8) CharT = T) ∧
     (* Float64/Word64 conversions *)
     (supported_conversion Float64T (WordT W64) = T) ∧
     (supported_conversion (WordT W64) Float64T = T) ∧
     (supported_conversion (from_ty:prim_type) (to_ty:prim_type) = F)
   End -/
def supported_conversion : prim_type → prim_type → Prop
  | .WordT .W8, .IntT => True
  | .WordT .W64, .IntT => True
  | .IntT, .WordT .W8 => True
  | .IntT, .WordT .W64 => True
  | .CharT, .IntT => True
  | .IntT, .CharT => True
  | .CharT, .WordT .W8 => True
  | .WordT .W8, .CharT => True
  | .Float64T, .WordT .W64 => True
  | .WordT .W64, .Float64T => True
  | _, _ => False

/- HOL4:
   (* Check that the operator can have type (t1 -> ... -> tn -> t) *)
   Definition type_op_def:
    (type_op:op -> t list -> t -> bool) op ts t=
      case (op,ts) of
         (Opapp, [t1; t2]) => t1 = Tfn t2 t
       | (Shift W8 _ _, [t1]) => (t1 = Tword8) /\ (t = Tword8)
       | (Shift W64 _ _, [t1]) => (t1 = Tword64) /\ (t = Tword64)
       | (Equality, [t1; t2]) => (t1 = t2) /\ (t = Tbool)
       | (Arith a ty, ts) => EVERY (λarg. arg = t_of ty) ts /\ (t = t_of ty) /\
                             supported_arith a ty = SOME (LENGTH ts)
       | (FromTo ty1 ty2, [t1]) => (t1 = t_of ty1) /\ (t = t_of ty2) /\
                                   supported_conversion ty1 ty2
       | (Test test ty, [t1; t2]) => (t1 = t2) /\ (t = Tbool) /\ (t1 = t_of ty) /\
                                     supported_test test ty
       | (Opassign, [t1; t2]) => (t1 = Tref t2) /\ (t = Ttup [])
       | (Opref, [t1]) => t = Tref t1
       | (Opderef, [t1]) => t1 = Tref t
       | (Aw8alloc, [t1; t2]) => (t1 = Tint) /\ (t2 = Tword8) /\ (t = Tword8array)
       | (Aw8sub, [t1; t2]) => (t1 = Tword8array) /\ (t2 = Tint) /\ (t = Tword8)
       | (Aw8length, [t1]) => (t1 = Tword8array) /\ (t = Tint)
       | (Aw8update, [t1; t2; t3]) => (t1 = Tword8array) /\ (t2 = Tint) /\ (t3 = Tword8) /\ (t = Ttup [])
       | (CopyStrStr, [t1; t2; t3]) => (t1 = Tstring) /\ (t2 = Tint) /\ (t3 = Tint) /\ (t = Tstring)
       | (CopyStrAw8, [t1; t2; t3; t4; t5]) =>
         (t1 = Tstring) /\ (t2 = Tint) /\ (t3 = Tint) /\ (t4 = Tword8array) /\ (t5 = Tint) /\ (t = Ttup [])
       | (CopyAw8Str, [t1; t2; t3]) => (t1 = Tword8array) /\ (t2 = Tint) /\ (t3 = Tint) /\ (t = Tstring)
       | (CopyAw8Aw8, [t1; t2; t3; t4; t5]) =>
         (t1 = Tword8array) /\ (t2 = Tint) /\ (t3 = Tint) /\ (t4 = Tword8array) /\ (t5 = Tint) /\ (t = Ttup [])
       | (Implode, [t1]) => (t1 = Tlist Tchar) /\ (t = Tstring)
       | (Explode, [t1]) => (t1 = Tstring) /\ (t = Tlist Tchar)
       | (Strsub, [t1; t2]) => (t1 = Tstring) /\ (t2 = Tint) /\ (t = Tchar)
       | (Strlen, [t1]) => (t1 = Tstring) /\ (t = Tint)
       | (Strcat, [t1]) => (t1 = Tlist Tstring) /\ (t = Tstring)
       | (VfromList, [Tapp [t1] ctor]) => (ctor = Tlist_num) /\ (t = Tvector t1)
       | (Vsub, [t1; t2]) => (t2 = Tint) /\ (Tvector t = t1)
       | (Vlength, [Tapp [t1] ctor]) => (ctor = Tvector_num) /\ (t = Tint)
       | (Aalloc, [t1; t2]) => (t1 = Tint) /\ (t = Tarray t2)
       | (AallocEmpty, [t1]) => (t1 = Ttup []) /\ (? t2. t = Tarray t2)
       | (Asub, [t1; t2]) => (t2 = Tint) /\ (Tarray t = t1)
       | (Alength, [Tapp [t1] ctor]) => (ctor = Tarray_num) /\ (t = Tint)
       | (Aupdate, [t1; t2; t3]) => (t1 = Tarray t3) /\ (t2 = Tint) /\ (t = Ttup [])
       | (ConfigGC, [t1;t2]) => (t1 = Tint) /\ (t2 = Tint) /\ (t = Ttup [])
       | (FFI n, [t1;t2]) => (t1 = Tstring) /\ (t2 = Tword8array) /\ (t = Ttup [])
       | (ListAppend, [Tapp [t1] ctor; t2]) => (ctor = Tlist_num) /\ (t2 = Tapp [t1] ctor) /\ (t = t2)
       | _ => F
   End -/
def type_op (o : op) (ts : List Ty) (t : Ty) : Prop :=
  match o, ts with
  | .Opapp, [t1, t2] => t1 = Tfn t2 t
  | .Shift .W8 _ _, [t1] => (t1 = Tword8) ∧ (t = Tword8)
  | .Shift .W64 _ _, [t1] => (t1 = Tword64) ∧ (t = Tword64)
  | .Equality, [t1, t2] => (t1 = t2) ∧ (t = Tbool)
  | .Arith a ty, ts =>
    EVERY (fun arg => arg = t_of ty) ts ∧ (t = t_of ty) ∧ supported_arith a ty = some (LENGTH ts)
  | .FromTo ty1 ty2, [t1] => (t1 = t_of ty1) ∧ (t = t_of ty2) ∧ supported_conversion ty1 ty2
  | .Test tst ty, [t1, t2] =>
    (t1 = t2) ∧ (t = Tbool) ∧ (t1 = t_of ty) ∧ supported_test tst ty
  | .Opassign, [t1, t2] => (t1 = Tref t2) ∧ (t = Ttup [])
  | .Opref, [t1] => t = Tref t1
  | .Opderef, [t1] => t1 = Tref t
  | .Aw8alloc, [t1, t2] => (t1 = Tint) ∧ (t2 = Tword8) ∧ (t = Tword8array)
  | .Aw8sub, [t1, t2] => (t1 = Tword8array) ∧ (t2 = Tint) ∧ (t = Tword8)
  | .Aw8length, [t1] => (t1 = Tword8array) ∧ (t = Tint)
  | .Aw8update, [t1, t2, t3] =>
    (t1 = Tword8array) ∧ (t2 = Tint) ∧ (t3 = Tword8) ∧ (t = Ttup [])
  | .CopyStrStr, [t1, t2, t3] => (t1 = Tstring) ∧ (t2 = Tint) ∧ (t3 = Tint) ∧ (t = Tstring)
  | .CopyStrAw8, [t1, t2, t3, t4, t5] =>
    (t1 = Tstring) ∧ (t2 = Tint) ∧ (t3 = Tint) ∧ (t4 = Tword8array) ∧ (t5 = Tint) ∧
      (t = Ttup [])
  | .CopyAw8Str, [t1, t2, t3] => (t1 = Tword8array) ∧ (t2 = Tint) ∧ (t3 = Tint) ∧ (t = Tstring)
  | .CopyAw8Aw8, [t1, t2, t3, t4, t5] =>
    (t1 = Tword8array) ∧ (t2 = Tint) ∧ (t3 = Tint) ∧ (t4 = Tword8array) ∧ (t5 = Tint) ∧
      (t = Ttup [])
  | .Implode, [t1] => (t1 = Tlist Tchar) ∧ (t = Tstring)
  | .Explode, [t1] => (t1 = Tstring) ∧ (t = Tlist Tchar)
  | .Strsub, [t1, t2] => (t1 = Tstring) ∧ (t2 = Tint) ∧ (t = Tchar)
  | .Strlen, [t1] => (t1 = Tstring) ∧ (t = Tint)
  | .Strcat, [t1] => (t1 = Tlist Tstring) ∧ (t = Tstring)
  | .VfromList, [.Tapp [t1] ctor] => (ctor = Tlist_num) ∧ (t = Tvector t1)
  | .Vsub, [t1, t2] => (t2 = Tint) ∧ (Tvector t = t1)
  | .Vlength, [.Tapp [_] ctor] => (ctor = Tvector_num) ∧ (t = Tint)
  | .Aalloc, [t1, t2] => (t1 = Tint) ∧ (t = Tarray t2)
  | .AallocEmpty, [t1] => (t1 = Ttup []) ∧ (∃ t2, t = Tarray t2)
  | .Asub, [t1, t2] => (t2 = Tint) ∧ (Tarray t = t1)
  | .Alength, [.Tapp [_] ctor] => (ctor = Tarray_num) ∧ (t = Tint)
  | .Aupdate, [t1, t2, t3] => (t1 = Tarray t3) ∧ (t2 = Tint) ∧ (t = Ttup [])
  | .ConfigGC, [t1, t2] => (t1 = Tint) ∧ (t2 = Tint) ∧ (t = Ttup [])
  | .FFI _, [t1, t2] => (t1 = Tstring) ∧ (t2 = Tword8array) ∧ (t = Ttup [])
  | .ListAppend, [.Tapp [t1] ctor, t2] => (ctor = Tlist_num) ∧ (t2 = .Tapp [t1] ctor) ∧ (t = t2)
  | _, _ => False

/- HOL4:
   Definition check_type_names_def:
   ((check_type_names:((mlstring),(mlstring),((mlstring)list#t))namespace -> ast_t -> bool) tenvT (Atvar tv)=
      T)
   /\
   ((check_type_names:((mlstring),(mlstring),((mlstring)list#t))namespace -> ast_t -> bool) tenvT (Attup ts)=
      (EVERY (check_type_names tenvT) ts))
   /\
   ((check_type_names:((mlstring),(mlstring),((mlstring)list#t))namespace -> ast_t -> bool) tenvT (Atfun t1 t2)=
      (check_type_names tenvT t1 /\ check_type_names tenvT t2))
   /\
   ((check_type_names:((mlstring),(mlstring),((mlstring)list#t))namespace -> ast_t -> bool) tenvT (Atapp ts tn)=
      ((case nsLookup tenvT tn of
       SOME (tvs, _) => LENGTH tvs = LENGTH ts
     | NONE => F
     ) /\
     EVERY (check_type_names tenvT) ts))
   End -/
mutual
def check_type_names (tenvT : Namespace mlstring mlstring (List mlstring × Ty)) : ast_t → Prop
  | .Atvar _ => True
  | .Attup ts => check_type_names_list tenvT ts
  | .Atfun t1 t2 => check_type_names tenvT t1 ∧ check_type_names tenvT t2
  | .Atapp ts tn =>
    (match nsLookup tenvT tn with
     | some (tvs, _) => LENGTH tvs = LENGTH ts
     | none => False) ∧
    check_type_names_list tenvT ts
def check_type_names_list (tenvT : Namespace mlstring mlstring (List mlstring × Ty)) :
    List ast_t → Prop
  | [] => True
  | t :: ts => check_type_names tenvT t ∧ check_type_names_list tenvT ts
end

theorem check_type_names_list_eq (tenvT : Namespace mlstring mlstring (List mlstring × Ty))
    (ts : List ast_t) :
    check_type_names_list tenvT ts = EVERY (check_type_names tenvT) ts := by
  induction ts with
  | nil => rfl
  | cons t ts ih => simp only [check_type_names_list, EVERY, ih]

/- HOL4:
   (* Substitution of type names for the type they abbreviate *)
   Definition type_name_subst_def:
   ((type_name_subst:((mlstring),(mlstring),((mlstring)list#t))namespace -> ast_t -> t) tenvT (Atvar tv)=  (Tvar tv))
   /\
   ((type_name_subst:((mlstring),(mlstring),((mlstring)list#t))namespace -> ast_t -> t) tenvT (Attup ts)=
      (Ttup (MAP (type_name_subst tenvT) ts)))
   /\
   ((type_name_subst:((mlstring),(mlstring),((mlstring)list#t))namespace -> ast_t -> t) tenvT (Atfun t1 t2)=
      (Tfn (type_name_subst tenvT t1) (type_name_subst tenvT t2)))
   /\
   ((type_name_subst:((mlstring),(mlstring),((mlstring)list#t))namespace -> ast_t -> t) tenvT (Atapp ts tc)=
      (let args = (MAP (type_name_subst tenvT) ts) in
     (case nsLookup tenvT tc of
       SOME (tvs, t) => type_subst (alist_to_fmap (ZIP (tvs, args))) t
     | NONE => Ttup args (* can't happen, for a type that passes the check *)
     )))
   End -/
mutual
def type_name_subst (tenvT : Namespace mlstring mlstring (List mlstring × Ty)) : ast_t → Ty
  | .Atvar tv => .Tvar tv
  | .Attup ts => Ttup (type_name_subst_list tenvT ts)
  | .Atfun t1 t2 => Tfn (type_name_subst tenvT t1) (type_name_subst tenvT t2)
  | .Atapp ts tc =>
    let args := type_name_subst_list tenvT ts
    match nsLookup tenvT tc with
    | some (tvs, t) => type_subst (alist_to_fmap (ZIP (tvs, args))) t
    | none => Ttup args
def type_name_subst_list (tenvT : Namespace mlstring mlstring (List mlstring × Ty)) :
    List ast_t → List Ty
  | [] => []
  | t :: ts => type_name_subst tenvT t :: type_name_subst_list tenvT ts
end

theorem type_name_subst_list_eq (tenvT : Namespace mlstring mlstring (List mlstring × Ty))
    (ts : List ast_t) :
    type_name_subst_list tenvT ts = MAP (type_name_subst tenvT) ts := by
  induction ts with
  | nil => rfl
  | cons t ts ih => simp only [type_name_subst_list, MAP, List.map_cons, ih]

/- HOL4:
   (* Check that a type definition defines no already defined types or duplicate
    * constructors, and that the free type variables of each constructor argument
    * type are included in the type's type parameters. Also check that all of the
    * types mentioned are in scope. *)
   Definition check_ctor_tenv_def:
    ((check_ctor_tenv:((modN),(typeN),((tvarN)list#t))namespace ->((tvarN)list#mlstring#(conN#(ast_t)list)list)list -> bool) tenvT []=  T)
   /\ ((check_ctor_tenv:((modN),(typeN),((tvarN)list#t))namespace ->((tvarN)list#mlstring#(conN#(ast_t)list)list)list -> bool) tenvT ((tvs,tn,ctors)::tds)=
      (check_dup_ctors (tvs,tn,ctors) /\
     ALL_DISTINCT tvs /\
     EVERY
       (\ (cn,ts) .  EVERY (check_freevars_ast tvs) ts /\ EVERY (check_type_names tenvT) ts)
       ctors /\
     ~ (MEM tn (MAP (\p .
     (case (p ) of ( (_,tn,_) ) => tn )) tds)) /\
     check_ctor_tenv tenvT tds))
   End -/
def check_ctor_tenv (tenvT : Namespace modN typeN (List tvarN × Ty)) :
    List (List tvarN × mlstring × List (conN × List ast_t)) → Prop
  | [] => True
  | (tvs, tn, ctors) :: tds =>
    check_dup_ctors (tvs, tn, ctors) ∧
    ALL_DISTINCT tvs ∧
    EVERY (fun cnts => EVERY (check_freevars_ast tvs) cnts.2 ∧ EVERY (check_type_names tenvT) cnts.2)
      ctors ∧
    ¬ MEM tn (MAP (fun p => p.2.1) tds) ∧
    check_ctor_tenv tenvT tds

/- HOL4:
   Definition build_ctor_tenv_def:
    (build_ctor_tenv tenvT [] []=  (alist_to_ns []))
   /\ (build_ctor_tenv tenvT ((tvs,tn,ctors)::tds) (id::ids)=
      (nsAppend
       (build_ctor_tenv tenvT tds ids)
       (alist_to_ns
         (REVERSE
           (MAP
             (\ (cn,ts) .  (cn,(tvs,MAP (type_name_subst tenvT) ts, id)))
             ctors)))))
   /\ (build_ctor_tenv tenvT _ _=  (alist_to_ns []))
   End -/
def build_ctor_tenv (tenvT : Namespace modN typeN (List tvarN × Ty)) :
    List (List tvarN × mlstring × List (conN × List ast_t)) → List type_ident → tenv_ctor
  | [], [] => alist_to_ns []
  | (tvs, _, ctors) :: tds, i :: ids =>
    nsAppend (build_ctor_tenv tenvT tds ids)
      (alist_to_ns
        (REVERSE (MAP (fun cnts => (cnts.1, (tvs, MAP (type_name_subst tenvT) cnts.2, i))) ctors)))
  | _, _ => alist_to_ns []

/- HOL4:
   (* For the value restriction on let-based polymorphism *)
   Definition is_value_def:
   ((is_value:exp -> bool) (Lit _)=  T)
   /\
   ((is_value:exp -> bool) (Con _ es)=  (EVERY is_value es))
   /\
   ((is_value:exp -> bool) (Var _)=  T)
   /\
   ((is_value:exp -> bool) (Fun _ _)=  T)
   /\
   ((is_value:exp -> bool) (Tannot e _)=  (is_value e))
   /\
   ((is_value:exp -> bool) (Lannot e _)=  (is_value e))
   /\
   ((is_value:exp -> bool) _=  F)
   End -/
mutual
def is_value : exp → Prop
  | .Lit _ => True
  | .Con _ es => is_value_list es
  | .Var _ => True
  | .Fun _ _ => True
  | .Tannot e _ => is_value e
  | .Lannot e _ => is_value e
  | _ => False
def is_value_list : List exp → Prop
  | [] => True
  | e :: es => is_value e ∧ is_value_list es
end

theorem is_value_list_eq (es : List exp) : is_value_list es = EVERY is_value es := by
  induction es with
  | nil => rfl
  | cons e es ih => simp only [is_value_list, EVERY, ih]

/- HOL4:
   Inductive type_p:
   (! tvs tenv t.
   (check_freevars tvs [] t)
   ==>
   type_p tvs tenv Pany t [])

   /\ (! tvs tenv n t.
   (check_freevars tvs [] t)
   ==>
   type_p tvs tenv (Pvar n) t [(n,t)])

   /\ (! tvs tenv n.
   T
   ==>
   type_p tvs tenv (Plit (IntLit n)) Tint [])

   /\ (! tvs tenv c.
   T
   ==>
   type_p tvs tenv (Plit (Char c)) Tchar [])

   /\ (! tvs tenv s.
   T
   ==>
   type_p tvs tenv (Plit (StrLit s)) Tstring [])

   /\ (! tvs tenv w.
   T
   ==>
   type_p tvs tenv (Plit (Word8 w)) Tword8 [])

   /\ (! tvs tenv w.
   T
   ==>
   type_p tvs tenv (Plit (Word64 w)) Tword64 [])

   /\ (! tvs tenv cn ps ts tvs' tn ts' bindings.
   (EVERY (check_freevars tvs []) ts' /\
   (LENGTH ts' = LENGTH tvs') /\
   type_ps tvs tenv ps (MAP (type_subst (alist_to_fmap (ZIP (tvs', ts')))) ts) bindings /\
   (nsLookup tenv.c cn = SOME (tvs', ts, tn)))
   ==>
   type_p tvs tenv (Pcon (SOME cn) ps) (Tapp ts' tn) bindings)

   /\ (! tvs tenv ps ts bindings.
   (type_ps tvs tenv ps ts bindings)
   ==>
   type_p tvs tenv (Pcon NONE ps) (Ttup ts) bindings)

   /\ (! tvs tenv p t bindings.
   (type_p tvs tenv p t bindings)
   ==>
   type_p tvs tenv (Pref p) (Tref t) bindings)

   /\ (!tvs tenv pat v t bindings.
   (type_p tvs tenv pat t bindings)
   ==>
   type_p tvs tenv (Pas pat v) t (bindings ++ [(v,t)]))

   /\ (! tvs tenv p t bindings.
   (check_freevars_ast [] t /\
   check_type_names tenv.t t /\
   type_p tvs tenv p (type_name_subst tenv.t t) bindings)
   ==>
   type_p tvs tenv (Ptannot p t) (type_name_subst tenv.t t) bindings)

   /\ (! tvs tenv.
   T
   ==>
   type_ps tvs tenv [] [] [])

   /\ (! tvs tenv p ps t ts bindings bindings'.
   (type_p tvs tenv p t bindings /\
   type_ps tvs tenv ps ts bindings')
   ==>
   type_ps tvs tenv (p::ps) (t::ts) (bindings'++bindings))
   End
   (Lean: the conjunctions of the premises are separate constructor arguments (equivalent);
   `type_p` and `type_ps` are mutually inductive.  Rules are named after the syntax they type.) -/
mutual
inductive type_p : Nat → type_env → pat → Ty → List (varN × Ty) → Prop where
  | pany (tvs : Nat) (tenv : type_env) (t : Ty) :
    check_freevars tvs [] t →
    type_p tvs tenv .Pany t []
  | pvar (tvs : Nat) (tenv : type_env) (n : varN) (t : Ty) :
    check_freevars tvs [] t →
    type_p tvs tenv (.Pvar n) t [(n, t)]
  | plit_int (tvs : Nat) (tenv : type_env) (n : Int) :
    type_p tvs tenv (.Plit (.IntLit n)) Tint []
  | plit_char (tvs : Nat) (tenv : type_env) (c : char) :
    type_p tvs tenv (.Plit (.Char c)) Tchar []
  | plit_str (tvs : Nat) (tenv : type_env) (s : mlstring) :
    type_p tvs tenv (.Plit (.StrLit s)) Tstring []
  | plit_word8 (tvs : Nat) (tenv : type_env) (w : word8) :
    type_p tvs tenv (.Plit (.Word8 w)) Tword8 []
  | plit_word64 (tvs : Nat) (tenv : type_env) (w : word64) :
    type_p tvs tenv (.Plit (.Word64 w)) Tword64 []
  | pcon_some (tvs : Nat) (tenv : type_env) (cn : Ident modN conN) (ps : List pat)
      (ts : List Ty) (tvs' : List tvarN) (tn : type_ident) (ts' : List Ty)
      (bindings : List (varN × Ty)) :
    EVERY (check_freevars tvs []) ts' →
    LENGTH ts' = LENGTH tvs' →
    type_ps tvs tenv ps (MAP (type_subst (alist_to_fmap (ZIP (tvs', ts')))) ts) bindings →
    nsLookup tenv.c cn = some (tvs', ts, tn) →
    type_p tvs tenv (.Pcon (some cn) ps) (.Tapp ts' tn) bindings
  | pcon_none (tvs : Nat) (tenv : type_env) (ps : List pat) (ts : List Ty)
      (bindings : List (varN × Ty)) :
    type_ps tvs tenv ps ts bindings →
    type_p tvs tenv (.Pcon none ps) (Ttup ts) bindings
  | pref (tvs : Nat) (tenv : type_env) (p : pat) (t : Ty) (bindings : List (varN × Ty)) :
    type_p tvs tenv p t bindings →
    type_p tvs tenv (.Pref p) (Tref t) bindings
  | pas (tvs : Nat) (tenv : type_env) (pat : pat) (v : varN) (t : Ty)
      (bindings : List (varN × Ty)) :
    type_p tvs tenv pat t bindings →
    type_p tvs tenv (.Pas pat v) t (bindings ++ [(v, t)])
  | ptannot (tvs : Nat) (tenv : type_env) (p : pat) (t : ast_t) (bindings : List (varN × Ty)) :
    check_freevars_ast [] t →
    check_type_names tenv.t t →
    type_p tvs tenv p (type_name_subst tenv.t t) bindings →
    type_p tvs tenv (.Ptannot p t) (type_name_subst tenv.t t) bindings
inductive type_ps : Nat → type_env → List pat → List Ty → List (varN × Ty) → Prop where
  | nil (tvs : Nat) (tenv : type_env) :
    type_ps tvs tenv [] [] []
  | cons (tvs : Nat) (tenv : type_env) (p : pat) (ps : List pat) (t : Ty) (ts : List Ty)
      (bindings bindings' : List (varN × Ty)) :
    type_p tvs tenv p t bindings →
    type_ps tvs tenv ps ts bindings' →
    type_ps tvs tenv (p :: ps) (t :: ts) (bindings' ++ bindings)
end

/- HOL4:
   Inductive type_e:
   (! tenv tenvE n.
   T
   ==>
   type_e tenv tenvE (Lit (IntLit n)) Tint)
   /\ (! tenv tenvE c.  T  ==>  type_e tenv tenvE (Lit (Char c)) Tchar)
   /\ (! tenv tenvE s.  T  ==>  type_e tenv tenvE (Lit (StrLit s)) Tstring)
   /\ (! tenv tenvE w.  T  ==>  type_e tenv tenvE (Lit (Word8 w)) Tword8)
   /\ (! tenv tenvE w.  T  ==>  type_e tenv tenvE (Lit (Word64 w)) Tword64)
   /\ (! tenv tenvE w.  T  ==>  type_e tenv tenvE (Lit (Float64 w)) Tdouble)

   /\ (! tenv tenvE e t.
   (check_freevars (num_tvs tenvE) [] t /\
   type_e tenv tenvE e Texn)
   ==>
   type_e tenv tenvE (Raise e) t)

   /\ (! tenv tenvE e pes t.
   (type_e tenv tenvE e t /\ ~ (pes = []) /\
   (! ((p,e) :: LIST_TO_SET pes). ? bindings.
      ALL_DISTINCT (pat_bindings p []) /\
      type_p (num_tvs tenvE) tenv p Texn bindings /\
      type_e tenv (bind_var_list(( 0 : num)) bindings tenvE) e t))
   ==>
   type_e tenv tenvE (Handle e pes) t)

   /\ (! tenv tenvE cn es tvs tn ts' ts.
   (EVERY (check_freevars (num_tvs tenvE) []) ts' /\
   (LENGTH tvs = LENGTH ts') /\
   type_es tenv tenvE es (MAP (type_subst (alist_to_fmap (ZIP (tvs, ts')))) ts) /\
   (nsLookup tenv.c cn = SOME (tvs, ts, tn)))
   ==>
   type_e tenv tenvE (Con (SOME cn) es) (Tapp ts' tn))

   /\ (! tenv tenvE es ts.
   (type_es tenv tenvE es ts)
   ==>
   type_e tenv tenvE (Con NONE es) (Ttup ts))

   /\ (! tenv tenvE n t targs tvs.
   ((tvs = LENGTH targs) /\
   EVERY (check_freevars (num_tvs tenvE) []) targs /\
   (lookup_var n tenvE tenv = SOME (tvs,t)))
   ==>
   type_e tenv tenvE (Var n) (deBruijn_subst(( 0 : num)) targs t))

   /\ (! tenv tenvE n e t1 t2.
   (check_freevars (num_tvs tenvE) [] t1 /\
   type_e tenv (Bind_name n(( 0 : num)) t1 tenvE) e t2)
   ==>
   type_e tenv tenvE (Fun n e) (Tfn t1 t2))

   /\ (! tenv tenvE op es ts t.
   (type_es tenv tenvE es ts /\
   type_op op ts t /\
   check_freevars (num_tvs tenvE) [] t)
   ==>
   type_e tenv tenvE (App op es) t)

   /\ (! tenv tenvE l e1 e2.
   (type_e tenv tenvE e1 Tbool /\
   type_e tenv tenvE e2 Tbool)
   ==>
   type_e tenv tenvE (Log l e1 e2) Tbool)

   /\ (! tenv tenvE e1 e2 e3 t.
   (type_e tenv tenvE e1 Tbool /\
   type_e tenv tenvE e2 t /\
   type_e tenv tenvE e3 t)
   ==>
   type_e tenv tenvE (If e1 e2 e3) t)

   /\ (! tenv tenvE e pes t1 t2.
   (type_e tenv tenvE e t1 /\ ~ (pes = []) /\
   (! ((p,e) :: LIST_TO_SET pes) . ? bindings.
      ALL_DISTINCT (pat_bindings p []) /\
      type_p (num_tvs tenvE) tenv p t1 bindings /\
      type_e tenv (bind_var_list(( 0 : num)) bindings tenvE) e t2))
   ==>
   type_e tenv tenvE (Mat e pes) t2)

   /\ (! tenv tenvE n e1 e2 t1 t2.
   (type_e tenv tenvE e1 t1 /\
   type_e tenv (opt_bind_name n(( 0 : num)) t1 tenvE) e2 t2)
   ==>
   type_e tenv tenvE (Let n e1 e2) t2)

   (* ... commented-out letrec rule omitted ... *)

   /\ (! tenv tenvE funs e t bindings.
   (type_funs tenv (bind_var_list(( 0 : num)) bindings tenvE) funs bindings /\
   type_e tenv (bind_var_list(( 0 : num)) bindings tenvE) e t)
   ==>
   type_e tenv tenvE (Letrec funs e) t)

   /\ (! tenv tenvE e t.
   (check_freevars_ast [] t /\
   check_type_names tenv.t t /\
   type_e tenv tenvE e (type_name_subst tenv.t t))
   ==>
   type_e tenv tenvE (Tannot e t) (type_name_subst tenv.t t))

   /\ (! tenv tenvE e l t.
   (type_e tenv tenvE e t)
   ==>
   type_e tenv tenvE (Lannot e l) t)

   /\ (! tenv tenvE.
   T
   ==>
   type_es tenv tenvE [] [])

   /\ (! tenv tenvE e es t ts.
   (type_e tenv tenvE e t /\
   type_es tenv tenvE es ts)
   ==>
   type_es tenv tenvE (e::es) (t::ts))

   /\ (! tenv tenvE.
   T
   ==>
   type_funs tenv tenvE [] [])

   /\ (! tenv tenvE fn n e funs bindings t1 t2.
   (check_freevars (num_tvs tenvE) [] (Tfn t1 t2) /\
   type_e tenv (Bind_name n(( 0 : num)) t1 tenvE) e t2 /\
   type_funs tenv tenvE funs bindings /\
   (ALOOKUP bindings fn = NONE))
   ==>
   type_funs tenv tenvE ((fn, n, e)::funs) ((fn, Tfn t1 t2)::bindings))
   End
   (Lean: premises are separate constructor arguments.  The premises
   `!((p,e) :: LIST_TO_SET pes). ?bindings. A /\ B /\ C` of `Handle`/`Mat` are encoded with a
   Skolem function `bs : pat -> exp -> (varN # t) list` giving the bindings of each pattern/body
   pair (an existential under a universal cannot be nested inside an inductive occurrence in
   Lean); the resulting rule is equivalent in classical logic (choice).  `type_e`, `type_es`,
   `type_funs` are mutually inductive.) -/
mutual
inductive type_e : type_env → tenv_val_exp → exp → Ty → Prop where
  | lit_int (tenv : type_env) (tenvE : tenv_val_exp) (n : Int) :
    type_e tenv tenvE (.Lit (.IntLit n)) Tint
  | lit_char (tenv : type_env) (tenvE : tenv_val_exp) (c : char) :
    type_e tenv tenvE (.Lit (.Char c)) Tchar
  | lit_str (tenv : type_env) (tenvE : tenv_val_exp) (s : mlstring) :
    type_e tenv tenvE (.Lit (.StrLit s)) Tstring
  | lit_word8 (tenv : type_env) (tenvE : tenv_val_exp) (w : word8) :
    type_e tenv tenvE (.Lit (.Word8 w)) Tword8
  | lit_word64 (tenv : type_env) (tenvE : tenv_val_exp) (w : word64) :
    type_e tenv tenvE (.Lit (.Word64 w)) Tword64
  | lit_float64 (tenv : type_env) (tenvE : tenv_val_exp) (w : word64) :
    type_e tenv tenvE (.Lit (.Float64 w)) Tdouble
  | raise (tenv : type_env) (tenvE : tenv_val_exp) (e : exp) (t : Ty) :
    check_freevars (num_tvs tenvE) [] t →
    type_e tenv tenvE e Texn →
    type_e tenv tenvE (.Raise e) t
  | handle (tenv : type_env) (tenvE : tenv_val_exp) (e : exp) (pes : List (pat × exp)) (t : Ty)
      (bs : pat → exp → List (varN × Ty)) :
    type_e tenv tenvE e t →
    pes ≠ [] →
    (∀ p e', (p, e') ∈ LIST_TO_SET pes → ALL_DISTINCT (pat_bindings p [])) →
    (∀ p e', (p, e') ∈ LIST_TO_SET pes → type_p (num_tvs tenvE) tenv p Texn (bs p e')) →
    (∀ p e', (p, e') ∈ LIST_TO_SET pes →
      type_e tenv (bind_var_list 0 (bs p e') tenvE) e' t) →
    type_e tenv tenvE (.Handle e pes) t
  | con_some (tenv : type_env) (tenvE : tenv_val_exp) (cn : Ident modN conN) (es : List exp)
      (tvs : List tvarN) (tn : type_ident) (ts' ts : List Ty) :
    EVERY (check_freevars (num_tvs tenvE) []) ts' →
    LENGTH tvs = LENGTH ts' →
    type_es tenv tenvE es (MAP (type_subst (alist_to_fmap (ZIP (tvs, ts')))) ts) →
    nsLookup tenv.c cn = some (tvs, ts, tn) →
    type_e tenv tenvE (.Con (some cn) es) (.Tapp ts' tn)
  | con_none (tenv : type_env) (tenvE : tenv_val_exp) (es : List exp) (ts : List Ty) :
    type_es tenv tenvE es ts →
    type_e tenv tenvE (.Con none es) (Ttup ts)
  | var (tenv : type_env) (tenvE : tenv_val_exp) (n : Ident modN varN) (t : Ty)
      (targs : List Ty) (tvs : Nat) :
    tvs = LENGTH targs →
    EVERY (check_freevars (num_tvs tenvE) []) targs →
    lookup_var n tenvE tenv = some (tvs, t) →
    type_e tenv tenvE (.Var n) (deBruijn_subst 0 targs t)
  | fn (tenv : type_env) (tenvE : tenv_val_exp) (n : varN) (e : exp) (t1 t2 : Ty) :
    check_freevars (num_tvs tenvE) [] t1 →
    type_e tenv (.Bind_name n 0 t1 tenvE) e t2 →
    type_e tenv tenvE (.Fun n e) (Tfn t1 t2)
  | app (tenv : type_env) (tenvE : tenv_val_exp) (o : op) (es : List exp) (ts : List Ty)
      (t : Ty) :
    type_es tenv tenvE es ts →
    type_op o ts t →
    check_freevars (num_tvs tenvE) [] t →
    type_e tenv tenvE (.App o es) t
  | log (tenv : type_env) (tenvE : tenv_val_exp) (l : lop) (e1 e2 : exp) :
    type_e tenv tenvE e1 Tbool →
    type_e tenv tenvE e2 Tbool →
    type_e tenv tenvE (.Log l e1 e2) Tbool
  | if_ (tenv : type_env) (tenvE : tenv_val_exp) (e1 e2 e3 : exp) (t : Ty) :
    type_e tenv tenvE e1 Tbool →
    type_e tenv tenvE e2 t →
    type_e tenv tenvE e3 t →
    type_e tenv tenvE (.If e1 e2 e3) t
  | mat (tenv : type_env) (tenvE : tenv_val_exp) (e : exp) (pes : List (pat × exp))
      (t1 t2 : Ty) (bs : pat → exp → List (varN × Ty)) :
    type_e tenv tenvE e t1 →
    pes ≠ [] →
    (∀ p e', (p, e') ∈ LIST_TO_SET pes → ALL_DISTINCT (pat_bindings p [])) →
    (∀ p e', (p, e') ∈ LIST_TO_SET pes → type_p (num_tvs tenvE) tenv p t1 (bs p e')) →
    (∀ p e', (p, e') ∈ LIST_TO_SET pes →
      type_e tenv (bind_var_list 0 (bs p e') tenvE) e' t2) →
    type_e tenv tenvE (.Mat e pes) t2
  | let_ (tenv : type_env) (tenvE : tenv_val_exp) (n : Option varN) (e1 e2 : exp)
      (t1 t2 : Ty) :
    type_e tenv tenvE e1 t1 →
    type_e tenv (opt_bind_name n 0 t1 tenvE) e2 t2 →
    type_e tenv tenvE (.Let n e1 e2) t2
  | letrec (tenv : type_env) (tenvE : tenv_val_exp) (funs : List (varN × varN × exp)) (e : exp)
      (t : Ty) (bindings : List (varN × Ty)) :
    type_funs tenv (bind_var_list 0 bindings tenvE) funs bindings →
    type_e tenv (bind_var_list 0 bindings tenvE) e t →
    type_e tenv tenvE (.Letrec funs e) t
  | tannot (tenv : type_env) (tenvE : tenv_val_exp) (e : exp) (t : ast_t) :
    check_freevars_ast [] t →
    check_type_names tenv.t t →
    type_e tenv tenvE e (type_name_subst tenv.t t) →
    type_e tenv tenvE (.Tannot e t) (type_name_subst tenv.t t)
  | lannot (tenv : type_env) (tenvE : tenv_val_exp) (e : exp) (l : locs) (t : Ty) :
    type_e tenv tenvE e t →
    type_e tenv tenvE (.Lannot e l) t
inductive type_es : type_env → tenv_val_exp → List exp → List Ty → Prop where
  | nil (tenv : type_env) (tenvE : tenv_val_exp) :
    type_es tenv tenvE [] []
  | cons (tenv : type_env) (tenvE : tenv_val_exp) (e : exp) (es : List exp) (t : Ty)
      (ts : List Ty) :
    type_e tenv tenvE e t →
    type_es tenv tenvE es ts →
    type_es tenv tenvE (e :: es) (t :: ts)
inductive type_funs : type_env → tenv_val_exp → List (varN × varN × exp) →
    List (varN × Ty) → Prop where
  | nil (tenv : type_env) (tenvE : tenv_val_exp) :
    type_funs tenv tenvE [] []
  | cons (tenv : type_env) (tenvE : tenv_val_exp) (fn n : varN) (e : exp)
      (funs : List (varN × varN × exp)) (bindings : List (varN × Ty)) (t1 t2 : Ty) :
    check_freevars (num_tvs tenvE) [] (Tfn t1 t2) →
    type_e tenv (.Bind_name n 0 t1 tenvE) e t2 →
    type_funs tenv tenvE funs bindings →
    ALOOKUP bindings fn = none →
    type_funs tenv tenvE ((fn, n, e) :: funs) ((fn, Tfn t1 t2) :: bindings)
end

/- HOL4:
   Definition tenv_add_tvs_def:
    ((tenv_add_tvs:num ->(mlstring#t)list ->(mlstring#(num#t))list) tvs bindings=
      (MAP (\ (n,t) .  (n,(tvs,t))) bindings))
   End -/
def tenv_add_tvs (tvs : Nat) (bindings : List (mlstring × Ty)) : List (mlstring × (Nat × Ty)) :=
  MAP (fun nt => (nt.1, (tvs, nt.2))) bindings

/- HOL4:
   Definition type_pe_determ_def:
    ((type_pe_determ:type_env -> tenv_val_exp -> pat -> exp -> bool) tenv tenvE p e=
      (! t1 tenv1 t2 tenv2.
       (type_p(( 0 : num)) tenv p t1 tenv1 /\ type_e tenv tenvE e t1 /\
       type_p(( 0 : num)) tenv p t2 tenv2 /\ type_e tenv tenvE e t2)
       ==>
       (tenv1 = tenv2)))
   End -/
def type_pe_determ (tenv : type_env) (tenvE : tenv_val_exp) (p : pat) (e : exp) : Prop :=
  ∀ t1 tenv1 t2 tenv2,
    (type_p 0 tenv p t1 tenv1 ∧ type_e tenv tenvE e t1 ∧
      type_p 0 tenv p t2 tenv2 ∧ type_e tenv tenvE e t2) →
    tenv1 = tenv2

/- HOL4:
   Definition tscheme_inst_def:
    ((tscheme_inst:num#t -> num#t -> bool) (tvs_spec, t_spec) (tvs_impl, t_impl)=
      (? subst.
       (LENGTH subst = tvs_impl) /\
       check_freevars tvs_impl [] t_impl /\
       EVERY (check_freevars tvs_spec []) subst /\
       (deBruijn_subst(( 0 : num)) subst t_impl = t_spec)))
   End -/
def tscheme_inst (spec impl : Nat × Ty) : Prop :=
  ∃ subst : List Ty,
    (LENGTH subst = impl.1) ∧
    check_freevars impl.1 [] impl.2 ∧
    EVERY (check_freevars spec.1 []) subst ∧
    (deBruijn_subst 0 subst impl.2 = spec.2)

/- HOL4:
   Definition tenvLift_def:
    ((tenvLift:mlstring -> type_env -> type_env) mn tenv=
      (<| v := (nsLift mn tenv.v); c := (nsLift mn tenv.c); t := (nsLift mn tenv.t)  |>))
   End -/
def tenvLift (mn : mlstring) (tenv : type_env) : type_env :=
  ⟨nsLift mn tenv.v, nsLift mn tenv.c, nsLift mn tenv.t⟩

/- HOL4:
   Inductive type_d:
   (! extra_checks tvs tenv p e t bindings locs.
   (is_value e /\
   ALL_DISTINCT (pat_bindings p []) /\
   type_p tvs tenv p t bindings /\
   type_e tenv (bind_tvar tvs Empty) e t /\
   (extra_checks ==>
     (! tvs' bindings' t'.
       (type_p tvs' tenv p t' bindings' /\
       type_e tenv (bind_tvar tvs' Empty) e t') ==>
         EVERY2 tscheme_inst (MAP SND (tenv_add_tvs tvs' bindings')) (MAP SND (tenv_add_tvs tvs bindings)))))
   ==>
   type_d extra_checks tenv (Dlet locs p e)
     {}
     <| v := (alist_to_ns (tenv_add_tvs tvs bindings)); c := nsEmpty; t := nsEmpty |>)

   /\ (! extra_checks tenv p e t bindings locs.
   (
   (* The following line makes sure that when the value restriction prohibits
      generalisation, a type error is given rather than picking an arbitrary
      instantiation. However, we should only do the check when the extra_checks
      argument tells us to. *)(extra_checks ==> (~ (is_value e) /\ type_pe_determ tenv Empty p e)) /\
   ALL_DISTINCT (pat_bindings p []) /\
   type_p(( 0 : num)) tenv p t bindings /\
   type_e tenv Empty e t)
   ==>
   type_d extra_checks tenv (Dlet locs p e)
     {} <| v := (alist_to_ns (tenv_add_tvs(( 0 : num)) bindings)); c := nsEmpty; t := nsEmpty |>)

   /\ (! extra_checks tenv funs bindings tvs locs.
   (type_funs tenv (bind_var_list(( 0 : num)) bindings (bind_tvar tvs Empty)) funs bindings /\
   (extra_checks ==>
     (! tvs' bindings'.
       type_funs tenv (bind_var_list(( 0 : num)) bindings' (bind_tvar tvs' Empty)) funs bindings' ==>
         EVERY2 tscheme_inst (MAP SND (tenv_add_tvs tvs' bindings')) (MAP SND (tenv_add_tvs tvs bindings)))))
   ==>
   type_d extra_checks tenv (Dletrec locs funs)
     {} <| v := (alist_to_ns (tenv_add_tvs tvs bindings)); c := nsEmpty; t := nsEmpty |>)

   /\ (! extra_checks tenv tdefs type_identities tenvT locs.
   (ALL_DISTINCT type_identities /\
   DISJOINT (LIST_TO_SET type_identities)
            (LIST_TO_SET (Tlist_num :: (Tbool_num :: prim_type_nums))) /\
   check_ctor_tenv (nsAppend tenvT tenv.t) tdefs /\
   (LENGTH type_identities = LENGTH tdefs) /\
   (tenvT = alist_to_ns (MAP2
                         (\ (tvs,tn,ctors) i .
                           (tn, (tvs, Tapp (MAP Tvar tvs) i)))
                         tdefs type_identities)))
   ==>
   type_d extra_checks tenv (Dtype locs tdefs)
     (LIST_TO_SET type_identities)
     <| v := nsEmpty; c := (build_ctor_tenv (nsAppend tenvT tenv.t) tdefs type_identities); t := tenvT |>)

   /\ (! extra_checks tenv tvs tn t locs.
   (check_freevars_ast tvs t /\
   check_type_names tenv.t t /\
   ALL_DISTINCT tvs)
   ==>
   type_d extra_checks tenv (Dtabbrev locs tvs tn t)
     {}
     <| v := nsEmpty; c := nsEmpty; t := (nsSing tn (tvs,type_name_subst tenv.t t)) |>)

   /\ (! extra_checks tenv cn ts locs.
   (EVERY (check_freevars_ast []) ts /\
   EVERY (check_type_names tenv.t) ts)
   ==>
   type_d extra_checks tenv (Dexn locs cn ts)
     {}
     <| v := nsEmpty;
        c := (nsSing cn ([], MAP (type_name_subst tenv.t) ts, Texn_num));
        t := nsEmpty |>)

   /\ (! extra_checks tenv mn ds decls tenv'.
   (type_ds extra_checks tenv ds decls tenv')
   ==>
   type_d extra_checks tenv (Dmod mn ds) decls (tenvLift mn tenv'))

   /\ (! extra_checks tenv lds ds tenv1 tenv2 decls1 decls2.
   (type_ds extra_checks tenv lds decls1 tenv1 /\
   type_ds extra_checks (extend_dec_tenv tenv1 tenv) ds decls2 tenv2 /\
   DISJOINT decls1 decls2)
   ==>
   type_d extra_checks tenv (Dlocal lds ds) (decls1 UNION decls2) tenv2)

   /\ (! extra_checks tenv.
   T
   ==>
   type_ds extra_checks tenv []
     {}
     <| v := nsEmpty; c := nsEmpty; t := nsEmpty |>)

   /\ (! extra_checks tenv d ds tenv1 tenv2 decls1 decls2.
   (type_d extra_checks tenv d decls1 tenv1 /\
   type_ds extra_checks (extend_dec_tenv tenv1 tenv) ds decls2 tenv2 /\
   DISJOINT decls1 decls2)
   ==>
   type_ds extra_checks tenv (d::ds)
     (decls1 UNION decls2) (extend_dec_tenv tenv2 tenv1))
   End
   (Lean: premises are separate constructor arguments; `extra_checks` is a `Prop` index
   (HOL4 `bool`); `type_d`, `type_ds` are mutually inductive.) -/
mutual
inductive type_d : Prop → type_env → dec → Set type_ident → type_env → Prop where
  | dlet_value (extra_checks : Prop) (tvs : Nat) (tenv : type_env) (p : pat) (e : exp) (t : Ty)
      (bindings : List (varN × Ty)) (locs : locs) :
    is_value e →
    ALL_DISTINCT (pat_bindings p []) →
    type_p tvs tenv p t bindings →
    type_e tenv (bind_tvar tvs .Empty) e t →
    (extra_checks →
      ∀ tvs' bindings' t',
        type_p tvs' tenv p t' bindings' →
        type_e tenv (bind_tvar tvs' .Empty) e t' →
        LIST_REL tscheme_inst (MAP SND (tenv_add_tvs tvs' bindings'))
          (MAP SND (tenv_add_tvs tvs bindings))) →
    type_d extra_checks tenv (.Dlet locs p e) ∅
      ⟨alist_to_ns (tenv_add_tvs tvs bindings), nsEmpty, nsEmpty⟩
  | dlet_nonvalue (extra_checks : Prop) (tenv : type_env) (p : pat) (e : exp) (t : Ty)
      (bindings : List (varN × Ty)) (locs : locs) :
    (extra_checks → ¬ is_value e ∧ type_pe_determ tenv .Empty p e) →
    ALL_DISTINCT (pat_bindings p []) →
    type_p 0 tenv p t bindings →
    type_e tenv .Empty e t →
    type_d extra_checks tenv (.Dlet locs p e) ∅
      ⟨alist_to_ns (tenv_add_tvs 0 bindings), nsEmpty, nsEmpty⟩
  | dletrec (extra_checks : Prop) (tenv : type_env) (funs : List (varN × varN × exp))
      (bindings : List (varN × Ty)) (tvs : Nat) (locs : locs) :
    type_funs tenv (bind_var_list 0 bindings (bind_tvar tvs .Empty)) funs bindings →
    (extra_checks →
      ∀ tvs' bindings',
        type_funs tenv (bind_var_list 0 bindings' (bind_tvar tvs' .Empty)) funs bindings' →
        LIST_REL tscheme_inst (MAP SND (tenv_add_tvs tvs' bindings'))
          (MAP SND (tenv_add_tvs tvs bindings))) →
    type_d extra_checks tenv (.Dletrec locs funs) ∅
      ⟨alist_to_ns (tenv_add_tvs tvs bindings), nsEmpty, nsEmpty⟩
  | dtype (extra_checks : Prop) (tenv : type_env)
      (tdefs : List (List tvarN × mlstring × List (conN × List ast_t)))
      (type_identities : List type_ident) (tenvT : Namespace modN typeN (List tvarN × Ty))
      (locs : locs) :
    ALL_DISTINCT type_identities →
    DISJOINT (LIST_TO_SET type_identities)
      (LIST_TO_SET (Tlist_num :: (Tbool_num :: prim_type_nums))) →
    check_ctor_tenv (nsAppend tenvT tenv.t) tdefs →
    LENGTH type_identities = LENGTH tdefs →
    tenvT = alist_to_ns (MAP2 (fun tvs_tn_ctors i =>
        (tvs_tn_ctors.2.1, (tvs_tn_ctors.1, Ty.Tapp (MAP Ty.Tvar tvs_tn_ctors.1) i)))
      tdefs type_identities) →
    type_d extra_checks tenv (.Dtype locs tdefs) (LIST_TO_SET type_identities)
      ⟨nsEmpty, build_ctor_tenv (nsAppend tenvT tenv.t) tdefs type_identities, tenvT⟩
  | dtabbrev (extra_checks : Prop) (tenv : type_env) (tvs : List tvarN) (tn : typeN) (t : ast_t)
      (locs : locs) :
    check_freevars_ast tvs t →
    check_type_names tenv.t t →
    ALL_DISTINCT tvs →
    type_d extra_checks tenv (.Dtabbrev locs tvs tn t) ∅
      ⟨nsEmpty, nsEmpty, nsSing tn (tvs, type_name_subst tenv.t t)⟩
  | dexn (extra_checks : Prop) (tenv : type_env) (cn : conN) (ts : List ast_t) (locs : locs) :
    EVERY (check_freevars_ast []) ts →
    EVERY (check_type_names tenv.t) ts →
    type_d extra_checks tenv (.Dexn locs cn ts) ∅
      ⟨nsEmpty, nsSing cn ([], MAP (type_name_subst tenv.t) ts, Texn_num), nsEmpty⟩
  | dmod (extra_checks : Prop) (tenv : type_env) (mn : modN) (ds : List dec)
      (decls : Set type_ident) (tenv' : type_env) :
    type_ds extra_checks tenv ds decls tenv' →
    type_d extra_checks tenv (.Dmod mn ds) decls (tenvLift mn tenv')
  | dlocal (extra_checks : Prop) (tenv : type_env) (lds ds : List dec)
      (tenv1 tenv2 : type_env) (decls1 decls2 : Set type_ident) :
    type_ds extra_checks tenv lds decls1 tenv1 →
    type_ds extra_checks (extend_dec_tenv tenv1 tenv) ds decls2 tenv2 →
    DISJOINT decls1 decls2 →
    type_d extra_checks tenv (.Dlocal lds ds) (decls1 ∪ decls2) tenv2
inductive type_ds : Prop → type_env → List dec → Set type_ident → type_env → Prop where
  | nil (extra_checks : Prop) (tenv : type_env) :
    type_ds extra_checks tenv [] ∅ ⟨nsEmpty, nsEmpty, nsEmpty⟩
  | cons (extra_checks : Prop) (tenv : type_env) (d : dec) (ds : List dec)
      (tenv1 tenv2 : type_env) (decls1 decls2 : Set type_ident) :
    type_d extra_checks tenv d decls1 tenv1 →
    type_ds extra_checks (extend_dec_tenv tenv1 tenv) ds decls2 tenv2 →
    DISJOINT decls1 decls2 →
    type_ds extra_checks tenv (d :: ds) (decls1 ∪ decls2) (extend_dec_tenv tenv2 tenv1)
end

/- HOL4:
   Definition tscheme_inst2_def:
    ((tscheme_inst2:'a -> num#t -> num#t -> bool) _ ts1 ts2=  (tscheme_inst ts1 ts2))
   End -/
def tscheme_inst2 {α : Type u} (_ : α) (ts1 ts2 : Nat × Ty) : Prop := tscheme_inst ts1 ts2

/- HOL4:
   Definition weak_tenv_def:
    ((weak_tenv:type_env -> type_env -> bool) tenv_impl tenv_spec=
      (nsSub tscheme_inst2 tenv_spec.v tenv_impl.v /\
     nsSub (\i x y .  (case (i ,x ,y ) of ( _ , x , y ) => x = y )) tenv_spec.c tenv_impl.c))
   End -/
def weak_tenv (tenv_impl tenv_spec : type_env) : Prop :=
  nsSub tscheme_inst2 tenv_spec.v tenv_impl.v ∧
  nsSub (fun _ x y => x = y) tenv_spec.c tenv_impl.c

end
