import CmlTS.Prelude.Set
import CmlTS.Prelude.List
/-
  Translation of HOL4 theory `namespace` (namespaceScript.sml).

  `namespace` is a Lean keyword and `id` is a Lean core function, so the HOL4 types
  `('m,'n,'v) namespace` and `('m,'n) id` are called `Namespace m n v` and `ident m n` here.
-/
set_option autoImplicit false

namespace CmlTS
open Classical

/- HOL4:
Type alist = ``: ('k # 'v) list`` -/
abbrev alist (k v : Type) : Type := List (k × v)

/- HOL4:
Datatype:
  id = Short 'n | Long 'm id
End -/
inductive ident (m n : Type)
  | Short (x : n)
  | Long (mn : m) (i : ident m n)
  deriving DecidableEq

export ident (Short Long)

instance (m n : Type) [Inhabited n] : Inhabited (ident m n) := ⟨.Short default⟩

/- HOL4:
Definition mk_id_def:
  mk_id [] n = Short n ∧
  mk_id (mn::mns) n = Long mn (mk_id mns n)
End -/
def mk_id {m n : Type} : List m → n → ident m n
  | [], x => .Short x
  | mn :: mns, x => .Long mn (mk_id mns x)

/- HOL4:
Definition id_to_n_def:
 id_to_n (Short n) = n ∧
 id_to_n (Long _ id) = id_to_n id
End -/
def id_to_n {m n : Type} : ident m n → n
  | .Short x => x
  | .Long _ i => id_to_n i

/- HOL4:
Definition id_to_mods_def:
  id_to_mods (Short _) = [] ∧
  id_to_mods (Long mn id) = mn::id_to_mods id
End -/
def id_to_mods {m n : Type} : ident m n → List m
  | .Short _ => []
  | .Long mn i => mn :: id_to_mods i

/- HOL4:
Datatype:
  namespace =
    Bind (('n,'v) alist) (('m,namespace) alist)
End -/
inductive Namespace (m n v : Type)
  | Bind (vs : List (n × v)) (ms : List (m × Namespace m n v))

instance (m n v : Type) : Inhabited (Namespace m n v) := ⟨.Bind [] []⟩

/- HOL4:
Definition nsLookup_def:
  nsLookup ((Bind v m):('m,'n,'v)namespace) (Short n) =
    ALOOKUP v n ∧
  nsLookup (Bind v m) (Long mn id) =
    case ALOOKUP m mn of
    | NONE => NONE
    | SOME env => nsLookup env id
End -/
noncomputable def nsLookup {m n v : Type} : Namespace m n v → ident m n → Option v
  | .Bind vs _, .Short x => ALOOKUP vs x
  | .Bind _ ms, .Long mn i =>
    match ALOOKUP ms mn with
    | none => none
    | some env => nsLookup env i
termination_by structural _ i => i

/- HOL4:
Definition nsLookupMod_def:
  nsLookupMod e [] = SOME (e:('m,'n,'v)namespace) ∧
  nsLookupMod (Bind v m) (mn::path) =
  case ALOOKUP m mn of NONE => NONE | SOME env => nsLookupMod env path
End -/
noncomputable def nsLookupMod {m n v : Type} : Namespace m n v → List m → Option (Namespace m n v)
  | e, [] => some e
  | .Bind _ ms, mn :: path =>
    match ALOOKUP ms mn with
    | none => none
    | some env => nsLookupMod env path
termination_by structural _ path => path

/- HOL4:
Definition nsEmpty_def:
  nsEmpty = Bind [] []
End -/
def nsEmpty {m n v : Type} : Namespace m n v := .Bind [] []

/- HOL4:
Definition nsAppend_def:
  nsAppend (Bind v1 m1) (Bind v2 m2) = Bind (v1 ++ v2) (m1 ++ m2)
End -/
def nsAppend {m n v : Type} : Namespace m n v → Namespace m n v → Namespace m n v
  | .Bind v1 m1, .Bind v2 m2 => .Bind (v1 ++ v2) (m1 ++ m2)

/- HOL4:
Definition nsLift_def:
  nsLift mn env = Bind [] [(mn,env)]
End -/
def nsLift {m n v : Type} (mn : m) (env : Namespace m n v) : Namespace m n v :=
  .Bind [] [(mn, env)]

/- HOL4:
Definition alist_to_ns_def:
  alist_to_ns a = Bind a []
End -/
def alist_to_ns {m n v : Type} (a : List (n × v)) : Namespace m n v := .Bind a []

/- HOL4:
Definition nsBind_def:
  nsBind k x (Bind v m) = Bind ((k,x)::v) m
End -/
def nsBind {m n v : Type} (k : n) (x : v) : Namespace m n v → Namespace m n v
  | .Bind vs ms => .Bind ((k, x) :: vs) ms

/- HOL4:
Definition nsBindList_def:
  nsBindList l e = FOLDR (λ(x,v) e. nsBind x v e) e l
End -/
def nsBindList {m n v : Type} (l : List (n × v)) (e : Namespace m n v) : Namespace m n v :=
  List.foldr (fun (x, v) e => nsBind x v e) e l

/- HOL4:
Definition nsOptBind_def:
  nsOptBind n x env = case n of NONE => env | SOME n => nsBind n x env
End -/
def nsOptBind {m n v : Type} (k : Option n) (x : v) (env : Namespace m n v) : Namespace m n v :=
  match k with
  | none => env
  | some k => nsBind k x env

/- HOL4:
Definition nsSing_def:
  nsSing n x = Bind [(n,x)] []
End -/
def nsSing {m n v : Type} (k : n) (x : v) : Namespace m n v := .Bind [(k, x)] []

/- HOL4:
Definition nsSub_def:
  nsSub r env1 env2 ⇔
     (∀id v1.
        nsLookup env1 id = SOME v1 ⇒
        ∃v2. nsLookup env2 id = SOME v2 ∧ r id v1 v2) ∧
     ∀path. nsLookupMod env2 path = NONE ⇒ nsLookupMod env1 path = NONE
End -/
def nsSub {m n v1 v2 : Type} (r : ident m n → v1 → v2 → Prop)
    (env1 : Namespace m n v1) (env2 : Namespace m n v2) : Prop :=
  (∀ id v1, nsLookup env1 id = some v1 → ∃ v2, nsLookup env2 id = some v2 ∧ r id v1 v2) ∧
  ∀ path, nsLookupMod env2 path = none → nsLookupMod env1 path = none

/- HOL4:
Definition nsAll_def:
  nsAll f env ⇔ ∀id v. nsLookup env id = SOME v ⇒ f id v
End -/
def nsAll {m n v : Type} (f : ident m n → v → Prop) (env : Namespace m n v) : Prop :=
  ∀ id v, nsLookup env id = some v → f id v

/- HOL4:
Definition nsAll2_def:
  nsAll2 r env1 env2 ⇔
    nsSub r env1 env2 ∧ nsSub (λx y z. r x z y) env2 env1
End -/
def nsAll2 {m n v1 v2 : Type} (r : ident m n → v1 → v2 → Prop)
    (env1 : Namespace m n v1) (env2 : Namespace m n v2) : Prop :=
  nsSub r env1 env2 ∧ nsSub (fun x y z => r x z y) env2 env1

/- HOL4:
Definition nsDom_def:
  nsDom (env:('m,'n,'v)namespace) =
     {n | (v,n) | v ∈ 𝕌(:φ) ∧ n ∈ 𝕌(:(ν, ξ) id) ∧ nsLookup env n = SOME v}
End -/
def nsDom {m n v : Type} (env : Namespace m n v) : Set (ident m n) :=
  {i | ∃ x : v, x ∈ (UNIV : Set v) ∧ i ∈ (UNIV : Set (ident m n)) ∧ nsLookup env i = some x}

/- HOL4:
Definition nsMap_def:
  nsMap (f:'v -> 'w) ((Bind v m):('m,'n,'v)namespace) =
    Bind (MAP (λ(n,x). (n,f x)) v) (MAP (λ(mn,e). (mn,nsMap f e)) m)
End
   (`λ(mn,e). (mn,nsMap f e)` is written with projections, for the termination proof) -/
def nsMap {m n v w : Type} (f : v → w) : Namespace m n v → Namespace m n w
  | .Bind vs ms =>
    .Bind (vs.map fun (k, x) => (k, f x)) (ms.map fun p => (p.1, nsMap f p.2))
termination_by e => e
decreasing_by
  have := sizeOf_snd_lt_of_mem (by assumption)
  simp
  omega

end CmlTS
