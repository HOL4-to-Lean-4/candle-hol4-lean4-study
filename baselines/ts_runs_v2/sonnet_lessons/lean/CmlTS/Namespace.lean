import CmlTS.Misc

/-!
# namespace (HOL4 theory `namespace`)

Nested namespaces where names can be short (e.g. `foo`) or long (e.g. `ModuleA.InnerB.bar`).

Renamed types (HOL4 -> Lean): `id` -> `Ident` (to avoid `id`), `namespace` -> `Namespace`
(keyword).  The type parameters keep HOL4's (alphabetical) order:
`('m,'n) id` = `Ident M N`, `('m,'n,'v) namespace` = `Namespace M N V`.
-/

universe u v w

noncomputable section

open Classical

/- HOL4:
   Datatype:
     id = Short 'n | Long 'm id
   End -/
inductive Ident (M : Type u) (N : Type v) : Type (max u v) where
  | Short (n : N) : Ident M N
  | Long (m : M) (i : Ident M N) : Ident M N

instance {M : Type u} {N : Type v} [Inhabited N] : Inhabited (Ident M N) := ⟨.Short default⟩

/- HOL4:
   Definition mk_id_def:
     mk_id [] n = Short n ∧
     mk_id (mn::mns) n = Long mn (mk_id mns n)
   End -/
def mk_id {M : Type u} {N : Type v} : List M → N → Ident M N
  | [], n => .Short n
  | mn :: mns, n => .Long mn (mk_id mns n)

/- HOL4:
   Definition id_to_n_def:
    id_to_n (Short n) = n ∧
    id_to_n (Long _ id) = id_to_n id
   End -/
def id_to_n {M : Type u} {N : Type v} : Ident M N → N
  | .Short n => n
  | .Long _ i => id_to_n i

/- HOL4:
   Definition id_to_mods_def:
     id_to_mods (Short _) = [] ∧
     id_to_mods (Long mn id) = mn::id_to_mods id
   End -/
def id_to_mods {M : Type u} {N : Type v} : Ident M N → List M
  | .Short _ => []
  | .Long mn i => mn :: id_to_mods i

/- HOL4:
   Datatype:
     namespace =
       Bind (('n,'v) alist) (('m,namespace) alist)
   End -/
inductive Namespace (M : Type u) (N : Type v) (V : Type w) : Type (max u v w) where
  | Bind (v : List (N × V)) (m : List (M × Namespace M N V)) : Namespace M N V

instance {M : Type u} {N : Type v} {V : Type w} : Inhabited (Namespace M N V) := ⟨.Bind [] []⟩

/- HOL4:
   Definition nsLookup_def:
     nsLookup ((Bind v m):('m,'n,'v)namespace) (Short n) =
       ALOOKUP v n ∧
     nsLookup (Bind v m) (Long mn id) =
       case ALOOKUP m mn of
       | NONE => NONE
       | SOME env => nsLookup env id
   End -/
def nsLookup {M : Type u} {N : Type v} {V : Type w} :
    Namespace M N V → Ident M N → Option V
  | .Bind v _, .Short n => ALOOKUP v n
  | .Bind _ m, .Long mn i =>
    match ALOOKUP m mn with
    | none => none
    | some env => nsLookup env i

/- HOL4:
   Definition nsLookupMod_def:
     nsLookupMod e [] = SOME (e:('m,'n,'v)namespace) ∧
     nsLookupMod (Bind v m) (mn::path) =
     case ALOOKUP m mn of NONE => NONE | SOME env => nsLookupMod env path
   End -/
def nsLookupMod {M : Type u} {N : Type v} {V : Type w} :
    Namespace M N V → List M → Option (Namespace M N V)
  | e, [] => some e
  | .Bind _ m, mn :: path =>
    match ALOOKUP m mn with
    | none => none
    | some env => nsLookupMod env path

/- HOL4:
   Definition nsEmpty_def:
     nsEmpty = Bind [] []
   End -/
def nsEmpty {M : Type u} {N : Type v} {V : Type w} : Namespace M N V := .Bind [] []

/- HOL4:
   Definition nsAppend_def:
     nsAppend (Bind v1 m1) (Bind v2 m2) = Bind (v1 ++ v2) (m1 ++ m2)
   End -/
def nsAppend {M : Type u} {N : Type v} {V : Type w} :
    Namespace M N V → Namespace M N V → Namespace M N V
  | .Bind v1 m1, .Bind v2 m2 => .Bind (v1 ++ v2) (m1 ++ m2)

/- HOL4:
   Definition nsLift_def:
     nsLift mn env = Bind [] [(mn,env)]
   End -/
def nsLift {M : Type u} {N : Type v} {V : Type w} (mn : M) (env : Namespace M N V) :
    Namespace M N V := .Bind [] [(mn, env)]

/- HOL4:
   Definition alist_to_ns_def:
     alist_to_ns a = Bind a []
   End -/
def alist_to_ns {M : Type u} {N : Type v} {V : Type w} (a : List (N × V)) : Namespace M N V :=
  .Bind a []

/- HOL4:
   Definition nsBind_def:
     nsBind k x (Bind v m) = Bind ((k,x)::v) m
   End -/
def nsBind {M : Type u} {N : Type v} {V : Type w} (k : N) (x : V) :
    Namespace M N V → Namespace M N V
  | .Bind v m => .Bind ((k, x) :: v) m

/- HOL4:
   Definition nsBindList_def:
     nsBindList l e = FOLDR (λ(x,v) e. nsBind x v e) e l
   End -/
def nsBindList {M : Type u} {N : Type v} {V : Type w} (l : List (N × V))
    (e : Namespace M N V) : Namespace M N V :=
  FOLDR (fun p e => nsBind p.1 p.2 e) e l

/- HOL4:
   Definition nsOptBind_def:
     nsOptBind n x env = case n of NONE => env | SOME n => nsBind n x env
   End -/
def nsOptBind {M : Type u} {N : Type v} {V : Type w} (n : Option N) (x : V)
    (env : Namespace M N V) : Namespace M N V :=
  match n with
  | none => env
  | some n => nsBind n x env

/- HOL4:
   Definition nsSing_def:
     nsSing n x = Bind [(n,x)] []
   End -/
def nsSing {M : Type u} {N : Type v} {V : Type w} (n : N) (x : V) : Namespace M N V :=
  .Bind [(n, x)] []

/- HOL4:
   Definition nsSub_def:
     nsSub r env1 env2 ⇔
        (∀id v1.
           nsLookup env1 id = SOME v1 ⇒
           ∃v2. nsLookup env2 id = SOME v2 ∧ r id v1 v2) ∧
        ∀path. nsLookupMod env2 path = NONE ⇒ nsLookupMod env1 path = NONE
   End -/
def nsSub {M : Type u} {N : Type v} {V : Type w} {V' : Type _}
    (r : Ident M N → V → V' → Prop) (env1 : Namespace M N V) (env2 : Namespace M N V') :
    Prop :=
  (∀ i v1, nsLookup env1 i = some v1 → ∃ v2, nsLookup env2 i = some v2 ∧ r i v1 v2) ∧
  ∀ path, nsLookupMod env2 path = none → nsLookupMod env1 path = none

/- HOL4:
   Definition nsAll_def:
     nsAll f env ⇔ ∀id v. nsLookup env id = SOME v ⇒ f id v
   End -/
def nsAll {M : Type u} {N : Type v} {V : Type w} (f : Ident M N → V → Prop)
    (env : Namespace M N V) : Prop :=
  ∀ i v, nsLookup env i = some v → f i v

/- HOL4:
   Definition nsAll2_def:
     nsAll2 r env1 env2 ⇔
       nsSub r env1 env2 ∧ nsSub (λx y z. r x z y) env2 env1
   End -/
def nsAll2 {M : Type u} {N : Type v} {V : Type w} {V' : Type _}
    (r : Ident M N → V → V' → Prop) (env1 : Namespace M N V) (env2 : Namespace M N V') : Prop :=
  nsSub r env1 env2 ∧ nsSub (fun x y z => r x z y) env2 env1

/- HOL4:
   Definition nsDom_def:
     nsDom (env:('m,'n,'v)namespace) =
        {n | (v,n) | v ∈ 𝕌(:φ) ∧ n ∈ 𝕌(:(ν, ξ) id) ∧ nsLookup env n = SOME v}
   End
   (the set of identifiers bound in `env`) -/
def nsDom {M : Type u} {N : Type v} {V : Type w} (env : Namespace M N V) : Set (Ident M N) :=
  fun n => ∃ v, nsLookup env n = some v

/- HOL4:
   Definition nsMap_def:
     nsMap (f:'v -> 'w) ((Bind v m):('m,'n,'v)namespace) =
       Bind (MAP (λ(n,x). (n,f x)) v) (MAP (λ(mn,e). (mn,nsMap f e)) m)
   End
   (Lean: structural recursion through the nested list, via the auxiliary `nsMapAux`;
   the HOL4 equation is the theorem `nsMap_eq`.) -/
mutual
def nsMap {M : Type u} {N : Type v} {V : Type w} {W : Type _} (f : V → W) :
    Namespace M N V → Namespace M N W
  | .Bind v m => .Bind (MAP (fun p => (p.1, f p.2)) v) (nsMapAux f m)
def nsMapAux {M : Type u} {N : Type v} {V : Type w} {W : Type _} (f : V → W) :
    List (M × Namespace M N V) → List (M × Namespace M N W)
  | [] => []
  | (mn, e) :: rest => (mn, nsMap f e) :: nsMapAux f rest
end

theorem nsMapAux_eq {M : Type u} {N : Type v} {V : Type w} {W : Type _} (f : V → W)
    (m : List (M × Namespace M N V)) :
    nsMapAux f m = MAP (fun p => (p.1, nsMap f p.2)) m := by
  induction m with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨mn, e⟩ := p
    simp only [nsMapAux, MAP, List.map_cons, ih]

/-- The HOL4 defining equation of `nsMap`. -/
theorem nsMap_eq {M : Type u} {N : Type v} {V : Type w} {W : Type _} (f : V → W)
    (v : List (N × V)) (m : List (M × Namespace M N V)) :
    nsMap f (.Bind v m) =
      .Bind (MAP (fun p => (p.1, f p.2)) v) (MAP (fun p => (p.1, nsMap f p.2)) m) := by
  simp only [nsMap, nsMapAux_eq]

end
