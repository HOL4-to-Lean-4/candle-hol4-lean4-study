import CmlTS.Prelude.ListLib

/-
HOL4 theory `namespace` (namespaceScript.sml).
The HOL4 types `id` and `namespace` are `ident` and `Namespace` here.
-/

namespace CmlTS

noncomputable section

open scoped Classical

/- HOL4: Type alist = ``: ('k # 'v) list`` -/
abbrev alist (κ ν : Type) : Type := List (κ × ν)

/- HOL4:
Datatype:
  id = Short 'n | Long 'm id
End
(the HOL4 type is `('m,'n) id`) -/
inductive ident (m n : Type)
  | Short (x : n)
  | Long (mn : m) (id : ident m n)

export ident (Short Long)

/- HOL4:
Datatype:
  namespace =
    Bind (('n,'v) alist) (('m,namespace) alist)
End
(the HOL4 type is `('m,'n,'v) namespace`) -/
inductive Namespace (m n v : Type)
  | Bind (l : List (n × v)) (ms : List (m × Namespace m n v))

variable {m n v w : Type}

/- HOL4:
Definition mk_id_def:
  mk_id [] n = Short n ∧
  mk_id (mn::mns) n = Long mn (mk_id mns n)
End -/
def mk_id : List m → n → ident m n
  | [], x => Short x
  | mn :: mns, x => Long mn (mk_id mns x)

/- HOL4:
Definition id_to_n_def:
 id_to_n (Short n) = n ∧
 id_to_n (Long _ id) = id_to_n id
End -/
def id_to_n : ident m n → n
  | Short x => x
  | Long _ id => id_to_n id

/- HOL4:
Definition id_to_mods_def:
  id_to_mods (Short _) = [] ∧
  id_to_mods (Long mn id) = mn::id_to_mods id
End -/
def id_to_mods : ident m n → List m
  | Short _ => []
  | Long mn id => mn :: id_to_mods id

/- HOL4:
Definition nsLookup_def:
  nsLookup ((Bind v m):('m,'n,'v)namespace) (Short n) =
    ALOOKUP v n ∧
  nsLookup (Bind v m) (Long mn id) =
    case ALOOKUP m mn of
    | NONE => NONE
    | SOME env => nsLookup env id
End -/
def nsLookup : Namespace m n v → ident m n → Option v
  | Namespace.Bind vs _, Short x => ALOOKUP vs x
  | Namespace.Bind _ ms, Long mn id =>
    match ALOOKUP ms mn with
    | none => none
    | some env => nsLookup env id

/- HOL4:
Definition nsLookupMod_def:
  nsLookupMod e [] = SOME (e:('m,'n,'v)namespace) ∧
  nsLookupMod (Bind v m) (mn::path) =
  case ALOOKUP m mn of NONE => NONE | SOME env => nsLookupMod env path
End -/
def nsLookupMod : Namespace m n v → List m → Option (Namespace m n v)
  | e, [] => some e
  | Namespace.Bind _ ms, mn :: path =>
    match ALOOKUP ms mn with
    | none => none
    | some env => nsLookupMod env path

/- HOL4:
Definition nsEmpty_def:
  nsEmpty = Bind [] []
End -/
def nsEmpty : Namespace m n v := Namespace.Bind [] []

instance : Nonempty (Namespace m n v) := ⟨nsEmpty⟩
instance : Inhabited (Namespace m n v) := ⟨nsEmpty⟩

/- HOL4:
Definition nsAppend_def:
  nsAppend (Bind v1 m1) (Bind v2 m2) = Bind (v1 ++ v2) (m1 ++ m2)
End -/
def nsAppend : Namespace m n v → Namespace m n v → Namespace m n v
  | Namespace.Bind v1 m1, Namespace.Bind v2 m2 => Namespace.Bind (v1 ++ v2) (m1 ++ m2)

/- HOL4:
Definition nsLift_def:
  nsLift mn env = Bind [] [(mn,env)]
End -/
def nsLift (mn : m) (env : Namespace m n v) : Namespace m n v := Namespace.Bind [] [(mn, env)]

/- HOL4:
Definition alist_to_ns_def:
  alist_to_ns a = Bind a []
End -/
def alist_to_ns (a : List (n × v)) : Namespace m n v := Namespace.Bind a []

/- HOL4:
Definition nsBind_def:
  nsBind k x (Bind v m) = Bind ((k,x)::v) m
End -/
def nsBind (k : n) (x : v) : Namespace m n v → Namespace m n v
  | Namespace.Bind vs ms => Namespace.Bind ((k, x) :: vs) ms

/- HOL4:
Definition nsBindList_def:
  nsBindList l e = FOLDR (λ(x,v) e. nsBind x v e) e l
End -/
def nsBindList (l : List (n × v)) (e : Namespace m n v) : Namespace m n v :=
  l.foldr (fun (x, v) e => nsBind x v e) e

/- HOL4:
Definition nsOptBind_def:
  nsOptBind n x env = case n of NONE => env | SOME n => nsBind n x env
End -/
def nsOptBind (o : Option n) (x : v) (env : Namespace m n v) : Namespace m n v :=
  match o with
  | none => env
  | some k => nsBind k x env

/- HOL4:
Definition nsSing_def:
  nsSing n x = Bind [(n,x)] []
End -/
def nsSing (k : n) (x : v) : Namespace m n v := Namespace.Bind [(k, x)] []

/- HOL4:
Definition nsSub_def:
  nsSub r env1 env2 ⇔
     (∀id v1.
        nsLookup env1 id = SOME v1 ⇒
        ∃v2. nsLookup env2 id = SOME v2 ∧ r id v1 v2) ∧
     ∀path. nsLookupMod env2 path = NONE ⇒ nsLookupMod env1 path = NONE
End -/
def nsSub (r : ident m n → v → w → Prop) (env1 : Namespace m n v) (env2 : Namespace m n w) :
    Prop :=
  (∀ id v1, nsLookup env1 id = some v1 → ∃ v2, nsLookup env2 id = some v2 ∧ r id v1 v2) ∧
  ∀ path, nsLookupMod env2 path = none → nsLookupMod env1 path = none

/- HOL4:
Definition nsAll_def:
  nsAll f env ⇔ ∀id v. nsLookup env id = SOME v ⇒ f id v
End -/
def nsAll (f : ident m n → v → Prop) (env : Namespace m n v) : Prop :=
  ∀ id x, nsLookup env id = some x → f id x

/- HOL4:
Definition nsAll2_def:
  nsAll2 r env1 env2 ⇔
    nsSub r env1 env2 ∧ nsSub (λx y z. r x z y) env2 env1
End -/
def nsAll2 (r : ident m n → v → w → Prop) (env1 : Namespace m n v) (env2 : Namespace m n w) :
    Prop :=
  nsSub r env1 env2 ∧ nsSub (fun x y z => r x z y) env2 env1

/- HOL4:
Definition nsDom_def:
  nsDom (env:('m,'n,'v)namespace) =
     {n | (v,n) | v ∈ 𝕌(:φ) ∧ n ∈ 𝕌(:(ν, ξ) id) ∧ nsLookup env n = SOME v}
End -/
def nsDom (env : Namespace m n v) : Set (ident m n) :=
  setOf fun x => ∃ y : v, y ∈ (UNIV : Set v) ∧ x ∈ (UNIV : Set (ident m n)) ∧
    nsLookup env x = some y

theorem Namespace_sizeOf_aux {l : List (n × v)} {ms : List (m × Namespace m n v)}
    {p : m × Namespace m n v} (h : p ∈ ms) : sizeOf p.2 < sizeOf (Namespace.Bind l ms) := by
  have h1 := List.sizeOf_lt_of_mem h
  cases p
  simp at h1 ⊢
  omega

/- HOL4:
Definition nsMap_def:
  nsMap (f:'v -> 'w) ((Bind v m):('m,'n,'v)namespace) =
    Bind (MAP (λ(n,x). (n,f x)) v) (MAP (λ(mn,e). (mn,nsMap f e)) m)
End -/
def nsMap (f : v → w) : Namespace m n v → Namespace m n w
  | Namespace.Bind vs ms =>
    Namespace.Bind (vs.map (fun (k, x) => (k, f x))) (ms.map (fun p => (p.1, nsMap f p.2)))
termination_by e => sizeOf e
decreasing_by
  rename_i h
  exact Namespace_sizeOf_aux h

/-! Helper lemmas (not HOL4 constants): `nsAll2` split into a relation-free part
and a pointwise part; used to justify the form of the rules of `type_v`. -/

theorem nsAll2_iff_aux {r : ident m n → v → w → Prop} {env1 : Namespace m n v}
    {env2 : Namespace m n w} :
    nsAll2 r env1 env2 ↔
      nsAll2 (fun _ _ _ => True) env1 env2 ∧
      ∀ id v1 v2, nsLookup env1 id = some v1 → nsLookup env2 id = some v2 → r id v1 v2 := by
  constructor
  · rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
    refine ⟨⟨⟨?_, h2⟩, ⟨?_, h4⟩⟩, ?_⟩
    · intro id v1 h; obtain ⟨v2, h', _⟩ := h1 id v1 h; exact ⟨v2, h', trivial⟩
    · intro id v1 h; obtain ⟨v2, h', _⟩ := h3 id v1 h; exact ⟨v2, h', trivial⟩
    · intro id v1 v2 ha hb
      obtain ⟨v2', h', hr⟩ := h1 id v1 ha
      rw [hb] at h'
      cases h'
      exact hr
  · rintro ⟨⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩, h5⟩
    refine ⟨⟨?_, h2⟩, ⟨?_, h4⟩⟩
    · intro id v1 h; obtain ⟨v2, h', _⟩ := h1 id v1 h; exact ⟨v2, h', h5 id v1 v2 h h'⟩
    · intro id v1 h; obtain ⟨v2, h', _⟩ := h3 id v1 h; exact ⟨v2, h', h5 id v2 v1 h' h⟩

end

end CmlTS
