import CmlTS
import Lean
/-!
Model-free dump of the Lean side for the S0 structural scan.
Prints lines starting with `@@T ` (one JSON object per theorem of the project modules)
and `@@D ` (one JSON object per non-theorem constant of the project modules).
No heuristics here: it only serialises elaborated `Expr` trees.
Expr node kinds: b(bvar i) c(const n) s(sort) a(app: h head, x explicit args, m implicit args,
ci instance-argument head names) l(lam) p(pi) n(nat lit) t(string lit) j(proj) let.
Usage: `lake env lean DumpLean.lean` from the project directory.
-/
open Lean Meta Elab Command

def biStr : BinderInfo → String
  | .default => "d" | .implicit => "i" | .strictImplicit => "s" | .instImplicit => "c"

def lvlStr (l : Level) : String :=
  if l.isZero then "Prop" else if l.isNeverZero then "Type" else "Sort"

/-- binder infos of the leading foralls of a constant's type. -/
def constBis (env : Environment) (n : Name) : Array BinderInfo :=
  match env.find? n with
  | none => #[]
  | some ci =>
    let rec go (e : Expr) (acc : Array BinderInfo) : Array BinderInfo :=
      match e with
      | .forallE _ _ b bi => go b (acc.push bi)
      | _ => acc
    go ci.type #[]

/-- kind of a binder domain: prop (hypothesis), sort (type variable), prop-sort (a variable of type Prop), data. -/
def domKind (t : Expr) : MetaM String := do
  try
    let t' ← whnfR t
    match t' with
    | .sort l => return (if l.isZero then "bool" else "tyvar")
    | _ =>
      let s ← whnf (← inferType t)
      match s with
      | .sort l => return (if l.isZero then "prop" else "data")
      | _ => return "data"
  catch _ => return "data"

/-- Serialise an expression. Binders are opened with fresh free variables, so every bound variable
occurrence is `{"k":"v","id":..}` and every binder carries the same `id`. -/
partial def toJ (env : Environment) (e : Expr) : MetaM Json := do
  match e with
  | .bvar i => return Json.mkObj [("k", "b"), ("i", i)]
  | .fvar id => return Json.mkObj [("k", "v"), ("id", id.name.toString)]
  | .mvar _ => return Json.mkObj [("k", "mv")]
  | .sort l => return Json.mkObj [("k", "s"), ("l", lvlStr l)]
  | .const n _ => return Json.mkObj [("k", "c"), ("n", n.toString)]
  | .app .. =>
    let f := e.getAppFn
    let args := e.getAppArgs
    match f with
    | .const n _ =>
      let bis := constBis env n
      let mut ex : Array Json := #[]
      let mut im : Array Json := #[]
      let mut ci : Array Json := #[]
      for i in [0:args.size] do
        let bi := if i < bis.size then bis[i]! else BinderInfo.default
        match bi with
        | .default => ex := ex.push (← toJ env args[i]!)
        | .instImplicit =>
          let hn := match args[i]!.getAppFn with | .const m _ => m.toString | _ => "?"
          ci := ci.push (Json.str hn)
        | _ => im := im.push (← toJ env args[i]!)
      return Json.mkObj [("k", "a"), ("h", Json.str n.toString), ("x", Json.arr ex), ("m", Json.arr im), ("ci", Json.arr ci)]
    | _ =>
      let mut ex : Array Json := #[]
      for a in args do ex := ex.push (← toJ env a)
      return Json.mkObj [("k", "a"), ("h", ← toJ env f), ("x", Json.arr ex), ("m", Json.arr #[]), ("ci", Json.arr #[])]
  | .lam n t b bi =>
    let tj ← toJ env t
    let dk ← domKind t
    withLocalDecl n bi t fun x => do
      let bj ← toJ env (b.instantiate1 x)
      return Json.mkObj [("k", "l"), ("id", x.fvarId!.name.toString), ("n", n.toString), ("bi", biStr bi), ("dk", dk), ("t", tj), ("b", bj)]
  | .forallE n t b bi =>
    let tj ← toJ env t
    let dk ← domKind t
    withLocalDecl n bi t fun x => do
      let bj ← toJ env (b.instantiate1 x)
      return Json.mkObj [("k", "p"), ("id", x.fvarId!.name.toString), ("n", n.toString), ("bi", biStr bi), ("dk", dk), ("t", tj), ("b", bj)]
  | .letE _ _ v b _ => toJ env (b.instantiate1 v)
  | .lit (.natVal v) => return Json.mkObj [("k", "n"), ("v", v)]
  | .lit (.strVal v) => return Json.mkObj [("k", "t"), ("v", v)]
  | .mdata _ e => toJ env e
  | .proj sn i e => return Json.mkObj [("k", "j"), ("s", sn.toString), ("i", i), ("e", ← toJ env e)]

partial def constsOf (e : Expr) (acc : NameSet) : NameSet :=
  match e with
  | .const n _ => acc.insert n
  | .app f a => constsOf a (constsOf f acc)
  | .lam _ t b _ => constsOf b (constsOf t acc)
  | .forallE _ t b _ => constsOf b (constsOf t acc)
  | .letE _ t v b _ => constsOf b (constsOf v (constsOf t acc))
  | .mdata _ e => constsOf e acc
  | .proj n _ e => constsOf e (acc.insert n)
  | _ => acc

def isProjectMod (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | some i => (env.header.moduleNames[i.toNat]!).getRoot == `CmlTS
  | none => false

def hasAux (n : Name) : Bool := n.components.any (· == `Aux)

def fileOf (env : Environment) (n : Name) : String :=
  match env.getModuleIdxFor? n with
  | some i => (env.header.moduleNames[i.toNat]!).toString
  | none => ""

def kindOf : ConstantInfo → String
  | .axiomInfo _ => "axiom" | .defnInfo _ => "def" | .thmInfo _ => "theorem"
  | .opaqueInfo _ => "opaque" | .quotInfo _ => "quot" | .inductInfo _ => "inductive"
  | .ctorInfo _ => "ctor" | .recInfo _ => "rec"

def axiomsOf (n : Name) : CoreM (Array Name) := do
  let env ← getEnv
  let (_, s) := ((Lean.CollectAxioms.collect n).run env).run {}
  pure s.axioms

/-- classes of the instance-implicit binders of a constant's type (what the constant needs in context). -/
def instClasses (ci : ConstantInfo) : Array String :=
  let rec go (e : Expr) (acc : Array String) : Array String :=
    match e with
    | .forallE _ d b bi =>
      go b (if bi.isInstImplicit then acc.push (match d.getAppFn with | .const m _ => m.toString | _ => "?") else acc)
    | _ => acc
  go ci.type #[]

/-- for a matcher over one inductive discriminant: constructor index of every alternative (from the casesOn in its body). -/
def matcherAltCtors (n : Name) (mi : Lean.Meta.MatcherInfo) : MetaM (Option (Array Nat)) := do
  let env ← getEnv
  let some ci := env.find? n | return none
  let some v := ci.value? | return none
  lambdaTelescope v fun xs body => do
    let altStart := mi.numParams + 1 + mi.numDiscrs
    let nalts := mi.altNumParams.size
    if xs.size != altStart + nalts || mi.numDiscrs != 1 then return none
    let .const cn _ := body.getAppFn | return none
    if cn.isAnonymous || cn.getString! != "casesOn" then return none
    let some (.inductInfo ii) := env.find? cn.getPrefix | return none
    let args := body.getAppArgs
    let nctors := ii.ctors.length
    if args.size < nctors then return none
    let minors := args.extract (args.size - nctors) args.size
    let mut res : Array Nat := (List.replicate nalts nctors).toArray
    for k in [0:minors.size] do
      let r ← lambdaTelescope minors[k]! fun _ b => pure b.getAppFn
      match r with
      | .fvar id =>
        for i in [0:nalts] do
          if xs[altStart + i]!.fvarId! == id then res := res.set! i k
      | _ => return none
    if res.any (· == nctors) then return none
    return some res

#eval show CommandElabM Unit from do
  let env ← getEnv
  let unfoldNames : List String := match (← IO.getEnv "S0_UNFOLD") with
    | some v => (v.splitOn ",").filter (fun x => x != "")
    | none => []
  for (n, _) in env.constants.map₁.toList do
    if !isProjectMod env n then continue
    if n.isInternal || n.isImplementationDetail then continue
    let some ci := env.find? n | continue
    let rng ← liftCoreM (do try findDeclarationRanges? n catch _ => pure none)
    let rngJ := match rng with
      | some r => Json.mkObj [("l0", r.range.pos.line), ("c0", r.range.pos.column), ("l1", r.range.endPos.line), ("c1", r.range.endPos.column)]
      | none => Json.null
    match ci with
    | .thmInfo v =>
      if hasAux n then continue
      let ax ← liftCoreM (axiomsOf n)
      let tj ← liftTermElabM (toJ env v.type)
      let usesSorry := ax.any (· == `sorryAx)
      let otherAx := ax.filter (fun a => a != `sorryAx)
      IO.println ("@@T " ++ (Json.mkObj [("name", n.toString), ("mod", fileOf env n), ("range", rngJ),
        ("proof_sorry", usesSorry), ("axioms", Json.arr (otherAx.map (fun a => Json.str a.toString))),
        ("type", tj)]).compress)
    | _ =>
      let isRed ← liftCoreM (do pure ((← getReducibilityStatus n) == ReducibilityStatus.reducible))
      let deps := constsOf ci.type {}
      let (deps, val, extra) := match ci with
        | .defnInfo v => (constsOf v.value deps, some v.value, if v.safety == DefinitionSafety.partial then "partial" else if v.safety == DefinitionSafety.unsafe then "unsafe" else "")
        | .opaqueInfo v => (constsOf v.value deps, none, if v.isUnsafe then "unsafe" else "")
        | _ => (deps, none, "")
      let valJ ← match val with
        | some v => if isRed || unfoldNames.contains n.toString then liftTermElabM (toJ env v) else pure Json.null
        | none => pure Json.null
      let depsJ := Json.arr ((deps.toList.filter (fun d => isProjectMod env d)).map (fun (d : Name) => Json.str d.toString)).toArray
      let ax ← liftCoreM (do try axiomsOf n catch _ => pure #[])
      let minfo ← liftCoreM (Lean.Meta.getMatcherInfo? n)
      let minfoJ := match minfo with
        | some mi => Json.mkObj [("nparams", mi.numParams), ("ndiscrs", mi.numDiscrs), ("altparams", Json.arr (mi.altNumParams.map (fun (x : Nat) => (x : Json))))]
        | none => Json.null
      let altJ ← match minfo with
        | some mi => do
          let r ← liftTermElabM (matcherAltCtors n mi)
          pure (match r with | some a => Json.arr (a.map (fun (x : Nat) => (x : Json))) | none => Json.null)
        | none => pure Json.null
      let hasPartialImpl := (env.find? (n ++ `_unsafe_rec)).isSome
      -- structure fields (declaration order) for record handling; empty for non-structures
      let fieldsJ := match ci with
        | .inductInfo _ => if isStructure env n then Json.arr ((getStructureFields env n).map (fun (f : Name) => Json.str f.toString)) else Json.null
        | _ => Json.null
      IO.println ("@@D " ++ (Json.mkObj [("name", n.toString), ("mod", fileOf env n), ("kind", kindOf ci),
        ("safety", extra), ("reducible", isRed), ("unsafe_rec", hasPartialImpl), ("range", rngJ),
        ("axioms", Json.arr (ax.map (fun a => Json.str a.toString))), ("deps", depsJ),
        ("insts", Json.arr ((instClasses ci).map Json.str)), ("matcher", minfoJ), ("altctors", altJ), ("fields", fieldsJ),
        ("value", valJ)]).compress)
