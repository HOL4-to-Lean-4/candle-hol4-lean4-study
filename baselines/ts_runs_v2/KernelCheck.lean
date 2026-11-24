import Lean
import CmlTS
open Lean Elab Command

/- Lists every constant declared in a `CmlTS.*` module that depends on `sorryAx`,
    with the axioms used by the rest. Selects by module, not by name prefix. -/
#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut nTotal := 0
  let mut nSorry := 0
  let mut nAxiom := 0
  let mut otherAx : Std.HashSet Name := {}
  for (n, ci) in env.constants.toList do
    let some idx := env.getModuleIdxFor? n | continue
    let m := env.header.moduleNames[idx.toNat]!
    if !(`CmlTS).isPrefixOf m then continue
    if n.isInternal then continue
    nTotal := nTotal + 1
    if let .axiomInfo _ := ci then
      nAxiom := nAxiom + 1
      IO.println s!"AXIOM\t{n}"
    let axs ← liftCoreM (Lean.collectAxioms n)
    let kind := match ci with
      | .thmInfo _ => "theorem" | .defnInfo _ => "def" | .opaqueInfo _ => "opaque"
      | .axiomInfo _ => "axiom" | _ => "other"
    if axs.contains ``sorryAx then
      nSorry := nSorry + 1
      IO.println s!"SORRY\t{kind}\t{m}\t{n}"
    else
      if kind == "theorem" then IO.println s!"PROVED\t{kind}\t{m}\t{n}"
      if kind == "opaque" then IO.println s!"OPAQUE\t{kind}\t{m}\t{n}"
      for a in axs do otherAx := otherAx.insert a
  IO.println s!"TOTAL\t{nTotal}"
  IO.println s!"SORRY_USERS\t{nSorry}"
  IO.println s!"DECLARED_AXIOMS\t{nAxiom}"
  IO.println s!"OTHER_AXIOMS\t{otherAx.toList}"
