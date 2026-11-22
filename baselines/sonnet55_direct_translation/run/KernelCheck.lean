import CandleLean
import Lean
open Lean Elab Command
#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut nTotal := 0
  let mut nSorry := 0
  let mut otherAx : Std.HashSet Name := {}
  for (n, ci) in env.constants.toList do
    let some idx := env.getModuleIdxFor? n | continue
    let mod := env.header.moduleNames[idx.toNat]!
    if !(`CandleLean).isPrefixOf mod then continue
    if n.isInternal then continue
    nTotal := nTotal + 1
    let axs ← liftCoreM (Lean.collectAxioms n)
    if axs.contains ``sorryAx then
      nSorry := nSorry + 1
      let kind := match ci with | .thmInfo _ => "theorem" | .defnInfo _ => "def" | _ => "other"
      IO.println s!"SORRY\t{kind}\t{n}"
    else
      for a in axs do otherAx := otherAx.insert a
  IO.println s!"TOTAL\t{nTotal}"
  IO.println s!"SORRY_USERS\t{nSorry}"
  IO.println s!"OTHER_AXIOMS\t{otherAx.toList}"
