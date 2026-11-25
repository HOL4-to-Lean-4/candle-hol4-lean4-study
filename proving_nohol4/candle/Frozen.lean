import Lean
import CandleLean
open Lean Elab Command

/- Dumps type (and value, for non-theorems) of every public constant of CandleLean, for the freeze check.
   Theorems: type only. One line per constant: kind, name, level params, type, value. -/
#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut lines : Array String := #[]
  for (n, ci) in env.constants.toList do
    let some idx := env.getModuleIdxFor? n | continue
    let m := env.header.moduleNames[idx.toNat]!
    if !(`CandleLean).isPrefixOf m then continue
    let u := (privateToUserName? n).getD n
    if u.isInternal then continue
    let kind := match ci with
      | .thmInfo _ => "theorem" | .defnInfo _ => "def" | .opaqueInfo _ => "opaque" | .axiomInfo _ => "axiom"
      | .inductInfo _ => "inductive" | .ctorInfo _ => "ctor" | .recInfo _ => "rec" | .quotInfo _ => "quot"
    let v := match ci with
      | .defnInfo d => toString d.value.hash
      | .opaqueInfo d => toString d.value.hash
      | _ => "-"
    lines := lines.push s!"{kind}\t{n}\t{ci.levelParams}\t{ci.type.hash}\t{v}"
  for l in lines.qsort (· < ·) do IO.println l
