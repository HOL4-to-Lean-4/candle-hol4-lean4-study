import Lean
import CmlTS
open Lean Meta Elab Command
#eval show CommandElabM Unit from do
  let env ← getEnv
  for (n, ci) in env.constants.toList do
    let some idx := env.getModuleIdxFor? n | continue
    let m := env.header.moduleNames[idx.toNat]!
    if !(`CmlTS).isPrefixOf m || n.isInternal then continue
    match ci with
    | .thmInfo _ | .recInfo _ => continue
    | _ => pure ()
    let k ← liftTermElabM <| forallTelescope ci.type fun xs _ => do
      let mut c := 0
      for x in xs do
        let t ← inferType x
        if t.isSort && !t.isProp then c := c + 1
      pure c
    let s ← liftTermElabM (do return toString (← ppExpr ci.type))
    IO.println s!"L\t{m}\t{n}\t{k}\t{s.replace "\n" " "}"
