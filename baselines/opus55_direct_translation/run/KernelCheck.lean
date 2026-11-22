import CandleLean
open Lean Elab Command

/-- Lists every `Candle.*` constant that depends on `sorryAx`, and the axioms used by the rest. -/
#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut sorryUsers : Array Name := #[]
  let mut otherAx : Std.HashSet Name := {}
  let mut nTotal := 0
  for (n, ci) in env.constants.toList do
    if !(`Candle).isPrefixOf n then continue
    if n.isInternal then continue
    nTotal := nTotal + 1
    let axs ← liftCoreM (Lean.collectAxioms n)
    if axs.contains ``sorryAx then
      let kind := match ci with
        | .thmInfo _ => "theorem" | .defnInfo _ => "def" | _ => "other"
      sorryUsers := sorryUsers.push n
      IO.println s!"SORRY\t{kind}\t{n}"
    else
      for a in axs do otherAx := otherAx.insert a
  IO.println s!"TOTAL_CANDLE\t{nTotal}"
  IO.println s!"SORRY_USERS\t{sorryUsers.size}"
  IO.println s!"OTHER_AXIOMS\t{otherAx.toList}"
