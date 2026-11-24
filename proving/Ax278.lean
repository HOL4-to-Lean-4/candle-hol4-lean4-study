import Lean
import CandleLean
open Lean Elab Command
#eval show CommandElabM Unit from do
  let env ← getEnv
  let txt ← IO.FS.readFile "../../targets278.txt"
  let mut ok := 0
  for s in txt.splitOn "\n" do
    let s := s.trimAscii.toString
    if s.isEmpty then continue
    let n := s.toName
    match env.find? n with
    | some (.thmInfo _) =>
      let axs ← liftCoreM (Lean.collectAxioms n)
      if axs.all (fun a => a == ``propext || a == ``Classical.choice || a == ``Quot.sound) then ok := ok + 1
      else IO.println s!"BAD {n} {axs}"
    | _ => IO.println s!"MISSING {n}"
  IO.println s!"OK {ok}"
