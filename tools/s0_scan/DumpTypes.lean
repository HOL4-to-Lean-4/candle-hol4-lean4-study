import CandleLean
import Lean
open Lean Meta Elab Command
/-- constants (with multiplicity) of the elaborated type of every theorem listed on stdin file `names.txt`. -/
partial def countConsts (e : Expr) (m : Std.HashMap Name Nat) : Std.HashMap Name Nat :=
  match e with
  | .const n _ => m.insert n ((m.getD n 0) + 1)
  | .app f a => countConsts a (countConsts f m)
  | .lam _ t b _ => countConsts b (countConsts t m)
  | .forallE _ t b _ => countConsts b (countConsts t m)
  | .letE _ t v b _ => countConsts b (countConsts v (countConsts t m))
  | .mdata _ e => countConsts e m
  | .proj n _ e => countConsts e (m.insert n ((m.getD n 0) + 1))
  | .lit _ => m.insert `literal ((m.getD `literal 0) + 1)
  | _ => m
#eval show CommandElabM Unit from do
  let env ← getEnv
  let names := (← IO.FS.readFile "names.txt").splitOn "\n" |>.filter (· ≠ "")
  for s in names do
    let n := s.trim.toName
    match env.find? n with
    | some ci =>
      let t := ci.type
      let rec bind (e : Expr) (nb np : Nat) : Nat × Nat := match e with
        | .forallE _ d b bi => if bi.isInstImplicit then bind b nb np else bind b (nb + 1) (if d.isProp then np else np)
        | _ => (nb, np)
      let (nb, _) := bind t 0 0
      let m := countConsts t {}
      let js := ",".intercalate (m.toList.map fun (k, v) => s!"\"{k}\":{v}")
      IO.println ("@@ {\"name\":\"" ++ s.trim ++ "\",\"binders\":" ++ toString nb ++ ",\"consts\":{" ++ js ++ "}}")
    | none => IO.println ("@@ {\"name\":\"" ++ s.trim ++ "\",\"missing\":true}")
