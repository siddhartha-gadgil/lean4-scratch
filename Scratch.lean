import Scratch.Egs
import Lean
import Lean.Meta
open Lean
open Meta
open Nat
open Lean.Core
open Lean.Meta
open Lean.Elab.Term
open Lean



def main (args: List String) : IO Unit := do
  IO.println "Hello, world!"
  let n : Nat := 
  match args.head? with
  | none => 3 
  | some s =>
      match s.toNat? with
      | some n => n 
      | none => 0 
  let u : MetaM Expr := 
    do 
      let e ← metaAddOne (mkNatLit n)
      -- let v ← exprView e
      return e
  let uu := u.run {}
  let names := [``Nat]
  let env ← mkEmptyEnvironment  -- importModules [⟨``Nat, false⟩] {}
  let uuu := uu.run {} {env}
  let ((uuuu, _), _) ←  uuu.toIO (fun _ => IO.Error.userError "")
  IO.println (uuuu)
  IO.println "done"
  return ()
