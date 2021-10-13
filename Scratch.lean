import Scratch.Egs
import Scratch.Eg9
import Scratch.TermSeq
import Lean
import Lean.Meta
import Lean.Data.Name
import Lean.Util.Path
open Lean
open Meta
open Nat
open Lean.Core
open Lean.Meta
open Lean.Elab.Term
open Lean



def main (args: List String) : IO Unit := do
  IO.println "Hello, world!"
  -- let nameList ← egNames
  -- IO.println nameList
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
  let _ ← initSearchPath (some "build:build/lib/lean")
  let sp ← searchPathRef.get
  IO.println sp
  let fname ← sp.findWithExt "olean" `Init
  IO.println fname
  -- IO.println (← fname.get!.pathExists)
  -- let (mod, region) ← readModuleData fname.get!
  IO.println "loaded"
  let initializing ← IO.initializing
  if initializing then 
      throw (IO.userError "environment objects cannot be created during initialization")
  let env ← mkEmptyEnvironment  
            -- importModules [⟨`Scratch.Egs, false⟩] {}
  let uuu := uu.run {} {env}
  let uStep ←  uuu.toIO'
  let uSplit : IO (Sum Expr String) :=
    match uStep with
    | Except.ok ((uuuu, _), _) => return (Sum.inl uuuu)
    | Except.error e => 
        do
          let msg ← e.toMessageData.toString
          return (Sum.inr msg)
  let uuuu ← uSplit
  IO.println (uuuu)
  let bd ← Lean.getBuildDir 
  IO.println bd
  let bs ← Lean.getBuiltinSearchPath
  IO.println bs
  IO.println "done"
  return ()
