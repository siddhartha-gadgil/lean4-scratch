import Scratch.Egs
import Scratch.Eg9
import Scratch.TermSeq
import Scratch.ConstDeps
import Scratch.MathDeps
import Scratch.Ackermann
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
      let v ← exprView e -- checking import
      IO.println e
      return ← whnf e
  let uu := u.run' {}
  initSearchPath (← Lean.findSysroot?) ["build/lib", "lean_packages/mathlib/build/lib/"]
  let env ← importModules [{module := `Scratch.Egs}] {}
  let uuu := uu.run' {} {env}
  let uStep ←  uuu.toIO'
  let uSplit : IO (Sum Expr String) :=
    match uStep with
    | Except.ok (uuuu) => return (Sum.inl uuuu)
    | Except.error e => 
        do
          let msg ← e.toMessageData.toString
          return (Sum.inr msg)
  let uuuu ← uSplit
  IO.println (uuuu)
  IO.println "done"
  let mathEnv ← MathDeps.mathEnv -- importModules ([{module := `Mathlib}]) {}
  let mathTriples ← MathDeps.mathTriples ()
  -- ConstDeps.offSpringTriple (pure mathEnv) [`Lean, `Std, `IO, 
          -- `Char, `String, `ST, `StateT, `Repr, `ReaderT, `EIO, `BaseIO]
  IO.println (mathTriples.length)
  let mathCount ← nameCount mathTriples
  let top200 ← topNames mathCount 200
  IO.println (top200)
  IO.println "Computing Ack(4, 1)"
  IO.println $ ackermann 4 2
  return ()

#check IO.wait
#check IO.ofExcept