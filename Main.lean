import Scratch.Egs
import Scratch.Eg9
import Scratch.Eg5
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

set_option compiler.extract_closed false
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
  let uu := u.run'
  initSearchPath (← Lean.findSysroot?) ["build/lib", "lean_packages/mathlib/build/lib/"]
  let env ← importModules [{module := `Scratch.Egs}] {}
  let natDecl := OpenDecl.simple ``Nat []
  let uuu := uu.run' {openDecls := [natDecl]} {env}
  let uStep ←  uuu.toIO'
  let uSplit : IO (Sum Expr String) :=
    match uStep with
    | Except.ok (uuuu) => return (Sum.inl uuuu)
    | Except.error e => 
        do
          IO.println "For meta add one"
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
  IO.println "Computing slow-minimum 2000"
  -- (tst 11).map <| fun _ => ()
  let t1 := Task.spawn  fun _ => slowMin 2000
  let t2 := Task.spawn  fun _ => slowMin 2100
  let t3 := Task.spawn  fun _ => slowMin 2200
  -- let res := slowMin 2000 
  -- IO.println (res)
  IO.println (t1.get + t2.get + t3.get)
  return ()

#check IO.wait
#check IO.ofExcept