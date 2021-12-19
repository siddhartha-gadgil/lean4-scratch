-- import Mathlib 
import Scratch.ConstDeps
import Lean.Meta 
open Lean
open Lean.Meta
open ConstDeps
open Elab

namespace MathDeps

def mathEnv: IO Environment := importModules ([{module := `Mathlib}]) {}

-- #eval (namePrefixes mathEnv)

def mathPairs := offSpringPairs mathEnv [`Lean, `Std, `IO]

#check mathPairs

def mathPairsString : IO String := do
  let pairs ← mathPairs
  let blob : String := pairs.foldl (
        fun s (p, l) => 
          s ++ "[" ++  (p.toString) ++ "," ++ l.toString  ++ "]\n") ""
  return blob

def mathDepFile := System.mkFilePath ["data/mathDeps.txt"]

def writeBlob : IO Unit := do
  let blob ← mathPairsString
  IO.FS.writeFile mathDepFile blob
  return ()

#eval writeBlob

def mathTriples  : Unit →  IO (List (Name × List Name × List Name)) := fun _ => do
        IO.println ("within math-triples")
        let result ← offSpringTriple mathEnv [`Lean, `Std, `IO, 
          `Char, `String, `ST, `StateT, `Repr, `ReaderT, `EIO, `BaseIO]
        IO.println "obtained  result"
        return result

/-
def mathTriplesString : IO String := do
  let blob : String := (← mathTriples).foldl (
        fun s (p, l, lt) => 
          s ++ "[" ++  (p.toString) ++ "," ++ l.toString  
            ++ "," ++ lt.toString ++ "]\n") ""
  return blob

def writeTriples : IO Unit := do
  let blob ← mathTriplesString
  let file := System.mkFilePath ["data/mathTriples.txt"]
  IO.FS.writeFile file blob
  return ()

#eval writeTriples
-/
end MathDeps