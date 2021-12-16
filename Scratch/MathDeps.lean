import Mathlib 
import Scratch.ConstDeps
import Lean.Meta 
open Lean
open Lean.Meta
open ConstDeps
open Elab

namespace MatDeps

def mathEnv: IO Environment := importModules ([{module := `Mathlib}]) {}

def mathPairs := offSpringPairs mathEnv none none

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

def mathTriplesString : IO String := do
  let pairs ← offSpringTriple mathEnv none none
  let blob : String := pairs.foldl (
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