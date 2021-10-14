import Lean.Util.Path
import Lean.Util.FindExpr
import Lean.Util.Profile
import Lean
import Lean.Meta
import Init.System
import Std.Data.HashMap
import Scratch.ConstDeps
open Std
open Lean
open Lean.Meta
open ConstDeps

namespace CoreDeps

def coreEnv : IO Environment := importModules ([⟨`Init, false⟩]) Options.empty

-- #eval offSpringPairs coreEnv (some 0) (some 100)

def corePairs := offSpringPairs coreEnv none none

#check corePairs

def quote : String →  String := fun s => "\"" ++ s ++ "\""

def corePairsString : IO String := do
  let pairs ← corePairs
  let blob : String := pairs.foldl (
        fun s (p, l) => 
          s ++ "[" ++  (p.toString) ++ "," ++ l.toString  ++ "]\n") ""
  return blob

def coreDepFile := System.mkFilePath ["data/coreDeps.txt"]

def writeBlob : IO Unit := do
  let blob ← corePairsString
  IO.FS.writeFile coreDepFile blob
  return ()

#eval writeBlob

def coreTriplesString : IO String := do
  let pairs ← offSpringTriple coreEnv none none
  let blob : String := pairs.foldl (
        fun s (p, l, lt) => 
          s ++ "[" ++  (p.toString) ++ "," ++ l.toString  
            ++ "," ++ lt.toString ++ "]\n") ""
  return blob

def writeTriples : IO Unit := do
  let blob ← coreTriplesString
  let file := System.mkFilePath ["data/coreTriples.txt"]
  IO.FS.writeFile file blob
  return ()

#eval writeTriples

end CoreDeps
