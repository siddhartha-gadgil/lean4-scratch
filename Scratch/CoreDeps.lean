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
open Elab

namespace CoreDeps

def coreEnv : IO Environment := importModules ([{module := `Init}]) {}

-- #eval offSpringPairs coreEnv (some 0) (some 100)

def corePairs := offSpringPairs coreEnv 

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
  let pairs ← offSpringTriple coreEnv 
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

def egEvalV (name: Name) : TermElabM (Option (List Name)) := do
  let env ← coreEnv
  offSpringV? env name

def egEval (name: Name) : TermElabM (Option (List Name)) := do
  let env ← coreEnv
  offSpring? env name

#eval egEval `Nat.pred_le_pred

set_option pp.all true

-- #eval egEvalV `Nat.pred_le_pred

-- #print Nat.pred_le_pred

end CoreDeps
