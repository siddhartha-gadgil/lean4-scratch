import Lean.Util.Path
import Lean.Util.FindExpr
import Lean.Util.Profile
import Lean
import Lean.Meta
import Scratch.Eg7
open Lean
open Meta
open Elab

#check Lean.findOLean

def initOLean := Lean.findOLean `Init

#check initOLean
#eval initOLean

def eg8Olean := Lean.findOLean `Scratch.Eg8

#eval eg8Olean

#check ModuleData

#check readModuleData

def initData : IO (ModuleData × CompactedRegion) := 
    do
      let path ← initOLean
      return ← readModuleData path

#check initData

def impEnv := importModules ([⟨`Init, false⟩,  ⟨`Scratch.Eg5, false⟩]) Options.empty

#check impEnv

def showEnv : TermElabM Unit :=
  do
    let env ← impEnv
    let expOpt ←  env.find? `Nat.pred
    let name := expOpt.map (fun s => s.name)
    let type := expOpt.map (fun s => s.type)
    let expr := expOpt.bind (fun s => s.value?)
    logInfo m!"evaluating: {name}"
    logInfo m!"type: {type}"
    logInfo m!"expr : {expr}"
    let m2 := env.constants.map₁
    let l2 ←  (m2.toList.map (fun (n, _) => n)).filterM (fun s => isWhiteListed s) 
    -- logInfo m!"constants: {l2.take 20}"
    -- env.displayStats
    return ()

#eval showEnv

def egNames : IO (List Name) :=
  do
    let env ← impEnv
    let l ← env.constants.map₁.toList.map (fun (n, _) => n)
    return l.take 20
  
unsafe def coreNames := unsafeIO egNames