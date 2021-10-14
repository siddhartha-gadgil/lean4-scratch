import Lean.Util.Path
import Lean.Util.FindExpr
import Lean.Util.Profile
import Lean
import Lean.Meta
import Init.System
import Std.Data.HashMap
open Std
open Lean
open Lean.Meta

namespace ConstDeps

def isBlackListed (env: Environment) (declName : Name) : IO  Bool := do
  declName.isInternal
  <||> isAuxRecursor env declName
  <||> isNoConfusion env declName
  <||> isRecCore env declName
  <||> isMatcherCore env declName

def isWhiteListed (env: Environment)(declName : Name) : IO Bool := do
  let bl ← isBlackListed env declName
  return !bl

def constantNames (envIO: IO Environment) : IO (List Name) := do
  let env ← envIO
  let decls ← env.constants.map₁.toList
  let allNames := decls.map $ fun (name, _) => name 
  let names ← allNames.filterM (isWhiteListed env)
  return names

def constantNameTypes (envIO: IO Environment) : IO (List (Name ×  Expr)) := do
  let env ← envIO
  let decls ← env.constants.map₁.toList
  let allNames := decls.map $ fun (name, dfn) => (name, dfn.type) 
  let names ← allNames.filterM (fun (name, _) => isWhiteListed env name)
  return names

def namePrefixes (envIO: IO Environment) : IO (List Name) := do
  let names ← constantNames envIO
  let prefixes := names.map $ fun name => name.getPrefix
  return prefixes.eraseDups

def nameExpr? : Environment → Name → Option Expr :=
  fun env name =>
      let info := (env.find? name)
      Option.bind info ConstantInfo.value?

initialize expNamesCache : IO.Ref (HashMap Expr (List Name)) ← IO.mkRef (HashMap.empty)

def getCached? (e : Expr) : IO (Option (List Name)) := do
  let cache ← expNamesCache.get
  return (cache.find? e)

def cache (e: Expr) (offs : List Name) : IO Unit := do
  let cache ← expNamesCache.get
  expNamesCache.set (cache.insert e offs)
  return ()


partial def recExprNames: Environment → Expr → IO (List Name) :=
  fun env e =>
  do 
  match ← getCached? e with
  | some offs => return offs
  | none =>
    let res ← match e with
      | Expr.const name _ _  =>
        do
        if ← (isWhiteListed env name) 
          then [name] 
          else
          if ← name.isInternal  then
            match nameExpr? env name with
            | some e => recExprNames env e
            | none => []
          else []        
      | Expr.app f a data => 
          do  
            let bi := data.binderInfo
            let impl := bi.isImplicit || bi.isStrictImplicit || bi.isInstImplicit
            let fdeps ← recExprNames env f
            let adeps ← recExprNames env a
            let s := 
              if impl then fdeps else
                fdeps ++ adeps
            return s.eraseDups
      | Expr.lam _ _ b _ => 
          do
            return ← recExprNames env b 
      | Expr.forallE _ _ b _ => do
          return  ← recExprNames env b 
      | Expr.letE _ _ _ b _ => 
            return ← recExprNames env b
      | _ => []
    cache e res
    return res

def offSpring?(env: Environment) (name: Name) : IO (Option (List Name)) := do
  let expr ← nameExpr? env name
  match expr with
  | some e => recExprNames env e
  | none => return none

def offSpringPairs(envIO: IO Environment)(startOpt: Option Nat)(boundOpt : Option Nat)
              : IO (List (Name × (List Name))) :=
  do
  let env ← envIO
  let keys ←  constantNames envIO
  let start := startOpt.getD 0
  let keyRange := 
    match boundOpt with
    | some bound => 
      (keys.drop start).take bound
    | none => keys.drop start
  let kv : List (Name × (List Name)) ←  (keyRange).filterMapM $ 
      fun n => 
          do 
          let off ← offSpring?  env n
          match off with
          | some l =>  some (n, l)
          | none => none
        return kv

def offSpringTriple(envIO: IO Environment)(startOpt: Option Nat)(boundOpt : Option Nat)
              : IO (List (Name × (List Name) × (List Name) )) :=
  do
  let env ← envIO
  let keys ←  constantNameTypes  envIO
  let start := startOpt.getD 0
  let keyRange := 
    match boundOpt with
    | some bound => 
      (keys.drop start).take bound
    | none => keys.drop start
  let kv : List (Name × (List Name) × (List Name)) ←  (keyRange).filterMapM $ 
      fun (n, type) => 
          do 
          let off ← offSpring?  env n
          match off with
          | some l =>  some (n, l, ← recExprNames env type)
          | none => none
        return kv

end ConstDeps