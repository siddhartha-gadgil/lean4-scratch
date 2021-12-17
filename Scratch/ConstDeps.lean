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
open Elab

namespace ConstDeps

def isBlackListed (env: Environment) (declName : Name) : IO  Bool := do
  declName.isInternal
  <||> isAuxRecursor env declName
  <||> isNoConfusion env declName
  <||> isRecCore env declName
  <||> isMatcherCore env declName

def isAux (env: Environment) (declName : Name) : IO  Bool := do
  isAuxRecursor env declName
  <||> isNoConfusion env declName
  
def isNotAux (env: Environment) (declName : Name) : IO  Bool := do
  let nAux ← isAux env declName
  return (not nAux)

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

def leanPrefixes (envIO: IO Environment) : IO (List Bool) := do
  let names ← constantNames envIO
  let prefixes := names.map $ fun name => (`Lean).isPrefixOf name
  return prefixes

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

def RunToIO? {α : Type}(n: MetaM α) (env: Environment) : IO (Option α)    :=
  do
  let core := n.run' {}
  let state : Core.State := Core.State.mk env (firstFrontendMacroScope + 1) {} {}
  let eio := core.run' {} state
  let io' : (Except Exception α)  ←   eio.toIO'
  match io' with
    | Except.ok a => return some a
    | Except.error e => return none
  

def inferTypeIO (expr: Expr) (env: Environment) : IO (Option Expr) := do
  let mtype : MetaM Expr := inferType expr
  RunToIO? mtype env

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
          if ← (isNotAux env name)  then
            match nameExpr? env name with
            | some e => recExprNames env e
            | none => []
          else []        
      | Expr.app f a _ => 
          do  
            -- let ftype ← inferTypeIO f env
            let ftype ← inferTypeIO f env
            let expl := 
              (ftype.map (fun ft => ft.data.binderInfo.isExplicit)).getD true
            let fdeps ← recExprNames env f
            let adeps ← recExprNames env a
            let s := 
              if !expl then fdeps else
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

partial def recExprNamesV: Environment → Expr → TermElabM (List Name) :=
  fun env e =>
  do 
  logInfo m!"resolving {e}"
  -- match ← getCached? e with
  -- | some offs => return offs
  -- | none =>
    let res ← match e with
      | Expr.const name _ _  =>
        do
        if ← (isWhiteListed env name) 
          then
            logInfo m!"Stopping with {name}" 
            [name] 
          else
          if ← (name.isInternal)  then
            logInfo m!"Continuing past {name}"
            match nameExpr? env name with
            | some e =>
              logInfo m!"Continuing with {e}" 
              recExprNamesV env e
            | none => []
          else []        
      | Expr.app f a data => 
          do  
            let ftype ← inferType f
            let bi := ftype.data.binderInfo
            let impl := !bi.isExplicit
            logInfo m!"Function application with {f} and {a}; implicit: {impl}"
            let fdeps ← recExprNamesV env f
            let adeps ← recExprNamesV env a
            let s := 
              if impl then fdeps else
                fdeps ++ adeps
            return s.eraseDups
      | Expr.lam _ _ b _ => 
          do
            logInfo m!"Lembda with body {b}"
            return ← recExprNamesV env b 
      | Expr.forallE _ _ b _ => do
          logInfo m!"Forall with body {b}"
          return  ← recExprNamesV env b 
      | Expr.letE _ _ _ b _ => 
            logInfo m!"Let with body {b}"
            return ← recExprNamesV env b
      | _ => []
    cache e res
    return res

def offSpringV?(env: Environment) (name: Name) : TermElabM (Option (List Name)) := do
  let expr ← nameExpr? env name
  match expr with
  | some e => recExprNamesV env e
  | none => return none


def offSpringPairs(envIO: IO Environment)(excludePrefixes: List Name := [])
              : IO (List (Name × (List Name))) :=
  do
  let env ← envIO
  let keys ←  (constantNames envIO)
  let goodKeys := keys.filter fun name =>
    !(excludePrefixes.any (fun pfx => pfx.isPrefixOf name))
  let kv : List (Name × (List Name)) ←  (goodKeys).filterMapM $ 
      fun n => 
          do 
          let off ← offSpring?  env n
          match off with
          | some l =>  some (n, l)
          | none => none
        return kv

def offSpringTriple(envIO: IO Environment)(excludePrefixes: List Name := [])
              : IO (List (Name × (List Name) × (List Name) )) :=
  do
  let env ← envIO
  let keys ←  constantNameTypes  envIO
  let goodKeys := keys.filter fun (name, _) =>
    !(excludePrefixes.any (fun pfx => pfx.isPrefixOf name))
  let kv : List (Name × (List Name) × (List Name)) ←  (goodKeys).filterMapM $ 
      fun (n, type) => 
          do 
          let off ← offSpring?  env n
          match off with
          | some l => 
            if excludePrefixes.any (fun pfx => 
               l.any $ fun n => pfx.isPrefixOf n) then none
                else some (n, l, ← recExprNames env type)
          | none => none
        return kv

end ConstDeps

def nameCount(data: List (Name × (List Name) × (List Name) )): HashMap Name Nat := Id.run do
    let mut count := {}
    for (n, inTerm, inType) in data do
      for term in inTerm do
        if !(inType.contains term) then
        let c := (count.find? term).getD 0
        count := count.insert term (c+1)
    return count
        

def topNames(count : HashMap Name Nat)(limit: Nat): List (Name × Nat) :=
  (count.toArray.qsort $ fun (_, n1) (_, n2) => n1 > n2).toList.take limit
