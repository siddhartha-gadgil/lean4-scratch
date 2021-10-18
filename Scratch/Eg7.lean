import Scratch.Eg6
import Scratch.Egs
import Scratch.Benchmark
import Lean
import Std.Data.HashMap
open Std

open Lean
open Lean.Meta
open Lean.Elab

-- experiments with subtypes, caching incomplete
-- correctly implemented in `ConstDeps`

#eval getX

#eval incX

#eval getX

#eval snapShot

#eval update snapShot

def ss := getXRef xx

#eval ss



#eval getX

def helloo := "Hello"

def hello.there := "Hello there"

def camel_case := ""

def Hello.camel_case := ""

def nameHead : Name → Name
 | Name.anonymous => Name.anonymous
 | Name.str n _ _ => n 
 | Name.num n _ _ => n

#eval nameHead `Nat.zero
#eval nameHead `xx.yy

def nameTails : Name → Option String
 | Name.anonymous => none
 | Name.str n s _ => some s
 | Name.num n _ _ => none

#eval nameTails `x.y.z

def isPrivate : Name →  Bool
 | Name.anonymous => false
 | Name.str n s _ => "_".isPrefixOf s || "match".isPrefixOf s || isPrivate n
 | Name.num n _ _ => true 

-- Better version from Sebastian Ulrich
def isBlackListed (declName : Name) : MetaM Bool := do
  let env ← getEnv
  declName.isInternal
  <||> isAuxRecursor env declName
  <||> isNoConfusion env declName
  <||> isRec declName
  <||> isMatcher declName

def isWhiteListed (declName : Name) : MetaM Bool := do
  let bl ← isBlackListed declName
  return !bl

def getExpr?: ConstantInfo →  Option Expr
  | ConstantInfo.defnInfo val => some val.value
  | ConstantInfo.thmInfo val => some val.value
  | _ => none

def envExpr : Environment → Name → Option Expr :=
  fun env name =>
      let info := (env.find? name)
      Option.bind info ConstantInfo.value?


def exprNames: Expr → List Name 
 | Expr.const name _ _  => [name]
 | Expr.app f a _ => (exprNames f ++ exprNames a).eraseDups
 | Expr.lam _ x y _ => (exprNames x ++ exprNames y).eraseDups
 | Expr.forallE _ x y _ => (exprNames x ++ exprNames y).eraseDups 
 | Expr.letE _ x y z _ => (exprNames x ++ exprNames y ++ exprNames z).eraseDups
 | _ => []

partial def recExprNames: Environment → Expr → MetaM (List Name) 
 | env, Expr.const name _ _  =>
    do
      if ← (isWhiteListed name) 
        then [name] 
        else
        if ← name.isInternal  then
          match envExpr env name with
          | some e => recExprNames env e
          | none => []
        else []        
 | env, Expr.app f a _ => 
        do  
          let s := ((← recExprNames env f) ++ (← recExprNames env a))
          return s.eraseDups
 | env, Expr.lam _ x y _ => 
        do
          return ((← recExprNames env x) ++ (← recExprNames env y)).eraseDups
 | env, Expr.forallE _ x y _ => do
        return  ((← recExprNames env x) ++ (← recExprNames env y)).eraseDups 
 | env, Expr.letE _ x y z _ => 
          return ((← recExprNames env x) ++ 
                    (← recExprNames env y) ++ (← recExprNames env z)).eraseDups
 | env, _ => []

partial def descendants : Nat → Environment → Name → List Name :=
  fun n env name =>
  match n with
  | 0 => []
  | m + 1 =>  
    match envExpr env name with
    | some e => 
      let offspring := exprNames e
      let desc := offspring.bind (descendants m env)
      (offspring ++ desc).eraseDups
    | none => []

initialize expOffCache : IO.Ref (HashMap Expr (List Name)) ←  IO.mkRef (HashMap.empty)

def getCached? (e : Expr) : MetaM (Option (List Name)) := do
  let cache ← expOffCache.get
  return (cache.find? e)

def cache (e: Expr) (offs : List Name) : MetaM Unit := do
  let cache ← expOffCache.get
  expOffCache.set (cache.insert e offs)
  return ()

def offSpring? : Bool →  Environment → Name → MetaM (Option (List Name)) :=
 fun clean env name =>
  do
   match envExpr env name with
   | some e =>
      let lookup ← getCached? e 
      match lookup with
      | some offs => return offs
      | none =>
        if clean then 
            -- let enames := exprNames e
            let fnames ← recExprNames env e
            cache e fnames
            return some fnames
          else
            let enames := exprNames e
            cache e enames
            return some enames
   | none => return none

def exprOffSpring : Bool →  Expr → MetaM (List Name) :=
  fun clean e =>
    do
    let lookup ← getCached? e 
        match lookup with
        | some offs => return offs
        | none =>
          if clean then 
              let enames := exprNames e
              let fnames ← enames.filterM (isWhiteListed)
              cache e fnames
              return fnames
            else
              let enames := exprNames e
              cache e enames
              return enames

def constsInfo : TermElabM (Nat × Nat) := 
  withReducible do 
    let env ← getEnv
    logInfo m!"main module : {env.mainModule}"
    let imps := env.allImportedModuleNames
    env.displayStats
    logInfo m!"imports: {imps}"
    let l1 ←  env.constants.map₁.toList.filterM (
      fun (n, _) => (isWhiteListed n))
    let n1 := l1.length
    let m2:= env.constants.map₂
    let l2 := m2.toList.map (fun (n, _) => n)
    let n2 := l2.length
    let ll ←  l2.filterM (fun n => isWhiteListed n)
    logInfo m!"local: {ll}"
    let name := `Nat.pred
    let natInfo := (env.find? name).get!
    let offspring ←  match getExpr? natInfo with
      | some e => (exprNames e).filterM (fun n => isWhiteListed n)
      | none => []
    let nat := natInfo.name
    logInfo m!"nat: {nat}"
    logInfo m!"offspring: {offspring}"
    let desc ← (descendants 4 env name).filterM (fun n => isWhiteListed n)
    logInfo m!"descendants: {desc}"
    return (n1, n2)

#eval constsInfo

#check Nat.lt_of_le_and_ne

#eval Name.mkStr `Nat "this"



def keyNames : MetaM (List Name) := do
  let env ← getEnv
  let keypairs ←  env.constants.map₁.toList.filterM (
    fun (n, _) => (isWhiteListed n))
  let keys := keypairs.map (fun (n, _) => n)
  return keys

def keyExprs : MetaM (Array (Name × Expr )) := do
  let env ← getEnv
  
  let keypairs ←  env.constants.map₁.toArray.filterM (
    fun (n, _) => (isWhiteListed n))
  let keys := keypairs.filterMap (
      fun (n, cf) => (getExpr? cf).map (fun e => (n, e)))
  return keys

def offSpringPairs(start: Nat)(bound : Nat)(clean: Bool) : MetaM (Nat × List (Name × (List Name))) :=
  withReducible do 
  let env ← getEnv
  let keys ←  keyNames
  let kv : List (Name × (List Name)) ←  ((keys.drop start).take bound).filterMapM $ 
      fun n => 
          do 
          let off ← offSpring? clean env n
          match off with
          | some l =>  some (n, l.eraseDups)
          | none => none
        return (keys.length, kv)

def offSpringPairsDirect(start: Nat)(bound : Nat)(clean: Bool) : MetaM (Nat × List (Name × (List Name))) :=
  withReducible do 
  let env ← getEnv
  let keyArr ←  keyExprs
  let keys := keyArr.toList
  let kv : List (Name × (List Name)) ←  ((keys.drop start).take bound).mapM $ 
      fun (n, expr) => 
          do 
          let off ← exprOffSpring clean expr
          return (n, off.eraseDups)
        return (keys.length, kv)
