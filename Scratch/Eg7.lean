import Scratch.Eg6
import Scratch.Egs
import Lean

open Lean
open Lean.Meta
open Lean.Elab

#eval getX

#eval incX

#eval getX

#eval snapShot

#eval update snapShot

def ss := getXRef xx

#eval ss



#eval getX

def hello := "Hello"

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

def getExpr: ConstantInfo →  Option Expr
  | ConstantInfo.defnInfo val => some val.value
  | ConstantInfo.thmInfo val => some val.value
  | _ => none

def envExpr : Environment → Name → Option Expr :=
  fun env name =>
      let info := (env.find? `Nat.le_total).get!
      Option.bind info getExpr


def exprNames: Expr → List Name 
 | Expr.const name _ _  => [name]
 | Expr.app f a _ => (exprNames f ++ exprNames a).eraseDups
 | Expr.lam _ x y _ => (exprNames x ++ exprNames y).eraseDups
 | Expr.forallE _ x y _ => (exprNames x ++ exprNames y).eraseDups 
 | Expr.letE _ x y z _ => (exprNames x ++ exprNames y ++ exprNames z).eraseDups
 | _ => []

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

def constsInfo : TermElabM (Nat × Nat) := 
  withReducible do 
    let env ← getEnv
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
    let offspring ←  match getExpr natInfo with
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

