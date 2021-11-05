import Scratch.ExprAppl
import Lean.Meta
import Lean.Elab
import Std.Data.HashMap
open Std
open Lean
open Meta
open Elab

-- this is the wrong approach, so moved here


partial def rewriteAllAux(type lhs rhs : Expr): Expr → MetaM (Array Expr) := fun e =>
  match e with
 | Expr.app f a _ =>
    do
    let fs ← recRewrite f
    let as ← recRewrite a
    let mut es : Array Expr := #[]
    for f in fs do
      for a in as do
        try 
          es ← es.push (mkApp f a)
        catch _ =>
          ()
    es
 | Expr.lam name x y data => 
    do
      let xs ← recRewrite x
      let ys ← recRewrite y
      let mut es : Array Expr := #[]
      for x in xs do
        for y in ys do
          try 
            es ← es.push ((mkLambda name data.binderInfo x y))
          catch _ =>
            ()
      es
 | Expr.forallE name x y data => 
    do
      let xs ← recRewrite x
      let ys ← recRewrite y
      let mut es : Array Expr := #[]
      for x in xs do
        for y in ys do
          try 
            es ← es.push (mkForall name data.binderInfo x y)
          catch _ =>
            ()
      es  
 | Expr.letE _ x y z _ => #[e]
 | _ => #[e]
 where recRewrite : Expr → MetaM (Array Expr) := 
  fun e => do
    let mut es : Array Expr ←  rewriteAllAux type lhs rhs e
    if ← isDefEq e lhs then es := es.push rhs 
    if ← isDefEq e rhs then es := es.push lhs
    es

def rewriteAll (eq : Expr) : Expr → MetaM (Array Expr) :=
  match eq.eq? with
  | none => fun _ => #[]
  | some (type, lhs, rhs) => 
    fun e => 
    do
      let base ← rewriteAllAux type lhs rhs (← whnf e)
      let filtered ← base.filterM $ fun x => do !(← isDefEq e x)
      return filtered

open Term

syntax (name:= rwall) "rewriteAll%" term "at" term : term
@[termElab rwall] def rewriteAllImp : TermElab :=
  fun stx expectedType? =>
  match stx with
  | `(rewriteAll% $eq at $t) =>
    do
      let eqn ← Term.elabTerm eq none
      let x ← Term.elabTerm t none
      let rewritten ← rewriteAll (← inferType eqn) x
      logInfo m!"rewritten: {rewritten}" 
      return mkConst ``Unit.unit
  | _ => throwIllFormedSyntax

example (a b : Nat)(f: Nat → Nat  → Bool)(eq: a = b) : Unit :=
    let g := fun x : Nat => f a b
    rewriteAll% eq at g

inductive Letter where
  | α : Letter
  | α! : Letter

initialize exprCache : IO.Ref (HashMap Name Expr) ← IO.mkRef (HashMap.empty)

def getCached? (name : Name) : IO (Option (Expr)) := do
  let cache ← exprCache.get
  return (cache.find? name)

def cache (name: Name)(e: Expr)  : IO Unit := do
  let cache ← exprCache.get
  exprCache.set (cache.insert name e)
  return ()

def saveExpr (name: Name)(e: Expr) : TermElabM Expr := do
  let e ← whnf e
  Term.synthesizeSyntheticMVarsNoPostponing 
  let (e, _) ← Term.levelMVarToParam (← instantiateMVars e)
  cache name e
  return e

syntax (name:= saveexpr) "cache!" term "at" ident : term
@[termElab saveexpr] def cacheImp : TermElab :=
  fun stx expectedType? =>
  match stx with
  | `(cache! $t at $name) =>
    do
      let t ← Term.elabTerm t none false
      let name ← name.getId
      saveExpr name t
  | _ => throwIllFormedSyntax

#check @id

syntax (name:= loadexpr) "load!" ident :term
@[termElab loadexpr] def loadImp : TermElab :=
  fun stx expectedType? =>
  match stx with
  | `(load! $name) =>
    do
      let name ← name.getId
      let cache ← exprCache.get
      logInfo m!"loading: {name}"
      let e ← cache.find? name
      logInfo m!"loading {name} : {e}"
      match e with
      | some e =>
        logInfo m!"level mvar? {e.hasLevelMVar}"
        logInfo m!"level param? {e.hasLevelParam}" 
        return e
      | none => throwError "no such expression"
  | _ => throwIllFormedSyntax

-- L∃∀N 

#eval (#[1, 3, 5]).back