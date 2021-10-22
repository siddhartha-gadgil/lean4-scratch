import Scratch.ExprAppl
import Lean.Meta
import Lean.Elab
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
