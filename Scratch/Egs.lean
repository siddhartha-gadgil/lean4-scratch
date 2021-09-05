import Lean.Meta
import Lean.Elab
open Lean.Core
open Lean.Meta
open Lean.Elab.Term
open Lean

def lower (n : MetaM Nat) : CoreM Nat :=
  n.run' {}

def raise (n: CoreM Nat) : MetaM Nat :=
  do 
    let i <- n
    return i

-- copied from source

syntax (name := fooKind) "foo!" term : term

@[termElab fooKind] def elabFoo : TermElab :=
fun stx expectedType? => elabTerm (stx.getArg 1) expectedType?

#check foo! 10

def eg1 : Bool := foo! true

-- example of how to use the elaborator

syntax (name := addone) "addone!" (term)? : term

@[termElab addone] def addoneImpl : TermElab :=
fun stx expectedType? =>
  match stx with
  | `(addone! $s) => 
    do
      let s0 ← s
      let expr0 ←  elabTerm s0 (some (Lean.mkConst `Nat)) 
      let name2 : Name := `Nat.succ
      let expr : Expr :=  
        mkApp (Lean.mkConst name2)  expr0 
            -- the expression returned by a function
      return expr
  | _ =>
    do
      let name : Name := `Nat.zero
      let name2 : Name := `Nat.succ
      let expr : Expr :=  
        mkApp (Lean.mkConst name2)  (Lean.mkConst name) 
            -- the expression returned by a function
      return expr

def eg2 := addone! 10

#eval eg2
#eval addone!

def metaAddOne (n: MetaM Nat) : MetaM Nat :=
  do
    let i <- n
    return i + 1

