import Lean.Meta
import Scratch.Benchmark
open Lean Meta

-- Running tasks and reporting sync and async

def fib : Nat → Nat
| 0 => 1
| 1 => 1
| (n+2) => fib n + fib (n+1)

#time #eval fib 33 

def ll (n: Nat) : Nat :=
  dbgTrace ("fib " ++ toString n) $ fun _ => fib n

#time def fib6 (n: Nat) : IO Nat :=
  let t1 := Task.spawn (fun _ => ll (n + 3)) 
  let t2 := Task.spawn (fun _ => ll (n + 3))
  let t3 := Task.spawn (fun _ => ll (n + 2))
  let t4 := Task.spawn (fun _ => ll (n + 3))
  let t5 := Task.spawn (fun _ => ll (n + 2))
  let t6 := Task.spawn (fun _ => ll (n + 3))
  t1.get + t2.get + t3.get + t4.get + t5.get + t6.get 


#time #eval fib6 30


def lll : List Nat := List.range 20

#eval lll

syntax (name:= fibshow) "fib!" : term 

open Lean.Core
open Lean.Meta
open Lean.Elab.Term
open Lean

def hello (place: Syntax) : TermElabM Unit := do
    Lean.Elab.logInfoAt place "Hello, world!"

def hellos (place: Syntax) (n: Nat) : TermElabM Unit := 
  match n with
  | 0 => pure ()
  | m + 1 => do
    Lean.Elab.logInfoAt place m!"fib : {fib (m + 1)}"
    hellos place m

def natCons (n: Nat)(l: List Nat): List Nat := n :: l
def natNil: List Nat:= []

def showFibs (place: Syntax) (xs: List Nat) : TermElabM Expr :=
  match xs with
  | [] => return mkConst `natNil
  | x :: xs => do
    Lean.Elab.logInfoAt place m!"fib ({x}) = {fib x}"
    let tail ← showFibs place xs
    return ← mkAppM `natCons #[ToExpr.toExpr x, tail]


@[termElab fibshow] def elabFibShow : TermElab := 
  fun stx expectedType? => 
  match stx with
  | `(fib!%$tk) => do
      let expr ← showFibs tk (List.range 32)
      return expr
  | _ => Elab.throwIllFormedSyntax

def fib20  := fib!
#eval fib20

def Task.zip {α β : Type} (t1 : Task α) (t2 : Task β) : Task (α × β) :=
  t1.bind fun a => t2.map fun b => (a, b)
  -- Task.spawn (fun _ => (t1.get, t2.get)) (the automcomplete)