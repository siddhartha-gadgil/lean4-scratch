import Lean
import Lean.Meta
-- https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/benchmarking.20commands/near/249677507


section
open Lean Elab Command

syntax (name := timeCmd)  "#time " command : command

@[commandElab timeCmd] def elabTimeCmd : CommandElab
  | `(#time%$tk $stx:command) => do
    let start ← IO.monoMsNow
    elabCommand stx
    logInfoAt tk m!"time: {(← IO.monoMsNow) - start}ms"
  | _ => throwUnsupportedSyntax

end

set_option maxRecDepth 200000 in
#time example : (List.range 5100).length = 5100 := rfl


def fib : Nat → Nat
| 0 => 1
| 1 => 1
| (n+2) => fib n + fib (n+1)

#time #eval fib 33 

def ll (n: Nat) : Nat :=
  dbgTrace ("ll " ++ toString n) $ fun _ => fib n

#time def l6 (n: Nat) : IO Nat :=
  let t1 := Task.spawn (fun _ => ll n) Task.Priority.dedicated 
  let t2 := Task.spawn (fun _ => ll (n + 1)) Task.Priority.dedicated
  let t3 := Task.spawn (fun _ => ll (n + 2)) Task.Priority.dedicated
  let t4 := Task.spawn (fun _ => ll (n + 3)) Task.Priority.dedicated
  let t5 := Task.spawn (fun _ => ll (n + 2)) Task.Priority.dedicated
  let t6 := Task.spawn (fun _ => ll (n + 1)) Task.Priority.dedicated
  return t1.get + t2.get + t3.get + t4.get + t5.get + t6.get 


#time #eval l6 30


def l : List Nat := List.range 20

#eval l

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