import Lean.Meta
import Lean.Elab
import Scratch.IntrosRwFind
open Lean
open Meta
open Lean.Elab.Tactic
open Elab
open introsRwFind

-- copied from source


def g (x : Nat) : Nat :=
dbgTrace ("g: " ++ toString x) $ fun _ =>
  x + 1

def f1 (x : Nat) : Nat :=
dbgSleep 1000 $ fun _ =>
dbgTrace ("f1: " ++ toString x) $ fun _ =>
  g (x + 1)

def f2 (x : Nat) : Nat :=
dbgSleep 100 $ fun _ =>
dbgTrace ("f2: " ++ toString x) $ fun  _ =>
  g x

def tst (n : Nat) : IO Nat :=
let t1 := Task.spawn fun _ => f1 n;
let t2 := Task.spawn fun _ => f2 n;
dbgSleep 1000 $ fun _ =>
IO.println (toString t1.get ++ " " ++ toString t2.get) *>
pure t1.get

#eval tst 10

#check tst 20

syntax (name:= tasktac) "tasktac" : tactic
@[tactic tasktac] def tasktacImp : Tactic :=
  fun stx =>
    do 
      let res ← tst 20
      let value ← ToExpr.toExpr res
      logInfo m!"got {res}"
      let type := mkConst `Nat
      liftMetaTactic $  addToContextM `result type value 
      return ()

def tt : Nat := by
  tasktac
  exact result

#eval tt

def tstDirect(n: Nat) : Nat :=
   let t1 := Task.spawn fun _ => n * 2
   let t2 := Task.spawn fun _ => n * 3
   t1.get + t2.get

#eval tstDirect 3
