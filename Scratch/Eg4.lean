import Lean.Meta
import Lean.Elab
open Lean.Core
open Lean.Meta
open Lean.Elab.Term
open Lean

def mvarMeta : MetaM Expr := do
  let mvar ← mkFreshExprMVar (some (mkConst ``Nat))
  let mvarId := mvar.mvarId!
  let mvar2 ← mkFreshExprMVar (some (mkConst ``Nat)) -- none works too
  let mvarId2 := mvar2.mvarId!
  assignExprMVar mvarId2 (mkApp (mkConst `Nat.succ) mvar) -- eg tactic returns mvar seeking mvar2
  withLocalDecl Name.anonymous BinderInfo.default (mkConst ``Nat)  $ fun x => 
  do
    assignExprMVar mvarId x
    let q ← mkLambdaFVars #[x] mvar2
    return q

syntax (name := minass) "minass!" : term

@[termElab minass] def minAssImpl : TermElab :=
  fun stx expectedType? =>
    do
      let e ← mvarMeta
      return  e

def chkMinAss  := minass!

#check chkMinAss
#eval chkMinAss 2

theorem zero_add : (n : Nat) →  0 + n = n := by
  intro n
  induction n
  case zero => rfl
  case succ n ih => rw [Nat.add_succ, ih]

open Nat

def recFn : Nat → Nat := 
  fun n =>
  match n with
   | zero =>  zero
   | succ n  =>  succ (recFn n)
  /-
  Nat.brecOn n
    fun n f =>
      (match n : (n : Nat) → Nat.below n → Nat with 
        | zero => fun x => zero
        | succ n => fun x => succ x.fst.fst)
        f
-/
/-by
  intro n
  match n with
   | zero => exact zero
   | succ n  => exact succ (recFn n)
-/
#print recFn

#check Nat.rec
#check Nat.below