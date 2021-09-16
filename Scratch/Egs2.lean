import Lean.Meta
import Lean.Elab
open Lean.Core
open Lean.Meta
open Lean.Elab.Term
open Lean

def syntaxPreProcess (stx: Syntax) : MacroM Syntax :=
  match stx with
  | `(this! $s) =>  `(- $s)
  | `($s $t) =>   `($t $s)
  | s => s

open Nat

def natExpr : Nat → Expr 
  | zero => mkConst `Nat.zero
  | succ k => mkApp (mkConst `Nat.succ) (natExpr k)

#eval natExpr 3

partial def exprNat : Expr → MetaM Nat := fun expr => 
  do
    let mvar ←  mkFreshExprMVar (some (mkConst ``Nat))
    let sExp := mkApp (mkConst `Nat.succ) mvar
    if ← isDefEq sExp expr then
      let prev ← exprNat mvar
      return succ (succ prev)
    else 
      return zero

#check exprNat (natExpr 3)
#eval exprNat (natExpr 3)

def m30 := exprNat (natExpr 30)
#check m30
#eval m30
