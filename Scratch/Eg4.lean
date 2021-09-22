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