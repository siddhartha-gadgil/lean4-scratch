import Lean.Meta
import Lean.Elab
open Lean Meta Elab Tactic Core 
open Lean.Elab.Term

def sigmaTypeExpr? (eType: Expr) : TermElabM (Option (Expr × Expr)) :=
  do 
    let eType ← whnf eType
    let u ← mkFreshLevelMVar
    let v ← mkFreshLevelMVar
    let α ← mkFreshExprMVar (mkSort (mkLevelSucc u))
    let type ← mkArrow α (mkSort (mkLevelSucc v))
    let β  ← mkFreshExprMVar type
    let m := mkAppN (Lean.mkConst ``Sigma [u, v]) #[α, β]
    logInfo m!"m: {m}"
    logInfo m!"eType : {eType}"
    if ← isDefEq m eType
      then
        logInfo m!"unified"  
        logInfo m!"α : {← whnf α}"
        logInfo m!"β : {← whnf β}"
        return some (← whnf α , ← whnf β)
      else 
        logInfo m!"did not unify"
        return none

def existsTypeExpr? (eType: Expr) : TermElabM (Option (Expr × Expr)) :=
  do 
    let eType ← whnf eType
    let u ← mkFreshLevelMVar
    let v := levelZero
    let α ← mkFreshExprMVar (mkSort u)
    let type ← mkArrow α (mkSort v)
    let β  ← mkFreshExprMVar type
    let m := mkAppN (Lean.mkConst ``Exists [u]) #[α, β]
    logInfo m!"m: {m}"
    logInfo m!"eType : {eType}"
    if ← isDefEq m eType
      then
        logInfo m!"unified"  
        logInfo m!"α : {← whnf α}"
        logInfo m!"β : {← whnf β}"
        return some (← whnf α , ← whnf β)
      else 
        logInfo m!"did not unify"
        return none

syntax (name:= useTactic) "use" term : tactic
@[tactic useTactic] def useTacticImpl : Tactic :=
  fun stx => 
  match stx with
  | `(tactic|use $t) =>
    do
    let mvar ← getMainGoal 
    let eType ← getMainTarget
    let stOpt ← sigmaTypeExpr? eType
    match stOpt with
    | some (α , β) =>
      let a ← Tactic.elabTerm t α  
      let bType ← whnf  (mkApp β a)
      logInfo m!"bType : {bType}"
      let b ← mkFreshExprMVar bType
      logInfo m!"β : {β}"
      let exp ←  mkAppOptM `Sigma.mk #[α, β, a, b]
      assignExprMVar mvar exp
      replaceMainGoal [b.mvarId!]
      return ()
    | none => 
      let etOpt ← existsTypeExpr? eType
      match etOpt with
      | some (α , β) =>
      let a ← Tactic.elabTerm t α  
      let bType ← whnf  (mkApp β a)
      logInfo m!"bType : {bType}"
      let b ← mkFreshExprMVar bType
      logInfo m!"β : {β}"
      let exp ←  mkAppOptM `Exists.intro #[α, β, a, b]
      assignExprMVar mvar exp
      replaceMainGoal [b.mvarId!]
      return ()
      | none => 
        throwTacticEx `use mvar "use only works for Exists and Sigma types"
  | _ => throwIllFormedSyntax

def Tuple : Nat → Type 
 | Nat.zero => Unit
 | Nat.succ n => Nat × (Tuple n)

example: Σ n: Nat, Tuple n := by
        use 2
        exact (2, 3, ())

example : ∃ n: Nat, 3 ≤ n := by
        use 3
        apply Nat.le_refl

syntax (name := sigmaHead) "sigmaHead!" term : term
@[termElab sigmaHead] def sigmaHeadImpl : TermElab := fun stx expectedType =>
  match stx with
  | `(sigmaHead! $t) => 
    do
      let eType ← elabType t
      let ht ← sigmaTypeExpr? eType
      match ht with
      | some (h, t) => return t
      | none => return mkConst `Nat.zero       
  | _ => throwIllFormedSyntax


example : Tuple 2 := (2, 3, ())

def Ntuple : Type := Σ n: Nat, Tuple n

set_option pp.all true

#check Ntuple

def chkSgma := sigmaHead! (Σ n: Nat, Tuple n)

#check chkSgma
#check @Sigma.mk

syntax (name := existsHead) "existsHead!" term : term
@[termElab existsHead] def existsHeadImpl : TermElab := fun stx expectedType =>
  match stx with
  | `(existsHead! $t) => 
    do
      let eType ← elabType t
      let ht ← existsTypeExpr? eType
      match ht with
      | some (h, t) => return t
      | none => return mkConst `Nat.zero       
  | _ => throwIllFormedSyntax

def chkExists := existsHead! (∃ n: Nat, n = n)

-- reference example
def checkProdMeta : TermElabM Expr :=
  do
    let env ← getEnv
    let ee ← Term.mkConst `three3
    let u ← mkFreshLevelMVar
    let v ← mkFreshLevelMVar
    let α ← mkFreshExprMVar (mkSort u)
    let β  ← mkFreshExprMVar (mkSort v)
    let a ← mkFreshExprMVar α 
    let b ← mkFreshExprMVar β 
    let f := mkAppN (Lean.mkConst ``PProd.mk [u, v]) #[α, β, a, b]
    logInfo f
    if ← isDefEq f ee
      then
        logInfo m!"unified"  
        return b
      else 
        logInfo m!"did not unify"
        return a