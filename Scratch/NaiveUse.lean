import Lean.Meta
import Lean.Elab
open Lean Meta Elab Tactic
open Lean.Elab.Term

def sigmaTypeExpr? (eType: Expr) : MetaM (Option (Expr × Expr)) :=
  do 
    let eType ← whnf eType
    let u ← mkFreshLevelMVar
    let v ← mkFreshLevelMVar
    let α ← mkFreshExprMVar (mkSort (mkLevelSucc u))
    let type ← mkArrow α (mkSort (mkLevelSucc v))
    let β  ← mkFreshExprMVar type
    let m := mkAppN (Lean.mkConst ``Sigma [u, v]) #[α, β]
    if ← isDefEq m eType
      then
        return some (← whnf α , ← whnf β)
      else 
        return none

def existsTypeExpr? (eType: Expr) : MetaM (Option (Expr × Expr)) :=
  do 
    let eType ← whnf eType
    let u ← mkFreshLevelMVar
    let v := levelZero
    let α ← mkFreshExprMVar (mkSort u)
    let type ← mkArrow α (mkSort v)
    let β  ← mkFreshExprMVar type
    let m := mkAppN (Lean.mkConst ``Exists [u]) #[α, β]
    if ← isDefEq m eType
      then
        return some (← whnf α , ← whnf β)
      else 
        return none

syntax (name:= naiveUseTactic) "naiveUse" term : tactic
@[tactic naiveUseTactic] def naiveUseTacticImpl : Tactic :=
  fun stx => 
  match stx with
  | `(tactic|naiveUse $t) =>
    do
    let mvar ← getMainGoal 
    let eType ← getMainTarget
    let stOpt ← sigmaTypeExpr? eType
    match stOpt with
    | some (α , β) =>
      let a ← Tactic.elabTerm t α  
      let bType ← whnf  (mkApp β a)
      let b ← mkFreshExprMVar bType
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
      let b ← mkFreshExprMVar bType
      let exp ←  mkAppOptM `Exists.intro #[α, β, a, b]
      assignExprMVar mvar exp
      replaceMainGoal [b.mvarId!]
      return ()
      | none => 
        throwTacticEx `naiveUse mvar "naiveUse only works for Exists and Sigma types"
  | _ => throwIllFormedSyntax

def Tuple : Nat → Type 
 | Nat.zero => Unit
 | Nat.succ n => Nat × (Tuple n)

example: Σ n: Nat, Tuple n := by
        naiveUse 2
        exact (2, 3, ())

example : ∃ n: Nat, 3 ≤ n := by
        naiveUse 3
        constructor


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
