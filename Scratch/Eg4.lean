import Lean.Meta
import Lean.Elab
open Lean.Core
open Lean.Meta
open Lean.Elab.Term
open Lean

def mvarMeta4 : MetaM Expr := do
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

@[termElab minass] def minAssImpl4 : TermElab :=
  fun stx expectedType? =>
    do
      let e ← mvarMeta4
      return  e

def chkMinAss4  := minass!

#check chkMinAss4
#eval chkMinAss4 2

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


#check Eq.mp
#check congrArg

def rwPush  (mvarId : MVarId) (e : Expr) (heq : Expr) 
      (symm : Bool := false): TermElabM (Expr × Nat) :=
  do
    let t ← inferType e
    let rwr ← Meta.rewrite mvarId t heq symm
    let pf := rwr.eqProof
    let tt := rwr.eNew
    Elab.logInfo m!"mvars : {rwr.mvarIds.length}"
    let pushed ← mkAppM `Eq.mp #[pf, e]
    return (pushed, rwr.mvarIds.length)

open Lean.Elab.Tactic

syntax (name := rwPushTac) "rwPushTac" term "on" term : tactic
@[tactic rwPushTac] def rwPushImpl : Tactic :=
  fun stx  => 
  match stx with
  | `(tactic|rwPushTac $t on $s) =>
    withMainContext $
    do
      let mvarId ← getMainGoal
      let e ← Elab.Tactic.elabTerm s none
      let heq ← Elab.Tactic.elabTerm t none
      let (rw, l) ← rwPush mvarId e heq
      Elab.logInfo m!"obtained {rw}"
      if ← isDefEq (← inferType rw) (← getMainTarget) 
        then
        assignExprMVar mvarId rw
        replaceMainGoal [] 
        else 
        throwTacticEx `rwPushTac mvarId m!"rwPush failed"      
      return ()
  | _ => Elab.throwIllFormedSyntax

def pushEg {α : Type}{P: α → Type}{a b : α}(heq : a = b)(x : P a) : P b := by
    rwPushTac heq on x

#check @pushEg
#reduce @pushEg

def transPf {α : Type}{a b c : α}(f: α → Nat) :
          a = b → b = c → a = c := by
          intros h1  h2
          rwPushTac h2 on h1


#reduce transPf
