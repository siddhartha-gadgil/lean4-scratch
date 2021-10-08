import Scratch.ExprRw
import Lean.Meta
open Lean
open Meta
open Lean.Elab.Tactic
open Elab

def types : List Expr → MetaM (List Expr) :=
    fun l =>
    match l with
    | [] => return []
    | h::t => do
      let h ← inferType h
      let t ← types t
      return (h::t)

syntax (name:= introsRwFind) "introsRwFind" (term)? : tactic
@[tactic introsRwFind] def introsfindImpl : Tactic :=
  fun stx  =>
  match stx with
  | `(tactic|introsRwFind) => 
    withMainContext do
      let mvar ← getMainGoal
      let ⟨intVars, codmvar⟩ ← Meta.intros mvar
      withMVarContext codmvar do
        let expVars := intVars.toList.map (fun x => mkFVar x)
        let target ←  getMVarType codmvar
        logInfo m!"intros : {← types expVars}"
        let oneStep ← iterAppRWM 1 codmvar expVars 
        logInfo m!"generated : {← types oneStep}"
        let found ← typInList? target oneStep
        match found with
        | some x => 
          do
            assignExprMVar codmvar x
            replaceMainGoal []
            return ()
        | none => 
          throwTacticEx `introsRwFind mvar m!"did not find {target} in sequence"
          return ()
  | `(tactic|introsRwFind $t) => 
    withMainContext do
      let n : Nat <- t.isNatLit?.getD 0
      let mvar ← getMainGoal
      let ⟨intVars, codmvar⟩ ← Meta.intros mvar
      withMVarContext codmvar do
        let expVars := intVars.toList.map (fun x => mkFVar x)
        let target ←  getMVarType codmvar
        logInfo m!"intros : {← types expVars}"
        let oneStep ← iterAppRWM n codmvar expVars 
        logInfo m!"generated : {← types oneStep}"
        let found ← typInList? target oneStep
        match found with
        | some x => 
          do
            assignExprMVar codmvar x
            replaceMainGoal []
            return ()
        | none => 
          throwTacticEx `introsRwFind mvar m!"did not find {target} in sequence"
          return ()
  | _ => Elab.throwIllFormedSyntax

syntax (name:= introsRwView) "introsRwView" (term)? : tactic
@[tactic introsRwView] def introsViewImpl : Tactic :=
  fun stx  =>
  match stx with
  | `(tactic|introsRwView) => 
    withMainContext do
      let mvar ← getMainGoal
      let ⟨intVars, codmvar⟩ ← Meta.intros mvar
      withMVarContext codmvar do
        let expVars := intVars.toList.map (fun x => mkFVar x)  
        let target ←  getMVarType codmvar
        logInfo m!"intros : {← types expVars}"
        let oneStep ← iterAppRWM 1 codmvar expVars 
        logInfo m!"generated : {← types oneStep}"
        return ()
  | `(tactic|introsRwView $t) => 
    withMainContext do
      let n : Nat <- t.isNatLit?.getD 0
      let mvar ← getMainGoal
      let ⟨intVars, codmvar⟩ ← Meta.intros mvar
      withMVarContext codmvar do
        let expVars := intVars.toList.map (fun x => mkFVar x)
        let target ←  getMVarType codmvar
        let oneStep ← iterAppRWM n codmvar expVars 
        logInfo m!"generated : {← types oneStep}"
        return ()
  | _ => Elab.throwIllFormedSyntax


def modusPonens {α β : Type} : α → (α → β) → β := by
      introsRwFind

def modus_ponens (α β : Prop) : α → (α → β) → β := by
      introsRwFind

#print modusPonens
#print modus_ponens

def constantFunction (α β : Type)  : α → β → α  := by
      introsRwFind

def constant_implication (α β : Prop)  : α → β → α := by
      introsRwFind

def reflImpl (α : Prop) : α → α  := by
      introsRwFind

def autoId (α : Type) : α → α := by
      introsRwFind 

#print autoId

theorem doubleMP{α β γ : Prop} : α → (α → β) →  (β →  γ) → γ  := by
      introsRwFind 2

def transPf {α : Type}{a b c : α}(f: α → Nat) :
          a = b → b = c → a = c := by
          introsRwFind

theorem idsEqual{μ : Type}{mul: μ → μ → μ}:
      (eₗ : μ) → (eᵣ : μ) → (leftId : (x : μ ) →  mul eₗ x = x) → 
      (rightId : (x : μ ) →  mul x eᵣ = x) →
      eₗ = eᵣ := by 
        introsRwFind 2
