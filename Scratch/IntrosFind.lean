import Scratch.ExprAppl
import Lean.Meta
open Lean
open Meta
open Lean.Elab.Tactic

syntax (name:= introsFind) "introsFind" (term)? : tactic
@[tactic introsFind] def introsfindImpl : Tactic :=
  fun stx  =>
  match stx with
  | `(tactic|introsFind) => 
    withMainContext do
      let mvar ← getMainGoal
      let ⟨intVars, codmvar⟩ ← Meta.intros mvar
      withMVarContext codmvar do
        let expVars := intVars.toList.map (fun x => mkFVar x)
        let target ←  getMVarType codmvar
        let oneStep ← applyPairsMeta expVars 
        let found ← typInList? target oneStep
        match found with
        | some x => 
          do
            assignExprMVar codmvar x
            replaceMainGoal []
            return ()
        | none => 
          throwTacticEx `findInSeq mvar m!"did not find {target} in sequence"
          return ()
  | `(tactic|introsFind $t) => 
    withMainContext do
      let n : Nat <- t.isNatLit?.getD 0
      let mvar ← getMainGoal
      let ⟨intVars, codmvar⟩ ← Meta.intros mvar
      withMVarContext codmvar do
        let expVars := intVars.toList.map (fun x => mkFVar x)
        let target ←  getMVarType codmvar
        let oneStep ← iterApplyPairsMeta n expVars 
        let found ← typInList? target oneStep
        match found with
        | some x => 
          do
            assignExprMVar codmvar x
            replaceMainGoal []
            return ()
        | none => 
          throwTacticEx `findInSeq mvar m!"did not find {target} in sequence"
          return ()
  | _ => Elab.throwIllFormedSyntax


def modusPonens {α β : Type} : α → (α → β) → β := by
      introsFind

def modus_ponens (α β : Prop) : α → (α → β) → β := by
      introsFind

#print modusPonens
#print modus_ponens

def constantFunction (α β : Type)  : α → β → α  := by
      introsFind

def constant_implication (α β : Prop)  : α → β → α := by
      introsFind

def reflImpl (α : Prop) : α → α  := by
      introsFind

def autoId (α : Type) : α → α := by
      introsFind 

#print autoId

theorem doubleMP{α β γ : Prop} : α → (α → β) →  (β →  γ) → γ  := by
      introsFind 2
