import Scratch.ExprRw
import Scratch.TermSeq
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

def factorThrough(α : Sort u) (β : Sort v)(b : β ) : (β  → α ) → α   := 
    fun g => g b

def addToContextM(name: Name) (type : Expr)(value: Expr) : 
     MVarId → MetaM (List MVarId) :=
  fun m => 
      do
        let target ← getMVarType m
        let exp ← mkAppM `factorThrough #[target, type, value]
        let appGoalList ←  apply m exp
        let appGoal := appGoalList.head!
        let ⟨_, introGoal⟩ ←  intro appGoal name  
        return [introGoal]



def addAllToContextM (values : List Expr) : 
     MVarId → MetaM (List MVarId) :=
     match values with
      | [] => fun m => return [m]
      | h::t => fun m => 
        do
          let newMVarIds ← addToContextM Name.anonymous (← inferType h) h m
          addAllToContextM t newMVarIds.head!

syntax (name:= introsRwFind) "introsRwFind" (term)? : tactic
@[tactic introsRwFind] def introsRwfindImpl : Tactic :=
  fun stx  =>
  match stx with
  | `(tactic|introsRwFind) => 
    introsRWAux 1
  | `(tactic|introsRwFind $t) => 
    withMainContext do
      let n : Nat <- t.isNatLit?.getD 0
      introsRWAux n
  | _ => Elab.throwIllFormedSyntax
      where introsRWAux (n: Nat) : TacticM Unit :=
        withMainContext do
        let mvar ← getMainGoal
        let ⟨introVars, codmvar⟩ ← Meta.intros mvar
        withMVarContext codmvar do
          let introFreeVars := introVars.toList.map (fun x => mkFVar x)
          let target ←  getMVarType codmvar
          logInfo m!"intros : {← types introFreeVars}"
          let oneStep ← iterAppRWMTask n codmvar introFreeVars 
          logInfo m!"generated : {← types oneStep}"
          let found ← typInList? target oneStep
          match found with
          | some x => 
            do
              assignExprMVar codmvar x
              replaceMainGoal []
              return ()
          | none => 
            replaceMainGoal [codmvar]
            let value ← TermSeq.pack oneStep
            let type ← inferType value
            let name := `genpack
            liftMetaTactic $  addToContextM name type value 
            return ()

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
        
