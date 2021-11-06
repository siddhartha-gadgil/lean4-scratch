import Scratch.ExprRw
import Scratch.TermSeq
import Scratch.ConstDeps
import Lean.Meta
open Lean
open Meta
open Lean.Elab.Tactic
open Elab

def exprPieces : Expr → MetaM (List Expr)
  | Expr.app f a _ => 
    do 
      let ft ← inferType f
      let expl := ft.data.binderInfo.isExplicit
      if expl then
      (←  exprPieces f) ++ (← exprPieces a) ++ [f, a]
      else [f]
  | e => try 
            return [e]
        catch _ => []

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

syntax (name:= introsRwFind) "introsRwFind" (term ("save:" ident)?)?: tactic
@[tactic introsRwFind] def introsRwfindImpl : Tactic :=
  fun stx  =>
  match stx with
  | `(tactic|introsRwFind) => 
    introsRWAux 1 none
  | `(tactic|introsRwFind $t) => 
    withMainContext do
      let n : Nat <- t.isNatLit?.getD 0
      introsRWAux n none
  | `(tactic|introsRwFind $t save:$name) => 
    withMainContext do
      let n : Nat <- t.isNatLit?.getD 0
      let name ← name.getId
      introsRWAux n (some name)
  | _ => Elab.throwIllFormedSyntax
      where introsRWAux (n: Nat)(nameOpt: Option Name) : TacticM Unit :=
        withMainContext do
        let mvar ← getMainGoal
        let ⟨introVars, codmvar⟩ ← Meta.intros mvar
        withMVarContext codmvar do
          let introFreeVars := introVars.map (fun x => mkFVar x)
          let target ←  getMVarType codmvar
          logInfo m!"intros : {← types introFreeVars.toList}"
          let goalPieces ← exprPieces target 
          let goalNames ← ConstDeps.recExprNames (← getEnv) target
          logInfo m!"goalNames : {goalNames}"
          let evolved ← iterAppRWTask n  (introFreeVars) goalNames.toArray
          -- let unit ←  match nameOpt with
          --   | some name => saveExprArr name evolved
          --   | none => return ()
          -- logInfo m!"generated types : {← evolved.mapM (fun e => inferType e)}"
          -- logInfo m!"generated terms : {evolved}"
          let found ← evolved.findM? (fun e => do isDefEq (← inferType e) target)
      --     let found ← typInList? target evolved
          match found with
          | some x => 
            do
              logInfo m!"found : {x}"
              logInfo m!"found-type: {← inferType x}"
              assignExprMVar codmvar x
              replaceMainGoal []
              let unit ←  match nameOpt with
                | some name =>
                  let exported ← evolved.mapM (
                      fun e => mkLambdaFVars introFreeVars e) 
                  saveExprArr name exported
                | none => return ()
              return ()
          | none => 
            replaceMainGoal [codmvar]
            -- let value ← TermSeq.pack evolved.toList
            -- let type ← inferType value
            -- let name := `genpack
            -- liftMetaTactic $  addToContextM name type value 
            let unit ←  match nameOpt with
                | some name =>
                  let exported ← evolved.mapM (
                      fun e => mkLambdaFVars introFreeVars e) 
                  saveExprArr name exported
                | none => return ()
            return ()


def modusPonens : {α β : Type} →  α → (α → β) → β := by
      introsRwFind 1 save:blah

def modus_ponens (α β : Prop) : α → (α → β) → β := by
      introsRwFind

def blah := loadExprArr `blah

def blahTypes : TermElabM (Array Expr) := do 
    let es ←  blah
    return ← es.mapM (fun e => inferType e)

#eval blahTypes
#eval blah

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
        
