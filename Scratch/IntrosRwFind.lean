import Scratch.ExprRw
import Scratch.TermSeq
import Scratch.ConstDeps
import Lean.Meta
open Lean
open Meta
open Lean.Elab.Tactic
open Elab

def whiteListed (n: Name) : TermElabM Bool := do
  let b ← ConstDeps.isWhiteListed (← getEnv) n
  return b

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

def generateSeek(n: Nat)(saveOpt: Option Name)
      (initState: Array Expr)(goalNames : List Name)(mvar: MVarId)
      (dynamics : Nat → Array Expr → Array Name → TermElabM (Array Expr)) : TacticM Unit :=
              withMVarContext mvar do
          -- logInfo m!"intros : {← types introFreeVars.toList}"
          let target ←  getMVarType mvar
          let init := initState
          let baseEvolved ← dynamics n  init goalNames.toArray
          -- logInfo m!"evolved elements: {baseEvolved.size}"
          let mut evolved : Array Expr := #[]
          -- let mut evolvedTypes : Array Expr := #[]
          for e in baseEvolved do
            let exp ← whnf $ ← reduce e
            unless evolved.contains exp do
              evolved :=  evolved.push exp
            let type ← inferType exp
            let type ← whnf $ ← reduce type
          let lctx ← getLCtx
          let fvarIds ← lctx.getFVarIds
          let fvIds ← fvarIds.filterM $ fun fid => whiteListed ((lctx.get! fid).userName) 
          let fvars := fvIds.map mkFVar
          let exported ← evolved.mapM (
                      fun e => mkLambdaFVars fvars e) 
          let found ← evolved.findM? (fun e => do isDefEq (← inferType e) target)
          match found with
          | some x => 
            do
              -- logInfo m!"found : {x}"
              -- logInfo m!"found-type: {← inferType x}"
              assignExprMVar mvar x
              replaceMainGoal []
          | none => 
            replaceMainGoal [mvar]
          match saveOpt with
            | some name => saveExprArr name exported
            | none => return ()
          return ()

syntax (name:= introsRwFind) "introsRwFind" (num ("save:" ident)?)?: tactic
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
      where introsRWAux (n: Nat)(saveOpt: Option Name) : TacticM Unit :=
        withMainContext do
        let mvar ← getMainGoal
        let goalNames ← ConstDeps.recExprNames (← getEnv) (← getMainTarget)
        let ⟨introVars, codmvar⟩ ← Meta.intros mvar
        let introFreeVars := introVars.map (fun x => mkFVar x)
        logInfo m!"goalNames : {goalNames}"
        generateSeek n saveOpt introFreeVars goalNames codmvar iterAppRWTask

syntax (name:= polyFind) "polyFind" ("#⟨" term,* "⟩")? (("load:" ident)? num
      ("save:" ident)?)?: tactic
@[tactic polyFind] def polyfindImpl : Tactic :=
  fun stx  =>
  match stx with
  | `(tactic|polyFind #⟨$[$xs:term],*⟩) => 
    withMainContext do
    let initState ←  xs.mapM (fun x => elabTerm x none)
    polyFindAux  initState 1 none
  | `(tactic|polyFind #⟨$[$xs:term],*⟩ $t:numLit) => 
    withMainContext do
      let initState ←  xs.mapM (fun x => elabTerm x none)
      let n : Nat <- t.isNatLit?.getD 0
      polyFindAux  initState n none
  | `(tactic|polyFind #⟨$[$xs:term],*⟩ $t:numLit save:$name) => 
    withMainContext do
      let initState ←  xs.mapM (fun x => elabTerm x none)
      let n : Nat <- t.isNatLit?.getD 0
      let name ← name.getId
      polyFindAux  initState n (some name)
  | `(tactic|polyFind  load:$name $t:numLit) => 
    withMainContext do
      let n : Nat <- t.isNatLit?.getD 0
      let name ← name.getId
      let initState ← loadedState name
      polyFindAux initState n none
  | `(tactic|polyFind load:$name $t:numLit save:$nameSave) => 
    withMainContext do
      let n : Nat <- t.isNatLit?.getD 0
      let name ← name.getId      
      let initState ← loadedState name
      polyFindAux  initState n (some nameSave.getId)
  | _ => Elab.throwIllFormedSyntax
      where 
      polyFindAux  (initState: Array Expr) 
          (n: Nat)(saveOpt: Option Name) : TacticM Unit :=
        withMainContext do
        let mvar ← getMainGoal
        let goalNames ← ConstDeps.recExprNames (← getEnv) (← getMainTarget)
        generateSeek n saveOpt  initState goalNames mvar iterAppRWTask
      loadedState (name : Name) : TacticM (Array Expr) := 
        withMainContext do
        let loadState ← loadExprArr name
        let lctx ← getLCtx
        let fvarIds ← lctx.getFVarIds
        let fvIds ← fvarIds.filterM $ fun fid => whiteListed ((lctx.get! fid).userName) 
        let fvars := fvIds.map mkFVar
        loadState.mapM $ fun e => reduce (mkAppN e fvars)

def modusPonens : {α β : Type} →  α → (α → β) → β := by
      introsRwFind 1 save:blah

example {α β : Type} : α → (α → β) → β := by
    intros x f
    polyFind #⟨x, f⟩ 

def modus_ponens (α β : Prop) : α → (α → β) → β := by
      introsRwFind

def blah := loadExprArr `blah

def blahTypes : TermElabM (Array Expr) := do 
    let es ←  blah
    return ← es.mapM (fun e => inferType e)

-- #eval blahTypes
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
        
example {μ : Type}{mul: μ → μ → μ}:
      (eₗ : μ) → (eᵣ : μ) → (leftId : (x : μ ) →  mul eₗ x = x) → 
      (rightId : (x : μ ) →  mul x eᵣ = x) → 
      eₗ = eᵣ := by
        intros eₗ eᵣ lid rid
        polyFind #⟨eₗ, eᵣ, lid, rid⟩ 2 save:poly

example {μ : Type}{mul: μ → μ → μ}:
      (eₗ : μ) → (eᵣ : μ) → (leftId : (x : μ ) →  mul eₗ x = x) → 
      (rightId : (x : μ ) →  mul x eᵣ = x) → 
      eₗ = eᵣ := by
        intros eₗ eᵣ lid rid
        polyFind #⟨eₗ, eᵣ, lid, rid⟩ 1 save:poly1
        polyFind load:poly1 1 save:poly2

-- deducing from equalities

syntax (name:= eqDeduc) "eqDeduc" ("#⟨" term,* "⟩") (num ("eqs:" ident)) ("save:" ident)?: tactic
@[tactic eqDeduc] def eqDeducImpl : Tactic :=
  fun stx  =>
  match stx with
  | `(tactic|eqDeduc #⟨$[$xs:term],*⟩ $t eqs: $name) => 
    withMainContext do
      let introFreeVars ←  xs.mapM (fun x => elabTerm x none)
      let n : Nat <- t.isNatLit?.getD 0
      let name ← name.getId
      let loadState ← loadExprArr name
      let lctx ← getLCtx
      let fvarIds ← lctx.getFVarIds
      let fvIds ← fvarIds.filterM $ fun fid => whiteListed ((lctx.get! fid).userName) 
      let fvars := fvIds.map mkFVar
      let prevState ← loadedState name
      let goalNames ← ConstDeps.recExprNames (← getEnv) (← getMainTarget)
      let dynamics : Nat → Array Expr → Array Name → TermElabM (Array Expr) :=
        fun m init names => eqIsles prevState 
        (fun list => (iterAppRWTask m list names)) init.toList
      let mvar ← getMainGoal
      generateSeek n none  introFreeVars goalNames mvar dynamics
  | `(tactic|eqDeduc #⟨$[$xs:term],*⟩ $t eqs: $name save:$saveName) => 
    withMainContext do
      let introFreeVars ←  xs.mapM (fun x => elabTerm x none)
      let n : Nat <- t.isNatLit?.getD 0
      let name ← name.getId
      let loadState ← loadExprArr name
      let lctx ← getLCtx
      let fvarIds ← lctx.getFVarIds
      let fvIds ← fvarIds.filterM $ fun fid => whiteListed ((lctx.get! fid).userName) 
      let fvars := fvIds.map mkFVar
      let prevState ← loadedState name
      let goalNames ← ConstDeps.recExprNames (← getEnv) (← getMainTarget)
      let dynamics : Nat → Array Expr → Array Name → TermElabM (Array Expr) :=
        fun m init names => eqIsles prevState 
        (fun list => (iterAppRWTask m list names)) init.toList
      let mvar ← getMainGoal
      generateSeek n (some saveName.getId) introFreeVars goalNames mvar dynamics
  | _ => Elab.throwIllFormedSyntax
  where
    loadedState (name: Name) : TacticM (Array Expr) := 
    withMainContext do
      let loadState ← loadExprArr name
      let lctx ← getLCtx
      let fvarIds ← lctx.getFVarIds
      let fvIds ← fvarIds.filterM $ fun fid => whiteListed ((lctx.get! fid).userName) 
      let fvars := fvIds.map mkFVar
      loadState.mapM $ fun e => do whnf $ ← reduce $ mkAppN e fvars

syntax (name:= lookup) "lookup"  ident: tactic
@[tactic lookup] def lookupImpl : Tactic :=
  fun stx  =>
  match stx with
  | `(tactic| lookup $name) => 
    withMainContext do
      let name ← name.getId
      let loadState ← loadExprArr name
      let lctx ← getLCtx
      let fvarIds ← lctx.getFVarIds
      let fvIds ← fvarIds.filterM $ fun fid => whiteListed ((lctx.get! fid).userName) 
      let fvars := fvIds.map mkFVar
      let memo ← loadState.mapM $ fun e => do whnf $ ← reduce $ mkAppN e fvars
      let mvar ← getMainGoal
      let target ← getMainTarget
      let found ← memo.findM? (fun e => do isDefEq (← inferType e) target)
          match found with
          | some x => 
            do
              -- logInfo m!"found : {x}"
              -- logInfo m!"found-type: {← inferType x}"
              assignExprMVar mvar x
              replaceMainGoal []
          | none => 
            replaceMainGoal [mvar]
          return ()
  | _ =>  Elab.throwIllFormedSyntax

syntax (name:= propeqs) "propeqs"  ident: tactic
@[tactic propeqs] def propeqsImpl : Tactic :=
  fun stx  =>
  match stx with
  | `(tactic| propeqs $name) => 
    withMainContext do
      let name ← name.getId
      let loadState ← loadExprArr name
      let lctx ← getLCtx
      let fvarIds ← lctx.getFVarIds
      let fvIds ← fvarIds.filterM $ fun fid => whiteListed ((lctx.get! fid).userName) 
      let fvars := fvIds.map mkFVar
      let initState ← loadState.mapM $ fun e => do whnf $ ← reduce $ mkAppN e fvars
      let mvar ← getMainGoal
      let target ← getMainTarget
      let evolved ← propagateEqualities initState
      let found ← evolved.findM? (fun e => do isDefEq (← inferType e) target)
          match found with
          | some x => 
            do
              logInfo m!"found : {x}"
              logInfo m!"found-type: {← inferType x}"
              assignExprMVar mvar x
              replaceMainGoal []
          | none => 
            replaceMainGoal [mvar]
          return ()
  | _ =>  Elab.throwIllFormedSyntax