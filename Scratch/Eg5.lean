import Lean.Meta
import Lean.Elab
import Scratch.IntrosRwFind
open Lean
open Meta
open Lean.Elab.Tactic
open Elab
open introsRwFind

-- copied from source


def g (x : Nat) : Nat :=
dbgTrace ("g: " ++ toString x) $ fun _ =>
  x + 1

def f1 (x : Nat) : Nat :=
dbgSleep 1000 $ fun _ =>
dbgTrace ("f1: " ++ toString x) $ fun _ =>
  g (x + 1)

def f2 (x : Nat) : Nat :=
dbgSleep 100 $ fun _ =>
dbgTrace ("f2: " ++ toString x) $ fun  _ =>
  g x

def tst (n : Nat) : IO Nat :=
let t1 := Task.spawn fun _ => f1 n;
let t2 := Task.spawn fun _ => f2 n;
dbgSleep 1000 $ fun _ =>
IO.println (toString t1.get ++ " " ++ toString t2.get) *>
pure t1.get

#eval tst 10

#check tst 20

syntax (name:= tasktac) "tasktac" : tactic
@[tactic tasktac] def tasktacImp : Tactic :=
  fun stx =>
    do 
      let res ← tst 20
      let value ← ToExpr.toExpr res
      logInfo m!"got {res}"
      let type := mkConst `Nat
      liftMetaTactic $  addToContextM `result type value 
      return ()

def tt : Nat := by
  tasktac
  exact result

#eval tt

def tstDirect(n: Nat) : Nat :=
   let t1 := Task.spawn fun _ => n * 2
   let t2 := Task.spawn fun _ => n * 3
   t1.get + t2.get

#eval tstDirect 3

def egRef := IO.mkRef 3

def egRefVal : IO Nat :=
  do
    let ref ← egRef
    let val ← ref.get
    return val

#eval egRefVal

def doubleEgRef : IO Nat :=
  do
    let ref ← egRef
    let val ← ref.get
    ref.set (val * 2)
    let val2 ← ref.get
    return val2

def egRefVal2 : IO Nat :=
  do
    let ref ← egRef
    let val ← ref.get
    return val

#eval egRefVal2
#eval doubleEgRef 

open Lean.Elab.Term

-- copied from source, removed error registering and so syntax
/- whnfCore + implicit consumption.
   Example: given `e` with `eType := {α : Type} → (fun β => List β) α `, it produces `(e ?m, List ?m)` where `?m` is fresh metavariable. -/
partial def consumeImplicits  (e eType : Expr) (hasArgs : Bool) : 
          TermElabM (Expr × Expr) := do
  let eType ← whnfCore eType
  match eType with
  | Expr.forallE n d b c =>
    if c.binderInfo.isImplicit || (hasArgs && c.binderInfo.isStrictImplicit) then
      let mvar ← mkFreshExprMVar d
      consumeImplicits (mkApp e mvar) (b.instantiate1 mvar) hasArgs
    else if c.binderInfo.isInstImplicit then
      let mvar ← mkInstMVar d
      let r := mkApp e mvar
      consumeImplicits  r (b.instantiate1 mvar) hasArgs
    else match d.getOptParamDefault? with
      | some defVal => 
          consumeImplicits (mkApp e defVal) (b.instantiate1 defVal) hasArgs
      -- TODO: we do not handle autoParams here.
      | _ => pure (e, eType)
  | _ => pure (e, eType)

partial def lambdaImplicits  (e  : Expr) (hasArgs : Bool) : 
          TermElabM Expr := do
  let eType ← inferType e
  let eType ← whnfCore eType
  match eType with
  | Expr.forallE n d b c =>
    if c.binderInfo.isImplicit || (hasArgs && c.binderInfo.isStrictImplicit) then
      withLocalDecl Name.anonymous BinderInfo.default d  $ fun x => 
        do
          let prev ← lambdaImplicits (mkApp e x)  hasArgs
          return ←  mkLambdaFVars #[x] prev
    else if c.binderInfo.isInstImplicit then
      withLocalDecl Name.anonymous BinderInfo.default d  $ fun x => 
        do
          let prev ← lambdaImplicits (mkApp e x)  hasArgs
          return ←  mkLambdaFVars #[x] prev

    else match d.getOptParamDefault? with
      | some defVal => 
          lambdaImplicits (mkApp e defVal)  hasArgs
      -- TODO: we do not handle autoParams here.
      | _ => pure e
  | _ => pure e


def getFnsAux : Expr → List Expr → List Expr
  | Expr.app f a _, l  => getFnsAux f (f :: a :: l) 
  | e, l => e :: l

def getFnsArgs : Expr → List Expr
  | e => getFnsAux e []

def consImpl (e: Expr) : TermElabM Expr := do
  let eType ← inferType e
  let (e, eType) ← consumeImplicits e eType true
  return e

def lamImpl (e: Expr) : TermElabM Expr := do
  let e ← lambdaImplicits e  true
  return e

universe u

inductive Singleton (α : Type u): α →  Type u where
  | mk :  (a : α) → Singleton α  a
  
def Singleton.value {α : Type u}{a: α} : Singleton α  a → α 
  | Singleton.mk a => a

def mkSingleton : (α : Type u) → (a : α) → Singleton α a :=
  fun α a => Singleton.mk a

def egSing := Singleton.mk 10

#check egSing

#check @Singleton.value

#eval egSing.value

def pad (s: String)(n: Nat) : String :=
  match n with
  | 0 => s
  | m + 1 => s ++ ⟨Char.ofNat (64 + n) :: []⟩

def addSingsToContextM (values : List Expr) : 
     MVarId → TermElabM (List MVarId) :=
     match values with
      | [] => fun m => 
      return [m]
      | h::t => fun m => 
        do
          let f := Lean.mkConst `mkSingleton
          let htype ← inferType h
          let exprOpt : Option Expr ← 
            try
              let expr ←  mkAppM `mkSingleton #[htype, h]
              some expr
            catch _ => none
          match exprOpt with
          | some expr =>
            let n := values.length
            let name := Name.mkSimple (pad "piece" n)
            let newMVarIds ← addToContextM name (← inferType expr) expr m
            addSingsToContextM t newMVarIds.head!
          | none => 
            addSingsToContextM t m

syntax (name:= exppieces) "exppieces" : tactic
@[tactic exppieces] def exppiecesImp : Tactic :=
  fun stx =>
    withMainContext
    do
      let e ← getMainTarget 
      let eType ← inferType e
      let pieces ← getFnsArgs e
      logInfo m!"got {pieces}"
      let fedPieces ← pieces.mapM (fun exp => consImpl exp)
      logInfo m!"refined {fedPieces}"
      let unchanged ← pieces.mapM (fun exp =>
          do 
          let fed ← consImpl exp
          return exp == fed
      )      
      logInfo m!"equal? {unchanged}"
      let lamPieces ← pieces.mapM (fun exp => lamImpl exp)
      logInfo m!"lambda {lamPieces}"
      let lamTypes ←  lamPieces.mapM (fun x => inferType x)
      logInfo m!"lambdaTypes {lamTypes}"
      liftMetaTactic $ fun mvar =>  (addSingsToContextM  lamPieces mvar).run' 
      return ()

set_option pp.all true

def transitPf {α : Type}:{a b c : α} → 
          a = b → b = c → a = c := by
          intros a b c eq1 eq2
          exppieces
          let p := pieceB.value
          let pg := pieceG.value 
          rw [eq2] at eq1
          exact eq1