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

partial def lambdaImplicits  (e  : Expr) (makeExplicit : Bool) : 
          MetaM Expr := do
  let eType ← inferType e
  let eType ← whnfCore eType
  match eType with
  | Expr.forallE n d b c =>
    let bind := if makeExplicit then BinderInfo.default else c.binderInfo 
    if c.binderInfo.isImplicit || c.binderInfo.isStrictImplicit then
      withLocalDecl Name.anonymous bind d  $ fun x => 
        do
          let prev ← lambdaImplicits (mkApp e x)  makeExplicit
          return ←  mkLambdaFVars #[x] prev
    else if c.binderInfo.isInstImplicit then
      withLocalDecl Name.anonymous bind d  $ fun x => 
        do
          let prev ← lambdaImplicits (mkApp e x)  makeExplicit
          return ←  mkLambdaFVars #[x] prev

    else match d.getOptParamDefault? with
      | some defVal => 
          lambdaImplicits (mkApp e defVal)  makeExplicit
      -- TODO: we do not handle autoParams here.
      | _ => pure e
  | _ => pure e

#check @Prod.mk

def three3 := PProd.mk "three" 3

#check three3

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

syntax (name:= checkmeta) "checkMeta!" : term
@[termElab checkmeta] def chkmImpl : TermElab :=
  fun _ _ => return ← checkProdMeta

def chk : Nat := checkMeta!

#eval chk

#eval checkProdMeta

def getFnsAux : Expr → List Expr → List Expr
  | Expr.app f a _, l  => getFnsAux f (f :: a :: l) 
  | e, l => e :: l

def getFnsArgs : Expr → MetaM (List Expr)
  | Expr.app f a _ => 
    do 
      let ft ← inferType f
      let expl := ft.data.binderInfo.isExplicit
      if expl then
      (←  getFnsArgs f) ++ (← getFnsArgs a) ++ [f, a]
      else [f]
  | e => try 
         do  [← lambdaImplicits e true]
        catch _ => []

def consImpl (e: Expr) : TermElabM Expr := do
  let eType ← inferType e
  let (e, eType) ← consumeImplicits e eType true
  return e

def lamImpl (e: Expr) (mkExplicit : Bool) : TermElabM Expr := do
  let e ← lambdaImplicits e  mkExplicit
  return e


inductive Θ {α : Type u}: α →  Type u where
  | mk :  (a : α) → Θ  a
  
def Θ.value {α : Type u}{a: α} : Θ a → α 
  | Θ.mk a => a

theorem Θ.value.eq {α : Type u}{a: α} : 
    ∀ (s : Θ a), Θ.value s = a := 
            by intro s; cases s; rfl 

initialize xxx : IO.Ref (Nat) ← IO.mkRef 0

#check xxx

def getX : IO Nat :=
  do
    let ref ← xxx
    return ← ref.get

def incX : IO Nat :=
  do
    let ref ← xxx
    let value ← ref.get
    ref.set (value + 1)
    return value

def getXRef (ref: IO.Ref Nat) : IO Nat :=
  do
    return ← ref.get

def incXRef(ref: IO.Ref Nat) : IO Nat :=
  do
    let value ← ref.get
    ref.set (value + 1)
    return value

#check getX


-- def incTask : IO Unit  :=
--   do 
--     let tsk := IO.asTask (dbgSleep 600 $ fun _ => incX)
--     tsk.map (fun _ => ())
--     return ()

-- #check incTask



def update (snap: IO Nat) : IO Unit :=
  do
    let ref ← xxx
    let value ← snap
    ref.set value
    return ()

syntax (name:= snapmem) "snap!" : tactic
@[tactic snapmem] def snapImpl : Tactic :=
  fun stx =>
    liftMetaTactic $ fun mvar => do
      let value ← getX
      assignExprMVar mvar (ToExpr.toExpr value)
      return [] 

syntax (name:= nrmlform)"whnf!" term : term
@[termElab nrmlform] def normalformImpl : TermElab :=
  fun stx expectedType? =>
  match stx with
  | `(whnf! $s) => 
      do
        let t ← Term.elabTerm s none 
        let e ← whnf t
        logInfo m!"whnf : {e}"
        return e
  | _ => Lean.Elab.throwIllFormedSyntax

-- expanded form of initialize
def initFn: IO (IO.Ref Nat) := do ← IO.mkRef 0
@[init initFn] constant yyy : IO.Ref Nat

def pad (s: String)(n: Nat) : String :=
  match n with
  | 0 => s
  | m + 1 => s ++ ⟨Char.ofNat (64 + n) :: []⟩

def addSingletonsToContextM (values : List Expr) : 
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
              let expr ←  mkAppM `Θ.mk #[h]
              some expr
            catch _ => none
          match exprOpt with
          | some expr =>
            let n := values.length
            let name := Name.mkSimple (pad "piece" n)
            let newMVarIds ← addToContextM name (← inferType expr) expr m
            addSingletonsToContextM t newMVarIds.head!
          | none => 
            addSingletonsToContextM t m

syntax (name:= exppieces) "exppieces" : tactic
@[tactic exppieces] def exppiecesImp : Tactic :=
  fun stx =>
    withMainContext
    do
      let e ← getMainTarget 
      let eType ← inferType e
      let e ← instantiateMVars e
      let pieces ← (← getFnsArgs e).eraseDups
      logInfo m!"got {pieces}"
      let fedPieces ← pieces.mapM (fun exp => consImpl exp)
      logInfo m!"refined {fedPieces}"
      let repieces ← pieces.mapM (fun exp => do whnf (← instantiateMVars exp))
      logInfo m!"rebuilt {repieces}"
      let h := fedPieces.head!
      let comp ← fedPieces.mapM (fun e => isDefEq h e)
      logInfo m!"compare {comp}"
      logInfo m!"post compare: {← fedPieces.mapM (fun e => whnf e)}"
      let unchanged ← pieces.mapM (fun exp =>
          do 
          let fed ← consImpl exp
          return exp == fed
      )      
      logInfo m!"equal? {unchanged}"
      let lamPieces ← pieces.mapM (fun exp => lamImpl exp true)
      let lamImplPieces ← pieces.mapM (fun exp => lamImpl exp false)
      logInfo m!"lambda {lamPieces}"
      let lamTypes ←  lamPieces.mapM (fun x => inferType x)
      logInfo m!"lambdaTypes {lamTypes}"
      liftMetaTactic $ fun mvar =>  
        (addSingletonsToContextM  (lamImplPieces ++ lamPieces) mvar).run' 
      return ()

-- set_option pp.all true

def transitPf {α : Type}:{a b c : α} → 
          a = b → b = c → a = c := by
          intros a b c eq1 eq2
          exppieces
          let p := pieceA.value
          let pg := pieceG.value
          have h1 : p  = @Eq α a  := by 
              apply Θ.value.eq
          rw [eq2] at eq1
          exact eq1

variable {M: Type u}[Mul M]

-- example : (∀ a b : M, (a * b) * b = a) → (∀ a b : M, a * (a * b) = b) →
--             (m n : M) →  (m * n) = n * m := by
--             intros eq1 eq2 m n
--             exppieces
--             exact sorry
            

#check @HMul.hMul Nat Nat Nat (inferInstance)

def op : Type := Nat → Nat → Nat 

#check Eq