import Lean.Meta
import Lean.Elab
open Lean.Core
open Lean.Meta
open Lean.Elab.Term
open Lean

-- experiments with syntax
-- expressions for numbers
-- function application

def syntaxPreProcess (stx: Syntax) : MacroM Syntax :=
  match stx with
  | `(this! $s) =>  `(- $s)
  | `($s $t) =>   `($t $s)
  | s => s

open Nat

def natExpr : Nat → Expr 
  | zero => mkConst `Nat.zero
  | succ k => mkApp (mkConst `Nat.succ) (natExpr k)

#eval natExpr 3

partial def exprNat : Expr → MetaM Nat := fun expr => 
  do
    let mvar ←  mkFreshExprMVar (some (mkConst ``Nat))
    let sExp := mkApp (mkConst `Nat.succ) mvar
    if ← isDefEq sExp expr then
      let prev ← exprNat mvar
      return succ (succ prev)
    else 
      return zero

#check exprNat (natExpr 3)
#eval exprNat (natExpr 3)
#eval exprNat (ToExpr.toExpr 3)

def m30 := exprNat (natExpr 30)
#check m30
#eval m30

syntax (name := tryapp) term ">>>>>" term : term

@[termElab tryapp] def tryappImpl3 : TermElab :=
fun stx expectedType? =>
  match stx with
  | `($s >>>>> $t) =>
    do
      let f <- elabTerm s none
      let x <- elabTerm t none
      let expr ← elabAppArgs f #[] #[Arg.expr x] expectedType? (explicit := false) (ellipsis := false)
      return expr
  | _ => Elab.throwIllFormedSyntax
    

def applyOptM2 (f x : Expr) : TermElabM (Option Expr) :=
  do
    try
      let expr ← elabAppArgs f #[] #[Arg.expr x] none (explicit := false) (ellipsis := false)
      return some expr
    catch e =>
      return none

#check Nat.succ >>>>> Nat.zero
#check Nat.succ >>>>> Nat.succ >>>>> Nat.zero
def one := Nat.succ >>>>> Nat.zero
#eval one

def self {α : Type}(a: α ) : α  := a

#eval self Nat.zero


def selfAppM : MetaM Expr :=
  do
    let e ← mkAppM' (mkConst `self) #[mkConst `Nat.zero]
    return e

#eval selfAppM -- checking if implicit variables are working

#check self >>>>> Nat.zero 
#eval self >>>>> Nat.zero


syntax (name := selfm) "self!" term : term

@[termElab selfm] def selfImpl : TermElab :=
  fun stx expectedType? =>  do
  match stx with
  | `(self! $t) =>
    let e ← elabTerm t none
    return e
  | _ => Elab.throwIllFormedSyntax

#eval self! Nat.zero

#check self! self

def qN : Quote Nat := inferInstance

def toExpN : ToExpr Nat := inferInstance

def toExprLN: ToExpr (List Nat) := inferInstance

#check ToExpr.toExpr 3

#check List.append
open List

def listSums : List Nat  → List Nat :=
  fun l =>
    List.bind l (fun x => l.map (fun y => x + y))

#eval listSums [1, 2, 4]

def listSumEv (init: List Nat)(ev: List Nat → List Nat) : List Nat :=
  listSums (ev init)

def isleEv (init: List Nat)(ev: List Nat → List Nat) : List Nat :=
  let inIsle := (ev (init.map (. + 1)))  
  inIsle.map (. * 5)

def evolve (depth: Nat)(init: List Nat) : List Nat :=
  match depth with
  |0 => init
  | m + 1 => List.append (listSumEv (init) (evolve m))  (isleEv (init) (evolve m))

#eval evolve 1 [1, 4]
#eval (evolve 1 [2, 5]).map (fun x => x  * 5)
#eval evolve 2 [1,  4]

def listAppArgs2 : Expr → List Expr → TermElabM (List Expr) :=
  fun f args =>
    match args with
    | [] => return []
    | x :: ys => 
      do
        let head ← applyOptM2 f x
        let tail ← listAppArgs2 f ys
        match head with
        | some expr => return expr :: tail
        | none => return tail

def listApps : List Expr →  List Expr  → TermElabM (List Expr)  := fun l args =>
  match l with
  | [] => return []
  | x :: ys => 
    do
      let head ← listAppArgs2 x args
      let tail ← listApps ys args
      return head ++ tail

def doubleFn: Nat→ Nat := fun x => x + x

def expList := [natExpr 1,  natExpr 3, Lean.mkConst `Nat.succ, Lean.mkConst `Nat.zero, 
              Lean.mkConst `doubleFn]

def evListEg2 := listApps expList expList

#eval evListEg2

#check Unit.unit

#check Prod

def mkProdFn {α β : Type} (a: α ) (b: β) : Prod α β := ⟨a, b⟩

def foldExps2 : List Expr → TermElabM Expr  
  | [] => return (mkConst `Unit.unit)
  | x :: ys => 
    do
      let tail ← foldExps2 ys
      let exp ← 
        mkAppM `Prod.mk  #[x, tail]
        -- elabAppArgs 
        -- (Lean.mkConst `List.cons) #[] #[Arg.expr x, Arg.expr tail] none 
        --   (explicit := false) (ellipsis := false)
      return exp

def listAppExp : List Expr → List Expr → TermElabM Expr := fun l args =>
  do
    let ls ← listApps l args
    let exp ← foldExps2 ls
    return exp

def evListExpEg := listAppExp expList expList

#check @List.cons

#eval foldExps2 []

#eval evListExpEg

syntax (name:= egl) "egl!" : term 

@[termElab egl] def eglImpl : TermElab :=
  fun stx expectedType? =>  evListExpEg

#eval egl!
#check egl!

syntax (name:= appevsyn) "appev!" term,* ";" : term

partial def traverseList : List (TermElabM Expr) → TermElabM (List Expr) :=
        fun l =>
          do
            let lst ← l
            match lst with
            | [] => return []
            | x :: ys => 
              let tail ← traverseList ys
              let head ← x
              return head :: tail

@[termElab appevsyn] def appevsynImpl : TermElab :=
  fun stx expectedType? =>  do
  match stx with
  | `(appev! ;) => 
    do
      let exp ← listAppExp [] []
      return exp
  | `(appev! $s;) => 
    do
      let exp ← elabTerm s none
      let exp ← listAppExp expList [exp]
      return exp
  | `(appev! $s, $ts;) => 
    do
      let tailSyn : Syntax ← `(appev! $ts;)
      let exp ← elabTerm s none
      let exp ← listAppExp expList [exp]
      return exp
  | _ => Elab.throwIllFormedSyntax

set_option pp.rawOnError true

def appevsynEg := appev! 5, 6;

#eval appevsynEg

constant f : Nat → Nat

open Lean.Elab.Command

def ml0 : MonadLiftT IO CommandElabM := inferInstance

def ml1 : MonadLiftT MetaM TermElabM := inferInstance

def ml2 : MonadControlT MetaM TermElabM := inferInstance

#print ml1


#eval 3.14 < 3

#eval 12 * 12 * 12