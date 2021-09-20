import Lean.Meta
import Lean.Elab
open Lean.Core
open Lean.Meta
open Lean.Elab.Term
open Lean

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

def m30 := exprNat (natExpr 30)
#check m30
#eval m30

syntax (name := tryapp) term ">>>>>" term : term

@[termElab tryapp] def tryappImpl : TermElab :=
fun stx expectedType? =>
  match stx with
  | `($s >>>>> $t) =>
    do
      let f <- elabTerm s none
      let x <- elabTerm t none
      let expr ← elabAppArgs f #[] #[Arg.expr x] expectedType? (explicit := false) (ellipsis := false)
      return expr
  | _ => Elab.throwIllFormedSyntax


#check Nat.succ >>>>> Nat.zero
def one := Nat.succ >>>>> Nat.zero
#eval one

def self {α : Type}(a: α ) : α  := a

#eval self Nat.zero


def selfAppM : MetaM Expr :=
  do
    let e ← mkAppM' (mkConst `self) #[mkConst `Nat.zero]
    return e

#eval selfAppM

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

